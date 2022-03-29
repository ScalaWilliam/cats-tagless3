/*
 * Copyright 2019 cats-tagless maintainers
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package cats.tagless

import cats.arrow.Profunctor
import cats.data.{ReaderT, Tuple2K}
import cats.tagless.aop.{Aspect, Instrument, Instrumentation}
import cats.{Bifunctor, Contravariant, FlatMap, Functor, Invariant, Semigroupal}

import scala.reflect.macros.blackbox

class DeriveMacros(val c: blackbox.Context) {
  import c.internal._
  import c.universe._

  /** A reified parameter definition with some useful methods for transforming it. */
  case class Parameter(name: TermName, signature: Type, modifiers: Modifiers) {
    def displayName: String = name.decodedName.toString
  }

  /** A reified method definition with some useful methods for transforming it. */
  case class Method(
      name: TermName,
      signature: Type,
      typeParams: List[TypeDef],
      paramLists: List[List[ValDef]],
      returnType: Type,
      body: Tree
  ) {

    def displayName: String = name.decodedName.toString
    def occursInSignature(symbol: Symbol): Boolean = occursIn(signature)(symbol)
    def occursInReturn(symbol: Symbol): Boolean = occursIn(returnType)(symbol)

    def occursOnlyInReturn(symbol: Symbol): Boolean =
      occursInReturn(symbol) && !signature.paramLists.iterator.flatten.exists(p => occursIn(p.info)(symbol))

    /** Construct a new set of parameter lists after substituting some type symbols. */
    def transformedParamLists(types: PartialFunction[Type, Type]): List[List[ValDef]] =
      for (ps <- paramLists) yield for (p <- ps) yield {
        val oldType = p.tpt.tpe
        val newType = types.applyOrElse(oldType, identity[Type])
        if (newType == oldType) p else ValDef(p.mods, p.name, TypeTree(newType), p.rhs)
      }

    /** Construct a new set of argument lists based on their name and type. */
    def transformedArgLists(f: PartialFunction[Parameter, Tree] = PartialFunction.empty): List[List[Tree]] = {
      def id(param: Parameter): Tree = Ident(param.name)

      val f_* : Parameter => Tree = {
        case Parameter(pn, RepeatedParam(pt), pm) =>
          q"${f.andThen(arg => q"for ($pn <- $pn) yield $arg").applyOrElse(Parameter(pn, pt, pm), id)}: _*"
        case Parameter(pn, ByNameParam(pt), pm) =>
          f.applyOrElse(Parameter(pn, pt, pm), id)
        case param =>
          f.applyOrElse(param, id)
      }

      for (ps <- paramLists)
        yield for (p <- ps)
          yield f_*(Parameter(p.name, p.tpt.tpe, p.mods))
    }

    /** Transform this method into another by applying transformations to types, arguments and body. */
    def transform(instance: Tree)(types: PartialFunction[Type, Type] = PartialFunction.empty)(
        argLists: PartialFunction[Parameter, Tree] = PartialFunction.empty
    )(body: PartialFunction[Tree, Tree] = PartialFunction.empty): Method = copy(
      paramLists = transformedParamLists(types),
      returnType = types.applyOrElse(returnType, identity[Type]),
      body = body.applyOrElse(delegate(instance, transformedArgLists(argLists)), identity[Tree])
    )

    /** Transform this method into another by applying substitution to types and transformations to arguments / body. */
    def transformSubst(instance: Symbol, types: (Symbol, Symbol)*)(
        argLists: PartialFunction[Parameter, Tree]
    )(body: PartialFunction[Tree, Tree]): Method = {
      val (from, to) = types.toList.unzip
      transform(Ident(instance)) { case tpe => tpe.substituteSymbols(from, to) }(argLists)(body)
    }

    /** Delegate this method to an existing instance, optionally providing different argument lists. */
    def delegate(to: Tree, argLists: List[List[Tree]] = transformedArgLists()): Tree = {
      val typeArgs = for (tp <- typeParams) yield typeRef(NoPrefix, tp.symbol, Nil)
      q"$to.$name[..$typeArgs](...$argLists)"
    }

    /** The definition of this method as a Scala tree. */
    def definition: Tree = q"override def $name[..$typeParams](...$paramLists): $returnType = $body"

    /** Summon an implicit instance of `A`'s type constructor applied to `typeArgs` if one exists in scope. */
    def summon[A: TypeTag](typeArgs: Type*): Tree = {
      val tpe = appliedType(typeOf[A].typeConstructor, typeArgs: _*)
      c.inferImplicitValue(tpe).orElse(abort(s"could not find implicit value of type $tpe in method $displayName"))
    }
  }

  case class MethodDef(name: String, rhs: Type => Option[Tree])
  object MethodDef {
    def apply(name: String)(rhs: PartialFunction[Type, Tree]): MethodDef = apply(name, rhs.lift)
  }

  final class ParamExtractor(symbol: Symbol) {
    def apply(tpe: Type): Type = appliedType(symbol, tpe)
    def unapply(tpe: Type): Option[Type] = if (tpe.typeSymbol == symbol) Some(tpe.typeArgs.head) else None
  }

  /** Constructor / extractor for repeated parameter (aka. vararg) types. */
  val RepeatedParam = new ParamExtractor(definitions.RepeatedParamClass)

  /** Constructor / extractor for by-name parameter types. */
  val ByNameParam = new ParamExtractor(definitions.ByNameParamClass)

  /** Return the dealiased and eta-expanded type constructor of this tag's type. */
  def typeConstructorOf(tag: WeakTypeTag[_]): Type =
    tag.tpe.typeConstructor.dealias.etaExpand

  /** Return the set of overridable members of `tpe`, excluding some undesired cases. */
  // TODO: Figure out what to do about different visibility modifiers.
  def overridableMembersOf(tpe: Type): Iterable[Symbol] = {
    import definitions._
    val exclude = Set[Symbol](AnyClass, AnyRefClass, AnyValClass, ObjectClass)
    tpe.members.filterNot(m =>
      m.isConstructor || m.isFinal || m.isImplementationArtifact || m.isSynthetic || exclude(m.owner)
    )
  }

  /** Temporarily refresh type parameter names, type-check the `tree` and restore the original names.
    *
    * The purpose is to avoid warnings about type parameter shadowing, which can be problematic when `-Xfatal-warnings`
    * is enabled. We know the warnings are harmless because we deal with types directly. Unfortunately
    * `c.typecheck(tree, silent = true)` does not suppress warnings.
    */
  def typeCheckWithFreshTypeParams(tree: Tree): Tree = {
    val typeParams = tree.collect { case method: DefDef =>
      method.tparams.map(_.symbol)
    }.flatten

    val originalNames = for (tp <- typeParams) yield {
      val original = tp.name.toTypeName
      setName(tp, c.freshName(TypeName(original.toString)))
      original
    }

    val typed = c.typecheck(tree)
    for ((tp, original) <- typeParams.zip(originalNames)) setName(tp, original)
    typed
  }

  /** Abort with a message at the current compiler position. */
  def abort(message: String): Nothing = c.abort(c.enclosingPosition, message)

  /** `tpe.contains` is broken before Scala 2.13. See scala/scala#6122. */
  def occursIn(tpe: Type)(symbol: Symbol): Boolean = tpe.exists(_.typeSymbol == symbol)

  /** Does the given `symbol` have a specified `flag` as modifier? */
  def hasFlag(symbol: Symbol)(flag: FlagSet): Boolean = {
    val flagSet = flags(symbol)
    (flagSet | flag) == flagSet
  }

  /** Delegate the definition of type members and aliases in `algebra`. */
  def delegateTypes(algebra: Type, members: Iterable[Symbol])(rhs: (TypeSymbol, List[Type]) => Type): Iterable[Tree] =
    for (member <- members if member.isType) yield {
      val tpe = member.asType
      val signature = tpe.typeSignatureIn(algebra)
      val typeParams = for (t <- signature.typeParams) yield typeDef(t)
      val typeArgs = for (t <- signature.typeParams) yield typeRef(NoPrefix, t, Nil)
      q"type ${tpe.name}[..$typeParams] = ${rhs(tpe, typeArgs)}"
    }

  /** Delegate the definition of abstract type members and aliases in `algebra` to an existing `instance`. */
  def delegateAbstractTypes(algebra: Type, members: Iterable[Symbol], instance: Type): Iterable[Tree] =
    delegateTypes(algebra, members.filter(_.isAbstract))((tpe, typeArgs) => typeRef(instance, tpe, typeArgs))

  /** Delegate the definition of methods in `algebra` to an existing `instance`. */
  def delegateMethods(algebra: Type, members: Iterable[Symbol], instance: Symbol)(
      transform: PartialFunction[Method, Method]
  ): Iterable[Tree] = for (member <- members if member.isMethod && !member.asMethod.isAccessor) yield {
    val name = member.name.toTermName
    val signature = member.typeSignatureIn(algebra)
    val typeParams = for (tp <- signature.typeParams) yield typeDef(tp)
    val typeArgs = for (tp <- signature.typeParams) yield typeRef(NoPrefix, tp, Nil)
    val paramLists = for (ps <- signature.paramLists) yield for (p <- ps) yield {
      // Only preserve the by-name and implicit modifiers (e.g. drop the default parameter flag).
      val flags = List(Flag.BYNAMEPARAM, Flag.IMPLICIT).filter(hasFlag(p))
      val modifiers = Modifiers(flags.foldLeft(Flag.PARAM)(_ | _))
      ValDef(modifiers, p.name.toTermName, TypeTree(p.typeSignatureIn(algebra)), EmptyTree)
    }

    val argLists = for (ps <- signature.paramLists) yield for (p <- ps) yield p.typeSignatureIn(algebra) match {
      case RepeatedParam(_) => q"${p.name.toTermName}: _*"
      case _ => Ident(p.name)
    }

    val body = q"$instance.$name[..$typeArgs](...$argLists)"
    val reified = Method(name, signature, typeParams, paramLists, signature.finalResultType, body)
    transform.applyOrElse(reified, identity[Method]).definition
  }

  /** Type-check a definition of type `instance` with stubbed methods to gain more type information. */
  def declare(instance: Type): Tree = {
    val members = overridableMembersOf(instance).filter(_.isAbstract)
    val stubs = delegateMethods(instance, members, NoSymbol) { case m => m.copy(body = q"_root_.scala.Predef.???") }
    val Block(List(declaration), _) = typeCheckWithFreshTypeParams(q"new $instance { ..$stubs }"): @unchecked
    declaration
  }

  /** Implement a possibly refined `algebra` with the provided `members`. */
  def implement(algebra: Type)(typeArgs: Symbol*)(members: Iterable[Tree]): Tree = {
    // If `members.isEmpty` we need an extra statement to ensure the generation of an anonymous class.
    val nonEmptyMembers = if (members.isEmpty) q"()" :: Nil else members
    val applied = appliedType(algebra, typeArgs.toList.map(_.asType.toTypeConstructor))

    applied match {
      case RefinedType(parents, scope) =>
        val refinements = delegateTypes(applied, scope.filterNot(_.isAbstract)) { (tpe, _) =>
          tpe.typeSignatureIn(applied).resultType
        }

        q"new ..$parents { ..$refinements; ..$nonEmptyMembers }"
      case _ =>
        q"new $applied { ..$nonEmptyMembers }"
    }
  }

  /** Create a new instance of `typeClass` for `algebra`. `rhs` should define a mapping for each method (by name) to an
    * implementation function based on type signature.
    */
  def instantiate[T: WeakTypeTag](tag: WeakTypeTag[_], typeArgs: Type*)(methods: (Type => MethodDef)*): Tree = {
    val algebra = typeConstructorOf(tag)
    val Ta = appliedType(symbolOf[T], algebra :: typeArgs.toList)
    val rhsMap = methods.iterator.map(_.apply(algebra)).flatMap(MethodDef.unapply).toMap
    val declaration @ ClassDef(_, _, _, Template(parents, self, members)) = declare(Ta): @unchecked
    val implementations = members.map {
      case member: DefDef =>
        val method = member.symbol.asMethod
        val impl = for {
          rhsOf <- rhsMap.get(method.name.toString)
          rhs <- rhsOf(method.typeSignatureIn(Ta))
        } yield defDef(method, rhs)
        impl.getOrElse(member)
      case member => member
    }

    val definition = classDef(declaration.symbol, Template(parents, self, implementations))
    typeCheckWithFreshTypeParams(q"{ $definition; new ${declaration.symbol} }")
  }

  // def map[A, B](fa: F[A])(f: A => B): F[B]
  def map(algebra: Type): MethodDef = MethodDef("map") {
    case PolyType(List(a, b), MethodType(List(fa), MethodType(List(f), _))) =>
      val Fa = singleType(NoPrefix, fa)
      val members = overridableMembersOf(Fa)
      val types = delegateAbstractTypes(Fa, members, Fa)
      val methods = delegateMethods(Fa, members, fa) {
        case method if method.occursInSignature(a) =>
          method.transformSubst(fa, a -> b) {
            case Parameter(pn, pt, _) if occursIn(pt)(a) =>
              val F = method.summon[Contravariant[Any]](polyType(a :: Nil, pt))
              q"$F.contramap[$b, $a]($pn)($f)"
          } {
            case delegate if method.occursInReturn(a) =>
              val F = method.summon[Functor[Any]](polyType(a :: Nil, method.returnType))
              q"$F.map[$a, $b]($delegate)($f)"
          }
      }

      implement(algebra)(b)(types ++ methods)
  }

//  def void[Alg[_[_]]](implicit tag: WeakTypeTag[Alg[Any]]): Tree =
//    const[Alg, Unit](q"()")

//  def readerT[Alg[_[_]], F[_]](implicit tag: WeakTypeTag[Alg[Any]], fTag: WeakTypeTag[F[Any]]): Tree = {
//    val algebra = typeConstructorOf(tag)
//    val F = typeConstructorOf(fTag)
//    val f = F.typeSymbol
//    val Af = appliedType(algebra, F)
//    val af = c.freshName(TermName("af"))
//    val ReaderT = typeOf[ReaderT[Any, Any, Any]].typeConstructor
//    val abstractMembers = overridableMembersOf(Af).filter(_.isAbstract)
//    val methods = delegateMethods(Af, abstractMembers, NoSymbol) {
//      case method if method.returnType.typeSymbol == f =>
//        method.transform(q"$af") {
//          case tpe if tpe.typeSymbol == f =>
//            appliedType(ReaderT, F :: Af :: tpe.typeArgs)
//        } {
//          case Parameter(pn, pt, _) if pt.typeSymbol == f =>
//            q"$pn.run($af)"
//        } { case delegate =>
//          val typeArgs = F :: Af :: method.returnType.typeArgs
//          q"${reify(cats.data.ReaderT)}[..$typeArgs](($af: $Af) => $delegate)"
//        }
//      case method =>
//        abort(s"Abstract method ${method.displayName} cannot be derived because it does not return in $F")
//    }
//
//    val b = ReaderT.typeParams.last.asType
//    val typeArg = polyType(b :: Nil, appliedType(ReaderT, F, Af, b.toType))
//    implement(appliedType(algebra, typeArg))()(methods)
//  }
//
//  def functor[F[_]](implicit tag: WeakTypeTag[F[Any]]): Tree =
//    instantiate[Functor[F]](tag)(map)
//
//  def contravariant[F[_]](implicit tag: WeakTypeTag[F[Any]]): Tree =
//    instantiate[Contravariant[F]](tag)(contramap)
//
//  def invariant[F[_]](implicit tag: WeakTypeTag[F[Any]]): Tree =
//    instantiate[Invariant[F]](tag)(imap)
//
//  def profunctor[F[_, _]](implicit tag: WeakTypeTag[F[Any, Any]]): Tree =
//    instantiate[Profunctor[F]](tag)(dimap)
//
//  def bifunctor[F[_, _]](implicit tag: WeakTypeTag[F[Any, Any]]): Tree =
//    instantiate[Bifunctor[F]](tag)(bimap)
//
//  def semigroupal[F[_]](implicit tag: WeakTypeTag[F[Any]]): Tree =
//    instantiate[Semigroupal[F]](tag)(product)
//
//  def apply[F[_]](implicit tag: WeakTypeTag[F[Any]]): Tree =
//    instantiate[cats.Apply[F]](tag)(map, ap)
//
//  def flatMap[F[_]](implicit tag: WeakTypeTag[F[Any]]): Tree =
//    instantiate[FlatMap[F]](tag)(map, flatMap_, tailRecM)
//
//  def functorK[Alg[_[_]]](implicit tag: WeakTypeTag[Alg[Any]]): Tree =
//    instantiate[FunctorK[Alg]](tag)(mapK)
//
//  def contravariantK[Alg[_[_]]](implicit tag: WeakTypeTag[Alg[Any]]): Tree =
//    instantiate[ContravariantK[Alg]](tag)(contramapK)
//
//  def invariantK[Alg[_[_]]](implicit tag: WeakTypeTag[Alg[Any]]): Tree =
//    instantiate[InvariantK[Alg]](tag)(imapK)
//
//  def semigroupalK[Alg[_[_]]](implicit tag: WeakTypeTag[Alg[Any]]): Tree =
//    instantiate[SemigroupalK[Alg]](tag)(productK)
//
//  def applyK[Alg[_[_]]](implicit tag: WeakTypeTag[Alg[Any]]): Tree =
//    instantiate[ApplyK[Alg]](tag)(mapK, productK)
//
//  def instrument[Alg[_[_]]](implicit tag: WeakTypeTag[Alg[Any]]): Tree =
//    instantiate[Instrument[Alg]](tag)(instrumentation, mapK)
//
//  def aspect[Alg[_[_]], Dom[_], Cod[_]](implicit
//      tag: WeakTypeTag[Alg[Any]],
//      dom: WeakTypeTag[Dom[Any]],
//      cod: WeakTypeTag[Cod[Any]]
//  ): Tree = {
//    val Dom = typeConstructorOf(dom)
//    val Cod = typeConstructorOf(cod)
//    instantiate[Aspect[Alg, Dom, Cod]](tag, Dom, Cod)(weave(Dom, Cod), mapK)
//  }
}
