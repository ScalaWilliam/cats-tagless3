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

import cats._
import cats.arrow.FunctionK
import cats.data._
import cats.kernel.CommutativeMonoid

import scala.annotation.implicitNotFound

@implicitNotFound("Could not find an instance of InvariantK for ${Alg}")
trait InvariantK[Alg[_[_]]] extends Serializable {
  def imapK[F[_], G[_]](af: Alg[F])(fk: F ~> G)(gk: G ~> F): Alg[G]
}

object InvariantK extends InvariantKInstances01 {
  implicit def catsTaglessApplyKForEitherK[F[_], A]: ApplyK[[W[_]] =>> EitherK[F, W[_], A]] =
    eitherKInstance.asInstanceOf[ApplyK[[W[_]] =>> EitherK[F, W[_], A]]]

  implicit def catsTaglessApplyKForEitherT[A, B]: ApplyK[[W[_]] =>> EitherT[W[_], A, B]] =
    eitherTInstance.asInstanceOf[ApplyK[[W[_]] =>> EitherT[W[_], A, B]]]

  implicit def catsTaglessApplyKForFunc[A, B]: ApplyK[[W[_]] =>> Func[W[_], A, B]] =
    funcInstance.asInstanceOf[ApplyK[[W[_]] =>> Func[W[_], A, B]]]

  implicit def catsTaglessApplyKForIdT[A]: ApplyK[[W[_]] =>> IdT[W[_], A]] =
    idTInstance.asInstanceOf[ApplyK[[W[_]] =>> IdT[W[_], A]]]

  implicit def catsTaglessApplyKForIorT[A, B]: ApplyK[[W[_]] =>> IorT[W[_], A, B]] =
    iOrTInstance.asInstanceOf[ApplyK[[W[_]] =>> IorT[W[_], A, B]]]

  implicit def catsTaglessApplyKForKleisli[A, B]: ApplyK[[W[_]] =>> Kleisli[W[_], A, B]] =
    kleisliInstance.asInstanceOf[ApplyK[[W[_]] =>> Kleisli[W[_], A, B]]]

  implicit def catsTaglessApplyKForOptionT[A]: ApplyK[[W[_]] =>> OptionT[W[_], A]] =
    optionTInstance.asInstanceOf[ApplyK[[W[_]] =>> OptionT[W[_], A]]]

  implicit def catsTaglessApplyKForWriterT[A, B]: ApplyK[[W[_]] =>> WriterT[W[_], A, B]] =
    writerTInstance.asInstanceOf[ApplyK[[W[_]] =>> WriterT[W[_], A, B]]]

  implicit def catsTaglessContravariantKForCokleisli[A, B]: ContravariantK[[W[_]] =>> Cokleisli[W[_], A, B]] =
    cokleisliInstance.asInstanceOf[ContravariantK[[W[_]] =>> Cokleisli[W[_], A, B]]]

  implicit def catsTaglessFunctorKForNested[G[_], A]: FunctorK[[W[_]] =>> Nested[W[_], G, A]] =
    nestedInstance.asInstanceOf[FunctorK[[W[_]] =>> Nested[W[_], G, A]]]

  implicit def catsTaglessApplyKForOneAnd[A](implicit A: Semigroup[A]): ApplyK[[W[_]] =>> OneAnd[W[_], A]] =
    new ApplyK[[W[_]] =>> OneAnd[W[_], A]] {
      def mapK[F[_], G[_]](af: OneAnd[F, A])(fk: F ~> G) = af.mapK(fk)
      def productK[F[_], G[_]](af: OneAnd[F, A], ag: OneAnd[G, A]) =
        OneAnd(A.combine(af.head, ag.head), Tuple2K(af.tail, ag.tail))
    }

  implicit def catsTaglessApplyKForTuple2K1[H[_], A](implicit H: SemigroupK[H]): ApplyK[[W[_]] =>> Tuple2K[W[_], H, A]] =
    new ApplyK[[W[_]] =>> Tuple2K[W[_], H, A]] {
      def mapK[F[_], G[_]](af: Tuple2K[F, H, A])(fk: F ~> G) = Tuple2K(fk(af.first), af.second)
      def productK[F[_], G[_]](af: Tuple2K[F, H, A], ag: Tuple2K[G, H, A]): Tuple2K[[W] =>> Tuple2K[F, G, W], H, A] =
        Tuple2K(Tuple2K(af.first, ag.first), H.combineK(af.second, ag.second))
    }

  implicit def catsTaglessApplyKForTuple2K2[H[_], A](implicit H: SemigroupK[H]): ApplyK[[W[_]] =>> Tuple2K[H, W[_], A]] =
    new ApplyK[[W[_]] =>> Tuple2K[H, W[_], A]] {
      def mapK[F[_], G[_]](af: Tuple2K[H, F, A])(fk: F ~> G) = af.mapK(fk)
      def productK[F[_], G[_]](af: Tuple2K[H, F, A], ag: Tuple2K[H, G, A]) =
        Tuple2K(H.combineK(af.first, ag.first), Tuple2K(af.second, ag.second))
    }

  implicit def catsTaglessContravariantForKFunctionK[G[_]]: ContravariantK[[W[_]] =>> FunctionK[W[_], G]] =
    functionKContravariantK.asInstanceOf[ContravariantK[[W[_]] =>> FunctionK[W[_], G]]]

  implicit def catsTaglessFunctorKForFunctionK[F[_]]: FunctorK[[W[_]] =>> FunctionK[F, W[_]]] =
    functionKFunctorK.asInstanceOf[FunctorK[[W[_]] =>> FunctionK[F, W[_]]]]

  implicit def catsTaglessContravariantKForFoldable: ContravariantK[Foldable] =
    new ContravariantK[Foldable] {
      override def contramapK[F[_], G[_]](af: Foldable[F])(gf: G ~> F): Foldable[G] =
        new ContraFoldable[F, G] { val F = af; val from = gf }
    }

  implicit def catsTaglessContravariantKForUnorderedFoldable: ContravariantK[UnorderedFoldable] =
    new ContravariantK[UnorderedFoldable] {
      override def contramapK[F[_], G[_]](af: UnorderedFoldable[F])(gf: G ~> F): UnorderedFoldable[G] =
        new ContraUnorderedFoldable[F, G] { val F = af; val from = gf }
    }

  private val eitherKInstance: ApplyK[[W[_]] =>> EitherK[[_] =>> Any, W[_], Any]] = new ApplyK[[W[_]] =>> EitherK[[_] =>> Any, W[_], Any]] {
    def mapK[F[_], G[_]](af: EitherK[[_] =>> Any, F, Any])(fk: F ~> G) = af.mapK(fk)
    def productK[F[_], G[_]](af: EitherK[[_] =>> Any, F, Any], ag: EitherK[[_] =>> Any, G, Any]) =
      (af.run, ag.run) match {
        case (Left(x), _) => EitherK.leftc[[_] =>> Any, [W] =>> Tuple2K[F, G, W], Any](x)
        case (_, Left(y)) => EitherK.leftc[[_] =>> Any, [W] =>> Tuple2K[F, G, W], Any](y)
        case (Right(fa), Right(ga)) => EitherK.rightc[[_] =>> Any, [W] =>> Tuple2K[F, G, W], Any](Tuple2K(fa, ga))
      }
  }

  private val eitherTInstance: ApplyK[[W[_]] =>> EitherT[W[_], Any, Any]] = new ApplyK[[W[_]] =>> EitherT[W[_], Any, Any]] {
    def mapK[F[_], G[_]](af: EitherT[F, Any, Any])(fk: F ~> G) = af.mapK(fk)
    def productK[F[_], G[_]](af: EitherT[F, Any, Any], ag: EitherT[G, Any, Any]) =
      EitherT(Tuple2K(af.value, ag.value))
  }

  private val funcInstance: ApplyK[[W[_]] =>> Func[W[_], Any, Any]] = new ApplyK[[W[_]] =>> Func[W[_], Any, Any]] {
    def mapK[F[_], G[_]](af: Func[F, Any, Any])(fk: F ~> G) = af.mapK(fk)
    def productK[F[_], G[_]](af: Func[F, Any, Any], ag: Func[G, Any, Any]) =
      Func.func(x => Tuple2K(af.run(x), ag.run(x)))
  }

  private val idTInstance: ApplyK[[W[_]] =>> IdT[W[_], Any]] = new ApplyK[[W[_]] =>> IdT[W[_], Any]] {
    def mapK[F[_], G[_]](af: IdT[F, Any])(fk: F ~> G) = af.mapK(fk)
    def productK[F[_], G[_]](af: IdT[F, Any], ag: IdT[G, Any]) =
      IdT(Tuple2K(af.value, ag.value))
  }

  private val iOrTInstance: ApplyK[[W[_]] =>> IorT[W[_], Any, Any]] = new ApplyK[[W[_]] =>> IorT[W[_], Any, Any]] {
    def mapK[F[_], G[_]](af: IorT[F, Any, Any])(fk: F ~> G) = af.mapK(fk)
    def productK[F[_], G[_]](af: IorT[F, Any, Any], ag: IorT[G, Any, Any]) =
      IorT(Tuple2K(af.value, ag.value))
  }

  private val kleisliInstance: ApplyK[[W[_]] =>> Kleisli[W[_], Any, Any]] = new ApplyK[[W[_]] =>> Kleisli[W[_], Any, Any]] {
    def mapK[F[_], G[_]](af: Kleisli[F, Any, Any])(fk: F ~> G) = af.mapK(fk)
    def productK[F[_], G[_]](af: Kleisli[F, Any, Any], ag: Kleisli[G, Any, Any]) =
      Kleisli(x => Tuple2K(af.run(x), ag.run(x)))
  }

  private val optionTInstance: ApplyK[[W[_]] =>> OptionT[W[_], Any]] = new ApplyK[[W[_]] =>> OptionT[W[_], Any]] {
    def mapK[F[_], G[_]](af: OptionT[F, Any])(fk: F ~> G) = af.mapK(fk)
    def productK[F[_], G[_]](af: OptionT[F, Any], ag: OptionT[G, Any]) =
      OptionT(Tuple2K(af.value, ag.value))
  }

  private val writerTInstance: ApplyK[[W[_]] =>> WriterT[W[_], Any, Any]] = new ApplyK[[W[_]] =>> WriterT[W[_], Any, Any]] {
    def mapK[F[_], G[_]](af: WriterT[F, Any, Any])(fk: F ~> G) = af.mapK(fk)
    def productK[F[_], G[_]](af: WriterT[F, Any, Any], ag: WriterT[G, Any, Any]) =
      WriterT(Tuple2K(af.run, ag.run))
  }

  private val cokleisliInstance: ContravariantK[[W[_]] =>> Cokleisli[W[_], Any, Any]] =
    new ContravariantK[[W[_]] =>> Cokleisli[W[_], Any, Any]] {
      def contramapK[F[_], G[_]](af: Cokleisli[F, Any, Any])(fk: G ~> F) = Cokleisli(ga => af.run(fk(ga)))
    }

  private val nestedInstance: FunctorK[[W[_]] =>> Nested[W[_], [_] =>> Any, Any]] = new FunctorK[[W[_]] =>> Nested[W[_], [_] =>> Any, Any]] {
    def mapK[F[_], G[_]](af: Nested[F, [_] =>> Any, Any])(fk: F ~> G) = af.mapK(fk)
  }

  private val functionKContravariantK: ContravariantK[[W[_]] =>> FunctionK[W[_], ([_] =>> Any)]] =
    new ContravariantK[[W[_]] =>> FunctionK[W[_], ([_] =>> Any)]] {
      def contramapK[F[_], G[_]](af: F ~> ([_] =>> Any))(fk: G ~> F) = af.compose(fk)
    }

  private val functionKFunctorK: FunctorK[[W[_]] =>> FunctionK[[_] =>> Any, W[_]]] =
    new FunctorK[[W[_]] =>> FunctionK[[_] =>> Any, W[_]]] {
      def mapK[F[_], G[_]](af: ([_] =>> Any) ~> F)(fn: F ~> G) = af.andThen(fn)
    }

  // =======================
  // Generated by simulacrum
  // =======================

  @inline def apply[Alg[_[_]]](implicit instance: InvariantK[Alg]): InvariantK[Alg] = instance

  trait AllOps[Alg[_[_]], F[_]] extends Ops[Alg, F] {
    type TypeClassType <: InvariantK[Alg]
    val typeClassInstance: TypeClassType
  }

  object ops {
    implicit def toAllInvariantKOps[Alg[_[_]], F[_]](target: Alg[F])(implicit tc: InvariantK[Alg]): AllOps[Alg, F] {
      type TypeClassType = InvariantK[Alg]
    } = new AllOps[Alg, F] {
      type TypeClassType = InvariantK[Alg]
      val self = target
      val typeClassInstance: TypeClassType = tc
    }
  }

  trait Ops[Alg[_[_]], F[_]] {
    type TypeClassType <: InvariantK[Alg]
    val typeClassInstance: TypeClassType
    def self: Alg[F]
    def imapK[G[_]](fk: F ~> G)(gk: G ~> F): Alg[G] =
      typeClassInstance.imapK[F, G](self)(fk)(gk)
  }

  trait ToInvariantKOps {
    implicit def toInvariantKOps[Alg[_[_]], F[_]](target: Alg[F])(implicit tc: InvariantK[Alg]): Ops[Alg, F] {
      type TypeClassType = InvariantK[Alg]
    } = new Ops[Alg, F] {
      type TypeClassType = InvariantK[Alg]
      val self = target
      val typeClassInstance: TypeClassType = tc
    }
  }

  object nonInheritedOps extends ToInvariantKOps
}

sealed private[tagless] trait InvariantKInstances01 {
  implicit def catsTaglessFunctorKForOneAnd[A]: FunctorK[[W[_]] =>> OneAnd[W[_], A]] =
    oneAndFunctorK.asInstanceOf[FunctorK[[W[_]] =>> OneAnd[W[_], A]]]

  implicit def catsTaglessFunctorKForTuple2K[F[_], A]: FunctorK[[W[_]] =>> Tuple2K[F, W[_], A]] =
    tuple2KFunctorK.asInstanceOf[FunctorK[[W[_]] =>> Tuple2K[F, W[_], A]]]

  private val oneAndFunctorK: FunctorK[[W[_]] =>> OneAnd[W[_], Any]] = new FunctorK[[W[_]] =>> OneAnd[W[_], Any]] {
    def mapK[F[_], G[_]](af: OneAnd[F, Any])(fk: F ~> G) = af.mapK(fk)
  }

  private val tuple2KFunctorK = new FunctorK[[W[_]] =>> Tuple2K[[_] =>> Any, W[_], Any]] {
    def mapK[F[_], G[_]](af: Tuple2K[[_] =>> Any, F, Any])(fk: F ~> G) = af.mapK(fk)
  }
}

private trait ContraUnorderedFoldable[F[_], G[_]] extends UnorderedFoldable[G] {
  def F: UnorderedFoldable[F]
  def from: G ~> F
  final override def unorderedFoldMap[A, B](fa: G[A])(f: A => B)(implicit M: CommutativeMonoid[B]): B =
    F.unorderedFoldMap(from(fa))(f)
}

private trait ContraFoldable[F[_], G[_]] extends Foldable[G] with ContraUnorderedFoldable[F, G] {
  def F: Foldable[F]
  final override def foldLeft[A, B](fa: G[A], b: B)(f: (B, A) => B): B =
    F.foldLeft(from(fa), b)(f)
  final override def foldRight[A, B](fa: G[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
    F.foldRight(from(fa), lb)(f)
}
