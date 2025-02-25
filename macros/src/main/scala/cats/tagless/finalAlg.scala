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

import scala.annotation.{StaticAnnotation, compileTimeOnly}
import scala.reflect.macros.whitebox

@compileTimeOnly("Cannot expand @finalAlg")
class finalAlg extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro finalAlgMacros.inst
}

private[tagless] class finalAlgMacros(override val c: whitebox.Context) extends MacroUtils {
  import c.universe._

  private def generateApply(algebraType: Tree, tparams: _root_.scala.collection.immutable.Seq[TypeDef]) =
    q"def apply[..$tparams](implicit inst: $algebraType): $algebraType = inst"

  def inst(annottees: c.Tree*): c.Tree =
    enrichAlgebra(annottees.toList, AlgebraResolver.AnyLastTypeParam)(algebra =>
      algebra.forAlgebraType(generateApply) :: Nil
    )

}
