import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

universe u u' v v' w w'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesLimits F] [PreservesColimits F]

end CategoryTheory
