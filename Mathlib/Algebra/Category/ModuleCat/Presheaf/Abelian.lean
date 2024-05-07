import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.CategoryTheory.Abelian.Basic

universe v v₁ u₁ u

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

instance : Abelian (PresheafOfModules.{v} R) := sorry

end PresheafOfModules
