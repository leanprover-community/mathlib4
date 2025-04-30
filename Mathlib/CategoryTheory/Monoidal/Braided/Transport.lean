import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Monoidal MonoidalCategory

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Monoidal

instance (e : C ≌ D) [MonoidalCategory.{v₁} C] [BraidedCategory C] :
    BraidedCategory (Transported e) :=
  braidedCategoryOfFullyFaithful (equivalenceTransported e).inverse

instance (e : C ≌ D) [MonoidalCategory.{v₁} C] [SymmetricCategory C] :
    SymmetricCategory (Transported e) :=
  symmetricCategoryOfFullyFaithful (equivalenceTransported e).inverse

instance (e : C ≌ D) [MonoidalCategory.{v₁} C] [SymmetricCategory C] [MonoidalClosed C] :
    MonoidalClosed (Transported e) :=
  Reflective.monoidalClosed (equivalenceTransported e).toAdjunction

end CategoryTheory.Monoidal
