import Mathlib.CategoryTheory.Sites.Sheaf

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

variable {C : Type*} [Category C]
variable {J K : GrothendieckTopology C}
variable (h : J = K)
variable (A : Type*) [Category A]

/-- The functor in the equivalence of sheaf categories. -/
def sheafCongr_functor : Sheaf J A ⥤ Sheaf K A where
  obj F := ⟨F.val, (by rw [← h]; exact F.cond)⟩
  map f := ⟨f.val⟩

/-- The inverse in the equivalence of sheaf categories. -/
def sheafCongr_inverse : Sheaf K A ⥤ Sheaf J A where
  obj F := ⟨F.val, (by rw [h]; exact F.cond)⟩
  map f := ⟨f.val⟩

@[simps!]
def sheafCongr : Sheaf J A ≌ Sheaf K A where
  functor := sheafCongr_functor h A
  inverse := sheafCongr_inverse h A
  unitIso := eqToIso rfl
  counitIso := eqToIso rfl
