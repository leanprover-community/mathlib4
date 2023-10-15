import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

namespace CategoryTheory

open Limits Triangulated

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

namespace Functor

variable (F : C ⥤ D) [F.CommShift ℤ] (t₁ : TStructure C) (t₂ : TStructure D)

structure RightTExact [F.IsTriangulated] : Prop where
  objGE (X : C) (n : ℤ) [t₁.IsGE X n] : t₂.IsGE (F.obj X) n

structure LeftTExact [F.IsTriangulated] : Prop where
  objLE (X : C) (n : ℤ) [t₁.IsLE X n] : t₂.IsLE (F.obj X) n

variable [F.IsTriangulated]

structure TExact : Prop where
  rightTExact : F.RightTExact t₁ t₂
  leftTExact : F.LeftTExact t₁ t₂

lemma RightTExact.mk' (h : ∀ (X : C) [t₁.IsGE X 0], t₂.IsGE (F.obj X) 0) :
    F.RightTExact t₁ t₂ where
  objGE X n _ := by
    have := t₁.isGE_shift X n n 0 (add_zero n)
    have : t₂.IsGE ((shiftFunctor C n ⋙ F).obj X) 0 := h (X⟦n⟧)
    have : t₂.IsGE ((F.obj X)⟦n⟧) 0 := t₂.isGE_of_iso ((F.commShiftIso n).app X) 0
    exact t₂.isGE_of_shift (F.obj X) n n 0 (add_zero n)

lemma LeftTExact.mk' (h : ∀ (X : C) [t₁.IsLE X 0], t₂.IsLE (F.obj X) 0) :
    F.LeftTExact t₁ t₂ where
  objLE X n _ := by
    have := t₁.isLE_shift X n n 0 (add_zero n)
    have : t₂.IsLE ((shiftFunctor C n ⋙ F).obj X) 0 := h (X⟦n⟧)
    have : t₂.IsLE ((F.obj X)⟦n⟧) 0 := t₂.isLE_of_iso ((F.commShiftIso n).app X) 0
    exact t₂.isLE_of_shift (F.obj X) n n 0 (add_zero n)

end Functor

end CategoryTheory
