/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc

/-!
# t-exact functors

Given a triangulated functor `F : C ⥤ D` where both `C` and `D` are equipped
with t-structures `t₁` and `t₂`, we introduce typeclasses
`F.LeftTExact t₁ t₂`, `F.RightTExact t₁ t₂` and `F.TExact t₁ t₂` which
correspond to the notion of left t-exact, right t-exact and t-exact functors.

## References
* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*, 1.2][bbd-1982]

-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits Triangulated Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- A triangulated functor `F` is left `t`-exact if `X ≥ n` implies `F.obj X ≥ n`.
(It suffices to test this for `n := 0`, see `LeftExact.mk'`.) -/
class LeftTExact (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (t₁ : TStructure C) (t₂ : TStructure D) : Prop where
  isGE_obj (F t₁ t₂) (X : C) (n : ℤ) [t₁.IsGE X n] : t₂.IsGE (F.obj X) n

/-- A triangulated functor `F` is right `t`-exact if `X ≤ n` implies `F.obj X ≤ n`.
 (It suffices to test this for `n := 0`, see `RightExact.mk'`.) -/
class RightTExact (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (t₁ : TStructure C) (t₂ : TStructure D) : Prop where
  isLE_obj (F t₁ t₂) (X : C) (n : ℤ) [t₁.IsLE X n] : t₂.IsLE (F.obj X) n

export LeftTExact (isGE_obj)
export RightTExact (isLE_obj)

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] (t₁ : TStructure C) (t₂ : TStructure D)

/-- A triangulated functor is `t`-exact if it is both left and right `t`-exact. -/
class TExact : Prop where
  rightTExact : F.RightTExact t₁ t₂ := by infer_instance
  leftTExact : F.LeftTExact t₁ t₂ := by infer_instance

attribute [instance] TExact.rightTExact TExact.leftTExact

/-- Constructor for `LeftTExact`. -/
lemma LeftTExact.mk' (h : ∀ (X : C) [t₁.IsGE X 0], t₂.IsGE (F.obj X) 0) :
    F.LeftTExact t₁ t₂ where
  isGE_obj X n _ := by
    have := t₁.isGE_shift X n n 0 (add_zero n)
    have : t₂.IsGE ((shiftFunctor C n ⋙ F).obj X) 0 := h (X⟦n⟧)
    have : t₂.IsGE ((F.obj X)⟦n⟧) 0 := t₂.isGE_of_iso ((F.commShiftIso n).app X) 0
    exact t₂.isGE_of_shift (F.obj X) n n 0 (add_zero n)

/-- Constructor for `RightTExact`. -/
lemma RightTExact.mk' (h : ∀ (X : C) [t₁.IsLE X 0], t₂.IsLE (F.obj X) 0) :
    F.RightTExact t₁ t₂ where
  isLE_obj X n _ := by
    have := t₁.isLE_shift X n n 0 (add_zero n)
    have : t₂.IsLE ((shiftFunctor C n ⋙ F).obj X) 0 := h (X⟦n⟧)
    have : t₂.IsLE ((F.obj X)⟦n⟧) 0 := t₂.isLE_of_iso ((F.commShiftIso n).app X) 0
    exact t₂.isLE_of_shift (F.obj X) n n 0 (add_zero n)

end CategoryTheory.Functor
