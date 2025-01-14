/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.GroupPower.IterateHom
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Regular elements

## Implementation details

Group powers and other definitions import a lot of the algebra hierarchy.
Lemmas about them are kept separate to be able to provide `IsRegular` early in the
algebra hierarchy.

-/


variable {R : Type*} {a b : R}

section Monoid

variable [Monoid R]

/-- Any power of a left-regular element is left-regular. -/
theorem IsLeftRegular.pow (n : ℕ) (rla : IsLeftRegular a) : IsLeftRegular (a ^ n) := by
  simp only [IsLeftRegular, ← mul_left_iterate, rla.iterate n]

/-- Any power of a right-regular element is right-regular. -/
theorem IsRightRegular.pow (n : ℕ) (rra : IsRightRegular a) : IsRightRegular (a ^ n) := by
  rw [IsRightRegular, ← mul_right_iterate]
  exact rra.iterate n

/-- Any power of a regular element is regular. -/
theorem IsRegular.pow (n : ℕ) (ra : IsRegular a) : IsRegular (a ^ n) :=
  ⟨IsLeftRegular.pow n ra.left, IsRightRegular.pow n ra.right⟩

/-- An element `a` is left-regular if and only if a positive power of `a` is left-regular. -/
theorem IsLeftRegular.pow_iff {n : ℕ} (n0 : 0 < n) : IsLeftRegular (a ^ n) ↔ IsLeftRegular a := by
  refine ⟨?_, IsLeftRegular.pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0, pow_succ]
  exact IsLeftRegular.of_mul

/-- An element `a` is right-regular if and only if a positive power of `a` is right-regular. -/
theorem IsRightRegular.pow_iff {n : ℕ} (n0 : 0 < n) :
    IsRightRegular (a ^ n) ↔ IsRightRegular a := by
  refine ⟨?_, IsRightRegular.pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0, pow_succ']
  exact IsRightRegular.of_mul

/-- An element `a` is regular if and only if a positive power of `a` is regular. -/
theorem IsRegular.pow_iff {n : ℕ} (n0 : 0 < n) : IsRegular (a ^ n) ↔ IsRegular a :=
  ⟨fun h => ⟨(IsLeftRegular.pow_iff n0).mp h.left, (IsRightRegular.pow_iff n0).mp h.right⟩, fun h =>
    ⟨IsLeftRegular.pow n h.left, IsRightRegular.pow n h.right⟩⟩

end Monoid

section CommMonoid

variable {ι R : Type*} [CommMonoid R] {s : Finset ι} {f : ι → R}

lemma IsLeftRegular.prod (h : ∀ i ∈ s, IsLeftRegular (f i)) :
    IsLeftRegular (∏ i ∈ s, f i) :=
  s.prod_induction _ _ (@IsLeftRegular.mul R _) isRegular_one.left h

lemma IsRightRegular.prod (h : ∀ i ∈ s, IsRightRegular (f i)) :
    IsRightRegular (∏ i ∈ s, f i) :=
  s.prod_induction _ _ (@IsRightRegular.mul R _) isRegular_one.right h

lemma IsRegular.prod (h : ∀ i ∈ s, IsRegular (f i)) :
    IsRegular (∏ i ∈ s, f i) :=
  ⟨IsLeftRegular.prod fun a ha ↦ (h a ha).left,
   IsRightRegular.prod fun a ha ↦ (h a ha).right⟩

end CommMonoid
