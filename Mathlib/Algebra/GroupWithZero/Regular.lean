/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Tactic.Push

/-!
# Results about `IsRegular` and `0`
-/

variable {R}

section MulZeroClass
variable [MulZeroClass R] {a b : R}

/-- The element `0` is left-regular if and only if `R` is trivial. -/
theorem IsLeftRegular.subsingleton (h : IsLeftRegular (0 : R)) : Subsingleton R :=
  ⟨fun a b => h <| Eq.trans (zero_mul a) (zero_mul b).symm⟩

/-- The element `0` is right-regular if and only if `R` is trivial. -/
theorem IsRightRegular.subsingleton (h : IsRightRegular (0 : R)) : Subsingleton R :=
  ⟨fun a b => h <| Eq.trans (mul_zero a) (mul_zero b).symm⟩

/-- The element `0` is regular if and only if `R` is trivial. -/
theorem IsRegular.subsingleton (h : IsRegular (0 : R)) : Subsingleton R :=
  h.left.subsingleton

/-- The element `0` is left-regular if and only if `R` is trivial. -/
theorem isLeftRegular_zero_iff_subsingleton : IsLeftRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

/-- In a non-trivial `MulZeroClass`, the `0` element is not left-regular. -/
theorem not_isLeftRegular_zero_iff : ¬IsLeftRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, isLeftRegular_zero_iff_subsingleton, subsingleton_iff]
  push_neg
  exact Iff.rfl

/-- The element `0` is right-regular if and only if `R` is trivial. -/
theorem isRightRegular_zero_iff_subsingleton : IsRightRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

/-- In a non-trivial `MulZeroClass`, the `0` element is not right-regular. -/
theorem not_isRightRegular_zero_iff : ¬IsRightRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, isRightRegular_zero_iff_subsingleton, subsingleton_iff]
  push_neg
  exact Iff.rfl

/-- The element `0` is regular if and only if `R` is trivial. -/
theorem isRegular_iff_subsingleton : IsRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.left.subsingleton, fun h =>
    ⟨isLeftRegular_zero_iff_subsingleton.mpr h, isRightRegular_zero_iff_subsingleton.mpr h⟩⟩

/-- A left-regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
theorem IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (la (?_ : 0 * x = 0 * y)) -- Porting note: lean4 seems to need the type signature
  rw [zero_mul, zero_mul]

/-- A right-regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
theorem IsRightRegular.ne_zero [Nontrivial R] (ra : IsRightRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (ra (?_ : x * 0 = y * 0))
  rw [mul_zero, mul_zero]

/-- A regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
theorem IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) : a ≠ 0 :=
  la.left.ne_zero

/-- In a non-trivial ring, the element `0` is not left-regular -- with typeclasses. -/
theorem not_isLeftRegular_zero [nR : Nontrivial R] : ¬IsLeftRegular (0 : R) :=
  not_isLeftRegular_zero_iff.mpr nR

/-- In a non-trivial ring, the element `0` is not right-regular -- with typeclasses. -/
theorem not_isRightRegular_zero [nR : Nontrivial R] : ¬IsRightRegular (0 : R) :=
  not_isRightRegular_zero_iff.mpr nR

/-- In a non-trivial ring, the element `0` is not regular -- with typeclasses. -/
theorem not_isRegular_zero [Nontrivial R] : ¬IsRegular (0 : R) := fun h => IsRegular.ne_zero h rfl

@[simp] lemma IsLeftRegular.mul_left_eq_zero_iff (hb : IsLeftRegular b) : b * a = 0 ↔ a = 0 := by
  conv_lhs => rw [← mul_zero b]
  exact ⟨fun h ↦ hb h, fun ha ↦ by rw [ha]⟩

@[simp] lemma IsRightRegular.mul_right_eq_zero_iff (hb : IsRightRegular b) : a * b = 0 ↔ a = 0 := by
  conv_lhs => rw [← zero_mul b]
  exact ⟨fun h ↦ hb h, fun ha ↦ by rw [ha]⟩

end MulZeroClass

section CancelMonoidWithZero
variable [MulZeroClass R] [IsCancelMulZero R] {a : R}

/-- Non-zero elements of an integral domain are regular. -/
theorem isRegular_of_ne_zero (a0 : a ≠ 0) : IsRegular a :=
  ⟨fun _ _ => mul_left_cancel₀ a0, fun _ _ => mul_right_cancel₀ a0⟩

/-- In a non-trivial integral domain, an element is regular iff it is non-zero. -/
theorem isRegular_iff_ne_zero [Nontrivial R] : IsRegular a ↔ a ≠ 0 :=
  ⟨IsRegular.ne_zero, isRegular_of_ne_zero⟩

end CancelMonoidWithZero
