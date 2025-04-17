/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Data.ENNReal.Inv

/-! # Hölder triples

This file defines a new class: `ENNReal.HolderTriple` which takes arguments `p q r : ℝ≥0∞`,
with `r` marked as a `semiOutParam`, and states that `p⁻¹ + q⁻¹ = r⁻¹`. This is exactly the
condition for which **Hölder's inequality** is valid (see `MeasureTheory.MemLp.smul`).
This allows us to declare a heterogeneous scalar multiplication (`HSMul`) instance on
`MeasureTheory.Lp` spaces.

In this file we provide many convenience lemmas in the presence of a `HolderTriple` instance.
All these are easily provable from facts about `ℝ≥0∞`, but it's convenient not to be forced
to reprove them each time.

For convenience we also define `ENNReal.HolderConjugate` (with arguments `p q`) as an
abbreviation for `ENNReal.HolderTriple p q 1`.
-/

namespace ENNReal

/-- A class stating that `p q r : ℝ≥0∞` satisfy `p⁻¹ + q⁻¹ = r⁻¹`.
This is exactly the condition for which **Hölder's inequality** is valid
(see `MeasureTheory.MemLp.smul`).

When `r := 1`, one generally says that `p q` are **Hölder conjugate**.

This class exists so that we can define a heterogeneous scalar multiplication
on `MeasureTheory.Lp`, and this is why `r` must be marked as a
`semiOutParam`. We don't mark it as an `outParam` because this would
prevent Lean from using `HolderTriple p q r` and `HolderTriple p q r'`
within a single proof, as may be occasionally convenient. -/
@[mk_iff]
class HolderTriple (p q : ℝ≥0∞) (r : semiOutParam ℝ≥0∞) : Prop where
  inv_add_inv_eq_inv (p q r) : p⁻¹ + q⁻¹ = r⁻¹

/-- An abbreviation for `ENNReal.HolderTriple p q 1`, this class states `p⁻¹ + q⁻¹ = 1`. -/
abbrev HolderConjugate (p q : ℝ≥0∞) := HolderTriple p q 1

lemma holderConjugate_iff {p q : ℝ≥0∞} : HolderConjugate p q ↔ p⁻¹ + q⁻¹ = 1 := by
  simp [holderTriple_iff]

/-! ### Hölder triples -/

namespace HolderTriple

/-- This is not marked as an instance so that Lean doesn't always find this one
and a more canonical value of `r` can be used. -/
lemma of (p q : ℝ≥0∞) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  inv_add_inv_eq_inv := inv_inv _ |>.symm

/- This instance causes a trivial loop, but this is exactly the kind of loop that
Lean should be able to detect and avoid. -/
instance symm {p q r : ℝ≥0∞} [hpqr : HolderTriple p q r] : HolderTriple q p r where
  inv_add_inv_eq_inv := add_comm p⁻¹ q⁻¹ ▸ hpqr.inv_add_inv_eq_inv

instance instInfty (p : ℝ≥0∞) : HolderTriple p ∞ p where
  inv_add_inv_eq_inv := by simp

instance instZero (p : ℝ≥0∞) : HolderTriple p 0 0 where
  inv_add_inv_eq_inv := by simp

variable (p q r : ℝ≥0∞) [HolderTriple p q r]

lemma inv_eq : r⁻¹ = p⁻¹ + q⁻¹ := (inv_add_inv_eq_inv ..).symm

lemma unique (r' : ℝ≥0∞) [hr' : HolderTriple p q r'] : r = r' := by
  rw [← inv_inj, inv_eq p q r, inv_eq p q r']

@[deprecated inv_add_inv_eq_inv (since := "2025-04-09")]
lemma one_div_add_one_div : 1 / p + 1 / q = 1 / r := by simpa using inv_add_inv_eq_inv ..

@[deprecated inv_eq (since := "2025-04-09")]
lemma one_div_eq : 1 / r = 1 / p + 1 / q := by simpa using inv_eq p q r

lemma inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r := by
  simp [inv_add_inv_eq_inv p q r]

include q in lemma left_inv_le_inv : p⁻¹ ≤ r⁻¹ := by simp [inv_eq p q r]
include p in lemma right_inv_le_inv : q⁻¹ ≤ r⁻¹ := by simp [inv_eq p q r]

include q in lemma le_left : r ≤ p := by simpa using left_inv_le_inv p q r
include p in lemma le_right : r ≤ q := by simpa using right_inv_le_inv p q r

variable {r} in
/-- See also `ENNReal.HolderTriple.inv_sub_right_inv_eq_left_inv'` for a version that assumes
`q ≠ 0` instead of `r ≠ 0`. -/
lemma inv_sub_right_inv_eq_left_inv (hr : r ≠ 0) : r⁻¹ - q⁻¹ = p⁻¹ := by
  apply ENNReal.sub_eq_of_eq_add (ne_of_lt ?_) (inv_eq p q r)
  calc
    q⁻¹ ≤ r⁻¹ := HolderTriple.left_inv_le_inv q p r
    _ < ∞ := by simpa using pos_iff_ne_zero.mpr hr

variable {r} in
/-- See also `ENNReal.HolderTriple.inv_sub_left_inv_eq_right_inv'` for a version that assumes
`p ≠ 0` instead of `r ≠ 0`. -/
lemma inv_sub_left_inv_eq_right_inv (hr : r ≠ 0) : r⁻¹ - p⁻¹ = q⁻¹ :=
  inv_sub_right_inv_eq_left_inv q p hr

variable {q} in
/-- See also `ENNReal.HolderTriple.inv_sub_right_inv_eq_left_inv` for a version that assumes
`r ≠ 0` instead of `q ≠ 0`. -/
lemma inv_sub_right_inv_eq_left_inv' (hq : q ≠ 0) : r⁻¹ - q⁻¹ = p⁻¹ := by
  obtain (rfl | hr) := eq_zero_or_pos r
  · suffices p = 0 by simpa [this]
    by_contra! hp
    have := calc
      0⁻¹ = p⁻¹ + q⁻¹ := inv_eq p q 0
      _ < ⊤ + ⊤ := by simp [hp, hq, pos_iff_ne_zero]
      _ = ⊤ := by simp
    simp_all
  · exact inv_sub_right_inv_eq_left_inv p q hr.ne'

variable {p} in
/-- See also `ENNReal.HolderTriple.inv_sub_left_inv_eq_right_inv` for a version that assumes
`r ≠ 0` instead of `p ≠ 0`. -/
lemma inv_sub_left_inv_eq_right_inv' (hp : p ≠ 0) : r⁻¹ - p⁻¹ = q⁻¹ :=
  inv_sub_right_inv_eq_left_inv' _ _ hp

variable {r} in
lemma right_unique_of_ne_zero (q' : ℝ≥0∞) (hr : r ≠ 0) [HolderTriple p q' r] : q = q' := by
  rw [← inv_inj, ← inv_sub_right_inv_eq_left_inv q p hr, ← inv_sub_right_inv_eq_left_inv q' p hr]

variable {r} in
lemma left_unique_of_ne_zero (p' : ℝ≥0∞) (hr : r ≠ 0) [HolderTriple p' q r] : p = p' :=
  right_unique_of_ne_zero q p p' hr

lemma holderConjugate_div_div (hr₀ : r ≠ 0) (hr : r ≠ ∞) : HolderConjugate (p / r) (q / r) where
  inv_add_inv_eq_inv := by
    rw [ENNReal.inv_div (.inl hr) (.inl hr₀), ENNReal.inv_div (.inl hr) (.inl hr₀), div_eq_mul_inv,
      div_eq_mul_inv, ← mul_add, inv_add_inv_eq_inv p q r, ENNReal.mul_inv_cancel hr₀ hr, inv_one]

lemma holderConjugate_div_div (hr₀ : r ≠ 0) (hr : r ≠ ∞) : HolderConjugate (p / r) (q / r) where
  inv_add_inv_eq_inv := by
    rw [ENNReal.inv_div (.inl hr) (.inl hr₀), ENNReal.inv_div (.inl hr) (.inl hr₀), div_eq_mul_inv,
      div_eq_mul_inv, ← mul_add, inv_add_inv_eq_inv p q r, ENNReal.mul_inv_cancel hr₀ hr, inv_one]

end HolderTriple

/-! ### Hölder conjugates -/

namespace HolderConjugate

/- This instance causes a trivial loop, but this is exactly the kind of loop that
Lean should be able to detect and avoid. -/
instance symm {p q : ℝ≥0∞} [hpq : HolderConjugate p q] : HolderConjugate q p :=
  inferInstance

instance instTwoTwo : HolderConjugate 2 2 where
  inv_add_inv_eq_inv := by
    rw [← two_mul, ENNReal.mul_inv_cancel]
    all_goals norm_num

-- I'm not sure this is necessary, but maybe it's nice to have around given the `abbrev`.
instance instOneInfty : HolderConjugate 1 ∞ := inferInstance

variable (p q : ℝ≥0∞) [HolderConjugate p q]

include q in lemma one_le_left : 1 ≤ p := HolderTriple.le_left p q 1
include p in lemma one_le_right : 1 ≤ q := HolderTriple.le_right p q 1

include q in lemma left_pos : 0 < p := zero_lt_one.trans_le (one_le_left p q)
include p in lemma right_pos : 0 < q := zero_lt_one.trans_le (one_le_right p q)

include q in lemma left_ne_zero : p ≠ 0 := left_pos p q |>.ne'
include p in lemma right_ne_zero : q ≠ 0 := right_pos p q |>.ne'

lemma inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1 := @inv_one ℝ≥0∞ _ ▸ HolderTriple.inv_add_inv_eq_inv p q 1

lemma one_sub_left_inv : 1 - p⁻¹ = q⁻¹ := by
  simpa using HolderTriple.inv_sub_left_inv_eq_right_inv p q one_ne_zero

lemma one_sub_right_inv : 1 - q⁻¹ = p⁻¹ := by
  simpa using HolderTriple.inv_sub_right_inv_eq_left_inv p q one_ne_zero

lemma left_unique (p' : ℝ≥0∞) [HolderConjugate p' q] : p = p' :=
  HolderTriple.left_unique_of_ne_zero _ q _ one_ne_zero

lemma right_unique (q' : ℝ≥0∞) [HolderConjugate p q'] : q = q' := left_unique _ p _

lemma left_eq_top_iff_right_eq_one : p = ∞ ↔ q = 1 where
  mp := by rintro rfl; rw [← inv_inv q, ← one_sub_left_inv ∞ q]; simp
  mpr := by rintro rfl; rw [← inv_inv p, ← one_sub_right_inv p 1]; simp

lemma right_eq_top_iff_left_eq_one : q = ∞ ↔ p = 1 := left_eq_top_iff_right_eq_one q p

lemma left_ne_top_iff_right_ne_one : p ≠ ∞ ↔ q ≠ 1 := (left_eq_top_iff_right_eq_one _ _).ne
lemma right_ne_top_iff_left_ne_one : q ≠ ∞ ↔ p ≠ 1 := (left_eq_top_iff_right_eq_one _ _).ne

lemma left_lt_top_iff_one_lt_right : p < ∞ ↔ 1 < q := by
  rw [lt_top_iff_ne_top, left_ne_top_iff_right_ne_one _ q, ne_comm, lt_iff_le_and_ne]
  simp [one_le_right p q]

lemma right_lt_top_iff_one_lt_left : q < ∞ ↔ 1 < p := left_lt_top_iff_one_lt_right q p

variable {p} in
lemma left_sub_one_mul_left_inv (hp : p ≠ ⊤) : (p - 1) * p⁻¹ = q⁻¹ := by
  have := left_pos p q |>.ne'
  rw [ENNReal.sub_mul (by aesop), ENNReal.mul_inv_cancel this (by aesop)]
  simp [one_sub_left_inv p q]

variable {q} in
lemma right_sub_one_mul_right_inv (hq : q ≠ ⊤) : (q - 1) * q⁻¹ = p⁻¹ :=
  left_sub_one_mul_left_inv _ hq

end HolderConjugate

end ENNReal
