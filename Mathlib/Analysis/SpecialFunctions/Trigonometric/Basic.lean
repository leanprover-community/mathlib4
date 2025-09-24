/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathlib.Algebra.Field.NegOnePow
import Mathlib.Algebra.Field.Periodic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Trigonometric functions

## Main definitions

This file contains the definition of `π`.

See also `Analysis.SpecialFunctions.Trigonometric.Inverse` and
`Analysis.SpecialFunctions.Trigonometric.Arctan` for the inverse trigonometric functions.

See also `Analysis.SpecialFunctions.Complex.Arg` and
`Analysis.SpecialFunctions.Complex.Log` for the complex argument function
and the complex logarithm.

## Main statements

Many basic inequalities on the real trigonometric functions are established.

The continuity of the usual trigonometric functions is proved.

Several facts about the real trigonometric functions have the proofs deferred to
`Analysis.SpecialFunctions.Trigonometric.Complex`,
as they are most easily proved by appealing to the corresponding fact for
complex trigonometric functions.

See also `Analysis.SpecialFunctions.Trigonometric.Chebyshev` for the multiple angle formulas
in terms of Chebyshev polynomials.

## Tags

sin, cos, tan, angle
-/


noncomputable section

open Topology Filter Set

namespace Complex

@[continuity, fun_prop]
theorem continuous_sin : Continuous sin := by
  change Continuous fun z => (exp (-z * I) - exp (z * I)) * I / 2
  fun_prop

@[fun_prop]
theorem continuousOn_sin {s : Set ℂ} : ContinuousOn sin s :=
  continuous_sin.continuousOn

@[continuity, fun_prop]
theorem continuous_cos : Continuous cos := by
  change Continuous fun z => (exp (z * I) + exp (-z * I)) / 2
  fun_prop

@[fun_prop]
theorem continuousOn_cos {s : Set ℂ} : ContinuousOn cos s :=
  continuous_cos.continuousOn

@[continuity, fun_prop]
theorem continuous_sinh : Continuous sinh := by
  change Continuous fun z => (exp z - exp (-z)) / 2
  fun_prop

@[continuity, fun_prop]
theorem continuous_cosh : Continuous cosh := by
  change Continuous fun z => (exp z + exp (-z)) / 2
  fun_prop

end Complex

namespace Real

variable {x y z : ℝ}

@[continuity, fun_prop]
theorem continuous_sin : Continuous sin :=
  Complex.continuous_re.comp (Complex.continuous_sin.comp Complex.continuous_ofReal)

@[fun_prop]
theorem continuousOn_sin {s} : ContinuousOn sin s :=
  continuous_sin.continuousOn

@[continuity, fun_prop]
theorem continuous_cos : Continuous cos :=
  Complex.continuous_re.comp (Complex.continuous_cos.comp Complex.continuous_ofReal)

@[fun_prop]
theorem continuousOn_cos {s} : ContinuousOn cos s :=
  continuous_cos.continuousOn

@[continuity, fun_prop]
theorem continuous_sinh : Continuous sinh :=
  Complex.continuous_re.comp (Complex.continuous_sinh.comp Complex.continuous_ofReal)

@[continuity, fun_prop]
theorem continuous_cosh : Continuous cosh :=
  Complex.continuous_re.comp (Complex.continuous_cosh.comp Complex.continuous_ofReal)

end Real

namespace Real

theorem exists_cos_eq_zero : 0 ∈ cos '' Icc (1 : ℝ) 2 :=
  intermediate_value_Icc' (by simp) continuousOn_cos
    ⟨le_of_lt cos_two_neg, le_of_lt cos_one_pos⟩

/-- The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2],
from which one can derive all its properties. For explicit bounds on π,
see `Mathlib/Analysis/Real/Pi/Bounds.lean`.

Denoted `π`, once the `Real` namespace is opened. -/
protected noncomputable def pi : ℝ :=
  2 * Classical.choose exists_cos_eq_zero

@[inherit_doc]
scoped notation "π" => Real.pi

@[simp]
theorem cos_pi_div_two : cos (π / 2) = 0 := by
  rw [Real.pi, mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).2

theorem one_le_pi_div_two : (1 : ℝ) ≤ π / 2 := by
  rw [Real.pi, mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).1.1

theorem pi_div_two_le_two : π / 2 ≤ 2 := by
  rw [Real.pi, mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).1.2

theorem two_le_pi : (2 : ℝ) ≤ π :=
  (div_le_div_iff_of_pos_right zero_lt_two).1
    (by rw [div_self two_ne_zero]; exact one_le_pi_div_two)

theorem pi_le_four : π ≤ 4 :=
  (div_le_div_iff_of_pos_right zero_lt_two).1
    (calc
      π / 2 ≤ 2 := pi_div_two_le_two
      _ = 4 / 2 := by norm_num)

@[bound]
theorem pi_pos : 0 < π :=
  lt_of_lt_of_le (by simp) two_le_pi

@[bound]
theorem pi_nonneg : 0 ≤ π :=
  pi_pos.le

@[simp]
theorem pi_ne_zero : π ≠ 0 :=
  pi_pos.ne'

theorem pi_div_two_pos : 0 < π / 2 :=
  half_pos pi_pos

theorem two_pi_pos : 0 < 2 * π := by linarith [pi_pos]

end Real

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `π` is always positive. -/
@[positivity Real.pi]
def evalRealPi : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.pi) =>
    assertInstancesCommute
    pure (.positive q(Real.pi_pos))
  | _, _, _ => throwError "not Real.pi"

end Mathlib.Meta.Positivity

namespace NNReal

open Real

open Real NNReal

/-- `π` considered as a nonnegative real. -/
noncomputable def pi : ℝ≥0 :=
  ⟨π, Real.pi_pos.le⟩

@[simp]
theorem coe_real_pi : (pi : ℝ) = π :=
  rfl

theorem pi_pos : 0 < pi := mod_cast Real.pi_pos

theorem pi_ne_zero : pi ≠ 0 :=
  pi_pos.ne'

end NNReal

namespace Real

@[simp]
theorem sin_pi : sin π = 0 := by
  rw [← mul_div_cancel_left₀ π two_ne_zero, two_mul, add_div, sin_add, cos_pi_div_two]; simp

@[simp]
theorem cos_pi : cos π = -1 := by
  rw [← mul_div_cancel_left₀ π two_ne_zero, mul_div_assoc, cos_two_mul, cos_pi_div_two]
  norm_num

@[simp]
theorem sin_two_pi : sin (2 * π) = 0 := by simp [two_mul, sin_add]

@[simp]
theorem cos_two_pi : cos (2 * π) = 1 := by simp [two_mul, cos_add]

theorem sin_antiperiodic : Function.Antiperiodic sin π := by simp [sin_add]

theorem sin_periodic : Function.Periodic sin (2 * π) :=
  sin_antiperiodic.periodic_two_mul

@[simp]
theorem sin_add_pi (x : ℝ) : sin (x + π) = -sin x :=
  sin_antiperiodic x

@[simp]
theorem sin_add_two_pi (x : ℝ) : sin (x + 2 * π) = sin x :=
  sin_periodic x

@[simp]
theorem sin_sub_pi (x : ℝ) : sin (x - π) = -sin x :=
  sin_antiperiodic.sub_eq x

@[simp]
theorem sin_sub_two_pi (x : ℝ) : sin (x - 2 * π) = sin x :=
  sin_periodic.sub_eq x

@[simp]
theorem sin_pi_sub (x : ℝ) : sin (π - x) = sin x :=
  neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

@[simp]
theorem sin_two_pi_sub (x : ℝ) : sin (2 * π - x) = -sin x :=
  sin_neg x ▸ sin_periodic.sub_eq'

@[simp]
theorem sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
  sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

@[simp]
theorem sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
  sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

@[simp]
theorem sin_add_nat_mul_two_pi (x : ℝ) (n : ℕ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.nat_mul n x

@[simp]
theorem sin_add_int_mul_two_pi (x : ℝ) (n : ℤ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.int_mul n x

@[simp]
theorem sin_sub_nat_mul_two_pi (x : ℝ) (n : ℕ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_nat_mul_eq n

@[simp]
theorem sin_sub_int_mul_two_pi (x : ℝ) (n : ℤ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_int_mul_eq n

@[simp]
theorem sin_nat_mul_two_pi_sub (x : ℝ) (n : ℕ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

@[simp]
theorem sin_int_mul_two_pi_sub (x : ℝ) (n : ℤ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.int_mul_sub_eq n

theorem sin_add_int_mul_pi (x : ℝ) (n : ℤ) : sin (x + n * π) = (-1) ^ n * sin x :=
  n.cast_negOnePow ℝ ▸ sin_antiperiodic.add_int_mul_eq n

theorem sin_add_nat_mul_pi (x : ℝ) (n : ℕ) : sin (x + n * π) = (-1) ^ n * sin x :=
  sin_antiperiodic.add_nat_mul_eq n

theorem sin_sub_int_mul_pi (x : ℝ) (n : ℤ) : sin (x - n * π) = (-1) ^ n * sin x :=
  n.cast_negOnePow ℝ ▸ sin_antiperiodic.sub_int_mul_eq n

theorem sin_sub_nat_mul_pi (x : ℝ) (n : ℕ) : sin (x - n * π) = (-1) ^ n * sin x :=
  sin_antiperiodic.sub_nat_mul_eq n

theorem sin_int_mul_pi_sub (x : ℝ) (n : ℤ) : sin (n * π - x) = -((-1) ^ n * sin x) := by
  simpa only [sin_neg, mul_neg, Int.cast_negOnePow] using sin_antiperiodic.int_mul_sub_eq n

theorem sin_nat_mul_pi_sub (x : ℝ) (n : ℕ) : sin (n * π - x) = -((-1) ^ n * sin x) := by
  simpa only [sin_neg, mul_neg] using sin_antiperiodic.nat_mul_sub_eq n

theorem cos_antiperiodic : Function.Antiperiodic cos π := by simp [cos_add]

theorem cos_periodic : Function.Periodic cos (2 * π) :=
  cos_antiperiodic.periodic_two_mul

@[simp]
theorem abs_cos_int_mul_pi (k : ℤ) : |cos (k * π)| = 1 := by
  simp [abs_cos_eq_sqrt_one_sub_sin_sq]

@[simp]
theorem cos_add_pi (x : ℝ) : cos (x + π) = -cos x :=
  cos_antiperiodic x

@[simp]
theorem cos_add_two_pi (x : ℝ) : cos (x + 2 * π) = cos x :=
  cos_periodic x

@[simp]
theorem cos_sub_pi (x : ℝ) : cos (x - π) = -cos x :=
  cos_antiperiodic.sub_eq x

@[simp]
theorem cos_sub_two_pi (x : ℝ) : cos (x - 2 * π) = cos x :=
  cos_periodic.sub_eq x

@[simp]
theorem cos_pi_sub (x : ℝ) : cos (π - x) = -cos x :=
  cos_neg x ▸ cos_antiperiodic.sub_eq'

@[simp]
theorem cos_two_pi_sub (x : ℝ) : cos (2 * π - x) = cos x :=
  cos_neg x ▸ cos_periodic.sub_eq'

@[simp]
theorem cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.nat_mul_eq n).trans cos_zero

@[simp]
theorem cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.int_mul_eq n).trans cos_zero

@[simp]
theorem cos_add_nat_mul_two_pi (x : ℝ) (n : ℕ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.nat_mul n x

@[simp]
theorem cos_add_int_mul_two_pi (x : ℝ) (n : ℤ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.int_mul n x

@[simp]
theorem cos_sub_nat_mul_two_pi (x : ℝ) (n : ℕ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_nat_mul_eq n

@[simp]
theorem cos_sub_int_mul_two_pi (x : ℝ) (n : ℤ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_int_mul_eq n

@[simp]
theorem cos_nat_mul_two_pi_sub (x : ℝ) (n : ℕ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

@[simp]
theorem cos_int_mul_two_pi_sub (x : ℝ) (n : ℤ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.int_mul_sub_eq n

theorem cos_add_int_mul_pi (x : ℝ) (n : ℤ) : cos (x + n * π) = (-1) ^ n * cos x :=
  n.cast_negOnePow ℝ ▸ cos_antiperiodic.add_int_mul_eq n

theorem cos_add_nat_mul_pi (x : ℝ) (n : ℕ) : cos (x + n * π) = (-1) ^ n * cos x :=
  cos_antiperiodic.add_nat_mul_eq n

theorem cos_sub_int_mul_pi (x : ℝ) (n : ℤ) : cos (x - n * π) = (-1) ^ n * cos x :=
  n.cast_negOnePow ℝ ▸ cos_antiperiodic.sub_int_mul_eq n

theorem cos_sub_nat_mul_pi (x : ℝ) (n : ℕ) : cos (x - n * π) = (-1) ^ n * cos x :=
  cos_antiperiodic.sub_nat_mul_eq n

theorem cos_int_mul_pi_sub (x : ℝ) (n : ℤ) : cos (n * π - x) = (-1) ^ n * cos x :=
  n.cast_negOnePow ℝ ▸ cos_neg x ▸ cos_antiperiodic.int_mul_sub_eq n

theorem cos_nat_mul_pi_sub (x : ℝ) (n : ℕ) : cos (n * π - x) = (-1) ^ n * cos x :=
  cos_neg x ▸ cos_antiperiodic.nat_mul_sub_eq n

theorem cos_nat_mul_two_pi_add_pi (n : ℕ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

theorem cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

theorem cos_nat_mul_two_pi_sub_pi (n : ℕ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

theorem cos_int_mul_two_pi_sub_pi (n : ℤ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

theorem sin_pos_of_pos_of_lt_pi {x : ℝ} (h0x : 0 < x) (hxp : x < π) : 0 < sin x :=
  if hx2 : x ≤ 2 then sin_pos_of_pos_of_le_two h0x hx2
  else
    have : (2 : ℝ) + 2 = 4 := by norm_num
    have : π - x ≤ 2 :=
      sub_le_iff_le_add.2 (le_trans pi_le_four (this ▸ add_le_add_left (le_of_not_ge hx2) _))
    sin_pi_sub x ▸ sin_pos_of_pos_of_le_two (sub_pos.2 hxp) this

theorem sin_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 π) : 0 < sin x :=
  sin_pos_of_pos_of_lt_pi hx.1 hx.2

theorem sin_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc 0 π) : 0 ≤ sin x := by
  rw [← closure_Ioo pi_ne_zero.symm] at hx
  exact
    closure_lt_subset_le continuous_const continuous_sin
      (closure_mono (fun y => sin_pos_of_mem_Ioo) hx)

theorem sin_nonneg_of_nonneg_of_le_pi {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π) : 0 ≤ sin x :=
  sin_nonneg_of_mem_Icc ⟨h0x, hxp⟩

theorem sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx0 : x < 0) (hpx : -π < x) : sin x < 0 :=
  neg_pos.1 <| sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)

theorem sin_nonpos_of_nonpos_of_neg_pi_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -π ≤ x) : sin x ≤ 0 :=
  neg_nonneg.1 <| sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hx0) (neg_le.1 hpx)

@[deprecated (since := "2025-07-27")]
alias sin_nonpos_of_nonnpos_of_neg_pi_le := sin_nonpos_of_nonpos_of_neg_pi_le

@[simp]
theorem sin_pi_div_two : sin (π / 2) = 1 :=
  have : sin (π / 2) = 1 ∨ sin (π / 2) = -1 := by
    simpa [sq, mul_self_eq_one_iff] using sin_sq_add_cos_sq (π / 2)
  this.resolve_right fun h =>
    show ¬(0 : ℝ) < -1 by simp <|
      h ▸ sin_pos_of_pos_of_lt_pi pi_div_two_pos (half_lt_self pi_pos)

theorem sin_add_pi_div_two (x : ℝ) : sin (x + π / 2) = cos x := by simp [sin_add]

theorem sin_sub_pi_div_two (x : ℝ) : sin (x - π / 2) = -cos x := by simp [sub_eq_add_neg, sin_add]

theorem sin_pi_div_two_sub (x : ℝ) : sin (π / 2 - x) = cos x := by simp [sub_eq_add_neg, sin_add]

theorem cos_add_pi_div_two (x : ℝ) : cos (x + π / 2) = -sin x := by simp [cos_add]

theorem cos_sub_pi_div_two (x : ℝ) : cos (x - π / 2) = sin x := by simp [sub_eq_add_neg, cos_add]

theorem cos_pi_div_two_sub (x : ℝ) : cos (π / 2 - x) = sin x := by
  rw [← cos_neg, neg_sub, cos_sub_pi_div_two]

theorem cos_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) : 0 < cos x :=
  sin_add_pi_div_two x ▸ sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem cos_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) : 0 ≤ cos x :=
  sin_add_pi_div_two x ▸ sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem cos_nonneg_of_neg_pi_div_two_le_of_le {x : ℝ} (hl : -(π / 2) ≤ x) (hu : x ≤ π / 2) :
    0 ≤ cos x :=
  cos_nonneg_of_mem_Icc ⟨hl, hu⟩

theorem cos_neg_of_pi_div_two_lt_of_lt {x : ℝ} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2) :
    cos x < 0 :=
  neg_pos.1 <| cos_pi_sub x ▸ cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

theorem cos_nonpos_of_pi_div_two_le_of_le {x : ℝ} (hx₁ : π / 2 ≤ x) (hx₂ : x ≤ π + π / 2) :
    cos x ≤ 0 :=
  neg_nonneg.1 <| cos_pi_sub x ▸ cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

theorem sin_eq_sqrt_one_sub_cos_sq {x : ℝ} (hl : 0 ≤ x) (hu : x ≤ π) :
    sin x = √(1 - cos x ^ 2) := by
  rw [← abs_sin_eq_sqrt_one_sub_cos_sq, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hl hu)]

theorem cos_eq_sqrt_one_sub_sin_sq {x : ℝ} (hl : -(π / 2) ≤ x) (hu : x ≤ π / 2) :
    cos x = √(1 - sin x ^ 2) := by
  rw [← abs_cos_eq_sqrt_one_sub_sin_sq, abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨hl, hu⟩)]

lemma cos_half {x : ℝ} (hl : -π ≤ x) (hr : x ≤ π) : cos (x / 2) = √((1 + cos x) / 2) := by
  have : 0 ≤ cos (x / 2) := cos_nonneg_of_mem_Icc <| by constructor <;> linarith
  rw [← sqrt_sq this, cos_sq, add_div, two_mul, add_halves]

lemma abs_sin_half (x : ℝ) : |sin (x / 2)| = √((1 - cos x) / 2) := by
  rw [← sqrt_sq_eq_abs, sin_sq_eq_half_sub, two_mul, add_halves, sub_div]

lemma sin_half_eq_sqrt {x : ℝ} (hl : 0 ≤ x) (hr : x ≤ 2 * π) :
    sin (x / 2) = √((1 - cos x) / 2) := by
  rw [← abs_sin_half, abs_of_nonneg]
  apply sin_nonneg_of_nonneg_of_le_pi <;> linarith

lemma sin_half_eq_neg_sqrt {x : ℝ} (hl : -(2 * π) ≤ x) (hr : x ≤ 0) :
    sin (x / 2) = -√((1 - cos x) / 2) := by
  rw [← abs_sin_half, abs_of_nonpos, neg_neg]
  apply sin_nonpos_of_nonpos_of_neg_pi_le <;> linarith

theorem sin_eq_zero_iff_of_lt_of_lt {x : ℝ} (hx₁ : -π < x) (hx₂ : x < π) : sin x = 0 ↔ x = 0 :=
  ⟨fun h => by
    contrapose! h
    cases h.lt_or_gt with
    | inl h0 => exact (sin_neg_of_neg_of_neg_pi_lt h0 hx₁).ne
    | inr h0 => exact (sin_pos_of_pos_of_lt_pi h0 hx₂).ne',
  fun h => by simp [h]⟩

theorem sin_eq_zero_iff {x : ℝ} : sin x = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = x :=
  ⟨fun h =>
    ⟨⌊x / π⌋,
      le_antisymm (sub_nonneg.1 (Int.sub_floor_div_mul_nonneg _ pi_pos))
        (sub_nonpos.1 <|
          le_of_not_gt fun h₃ =>
            (sin_pos_of_pos_of_lt_pi h₃ (Int.sub_floor_div_mul_lt _ pi_pos)).ne
              (by simp [sub_eq_add_neg, sin_add, h, sin_int_mul_pi]))⟩,
    fun ⟨_, hn⟩ => hn ▸ sin_int_mul_pi _⟩

theorem sin_ne_zero_iff {x : ℝ} : sin x ≠ 0 ↔ ∀ n : ℤ, (n : ℝ) * π ≠ x := by
  rw [← not_exists, not_iff_not, sin_eq_zero_iff]

theorem sin_eq_zero_iff_cos_eq {x : ℝ} : sin x = 0 ↔ cos x = 1 ∨ cos x = -1 := by
  rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq, sq, sq, right_eq_add, mul_eq_zero, or_self]

theorem cos_eq_zero_iff_sin_eq {x : ℝ} : cos x = 0 ↔ sin x = 1 ∨ sin x = -1 := by
  rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq, sq, sq, left_eq_add, mul_eq_zero, or_self]

theorem cos_eq_one_iff (x : ℝ) : cos x = 1 ↔ ∃ n : ℤ, (n : ℝ) * (2 * π) = x :=
  ⟨fun h =>
    let ⟨n, hn⟩ := sin_eq_zero_iff.1 (sin_eq_zero_iff_cos_eq.2 (Or.inl h))
    ⟨n / 2,
      (Int.emod_two_eq_zero_or_one n).elim
        (fun hn0 => by
          rwa [← mul_assoc, ← @Int.cast_two ℝ, ← Int.cast_mul,
            Int.ediv_mul_cancel (Int.dvd_iff_emod_eq_zero.2 hn0)])
        fun hn1 => by
        rw [← Int.emod_add_mul_ediv n 2, hn1, Int.cast_add, Int.cast_one, add_mul, one_mul,
          add_comm, mul_comm (2 : ℤ), Int.cast_mul, mul_assoc, Int.cast_two] at hn
        rw [← hn, cos_int_mul_two_pi_add_pi] at h
        exact absurd h (by norm_num)⟩,
    fun ⟨_, hn⟩ => hn ▸ cos_int_mul_two_pi _⟩

theorem cos_eq_one_iff_of_lt_of_lt {x : ℝ} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π) :
    cos x = 1 ↔ x = 0 :=
  ⟨fun h => by
    rcases (cos_eq_one_iff _).1 h with ⟨n, rfl⟩
    rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₂
    rw [neg_lt, neg_mul_eq_neg_mul, mul_lt_iff_lt_one_left two_pi_pos] at hx₁
    norm_cast at hx₁ hx₂
    obtain rfl : n = 0 := le_antisymm (by cutsat) (by cutsat)
    simp, fun h => by simp [h]⟩

theorem sin_lt_sin_of_lt_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hy₂ : y ≤ π / 2)
    (hxy : x < y) : sin x < sin y := by
  rw [← sub_pos, sin_sub_sin]
  have : 0 < sin ((y - x) / 2) := by apply sin_pos_of_pos_of_lt_pi <;> linarith
  have : 0 < cos ((y + x) / 2) := by refine cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith
  positivity

theorem strictMonoOn_sin : StrictMonoOn sin (Icc (-(π / 2)) (π / 2)) := fun _ hx _ hy hxy =>
  sin_lt_sin_of_lt_of_le_pi_div_two hx.1 hy.2 hxy

theorem monotoneOn_sin : MonotoneOn sin (Set.Icc (-(π / 2)) (π / 2)) :=
  strictMonoOn_sin.monotoneOn

theorem cos_lt_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x < y) :
    cos y < cos x := by
  rw [← sin_pi_div_two_sub, ← sin_pi_div_two_sub]
  apply sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith

theorem cos_lt_cos_of_nonneg_of_le_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π / 2)
    (hxy : x < y) : cos y < cos x :=
  cos_lt_cos_of_nonneg_of_le_pi hx₁ (hy₂.trans (by linarith)) hxy

theorem strictAntiOn_cos : StrictAntiOn cos (Icc 0 π) := fun _ hx _ hy hxy =>
  cos_lt_cos_of_nonneg_of_le_pi hx.1 hy.2 hxy

theorem antitoneOn_cos : AntitoneOn cos (Set.Icc 0 π) :=
  strictAntiOn_cos.antitoneOn

theorem cos_le_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x ≤ y) :
    cos y ≤ cos x :=
  (strictAntiOn_cos.le_iff_ge ⟨hx₁.trans hxy, hy₂⟩ ⟨hx₁, hxy.trans hy₂⟩).2 hxy

theorem sin_le_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hy₂ : y ≤ π / 2)
    (hxy : x ≤ y) : sin x ≤ sin y :=
  (strictMonoOn_sin.le_iff_le ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩).2 hxy

theorem injOn_sin : InjOn sin (Icc (-(π / 2)) (π / 2)) :=
  strictMonoOn_sin.injOn

theorem injOn_cos : InjOn cos (Icc 0 π) :=
  strictAntiOn_cos.injOn

theorem surjOn_sin : SurjOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) := by
  simpa only [sin_neg, sin_pi_div_two] using
    intermediate_value_Icc (neg_le_self pi_div_two_pos.le) continuous_sin.continuousOn

theorem surjOn_cos : SurjOn cos (Icc 0 π) (Icc (-1) 1) := by
  simpa only [cos_zero, cos_pi] using intermediate_value_Icc' pi_pos.le continuous_cos.continuousOn

theorem sin_mem_Icc (x : ℝ) : sin x ∈ Icc (-1 : ℝ) 1 :=
  ⟨neg_one_le_sin x, sin_le_one x⟩

theorem cos_mem_Icc (x : ℝ) : cos x ∈ Icc (-1 : ℝ) 1 :=
  ⟨neg_one_le_cos x, cos_le_one x⟩

theorem mapsTo_sin (s : Set ℝ) : MapsTo sin s (Icc (-1 : ℝ) 1) := fun x _ => sin_mem_Icc x

theorem mapsTo_cos (s : Set ℝ) : MapsTo cos s (Icc (-1 : ℝ) 1) := fun x _ => cos_mem_Icc x

theorem bijOn_sin : BijOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) :=
  ⟨mapsTo_sin _, injOn_sin, surjOn_sin⟩

theorem bijOn_cos : BijOn cos (Icc 0 π) (Icc (-1) 1) :=
  ⟨mapsTo_cos _, injOn_cos, surjOn_cos⟩

@[simp]
theorem range_cos : range cos = (Icc (-1) 1 : Set ℝ) :=
  Subset.antisymm (range_subset_iff.2 cos_mem_Icc) surjOn_cos.subset_range

@[simp]
theorem range_sin : range sin = (Icc (-1) 1 : Set ℝ) :=
  Subset.antisymm (range_subset_iff.2 sin_mem_Icc) surjOn_sin.subset_range

theorem range_cos_infinite : (range Real.cos).Infinite := by
  rw [Real.range_cos]
  exact Icc_infinite (by simp)

theorem range_sin_infinite : (range Real.sin).Infinite := by
  rw [Real.range_sin]
  exact Icc_infinite (by simp)

section CosDivSq

variable (x : ℝ)

/-- the series `sqrtTwoAddSeries x n` is `sqrt(2 + sqrt(2 + ... ))` with `n` square roots,
  starting with `x`. We define it here because `cos (pi / 2 ^ (n+1)) = sqrtTwoAddSeries 0 n / 2`
-/
@[simp]
noncomputable def sqrtTwoAddSeries (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => √(2 + sqrtTwoAddSeries x n)

theorem sqrtTwoAddSeries_zero : sqrtTwoAddSeries x 0 = x := by simp

theorem sqrtTwoAddSeries_one : sqrtTwoAddSeries 0 1 = √2 := by simp

theorem sqrtTwoAddSeries_two : sqrtTwoAddSeries 0 2 = √(2 + √2) := by simp

theorem sqrtTwoAddSeries_zero_nonneg : ∀ n : ℕ, 0 ≤ sqrtTwoAddSeries 0 n
  | 0 => le_refl 0
  | _ + 1 => sqrt_nonneg _

theorem sqrtTwoAddSeries_nonneg {x : ℝ} (h : 0 ≤ x) : ∀ n : ℕ, 0 ≤ sqrtTwoAddSeries x n
  | 0 => h
  | _ + 1 => sqrt_nonneg _

theorem sqrtTwoAddSeries_lt_two : ∀ n : ℕ, sqrtTwoAddSeries 0 n < 2
  | 0 => by simp
  | n + 1 => by
    refine lt_of_lt_of_le ?_ (sqrt_sq zero_lt_two.le).le
    rw [sqrtTwoAddSeries, sqrt_lt_sqrt_iff, ← lt_sub_iff_add_lt']
    · refine (sqrtTwoAddSeries_lt_two n).trans_le ?_
      norm_num
    · exact add_nonneg zero_le_two (sqrtTwoAddSeries_zero_nonneg n)

theorem sqrtTwoAddSeries_succ (x : ℝ) :
    ∀ n : ℕ, sqrtTwoAddSeries x (n + 1) = sqrtTwoAddSeries (√(2 + x)) n
  | 0 => rfl
  | n + 1 => by rw [sqrtTwoAddSeries, sqrtTwoAddSeries_succ _ _, sqrtTwoAddSeries]

theorem sqrtTwoAddSeries_monotone_left {x y : ℝ} (h : x ≤ y) :
    ∀ n : ℕ, sqrtTwoAddSeries x n ≤ sqrtTwoAddSeries y n
  | 0 => h
  | n + 1 => by
    rw [sqrtTwoAddSeries, sqrtTwoAddSeries]
    exact sqrt_le_sqrt (add_le_add_left (sqrtTwoAddSeries_monotone_left h _) _)

@[simp]
theorem cos_pi_over_two_pow : ∀ n : ℕ, cos (π / 2 ^ (n + 1)) = sqrtTwoAddSeries 0 n / 2
  | 0 => by simp
  | n + 1 => by
    have A : (1 : ℝ) < 2 ^ (n + 1) := one_lt_pow₀ one_lt_two n.succ_ne_zero
    have B : π / 2 ^ (n + 1) < π := div_lt_self pi_pos A
    have C : 0 < π / 2 ^ (n + 1) := by positivity
    rw [pow_succ, div_mul_eq_div_div, cos_half, cos_pi_over_two_pow n, sqrtTwoAddSeries,
      add_div_eq_mul_add_div, one_mul, ← div_mul_eq_div_div, sqrt_div, sqrt_mul_self] <;>
      linarith [sqrtTwoAddSeries_nonneg le_rfl n]

theorem sin_sq_pi_over_two_pow (n : ℕ) :
    sin (π / 2 ^ (n + 1)) ^ 2 = 1 - (sqrtTwoAddSeries 0 n / 2) ^ 2 := by
  rw [sin_sq, cos_pi_over_two_pow]

theorem sin_sq_pi_over_two_pow_succ (n : ℕ) :
    sin (π / 2 ^ (n + 2)) ^ 2 = 1 / 2 - sqrtTwoAddSeries 0 n / 4 := by
  rw [sin_sq_pi_over_two_pow, sqrtTwoAddSeries, div_pow, sq_sqrt, add_div, ← sub_sub]
  · congr
    · norm_num
    · norm_num
  · exact add_nonneg two_pos.le (sqrtTwoAddSeries_zero_nonneg _)

@[simp]
theorem sin_pi_over_two_pow_succ (n : ℕ) :
    sin (π / 2 ^ (n + 2)) = √(2 - sqrtTwoAddSeries 0 n) / 2 := by
  rw [eq_div_iff_mul_eq two_ne_zero, eq_comm, sqrt_eq_iff_eq_sq, mul_pow,
    sin_sq_pi_over_two_pow_succ, sub_mul]
  · congr <;> norm_num
  · rw [sub_nonneg]
    exact (sqrtTwoAddSeries_lt_two _).le
  refine mul_nonneg (sin_nonneg_of_nonneg_of_le_pi ?_ ?_) zero_le_two
  · positivity
  · exact div_le_self pi_pos.le <| one_le_pow₀ one_le_two

@[simp]
theorem cos_pi_div_four : cos (π / 4) = √2 / 2 := by
  trans cos (π / 2 ^ 2)
  · congr
    norm_num
  · simp

@[simp]
theorem sin_pi_div_four : sin (π / 4) = √2 / 2 := by
  trans sin (π / 2 ^ 2)
  · congr
    norm_num
  · simp

@[simp]
theorem cos_pi_div_eight : cos (π / 8) = √(2 + √2) / 2 := by
  trans cos (π / 2 ^ 3)
  · congr
    norm_num
  · simp

@[simp]
theorem sin_pi_div_eight : sin (π / 8) = √(2 - √2) / 2 := by
  trans sin (π / 2 ^ 3)
  · congr
    norm_num
  · simp

@[simp]
theorem cos_pi_div_sixteen : cos (π / 16) = √(2 + √(2 + √2)) / 2 := by
  trans cos (π / 2 ^ 4)
  · congr
    norm_num
  · simp

@[simp]
theorem sin_pi_div_sixteen : sin (π / 16) = √(2 - √(2 + √2)) / 2 := by
  trans sin (π / 2 ^ 4)
  · congr
    norm_num
  · simp

@[simp]
theorem cos_pi_div_thirty_two : cos (π / 32) = √(2 + √(2 + √(2 + √2))) / 2 := by
  trans cos (π / 2 ^ 5)
  · congr
    norm_num
  · simp

@[simp]
theorem sin_pi_div_thirty_two : sin (π / 32) = √(2 - √(2 + √(2 + √2))) / 2 := by
  trans sin (π / 2 ^ 5)
  · congr
    norm_num
  · simp

-- This section is also a convenient location for other explicit values of `sin` and `cos`.
/-- The cosine of `π / 3` is `1 / 2`. -/
@[simp]
theorem cos_pi_div_three : cos (π / 3) = 1 / 2 := by
  have h₁ : (2 * cos (π / 3) - 1) ^ 2 * (2 * cos (π / 3) + 2) = 0 := by
    have : cos (3 * (π / 3)) = cos π := by
      congr 1
      ring
    linarith [cos_pi, cos_three_mul (π / 3)]
  rcases mul_eq_zero.mp h₁ with h | h
  · linarith [pow_eq_zero h]
  · have : cos π < cos (π / 3) := by
      refine cos_lt_cos_of_nonneg_of_le_pi ?_ le_rfl ?_ <;> linarith [pi_pos]
    linarith [cos_pi]

/-- The cosine of `π / 6` is `√3 / 2`. -/
@[simp]
theorem cos_pi_div_six : cos (π / 6) = √3 / 2 := by
  rw [show (6 : ℝ) = 3 * 2 by norm_num, div_mul_eq_div_div, cos_half, cos_pi_div_three, one_add_div,
    ← div_mul_eq_div_div, two_add_one_eq_three, sqrt_div, sqrt_mul_self] <;> linarith [pi_pos]

/-- The square of the cosine of `π / 6` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
theorem sq_cos_pi_div_six : cos (π / 6) ^ 2 = 3 / 4 := by
  rw [cos_pi_div_six, div_pow, sq_sqrt] <;> norm_num

/-- The sine of `π / 6` is `1 / 2`. -/
@[simp]
theorem sin_pi_div_six : sin (π / 6) = 1 / 2 := by
  rw [← cos_pi_div_two_sub, ← cos_pi_div_three]
  congr
  ring

/-- The square of the sine of `π / 3` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
theorem sq_sin_pi_div_three : sin (π / 3) ^ 2 = 3 / 4 := by
  rw [← cos_pi_div_two_sub, ← sq_cos_pi_div_six]
  congr
  ring

/-- The sine of `π / 3` is `√3 / 2`. -/
@[simp]
theorem sin_pi_div_three : sin (π / 3) = √3 / 2 := by
  rw [← cos_pi_div_two_sub, ← cos_pi_div_six]
  congr
  ring

theorem quadratic_root_cos_pi_div_five :
    letI c := cos (π / 5)
    4 * c ^ 2 - 2 * c - 1 = 0 := by
  set θ := π / 5 with hθ
  set c := cos θ
  set s := sin θ
  suffices 2 * c = 4 * c ^ 2 - 1 by simp [this]
  have hs : s ≠ 0 := by
    rw [ne_eq, sin_eq_zero_iff, hθ]
    push_neg
    intro n hn
    replace hn : n * 5 = 1 := by field_simp at hn; norm_cast at hn
    omega
  suffices s * (2 * c) = s * (4 * c ^ 2 - 1) from mul_left_cancel₀ hs this
  calc s * (2 * c) = 2 * s * c := by rw [← mul_assoc, mul_comm 2]
                 _ = sin (2 * θ) := by rw [sin_two_mul]
                 _ = sin (π - 2 * θ) := by rw [sin_pi_sub]
                 _ = sin (2 * θ + θ) := by congr; simp [hθ]; linarith
                 _ = sin (2 * θ) * c + cos (2 * θ) * s := sin_add (2 * θ) θ
                 _ = 2 * s * c * c + cos (2 * θ) * s := by rw [sin_two_mul]
                 _ = 2 * s * c * c + (2 * c ^ 2 - 1) * s := by rw [cos_two_mul]
                 _ = s * (2 * c * c) + s * (2 * c ^ 2 - 1) := by linarith
                 _ = s * (4 * c ^ 2 - 1) := by linarith

open Polynomial in
theorem Polynomial.isRoot_cos_pi_div_five :
    (4 • X ^ 2 - 2 • X - C 1 : ℝ[X]).IsRoot (cos (π / 5)) := by
  simpa using quadratic_root_cos_pi_div_five

/-- The cosine of `π / 5` is `(1 + √5) / 4`. -/
@[simp]
theorem cos_pi_div_five : cos (π / 5) = (1 + √5) / 4 := by
  set c := cos (π / 5)
  have : 4 * (c * c) + (-2) * c + (-1) = 0 := by
    rw [← sq, neg_mul, ← sub_eq_add_neg, ← sub_eq_add_neg]
    exact quadratic_root_cos_pi_div_five
  have hd : discrim 4 (-2) (-1) = (2 * √5) * (2 * √5) := by norm_num [discrim, mul_mul_mul_comm]
  rcases (quadratic_eq_zero_iff (by simp) hd c).mp this with h | h
  · simp [h]; linarith
  · absurd (show 0 ≤ c from cos_nonneg_of_mem_Icc <| by constructor <;> linarith [pi_pos.le])
    rw [not_le, h]
    exact div_neg_of_neg_of_pos (by norm_num [lt_sqrt]) (by positivity)

end CosDivSq

/-- `Real.sin` as an `OrderIso` between `[-(π / 2), π / 2]` and `[-1, 1]`. -/
def sinOrderIso : Icc (-(π / 2)) (π / 2) ≃o Icc (-1 : ℝ) 1 :=
  (strictMonoOn_sin.orderIso _ _).trans <| OrderIso.setCongr _ _ bijOn_sin.image_eq

@[simp]
theorem coe_sinOrderIso_apply (x : Icc (-(π / 2)) (π / 2)) : (sinOrderIso x : ℝ) = sin x :=
  rfl

theorem sinOrderIso_apply (x : Icc (-(π / 2)) (π / 2)) : sinOrderIso x = ⟨sin x, sin_mem_Icc x⟩ :=
  rfl

@[simp]
theorem tan_pi_div_four : tan (π / 4) = 1 := by
  rw [tan_eq_sin_div_cos, cos_pi_div_four, sin_pi_div_four]
  have h : √2 / 2 > 0 := by positivity
  exact div_self (ne_of_gt h)

@[simp]
theorem tan_pi_div_two : tan (π / 2) = 0 := by simp [tan_eq_sin_div_cos]

@[simp]
theorem tan_pi_div_six : tan (π / 6) = 1 / √3 := by
  rw [tan_eq_sin_div_cos, sin_pi_div_six, cos_pi_div_six]
  ring

@[simp]
theorem tan_pi_div_three : tan (π / 3) = √3 := by
  rw [tan_eq_sin_div_cos, sin_pi_div_three, cos_pi_div_three]
  ring

theorem tan_pos_of_pos_of_lt_pi_div_two {x : ℝ} (h0x : 0 < x) (hxp : x < π / 2) : 0 < tan x := by
  rw [tan_eq_sin_div_cos]
  exact div_pos (sin_pos_of_pos_of_lt_pi h0x (by linarith)) (cos_pos_of_mem_Ioo ⟨by linarith, hxp⟩)

theorem tan_nonneg_of_nonneg_of_le_pi_div_two {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π / 2) : 0 ≤ tan x :=
  match lt_or_eq_of_le h0x, lt_or_eq_of_le hxp with
  | Or.inl hx0, Or.inl hxp => le_of_lt (tan_pos_of_pos_of_lt_pi_div_two hx0 hxp)
  | Or.inl _, Or.inr hxp => by simp [hxp, tan_eq_sin_div_cos]
  | Or.inr hx0, _ => by simp [hx0.symm]

theorem tan_neg_of_neg_of_pi_div_two_lt {x : ℝ} (hx0 : x < 0) (hpx : -(π / 2) < x) : tan x < 0 :=
  neg_pos.1 (tan_neg x ▸ tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos]))

theorem tan_nonpos_of_nonpos_of_neg_pi_div_two_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -(π / 2) ≤ x) :
    tan x ≤ 0 :=
  neg_nonneg.1 (tan_neg x ▸ tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))

theorem strictMonoOn_tan : StrictMonoOn tan (Ioo (-(π / 2)) (π / 2)) := by
  rintro x hx y hy hlt
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos,
    div_lt_div_iff₀ (cos_pos_of_mem_Ioo hx) (cos_pos_of_mem_Ioo hy), mul_comm, ← sub_pos, ← sin_sub]
  exact sin_pos_of_pos_of_lt_pi (sub_pos.2 hlt) <| by linarith [hx.1, hy.2]

theorem tan_lt_tan_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hy₂ : y < π / 2)
    (hxy : x < y) : tan x < tan y :=
  strictMonoOn_tan ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩ hxy

theorem tan_lt_tan_of_nonneg_of_lt_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y < π / 2)
    (hxy : x < y) : tan x < tan y :=
  tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) hy₂ hxy

theorem injOn_tan : InjOn tan (Ioo (-(π / 2)) (π / 2)) :=
  strictMonoOn_tan.injOn

theorem tan_inj_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
    (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : tan x = tan y) : x = y :=
  injOn_tan ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ hxy

theorem tan_periodic : Function.Periodic tan π := by
  simpa only [Function.Periodic, tan_eq_sin_div_cos] using sin_antiperiodic.div cos_antiperiodic

@[simp]
theorem tan_pi : tan π = 0 := by rw [tan_periodic.eq, tan_zero]

theorem tan_add_pi (x : ℝ) : tan (x + π) = tan x :=
  tan_periodic x

theorem tan_sub_pi (x : ℝ) : tan (x - π) = tan x :=
  tan_periodic.sub_eq x

theorem tan_pi_sub (x : ℝ) : tan (π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.sub_eq'

theorem tan_pi_div_two_sub (x : ℝ) : tan (π / 2 - x) = (tan x)⁻¹ := by
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, inv_div, sin_pi_div_two_sub, cos_pi_div_two_sub]

theorem tan_nat_mul_pi (n : ℕ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.nat_mul_eq n

theorem tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.int_mul_eq n

theorem tan_add_nat_mul_pi (x : ℝ) (n : ℕ) : tan (x + n * π) = tan x :=
  tan_periodic.nat_mul n x

theorem tan_add_int_mul_pi (x : ℝ) (n : ℤ) : tan (x + n * π) = tan x :=
  tan_periodic.int_mul n x

theorem tan_sub_nat_mul_pi (x : ℝ) (n : ℕ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_nat_mul_eq n

theorem tan_sub_int_mul_pi (x : ℝ) (n : ℤ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_int_mul_eq n

theorem tan_nat_mul_pi_sub (x : ℝ) (n : ℕ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

theorem tan_int_mul_pi_sub (x : ℝ) (n : ℤ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.int_mul_sub_eq n

theorem tendsto_sin_pi_div_two : Tendsto sin (𝓝[<] (π / 2)) (𝓝 1) := by
  convert continuous_sin.continuousWithinAt.tendsto
  simp

theorem tendsto_cos_pi_div_two : Tendsto cos (𝓝[<] (π / 2)) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert continuous_cos.continuousWithinAt.tendsto
    simp
  · filter_upwards [Ioo_mem_nhdsLT (neg_lt_self pi_div_two_pos)] with x hx
    exact cos_pos_of_mem_Ioo hx

theorem tendsto_tan_pi_div_two : Tendsto tan (𝓝[<] (π / 2)) atTop := by
  convert tendsto_cos_pi_div_two.inv_tendsto_nhdsGT_zero.atTop_mul_pos zero_lt_one
    tendsto_sin_pi_div_two using 1
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]

theorem tendsto_sin_neg_pi_div_two : Tendsto sin (𝓝[>] (-(π / 2))) (𝓝 (-1)) := by
  convert continuous_sin.continuousWithinAt.tendsto using 2
  simp

theorem tendsto_cos_neg_pi_div_two : Tendsto cos (𝓝[>] (-(π / 2))) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert continuous_cos.continuousWithinAt.tendsto
    simp
  · filter_upwards [Ioo_mem_nhdsGT (neg_lt_self pi_div_two_pos)] with x hx
    exact cos_pos_of_mem_Ioo hx

theorem tendsto_tan_neg_pi_div_two : Tendsto tan (𝓝[>] (-(π / 2))) atBot := by
  convert tendsto_cos_neg_pi_div_two.inv_tendsto_nhdsGT_zero.atTop_mul_neg (by simp)
      tendsto_sin_neg_pi_div_two using 1
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]

end Real

namespace Complex

open Real

theorem sin_eq_zero_iff_cos_eq {z : ℂ} : sin z = 0 ↔ cos z = 1 ∨ cos z = -1 := by
  rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq, sq, sq, right_eq_add, mul_eq_zero, or_self]

theorem cos_eq_zero_iff_sin_eq {z : ℂ} : cos z = 0 ↔ sin z = 1 ∨ sin z = -1 := by
  rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq, sq, sq, left_eq_add, mul_eq_zero, or_self]

@[simp]
theorem cos_pi_div_two : cos (π / 2) = 0 :=
  calc
    cos (π / 2) = Real.cos (π / 2) := by rw [ofReal_cos]; simp
    _ = 0 := by simp

@[simp]
theorem sin_pi_div_two : sin (π / 2) = 1 :=
  calc
    sin (π / 2) = Real.sin (π / 2) := by rw [ofReal_sin]; simp
    _ = 1 := by simp

@[simp]
theorem sin_pi : sin π = 0 := by rw [← ofReal_sin, Real.sin_pi]; simp

@[simp]
theorem cos_pi : cos π = -1 := by rw [← ofReal_cos, Real.cos_pi]; simp

@[simp]
theorem sin_two_pi : sin (2 * π) = 0 := by simp [two_mul, sin_add]

@[simp]
theorem cos_two_pi : cos (2 * π) = 1 := by simp [two_mul, cos_add]

theorem sin_antiperiodic : Function.Antiperiodic sin π := by simp [sin_add]

theorem sin_periodic : Function.Periodic sin (2 * π) :=
  sin_antiperiodic.periodic_two_mul

theorem sin_add_pi (x : ℂ) : sin (x + π) = -sin x :=
  sin_antiperiodic x

theorem sin_add_two_pi (x : ℂ) : sin (x + 2 * π) = sin x :=
  sin_periodic x

theorem sin_sub_pi (x : ℂ) : sin (x - π) = -sin x :=
  sin_antiperiodic.sub_eq x

theorem sin_sub_two_pi (x : ℂ) : sin (x - 2 * π) = sin x :=
  sin_periodic.sub_eq x

theorem sin_pi_sub (x : ℂ) : sin (π - x) = sin x :=
  neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

theorem sin_two_pi_sub (x : ℂ) : sin (2 * π - x) = -sin x :=
  sin_neg x ▸ sin_periodic.sub_eq'

theorem sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
  sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

theorem sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
  sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

theorem sin_add_nat_mul_two_pi (x : ℂ) (n : ℕ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.nat_mul n x

theorem sin_add_int_mul_two_pi (x : ℂ) (n : ℤ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.int_mul n x

theorem sin_sub_nat_mul_two_pi (x : ℂ) (n : ℕ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_nat_mul_eq n

theorem sin_sub_int_mul_two_pi (x : ℂ) (n : ℤ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_int_mul_eq n

theorem sin_nat_mul_two_pi_sub (x : ℂ) (n : ℕ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

theorem sin_int_mul_two_pi_sub (x : ℂ) (n : ℤ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.int_mul_sub_eq n

theorem cos_antiperiodic : Function.Antiperiodic cos π := by simp [cos_add]

theorem cos_periodic : Function.Periodic cos (2 * π) :=
  cos_antiperiodic.periodic_two_mul

theorem cos_add_pi (x : ℂ) : cos (x + π) = -cos x :=
  cos_antiperiodic x

theorem cos_add_two_pi (x : ℂ) : cos (x + 2 * π) = cos x :=
  cos_periodic x

theorem cos_sub_pi (x : ℂ) : cos (x - π) = -cos x :=
  cos_antiperiodic.sub_eq x

theorem cos_sub_two_pi (x : ℂ) : cos (x - 2 * π) = cos x :=
  cos_periodic.sub_eq x

theorem cos_pi_sub (x : ℂ) : cos (π - x) = -cos x :=
  cos_neg x ▸ cos_antiperiodic.sub_eq'

theorem cos_two_pi_sub (x : ℂ) : cos (2 * π - x) = cos x :=
  cos_neg x ▸ cos_periodic.sub_eq'

theorem cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.nat_mul_eq n).trans cos_zero

theorem cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.int_mul_eq n).trans cos_zero

theorem cos_add_nat_mul_two_pi (x : ℂ) (n : ℕ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.nat_mul n x

theorem cos_add_int_mul_two_pi (x : ℂ) (n : ℤ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.int_mul n x

theorem cos_sub_nat_mul_two_pi (x : ℂ) (n : ℕ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_nat_mul_eq n

theorem cos_sub_int_mul_two_pi (x : ℂ) (n : ℤ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_int_mul_eq n

theorem cos_nat_mul_two_pi_sub (x : ℂ) (n : ℕ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

theorem cos_int_mul_two_pi_sub (x : ℂ) (n : ℤ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.int_mul_sub_eq n

theorem cos_nat_mul_two_pi_add_pi (n : ℕ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

theorem cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

theorem cos_nat_mul_two_pi_sub_pi (n : ℕ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

theorem cos_int_mul_two_pi_sub_pi (n : ℤ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

theorem sin_add_pi_div_two (x : ℂ) : sin (x + π / 2) = cos x := by simp [sin_add]

theorem sin_sub_pi_div_two (x : ℂ) : sin (x - π / 2) = -cos x := by simp [sub_eq_add_neg, sin_add]

theorem sin_pi_div_two_sub (x : ℂ) : sin (π / 2 - x) = cos x := by simp [sub_eq_add_neg, sin_add]

theorem cos_add_pi_div_two (x : ℂ) : cos (x + π / 2) = -sin x := by simp [cos_add]

theorem cos_sub_pi_div_two (x : ℂ) : cos (x - π / 2) = sin x := by simp [sub_eq_add_neg, cos_add]

theorem cos_pi_div_two_sub (x : ℂ) : cos (π / 2 - x) = sin x := by
  rw [← cos_neg, neg_sub, cos_sub_pi_div_two]

theorem tan_periodic : Function.Periodic tan π := by
  simpa only [tan_eq_sin_div_cos] using sin_antiperiodic.div cos_antiperiodic

theorem tan_add_pi (x : ℂ) : tan (x + π) = tan x :=
  tan_periodic x

theorem tan_sub_pi (x : ℂ) : tan (x - π) = tan x :=
  tan_periodic.sub_eq x

theorem tan_pi_sub (x : ℂ) : tan (π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.sub_eq'

theorem tan_pi_div_two_sub (x : ℂ) : tan (π / 2 - x) = (tan x)⁻¹ := by
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, inv_div, sin_pi_div_two_sub, cos_pi_div_two_sub]

theorem tan_nat_mul_pi (n : ℕ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.nat_mul_eq n

theorem tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.int_mul_eq n

theorem tan_add_nat_mul_pi (x : ℂ) (n : ℕ) : tan (x + n * π) = tan x :=
  tan_periodic.nat_mul n x

theorem tan_add_int_mul_pi (x : ℂ) (n : ℤ) : tan (x + n * π) = tan x :=
  tan_periodic.int_mul n x

theorem tan_sub_nat_mul_pi (x : ℂ) (n : ℕ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_nat_mul_eq n

theorem tan_sub_int_mul_pi (x : ℂ) (n : ℤ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_int_mul_eq n

theorem tan_nat_mul_pi_sub (x : ℂ) (n : ℕ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

theorem tan_int_mul_pi_sub (x : ℂ) (n : ℤ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.int_mul_sub_eq n

theorem exp_antiperiodic : Function.Antiperiodic exp (π * I) := by simp [exp_add, exp_mul_I]

theorem exp_periodic : Function.Periodic exp (2 * π * I) :=
  (mul_assoc (2 : ℂ) π I).symm ▸ exp_antiperiodic.periodic_two_mul

theorem exp_mul_I_antiperiodic : Function.Antiperiodic (fun x => exp (x * I)) π := by
  simpa only [mul_inv_cancel_right₀ I_ne_zero] using exp_antiperiodic.mul_const I_ne_zero

theorem exp_mul_I_periodic : Function.Periodic (fun x => exp (x * I)) (2 * π) :=
  exp_mul_I_antiperiodic.periodic_two_mul

@[simp]
theorem exp_pi_mul_I : exp (π * I) = -1 :=
  exp_zero ▸ exp_antiperiodic.eq

@[simp]
theorem exp_two_pi_mul_I : exp (2 * π * I) = 1 :=
  exp_periodic.eq.trans exp_zero

@[simp]
lemma exp_pi_div_two_mul_I : exp (π / 2 * I) = I := by
  rw [← cos_add_sin_I, cos_pi_div_two, sin_pi_div_two, one_mul, zero_add]

@[simp]
lemma exp_neg_pi_div_two_mul_I : exp (-π / 2 * I) = -I := by
  rw [← cos_add_sin_I, neg_div, cos_neg, cos_pi_div_two, sin_neg, sin_pi_div_two, zero_add, neg_mul,
    one_mul]

@[simp]
theorem exp_nat_mul_two_pi_mul_I (n : ℕ) : exp (n * (2 * π * I)) = 1 :=
  (exp_periodic.nat_mul_eq n).trans exp_zero

@[simp]
theorem exp_int_mul_two_pi_mul_I (n : ℤ) : exp (n * (2 * π * I)) = 1 :=
  (exp_periodic.int_mul_eq n).trans exp_zero

@[simp]
theorem exp_add_pi_mul_I (z : ℂ) : exp (z + π * I) = -exp z :=
  exp_antiperiodic z

@[simp]
theorem exp_sub_pi_mul_I (z : ℂ) : exp (z - π * I) = -exp z :=
  exp_antiperiodic.sub_eq z

/-- A supporting lemma for the **Phragmen-Lindelöf principle** in a horizontal strip. If `z : ℂ`
belongs to a horizontal strip `|Complex.im z| ≤ b`, `b ≤ π / 2`, and `a ≤ 0`, then
$$\left|exp^{a\left(e^{z}+e^{-z}\right)}\right| \le e^{a\cos b \exp^{|re z|}}.$$
-/
theorem norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le {a b : ℝ} (ha : a ≤ 0) {z : ℂ}
    (hz : |z.im| ≤ b) (hb : b ≤ π / 2) :
    ‖exp (a * (exp z + exp (-z)))‖ ≤ Real.exp (a * Real.cos b * Real.exp |z.re|) := by
  simp only [norm_exp, Real.exp_le_exp, re_ofReal_mul, add_re, exp_re, neg_im, Real.cos_neg, ←
    add_mul, mul_assoc, mul_comm (Real.cos b), neg_re, ← Real.cos_abs z.im]
  have : Real.exp |z.re| ≤ Real.exp z.re + Real.exp (-z.re) :=
    apply_abs_le_add_of_nonneg (fun x => (Real.exp_pos x).le) z.re
  refine mul_le_mul_of_nonpos_left (mul_le_mul this ?_ ?_ ((Real.exp_pos _).le.trans this)) ha
  · exact
      Real.cos_le_cos_of_nonneg_of_le_pi (_root_.abs_nonneg _)
        (hb.trans <| half_le_self <| Real.pi_pos.le) hz
  · refine Real.cos_nonneg_of_mem_Icc ⟨?_, hb⟩
    exact (neg_nonpos.2 <| Real.pi_div_two_pos.le).trans ((_root_.abs_nonneg _).trans hz)

end Complex
