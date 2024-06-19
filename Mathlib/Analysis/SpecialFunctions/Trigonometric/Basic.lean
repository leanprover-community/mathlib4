/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity.Core
import Mathlib.Algebra.Ring.NegOnePow

#align_import analysis.special_functions.trigonometric.basic from "leanprover-community/mathlib"@"2c1d8ca2812b64f88992a5294ea3dba144755cd1"

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

open scoped Classical
open Topology Filter Set

namespace Complex

@[continuity]
theorem continuous_sin : Continuous sin := by
  change Continuous fun z => (exp (-z * I) - exp (z * I)) * I / 2
  continuity
#align complex.continuous_sin Complex.continuous_sin

theorem continuousOn_sin {s : Set ℂ} : ContinuousOn sin s :=
  continuous_sin.continuousOn
#align complex.continuous_on_sin Complex.continuousOn_sin

@[continuity]
theorem continuous_cos : Continuous cos := by
  change Continuous fun z => (exp (z * I) + exp (-z * I)) / 2
  continuity
#align complex.continuous_cos Complex.continuous_cos

theorem continuousOn_cos {s : Set ℂ} : ContinuousOn cos s :=
  continuous_cos.continuousOn
#align complex.continuous_on_cos Complex.continuousOn_cos

@[continuity]
theorem continuous_sinh : Continuous sinh := by
  change Continuous fun z => (exp z - exp (-z)) / 2
  continuity
#align complex.continuous_sinh Complex.continuous_sinh

@[continuity]
theorem continuous_cosh : Continuous cosh := by
  change Continuous fun z => (exp z + exp (-z)) / 2
  continuity
#align complex.continuous_cosh Complex.continuous_cosh

end Complex

namespace Real

variable {x y z : ℝ}

@[continuity]
theorem continuous_sin : Continuous sin :=
  Complex.continuous_re.comp (Complex.continuous_sin.comp Complex.continuous_ofReal)
#align real.continuous_sin Real.continuous_sin

theorem continuousOn_sin {s} : ContinuousOn sin s :=
  continuous_sin.continuousOn
#align real.continuous_on_sin Real.continuousOn_sin

@[continuity]
theorem continuous_cos : Continuous cos :=
  Complex.continuous_re.comp (Complex.continuous_cos.comp Complex.continuous_ofReal)
#align real.continuous_cos Real.continuous_cos

theorem continuousOn_cos {s} : ContinuousOn cos s :=
  continuous_cos.continuousOn
#align real.continuous_on_cos Real.continuousOn_cos

@[continuity]
theorem continuous_sinh : Continuous sinh :=
  Complex.continuous_re.comp (Complex.continuous_sinh.comp Complex.continuous_ofReal)
#align real.continuous_sinh Real.continuous_sinh

@[continuity]
theorem continuous_cosh : Continuous cosh :=
  Complex.continuous_re.comp (Complex.continuous_cosh.comp Complex.continuous_ofReal)
#align real.continuous_cosh Real.continuous_cosh

end Real

namespace Real

theorem exists_cos_eq_zero : 0 ∈ cos '' Icc (1 : ℝ) 2 :=
  intermediate_value_Icc' (by norm_num) continuousOn_cos
    ⟨le_of_lt cos_two_neg, le_of_lt cos_one_pos⟩
#align real.exists_cos_eq_zero Real.exists_cos_eq_zero

/-- The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from
which one can derive all its properties. For explicit bounds on π, see `Data.Real.Pi.Bounds`. -/
protected noncomputable def pi : ℝ :=
  2 * Classical.choose exists_cos_eq_zero
#align real.pi Real.pi

@[inherit_doc]
scoped notation "π" => Real.pi

@[simp]
theorem cos_pi_div_two : cos (π / 2) = 0 := by
  rw [Real.pi, mul_div_cancel_left₀ _ (two_ne_zero' ℝ)]
  exact (Classical.choose_spec exists_cos_eq_zero).2
#align real.cos_pi_div_two Real.cos_pi_div_two

theorem one_le_pi_div_two : (1 : ℝ) ≤ π / 2 := by
  rw [Real.pi, mul_div_cancel_left₀ _ (two_ne_zero' ℝ)]
  exact (Classical.choose_spec exists_cos_eq_zero).1.1
#align real.one_le_pi_div_two Real.one_le_pi_div_two

theorem pi_div_two_le_two : π / 2 ≤ 2 := by
  rw [Real.pi, mul_div_cancel_left₀ _ (two_ne_zero' ℝ)]
  exact (Classical.choose_spec exists_cos_eq_zero).1.2
#align real.pi_div_two_le_two Real.pi_div_two_le_two

theorem two_le_pi : (2 : ℝ) ≤ π :=
  (div_le_div_right (show (0 : ℝ) < 2 by norm_num)).1
    (by rw [div_self (two_ne_zero' ℝ)]; exact one_le_pi_div_two)
#align real.two_le_pi Real.two_le_pi

theorem pi_le_four : π ≤ 4 :=
  (div_le_div_right (show (0 : ℝ) < 2 by norm_num)).1
    (calc
      π / 2 ≤ 2 := pi_div_two_le_two
      _ = 4 / 2 := by norm_num)
#align real.pi_le_four Real.pi_le_four

theorem pi_pos : 0 < π :=
  lt_of_lt_of_le (by norm_num) two_le_pi
#align real.pi_pos Real.pi_pos

theorem pi_nonneg : 0 ≤ π :=
  pi_pos.le

theorem pi_ne_zero : π ≠ 0 :=
  pi_pos.ne'
#align real.pi_ne_zero Real.pi_ne_zero

theorem pi_div_two_pos : 0 < π / 2 :=
  half_pos pi_pos
#align real.pi_div_two_pos Real.pi_div_two_pos

theorem two_pi_pos : 0 < 2 * π := by linarith [pi_pos]
#align real.two_pi_pos Real.two_pi_pos

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
#align nnreal.pi NNReal.pi

@[simp]
theorem coe_real_pi : (pi : ℝ) = π :=
  rfl
#align nnreal.coe_real_pi NNReal.coe_real_pi

theorem pi_pos : 0 < pi := mod_cast Real.pi_pos
#align nnreal.pi_pos NNReal.pi_pos

theorem pi_ne_zero : pi ≠ 0 :=
  pi_pos.ne'
#align nnreal.pi_ne_zero NNReal.pi_ne_zero

end NNReal

namespace Real

open Real

@[simp]
theorem sin_pi : sin π = 0 := by
  rw [← mul_div_cancel_left₀ π (two_ne_zero' ℝ), two_mul, add_div, sin_add, cos_pi_div_two]; simp
#align real.sin_pi Real.sin_pi

@[simp]
theorem cos_pi : cos π = -1 := by
  rw [← mul_div_cancel_left₀ π (two_ne_zero' ℝ), mul_div_assoc, cos_two_mul, cos_pi_div_two]
  norm_num
#align real.cos_pi Real.cos_pi

@[simp]
theorem sin_two_pi : sin (2 * π) = 0 := by simp [two_mul, sin_add]
#align real.sin_two_pi Real.sin_two_pi

@[simp]
theorem cos_two_pi : cos (2 * π) = 1 := by simp [two_mul, cos_add]
#align real.cos_two_pi Real.cos_two_pi

theorem sin_antiperiodic : Function.Antiperiodic sin π := by simp [sin_add]
#align real.sin_antiperiodic Real.sin_antiperiodic

theorem sin_periodic : Function.Periodic sin (2 * π) :=
  sin_antiperiodic.periodic_two_mul
#align real.sin_periodic Real.sin_periodic

@[simp]
theorem sin_add_pi (x : ℝ) : sin (x + π) = -sin x :=
  sin_antiperiodic x
#align real.sin_add_pi Real.sin_add_pi

@[simp]
theorem sin_add_two_pi (x : ℝ) : sin (x + 2 * π) = sin x :=
  sin_periodic x
#align real.sin_add_two_pi Real.sin_add_two_pi

@[simp]
theorem sin_sub_pi (x : ℝ) : sin (x - π) = -sin x :=
  sin_antiperiodic.sub_eq x
#align real.sin_sub_pi Real.sin_sub_pi

@[simp]
theorem sin_sub_two_pi (x : ℝ) : sin (x - 2 * π) = sin x :=
  sin_periodic.sub_eq x
#align real.sin_sub_two_pi Real.sin_sub_two_pi

@[simp]
theorem sin_pi_sub (x : ℝ) : sin (π - x) = sin x :=
  neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'
#align real.sin_pi_sub Real.sin_pi_sub

@[simp]
theorem sin_two_pi_sub (x : ℝ) : sin (2 * π - x) = -sin x :=
  sin_neg x ▸ sin_periodic.sub_eq'
#align real.sin_two_pi_sub Real.sin_two_pi_sub

@[simp]
theorem sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
  sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n
#align real.sin_nat_mul_pi Real.sin_nat_mul_pi

@[simp]
theorem sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
  sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n
#align real.sin_int_mul_pi Real.sin_int_mul_pi

@[simp]
theorem sin_add_nat_mul_two_pi (x : ℝ) (n : ℕ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.nat_mul n x
#align real.sin_add_nat_mul_two_pi Real.sin_add_nat_mul_two_pi

@[simp]
theorem sin_add_int_mul_two_pi (x : ℝ) (n : ℤ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.int_mul n x
#align real.sin_add_int_mul_two_pi Real.sin_add_int_mul_two_pi

@[simp]
theorem sin_sub_nat_mul_two_pi (x : ℝ) (n : ℕ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_nat_mul_eq n
#align real.sin_sub_nat_mul_two_pi Real.sin_sub_nat_mul_two_pi

@[simp]
theorem sin_sub_int_mul_two_pi (x : ℝ) (n : ℤ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_int_mul_eq n
#align real.sin_sub_int_mul_two_pi Real.sin_sub_int_mul_two_pi

@[simp]
theorem sin_nat_mul_two_pi_sub (x : ℝ) (n : ℕ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.nat_mul_sub_eq n
#align real.sin_nat_mul_two_pi_sub Real.sin_nat_mul_two_pi_sub

@[simp]
theorem sin_int_mul_two_pi_sub (x : ℝ) (n : ℤ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.int_mul_sub_eq n
#align real.sin_int_mul_two_pi_sub Real.sin_int_mul_two_pi_sub

theorem sin_add_int_mul_pi (x : ℝ) (n : ℤ) : sin (x + n * π) = (-1) ^ n * sin x :=
  n.coe_negOnePow ℝ ▸ sin_antiperiodic.add_int_mul_eq n

theorem sin_add_nat_mul_pi (x : ℝ) (n : ℕ) : sin (x + n * π) = (-1) ^ n * sin x :=
  sin_antiperiodic.add_nat_mul_eq n

theorem sin_sub_int_mul_pi (x : ℝ) (n : ℤ) : sin (x - n * π) = (-1) ^ n * sin x :=
  n.coe_negOnePow ℝ ▸ sin_antiperiodic.sub_int_mul_eq n

theorem sin_sub_nat_mul_pi (x : ℝ) (n : ℕ) : sin (x - n * π) = (-1) ^ n * sin x :=
  sin_antiperiodic.sub_nat_mul_eq n

theorem sin_int_mul_pi_sub (x : ℝ) (n : ℤ) : sin (n * π - x) = -((-1) ^ n * sin x) := by
  simpa only [sin_neg, mul_neg, Int.coe_negOnePow] using sin_antiperiodic.int_mul_sub_eq n

theorem sin_nat_mul_pi_sub (x : ℝ) (n : ℕ) : sin (n * π - x) = -((-1) ^ n * sin x) := by
  simpa only [sin_neg, mul_neg] using sin_antiperiodic.nat_mul_sub_eq n

theorem cos_antiperiodic : Function.Antiperiodic cos π := by simp [cos_add]
#align real.cos_antiperiodic Real.cos_antiperiodic

theorem cos_periodic : Function.Periodic cos (2 * π) :=
  cos_antiperiodic.periodic_two_mul
#align real.cos_periodic Real.cos_periodic

@[simp]
theorem cos_add_pi (x : ℝ) : cos (x + π) = -cos x :=
  cos_antiperiodic x
#align real.cos_add_pi Real.cos_add_pi

@[simp]
theorem cos_add_two_pi (x : ℝ) : cos (x + 2 * π) = cos x :=
  cos_periodic x
#align real.cos_add_two_pi Real.cos_add_two_pi

@[simp]
theorem cos_sub_pi (x : ℝ) : cos (x - π) = -cos x :=
  cos_antiperiodic.sub_eq x
#align real.cos_sub_pi Real.cos_sub_pi

@[simp]
theorem cos_sub_two_pi (x : ℝ) : cos (x - 2 * π) = cos x :=
  cos_periodic.sub_eq x
#align real.cos_sub_two_pi Real.cos_sub_two_pi

@[simp]
theorem cos_pi_sub (x : ℝ) : cos (π - x) = -cos x :=
  cos_neg x ▸ cos_antiperiodic.sub_eq'
#align real.cos_pi_sub Real.cos_pi_sub

@[simp]
theorem cos_two_pi_sub (x : ℝ) : cos (2 * π - x) = cos x :=
  cos_neg x ▸ cos_periodic.sub_eq'
#align real.cos_two_pi_sub Real.cos_two_pi_sub

@[simp]
theorem cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.nat_mul_eq n).trans cos_zero
#align real.cos_nat_mul_two_pi Real.cos_nat_mul_two_pi

@[simp]
theorem cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.int_mul_eq n).trans cos_zero
#align real.cos_int_mul_two_pi Real.cos_int_mul_two_pi

@[simp]
theorem cos_add_nat_mul_two_pi (x : ℝ) (n : ℕ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.nat_mul n x
#align real.cos_add_nat_mul_two_pi Real.cos_add_nat_mul_two_pi

@[simp]
theorem cos_add_int_mul_two_pi (x : ℝ) (n : ℤ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.int_mul n x
#align real.cos_add_int_mul_two_pi Real.cos_add_int_mul_two_pi

@[simp]
theorem cos_sub_nat_mul_two_pi (x : ℝ) (n : ℕ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_nat_mul_eq n
#align real.cos_sub_nat_mul_two_pi Real.cos_sub_nat_mul_two_pi

@[simp]
theorem cos_sub_int_mul_two_pi (x : ℝ) (n : ℤ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_int_mul_eq n
#align real.cos_sub_int_mul_two_pi Real.cos_sub_int_mul_two_pi

@[simp]
theorem cos_nat_mul_two_pi_sub (x : ℝ) (n : ℕ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.nat_mul_sub_eq n
#align real.cos_nat_mul_two_pi_sub Real.cos_nat_mul_two_pi_sub

@[simp]
theorem cos_int_mul_two_pi_sub (x : ℝ) (n : ℤ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.int_mul_sub_eq n
#align real.cos_int_mul_two_pi_sub Real.cos_int_mul_two_pi_sub

theorem cos_add_int_mul_pi (x : ℝ) (n : ℤ) : cos (x + n * π) = (-1) ^ n * cos x :=
  n.coe_negOnePow ℝ ▸ cos_antiperiodic.add_int_mul_eq n

theorem cos_add_nat_mul_pi (x : ℝ) (n : ℕ) : cos (x + n * π) = (-1) ^ n * cos x :=
  cos_antiperiodic.add_nat_mul_eq n

theorem cos_sub_int_mul_pi (x : ℝ) (n : ℤ) : cos (x - n * π) = (-1) ^ n * cos x :=
  n.coe_negOnePow ℝ ▸ cos_antiperiodic.sub_int_mul_eq n

theorem cos_sub_nat_mul_pi (x : ℝ) (n : ℕ) : cos (x - n * π) = (-1) ^ n * cos x :=
  cos_antiperiodic.sub_nat_mul_eq n

theorem cos_int_mul_pi_sub (x : ℝ) (n : ℤ) : cos (n * π - x) = (-1) ^ n * cos x :=
  n.coe_negOnePow ℝ ▸ cos_neg x ▸ cos_antiperiodic.int_mul_sub_eq n

theorem cos_nat_mul_pi_sub (x : ℝ) (n : ℕ) : cos (n * π - x) = (-1) ^ n * cos x :=
  cos_neg x ▸ cos_antiperiodic.nat_mul_sub_eq n

-- Porting note (#10618): was @[simp], but simp can prove it
theorem cos_nat_mul_two_pi_add_pi (n : ℕ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic
#align real.cos_nat_mul_two_pi_add_pi Real.cos_nat_mul_two_pi_add_pi

-- Porting note (#10618): was @[simp], but simp can prove it
theorem cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic
#align real.cos_int_mul_two_pi_add_pi Real.cos_int_mul_two_pi_add_pi

-- Porting note (#10618): was @[simp], but simp can prove it
theorem cos_nat_mul_two_pi_sub_pi (n : ℕ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic
#align real.cos_nat_mul_two_pi_sub_pi Real.cos_nat_mul_two_pi_sub_pi

-- Porting note (#10618): was @[simp], but simp can prove it
theorem cos_int_mul_two_pi_sub_pi (n : ℤ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic
#align real.cos_int_mul_two_pi_sub_pi Real.cos_int_mul_two_pi_sub_pi

theorem sin_pos_of_pos_of_lt_pi {x : ℝ} (h0x : 0 < x) (hxp : x < π) : 0 < sin x :=
  if hx2 : x ≤ 2 then sin_pos_of_pos_of_le_two h0x hx2
  else
    have : (2 : ℝ) + 2 = 4 := by norm_num
    have : π - x ≤ 2 :=
      sub_le_iff_le_add.2 (le_trans pi_le_four (this ▸ add_le_add_left (le_of_not_ge hx2) _))
    sin_pi_sub x ▸ sin_pos_of_pos_of_le_two (sub_pos.2 hxp) this
#align real.sin_pos_of_pos_of_lt_pi Real.sin_pos_of_pos_of_lt_pi

theorem sin_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 π) : 0 < sin x :=
  sin_pos_of_pos_of_lt_pi hx.1 hx.2
#align real.sin_pos_of_mem_Ioo Real.sin_pos_of_mem_Ioo

theorem sin_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc 0 π) : 0 ≤ sin x := by
  rw [← closure_Ioo pi_ne_zero.symm] at hx
  exact
    closure_lt_subset_le continuous_const continuous_sin
      (closure_mono (fun y => sin_pos_of_mem_Ioo) hx)
#align real.sin_nonneg_of_mem_Icc Real.sin_nonneg_of_mem_Icc

theorem sin_nonneg_of_nonneg_of_le_pi {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π) : 0 ≤ sin x :=
  sin_nonneg_of_mem_Icc ⟨h0x, hxp⟩
#align real.sin_nonneg_of_nonneg_of_le_pi Real.sin_nonneg_of_nonneg_of_le_pi

theorem sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx0 : x < 0) (hpx : -π < x) : sin x < 0 :=
  neg_pos.1 <| sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)
#align real.sin_neg_of_neg_of_neg_pi_lt Real.sin_neg_of_neg_of_neg_pi_lt

theorem sin_nonpos_of_nonnpos_of_neg_pi_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -π ≤ x) : sin x ≤ 0 :=
  neg_nonneg.1 <| sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hx0) (neg_le.1 hpx)
#align real.sin_nonpos_of_nonnpos_of_neg_pi_le Real.sin_nonpos_of_nonnpos_of_neg_pi_le

@[simp]
theorem sin_pi_div_two : sin (π / 2) = 1 :=
  have : sin (π / 2) = 1 ∨ sin (π / 2) = -1 := by
    simpa [sq, mul_self_eq_one_iff] using sin_sq_add_cos_sq (π / 2)
  this.resolve_right fun h =>
    show ¬(0 : ℝ) < -1 by norm_num <|
      h ▸ sin_pos_of_pos_of_lt_pi pi_div_two_pos (half_lt_self pi_pos)
#align real.sin_pi_div_two Real.sin_pi_div_two

theorem sin_add_pi_div_two (x : ℝ) : sin (x + π / 2) = cos x := by simp [sin_add]
#align real.sin_add_pi_div_two Real.sin_add_pi_div_two

theorem sin_sub_pi_div_two (x : ℝ) : sin (x - π / 2) = -cos x := by simp [sub_eq_add_neg, sin_add]
#align real.sin_sub_pi_div_two Real.sin_sub_pi_div_two

theorem sin_pi_div_two_sub (x : ℝ) : sin (π / 2 - x) = cos x := by simp [sub_eq_add_neg, sin_add]
#align real.sin_pi_div_two_sub Real.sin_pi_div_two_sub

theorem cos_add_pi_div_two (x : ℝ) : cos (x + π / 2) = -sin x := by simp [cos_add]
#align real.cos_add_pi_div_two Real.cos_add_pi_div_two

theorem cos_sub_pi_div_two (x : ℝ) : cos (x - π / 2) = sin x := by simp [sub_eq_add_neg, cos_add]
#align real.cos_sub_pi_div_two Real.cos_sub_pi_div_two

theorem cos_pi_div_two_sub (x : ℝ) : cos (π / 2 - x) = sin x := by
  rw [← cos_neg, neg_sub, cos_sub_pi_div_two]
#align real.cos_pi_div_two_sub Real.cos_pi_div_two_sub

theorem cos_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) : 0 < cos x :=
  sin_add_pi_div_two x ▸ sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩
#align real.cos_pos_of_mem_Ioo Real.cos_pos_of_mem_Ioo

theorem cos_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) : 0 ≤ cos x :=
  sin_add_pi_div_two x ▸ sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩
#align real.cos_nonneg_of_mem_Icc Real.cos_nonneg_of_mem_Icc

theorem cos_nonneg_of_neg_pi_div_two_le_of_le {x : ℝ} (hl : -(π / 2) ≤ x) (hu : x ≤ π / 2) :
    0 ≤ cos x :=
  cos_nonneg_of_mem_Icc ⟨hl, hu⟩
#align real.cos_nonneg_of_neg_pi_div_two_le_of_le Real.cos_nonneg_of_neg_pi_div_two_le_of_le

theorem cos_neg_of_pi_div_two_lt_of_lt {x : ℝ} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2) :
    cos x < 0 :=
  neg_pos.1 <| cos_pi_sub x ▸ cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
#align real.cos_neg_of_pi_div_two_lt_of_lt Real.cos_neg_of_pi_div_two_lt_of_lt

theorem cos_nonpos_of_pi_div_two_le_of_le {x : ℝ} (hx₁ : π / 2 ≤ x) (hx₂ : x ≤ π + π / 2) :
    cos x ≤ 0 :=
  neg_nonneg.1 <| cos_pi_sub x ▸ cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
#align real.cos_nonpos_of_pi_div_two_le_of_le Real.cos_nonpos_of_pi_div_two_le_of_le

theorem sin_eq_sqrt_one_sub_cos_sq {x : ℝ} (hl : 0 ≤ x) (hu : x ≤ π) :
    sin x = √(1 - cos x ^ 2) := by
  rw [← abs_sin_eq_sqrt_one_sub_cos_sq, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hl hu)]
#align real.sin_eq_sqrt_one_sub_cos_sq Real.sin_eq_sqrt_one_sub_cos_sq

theorem cos_eq_sqrt_one_sub_sin_sq {x : ℝ} (hl : -(π / 2) ≤ x) (hu : x ≤ π / 2) :
    cos x = √(1 - sin x ^ 2) := by
  rw [← abs_cos_eq_sqrt_one_sub_sin_sq, abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨hl, hu⟩)]
#align real.cos_eq_sqrt_one_sub_sin_sq Real.cos_eq_sqrt_one_sub_sin_sq

lemma cos_half {x : ℝ} (hl : -π ≤ x) (hr : x ≤ π) : cos (x / 2) = sqrt ((1 + cos x) / 2) := by
  have : 0 ≤ cos (x / 2) := cos_nonneg_of_mem_Icc <| by constructor <;> linarith
  rw [← sqrt_sq this, cos_sq, add_div, two_mul, add_halves]

lemma abs_sin_half (x : ℝ) : |sin (x / 2)| = sqrt ((1 - cos x) / 2) := by
  rw [← sqrt_sq_eq_abs, sin_sq_eq_half_sub, two_mul, add_halves, sub_div]

lemma sin_half_eq_sqrt {x : ℝ} (hl : 0 ≤ x) (hr : x ≤ 2 * π) :
    sin (x / 2) = sqrt ((1 - cos x) / 2) := by
  rw [← abs_sin_half, abs_of_nonneg]
  apply sin_nonneg_of_nonneg_of_le_pi <;> linarith

lemma sin_half_eq_neg_sqrt {x : ℝ} (hl : -(2 * π) ≤ x) (hr : x ≤ 0) :
    sin (x / 2) = -sqrt ((1 - cos x) / 2) := by
  rw [← abs_sin_half, abs_of_nonpos, neg_neg]
  apply sin_nonpos_of_nonnpos_of_neg_pi_le <;> linarith

theorem sin_eq_zero_iff_of_lt_of_lt {x : ℝ} (hx₁ : -π < x) (hx₂ : x < π) : sin x = 0 ↔ x = 0 :=
  ⟨fun h => by
    contrapose! h
    cases h.lt_or_lt with
    | inl h0 => exact (sin_neg_of_neg_of_neg_pi_lt h0 hx₁).ne
    | inr h0 => exact (sin_pos_of_pos_of_lt_pi h0 hx₂).ne',
  fun h => by simp [h]⟩
#align real.sin_eq_zero_iff_of_lt_of_lt Real.sin_eq_zero_iff_of_lt_of_lt

theorem sin_eq_zero_iff {x : ℝ} : sin x = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = x :=
  ⟨fun h =>
    ⟨⌊x / π⌋,
      le_antisymm (sub_nonneg.1 (Int.sub_floor_div_mul_nonneg _ pi_pos))
        (sub_nonpos.1 <|
          le_of_not_gt fun h₃ =>
            (sin_pos_of_pos_of_lt_pi h₃ (Int.sub_floor_div_mul_lt _ pi_pos)).ne
              (by simp [sub_eq_add_neg, sin_add, h, sin_int_mul_pi]))⟩,
    fun ⟨n, hn⟩ => hn ▸ sin_int_mul_pi _⟩
#align real.sin_eq_zero_iff Real.sin_eq_zero_iff

theorem sin_ne_zero_iff {x : ℝ} : sin x ≠ 0 ↔ ∀ n : ℤ, (n : ℝ) * π ≠ x := by
  rw [← not_exists, not_iff_not, sin_eq_zero_iff]
#align real.sin_ne_zero_iff Real.sin_ne_zero_iff

theorem sin_eq_zero_iff_cos_eq {x : ℝ} : sin x = 0 ↔ cos x = 1 ∨ cos x = -1 := by
  rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq x, sq, sq, ← sub_eq_iff_eq_add, sub_self]
  exact ⟨fun h => by rw [h, mul_zero], eq_zero_of_mul_self_eq_zero ∘ Eq.symm⟩
#align real.sin_eq_zero_iff_cos_eq Real.sin_eq_zero_iff_cos_eq

theorem cos_eq_one_iff (x : ℝ) : cos x = 1 ↔ ∃ n : ℤ, (n : ℝ) * (2 * π) = x :=
  ⟨fun h =>
    let ⟨n, hn⟩ := sin_eq_zero_iff.1 (sin_eq_zero_iff_cos_eq.2 (Or.inl h))
    ⟨n / 2,
      (Int.emod_two_eq_zero_or_one n).elim
        (fun hn0 => by
          rwa [← mul_assoc, ← @Int.cast_two ℝ, ← Int.cast_mul,
            Int.ediv_mul_cancel ((Int.dvd_iff_emod_eq_zero _ _).2 hn0)])
        fun hn1 => by
        rw [← Int.emod_add_ediv n 2, hn1, Int.cast_add, Int.cast_one, add_mul, one_mul, add_comm,
              mul_comm (2 : ℤ), Int.cast_mul, mul_assoc, Int.cast_two] at hn
        rw [← hn, cos_int_mul_two_pi_add_pi] at h
        exact absurd h (by norm_num)⟩,
    fun ⟨n, hn⟩ => hn ▸ cos_int_mul_two_pi _⟩
#align real.cos_eq_one_iff Real.cos_eq_one_iff

theorem cos_eq_one_iff_of_lt_of_lt {x : ℝ} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π) :
    cos x = 1 ↔ x = 0 :=
  ⟨fun h => by
    rcases (cos_eq_one_iff _).1 h with ⟨n, rfl⟩
    rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₂
    rw [neg_lt, neg_mul_eq_neg_mul, mul_lt_iff_lt_one_left two_pi_pos] at hx₁
    norm_cast at hx₁ hx₂
    obtain rfl : n = 0 := le_antisymm (by omega) (by omega)
    simp, fun h => by simp [h]⟩
#align real.cos_eq_one_iff_of_lt_of_lt Real.cos_eq_one_iff_of_lt_of_lt

theorem sin_lt_sin_of_lt_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hy₂ : y ≤ π / 2)
    (hxy : x < y) : sin x < sin y := by
  rw [← sub_pos, sin_sub_sin]
  have : 0 < sin ((y - x) / 2) := by apply sin_pos_of_pos_of_lt_pi <;> linarith
  have : 0 < cos ((y + x) / 2) := by refine cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith
  positivity
#align real.sin_lt_sin_of_lt_of_le_pi_div_two Real.sin_lt_sin_of_lt_of_le_pi_div_two

theorem strictMonoOn_sin : StrictMonoOn sin (Icc (-(π / 2)) (π / 2)) := fun _ hx _ hy hxy =>
  sin_lt_sin_of_lt_of_le_pi_div_two hx.1 hy.2 hxy
#align real.strict_mono_on_sin Real.strictMonoOn_sin

theorem cos_lt_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x < y) :
    cos y < cos x := by
  rw [← sin_pi_div_two_sub, ← sin_pi_div_two_sub]
  apply sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith
#align real.cos_lt_cos_of_nonneg_of_le_pi Real.cos_lt_cos_of_nonneg_of_le_pi

theorem cos_lt_cos_of_nonneg_of_le_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π / 2)
    (hxy : x < y) : cos y < cos x :=
  cos_lt_cos_of_nonneg_of_le_pi hx₁ (hy₂.trans (by linarith)) hxy
#align real.cos_lt_cos_of_nonneg_of_le_pi_div_two Real.cos_lt_cos_of_nonneg_of_le_pi_div_two

theorem strictAntiOn_cos : StrictAntiOn cos (Icc 0 π) := fun _ hx _ hy hxy =>
  cos_lt_cos_of_nonneg_of_le_pi hx.1 hy.2 hxy
#align real.strict_anti_on_cos Real.strictAntiOn_cos

theorem cos_le_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x ≤ y) :
    cos y ≤ cos x :=
  (strictAntiOn_cos.le_iff_le ⟨hx₁.trans hxy, hy₂⟩ ⟨hx₁, hxy.trans hy₂⟩).2 hxy
#align real.cos_le_cos_of_nonneg_of_le_pi Real.cos_le_cos_of_nonneg_of_le_pi

theorem sin_le_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hy₂ : y ≤ π / 2)
    (hxy : x ≤ y) : sin x ≤ sin y :=
  (strictMonoOn_sin.le_iff_le ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩).2 hxy
#align real.sin_le_sin_of_le_of_le_pi_div_two Real.sin_le_sin_of_le_of_le_pi_div_two

theorem injOn_sin : InjOn sin (Icc (-(π / 2)) (π / 2)) :=
  strictMonoOn_sin.injOn
#align real.inj_on_sin Real.injOn_sin

theorem injOn_cos : InjOn cos (Icc 0 π) :=
  strictAntiOn_cos.injOn
#align real.inj_on_cos Real.injOn_cos

theorem surjOn_sin : SurjOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) := by
  simpa only [sin_neg, sin_pi_div_two] using
    intermediate_value_Icc (neg_le_self pi_div_two_pos.le) continuous_sin.continuousOn
#align real.surj_on_sin Real.surjOn_sin

theorem surjOn_cos : SurjOn cos (Icc 0 π) (Icc (-1) 1) := by
  simpa only [cos_zero, cos_pi] using intermediate_value_Icc' pi_pos.le continuous_cos.continuousOn
#align real.surj_on_cos Real.surjOn_cos

theorem sin_mem_Icc (x : ℝ) : sin x ∈ Icc (-1 : ℝ) 1 :=
  ⟨neg_one_le_sin x, sin_le_one x⟩
#align real.sin_mem_Icc Real.sin_mem_Icc

theorem cos_mem_Icc (x : ℝ) : cos x ∈ Icc (-1 : ℝ) 1 :=
  ⟨neg_one_le_cos x, cos_le_one x⟩
#align real.cos_mem_Icc Real.cos_mem_Icc

theorem mapsTo_sin (s : Set ℝ) : MapsTo sin s (Icc (-1 : ℝ) 1) := fun x _ => sin_mem_Icc x
#align real.maps_to_sin Real.mapsTo_sin

theorem mapsTo_cos (s : Set ℝ) : MapsTo cos s (Icc (-1 : ℝ) 1) := fun x _ => cos_mem_Icc x
#align real.maps_to_cos Real.mapsTo_cos

theorem bijOn_sin : BijOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) :=
  ⟨mapsTo_sin _, injOn_sin, surjOn_sin⟩
#align real.bij_on_sin Real.bijOn_sin

theorem bijOn_cos : BijOn cos (Icc 0 π) (Icc (-1) 1) :=
  ⟨mapsTo_cos _, injOn_cos, surjOn_cos⟩
#align real.bij_on_cos Real.bijOn_cos

@[simp]
theorem range_cos : range cos = (Icc (-1) 1 : Set ℝ) :=
  Subset.antisymm (range_subset_iff.2 cos_mem_Icc) surjOn_cos.subset_range
#align real.range_cos Real.range_cos

@[simp]
theorem range_sin : range sin = (Icc (-1) 1 : Set ℝ) :=
  Subset.antisymm (range_subset_iff.2 sin_mem_Icc) surjOn_sin.subset_range
#align real.range_sin Real.range_sin

theorem range_cos_infinite : (range Real.cos).Infinite := by
  rw [Real.range_cos]
  exact Icc_infinite (by norm_num)
#align real.range_cos_infinite Real.range_cos_infinite

theorem range_sin_infinite : (range Real.sin).Infinite := by
  rw [Real.range_sin]
  exact Icc_infinite (by norm_num)
#align real.range_sin_infinite Real.range_sin_infinite

section CosDivSq

variable (x : ℝ)

/-- the series `sqrtTwoAddSeries x n` is `sqrt(2 + sqrt(2 + ... ))` with `n` square roots,
  starting with `x`. We define it here because `cos (pi / 2 ^ (n+1)) = sqrtTwoAddSeries 0 n / 2`
-/
@[simp]
noncomputable def sqrtTwoAddSeries (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => √(2 + sqrtTwoAddSeries x n)
#align real.sqrt_two_add_series Real.sqrtTwoAddSeries

theorem sqrtTwoAddSeries_zero : sqrtTwoAddSeries x 0 = x := by simp
#align real.sqrt_two_add_series_zero Real.sqrtTwoAddSeries_zero

theorem sqrtTwoAddSeries_one : sqrtTwoAddSeries 0 1 = √2 := by simp
#align real.sqrt_two_add_series_one Real.sqrtTwoAddSeries_one

theorem sqrtTwoAddSeries_two : sqrtTwoAddSeries 0 2 = √(2 + √2) := by simp
#align real.sqrt_two_add_series_two Real.sqrtTwoAddSeries_two

theorem sqrtTwoAddSeries_zero_nonneg : ∀ n : ℕ, 0 ≤ sqrtTwoAddSeries 0 n
  | 0 => le_refl 0
  | _ + 1 => sqrt_nonneg _
#align real.sqrt_two_add_series_zero_nonneg Real.sqrtTwoAddSeries_zero_nonneg

theorem sqrtTwoAddSeries_nonneg {x : ℝ} (h : 0 ≤ x) : ∀ n : ℕ, 0 ≤ sqrtTwoAddSeries x n
  | 0 => h
  | _ + 1 => sqrt_nonneg _
#align real.sqrt_two_add_series_nonneg Real.sqrtTwoAddSeries_nonneg

theorem sqrtTwoAddSeries_lt_two : ∀ n : ℕ, sqrtTwoAddSeries 0 n < 2
  | 0 => by norm_num
  | n + 1 => by
    refine lt_of_lt_of_le ?_ (sqrt_sq zero_lt_two.le).le
    rw [sqrtTwoAddSeries, sqrt_lt_sqrt_iff, ← lt_sub_iff_add_lt']
    · refine (sqrtTwoAddSeries_lt_two n).trans_le ?_
      norm_num
    · exact add_nonneg zero_le_two (sqrtTwoAddSeries_zero_nonneg n)
#align real.sqrt_two_add_series_lt_two Real.sqrtTwoAddSeries_lt_two

theorem sqrtTwoAddSeries_succ (x : ℝ) :
    ∀ n : ℕ, sqrtTwoAddSeries x (n + 1) = sqrtTwoAddSeries (√(2 + x)) n
  | 0 => rfl
  | n + 1 => by rw [sqrtTwoAddSeries, sqrtTwoAddSeries_succ _ _, sqrtTwoAddSeries]
#align real.sqrt_two_add_series_succ Real.sqrtTwoAddSeries_succ

theorem sqrtTwoAddSeries_monotone_left {x y : ℝ} (h : x ≤ y) :
    ∀ n : ℕ, sqrtTwoAddSeries x n ≤ sqrtTwoAddSeries y n
  | 0 => h
  | n + 1 => by
    rw [sqrtTwoAddSeries, sqrtTwoAddSeries]
    exact sqrt_le_sqrt (add_le_add_left (sqrtTwoAddSeries_monotone_left h _) _)
#align real.sqrt_two_add_series_monotone_left Real.sqrtTwoAddSeries_monotone_left

@[simp]
theorem cos_pi_over_two_pow : ∀ n : ℕ, cos (π / 2 ^ (n + 1)) = sqrtTwoAddSeries 0 n / 2
  | 0 => by simp
  | n + 1 => by
    have A : (1 : ℝ) < 2 ^ (n + 1) := one_lt_pow one_lt_two n.succ_ne_zero
    have B : π / 2 ^ (n + 1) < π := div_lt_self pi_pos A
    have C : 0 < π / 2 ^ (n + 1) := by positivity
    rw [pow_succ, div_mul_eq_div_div, cos_half, cos_pi_over_two_pow n, sqrtTwoAddSeries,
      add_div_eq_mul_add_div, one_mul, ← div_mul_eq_div_div, sqrt_div, sqrt_mul_self] <;>
      linarith [sqrtTwoAddSeries_nonneg le_rfl n]
#align real.cos_pi_over_two_pow Real.cos_pi_over_two_pow

theorem sin_sq_pi_over_two_pow (n : ℕ) :
    sin (π / 2 ^ (n + 1)) ^ 2 = 1 - (sqrtTwoAddSeries 0 n / 2) ^ 2 := by
  rw [sin_sq, cos_pi_over_two_pow]
#align real.sin_sq_pi_over_two_pow Real.sin_sq_pi_over_two_pow

theorem sin_sq_pi_over_two_pow_succ (n : ℕ) :
    sin (π / 2 ^ (n + 2)) ^ 2 = 1 / 2 - sqrtTwoAddSeries 0 n / 4 := by
  rw [sin_sq_pi_over_two_pow, sqrtTwoAddSeries, div_pow, sq_sqrt, add_div, ← sub_sub]
  · congr
    · norm_num
    · norm_num
  · exact add_nonneg two_pos.le (sqrtTwoAddSeries_zero_nonneg _)
#align real.sin_sq_pi_over_two_pow_succ Real.sin_sq_pi_over_two_pow_succ

@[simp]
theorem sin_pi_over_two_pow_succ (n : ℕ) :
    sin (π / 2 ^ (n + 2)) = √(2 - sqrtTwoAddSeries 0 n) / 2 := by
  rw [eq_div_iff_mul_eq two_ne_zero, eq_comm, sqrt_eq_iff_sq_eq, mul_pow,
    sin_sq_pi_over_two_pow_succ, sub_mul]
  · congr <;> norm_num
  · rw [sub_nonneg]
    exact (sqrtTwoAddSeries_lt_two _).le
  refine mul_nonneg (sin_nonneg_of_nonneg_of_le_pi ?_ ?_) zero_le_two
  · positivity
  · exact div_le_self pi_pos.le <| one_le_pow_of_one_le one_le_two _
#align real.sin_pi_over_two_pow_succ Real.sin_pi_over_two_pow_succ

@[simp]
theorem cos_pi_div_four : cos (π / 4) = √2 / 2 := by
  trans cos (π / 2 ^ 2)
  · congr
    norm_num
  · simp
#align real.cos_pi_div_four Real.cos_pi_div_four

@[simp]
theorem sin_pi_div_four : sin (π / 4) = √2 / 2 := by
  trans sin (π / 2 ^ 2)
  · congr
    norm_num
  · simp
#align real.sin_pi_div_four Real.sin_pi_div_four

@[simp]
theorem cos_pi_div_eight : cos (π / 8) = √(2 + √2) / 2 := by
  trans cos (π / 2 ^ 3)
  · congr
    norm_num
  · simp
#align real.cos_pi_div_eight Real.cos_pi_div_eight

@[simp]
theorem sin_pi_div_eight : sin (π / 8) = √(2 - √2) / 2 := by
  trans sin (π / 2 ^ 3)
  · congr
    norm_num
  · simp
#align real.sin_pi_div_eight Real.sin_pi_div_eight

@[simp]
theorem cos_pi_div_sixteen : cos (π / 16) = √(2 + √(2 + √2)) / 2 := by
  trans cos (π / 2 ^ 4)
  · congr
    norm_num
  · simp
#align real.cos_pi_div_sixteen Real.cos_pi_div_sixteen

@[simp]
theorem sin_pi_div_sixteen : sin (π / 16) = √(2 - √(2 + √2)) / 2 := by
  trans sin (π / 2 ^ 4)
  · congr
    norm_num
  · simp
#align real.sin_pi_div_sixteen Real.sin_pi_div_sixteen

@[simp]
theorem cos_pi_div_thirty_two : cos (π / 32) = √(2 + √(2 + √(2 + √2))) / 2 := by
  trans cos (π / 2 ^ 5)
  · congr
    norm_num
  · simp
#align real.cos_pi_div_thirty_two Real.cos_pi_div_thirty_two

@[simp]
theorem sin_pi_div_thirty_two : sin (π / 32) = √(2 - √(2 + √(2 + √2))) / 2 := by
  trans sin (π / 2 ^ 5)
  · congr
    norm_num
  · simp
#align real.sin_pi_div_thirty_two Real.sin_pi_div_thirty_two

-- This section is also a convenient location for other explicit values of `sin` and `cos`.
/-- The cosine of `π / 3` is `1 / 2`. -/
@[simp]
theorem cos_pi_div_three : cos (π / 3) = 1 / 2 := by
  have h₁ : (2 * cos (π / 3) - 1) ^ 2 * (2 * cos (π / 3) + 2) = 0 := by
    have : cos (3 * (π / 3)) = cos π := by
      congr 1
      ring
    linarith [cos_pi, cos_three_mul (π / 3)]
  cases' mul_eq_zero.mp h₁ with h h
  · linarith [pow_eq_zero h]
  · have : cos π < cos (π / 3) := by
      refine cos_lt_cos_of_nonneg_of_le_pi ?_ le_rfl ?_ <;> linarith [pi_pos]
    linarith [cos_pi]
#align real.cos_pi_div_three Real.cos_pi_div_three

/-- The cosine of `π / 6` is `√3 / 2`. -/
@[simp]
theorem cos_pi_div_six : cos (π / 6) = √3 / 2 := by
  rw [show (6 : ℝ) = 3 * 2 by norm_num, div_mul_eq_div_div, cos_half, cos_pi_div_three, one_add_div,
    ← div_mul_eq_div_div, two_add_one_eq_three, sqrt_div, sqrt_mul_self] <;> linarith [pi_pos]
#align real.cos_pi_div_six Real.cos_pi_div_six

/-- The square of the cosine of `π / 6` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
theorem sq_cos_pi_div_six : cos (π / 6) ^ 2 = 3 / 4 := by
  rw [cos_pi_div_six, div_pow, sq_sqrt] <;> norm_num
#align real.sq_cos_pi_div_six Real.sq_cos_pi_div_six

/-- The sine of `π / 6` is `1 / 2`. -/
@[simp]
theorem sin_pi_div_six : sin (π / 6) = 1 / 2 := by
  rw [← cos_pi_div_two_sub, ← cos_pi_div_three]
  congr
  ring
#align real.sin_pi_div_six Real.sin_pi_div_six

/-- The square of the sine of `π / 3` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
theorem sq_sin_pi_div_three : sin (π / 3) ^ 2 = 3 / 4 := by
  rw [← cos_pi_div_two_sub, ← sq_cos_pi_div_six]
  congr
  ring
#align real.sq_sin_pi_div_three Real.sq_sin_pi_div_three

/-- The sine of `π / 3` is `√3 / 2`. -/
@[simp]
theorem sin_pi_div_three : sin (π / 3) = √3 / 2 := by
  rw [← cos_pi_div_two_sub, ← cos_pi_div_six]
  congr
  ring
#align real.sin_pi_div_three Real.sin_pi_div_three

end CosDivSq

/-- `Real.sin` as an `OrderIso` between `[-(π / 2), π / 2]` and `[-1, 1]`. -/
def sinOrderIso : Icc (-(π / 2)) (π / 2) ≃o Icc (-1 : ℝ) 1 :=
  (strictMonoOn_sin.orderIso _ _).trans <| OrderIso.setCongr _ _ bijOn_sin.image_eq
#align real.sin_order_iso Real.sinOrderIso

@[simp]
theorem coe_sinOrderIso_apply (x : Icc (-(π / 2)) (π / 2)) : (sinOrderIso x : ℝ) = sin x :=
  rfl
#align real.coe_sin_order_iso_apply Real.coe_sinOrderIso_apply

theorem sinOrderIso_apply (x : Icc (-(π / 2)) (π / 2)) : sinOrderIso x = ⟨sin x, sin_mem_Icc x⟩ :=
  rfl
#align real.sin_order_iso_apply Real.sinOrderIso_apply

@[simp]
theorem tan_pi_div_four : tan (π / 4) = 1 := by
  rw [tan_eq_sin_div_cos, cos_pi_div_four, sin_pi_div_four]
  have h : √2 / 2 > 0 := by positivity
  exact div_self (ne_of_gt h)
#align real.tan_pi_div_four Real.tan_pi_div_four

@[simp]
theorem tan_pi_div_two : tan (π / 2) = 0 := by simp [tan_eq_sin_div_cos]
#align real.tan_pi_div_two Real.tan_pi_div_two

@[simp]
theorem tan_pi_div_six : tan (π / 6) = 1 / sqrt 3 := by
  rw [tan_eq_sin_div_cos, sin_pi_div_six, cos_pi_div_six]
  ring

@[simp]
theorem tan_pi_div_three : tan (π / 3) = sqrt 3 := by
  rw [tan_eq_sin_div_cos, sin_pi_div_three, cos_pi_div_three]
  ring

theorem tan_pos_of_pos_of_lt_pi_div_two {x : ℝ} (h0x : 0 < x) (hxp : x < π / 2) : 0 < tan x := by
  rw [tan_eq_sin_div_cos]
  exact div_pos (sin_pos_of_pos_of_lt_pi h0x (by linarith)) (cos_pos_of_mem_Ioo ⟨by linarith, hxp⟩)
#align real.tan_pos_of_pos_of_lt_pi_div_two Real.tan_pos_of_pos_of_lt_pi_div_two

theorem tan_nonneg_of_nonneg_of_le_pi_div_two {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π / 2) : 0 ≤ tan x :=
  match lt_or_eq_of_le h0x, lt_or_eq_of_le hxp with
  | Or.inl hx0, Or.inl hxp => le_of_lt (tan_pos_of_pos_of_lt_pi_div_two hx0 hxp)
  | Or.inl _, Or.inr hxp => by simp [hxp, tan_eq_sin_div_cos]
  | Or.inr hx0, _ => by simp [hx0.symm]
#align real.tan_nonneg_of_nonneg_of_le_pi_div_two Real.tan_nonneg_of_nonneg_of_le_pi_div_two

theorem tan_neg_of_neg_of_pi_div_two_lt {x : ℝ} (hx0 : x < 0) (hpx : -(π / 2) < x) : tan x < 0 :=
  neg_pos.1 (tan_neg x ▸ tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos]))
#align real.tan_neg_of_neg_of_pi_div_two_lt Real.tan_neg_of_neg_of_pi_div_two_lt

theorem tan_nonpos_of_nonpos_of_neg_pi_div_two_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -(π / 2) ≤ x) :
    tan x ≤ 0 :=
  neg_nonneg.1 (tan_neg x ▸ tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))
#align real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le Real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le

theorem strictMonoOn_tan : StrictMonoOn tan (Ioo (-(π / 2)) (π / 2)) := by
  rintro x hx y hy hlt
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos,
    div_lt_div_iff (cos_pos_of_mem_Ioo hx) (cos_pos_of_mem_Ioo hy), mul_comm, ← sub_pos, ← sin_sub]
  exact sin_pos_of_pos_of_lt_pi (sub_pos.2 hlt) <| by linarith [hx.1, hy.2]
#align real.strict_mono_on_tan Real.strictMonoOn_tan

theorem tan_lt_tan_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hy₂ : y < π / 2)
    (hxy : x < y) : tan x < tan y :=
  strictMonoOn_tan ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩ hxy
#align real.tan_lt_tan_of_lt_of_lt_pi_div_two Real.tan_lt_tan_of_lt_of_lt_pi_div_two

theorem tan_lt_tan_of_nonneg_of_lt_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y < π / 2)
    (hxy : x < y) : tan x < tan y :=
  tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) hy₂ hxy
#align real.tan_lt_tan_of_nonneg_of_lt_pi_div_two Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two

theorem injOn_tan : InjOn tan (Ioo (-(π / 2)) (π / 2)) :=
  strictMonoOn_tan.injOn
#align real.inj_on_tan Real.injOn_tan

theorem tan_inj_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
    (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : tan x = tan y) : x = y :=
  injOn_tan ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ hxy
#align real.tan_inj_of_lt_of_lt_pi_div_two Real.tan_inj_of_lt_of_lt_pi_div_two

theorem tan_periodic : Function.Periodic tan π := by
  simpa only [Function.Periodic, tan_eq_sin_div_cos] using sin_antiperiodic.div cos_antiperiodic
#align real.tan_periodic Real.tan_periodic

-- Porting note (#10756): added theorem
@[simp]
theorem tan_pi : tan π = 0 := by rw [tan_periodic.eq, tan_zero]

theorem tan_add_pi (x : ℝ) : tan (x + π) = tan x :=
  tan_periodic x
#align real.tan_add_pi Real.tan_add_pi

theorem tan_sub_pi (x : ℝ) : tan (x - π) = tan x :=
  tan_periodic.sub_eq x
#align real.tan_sub_pi Real.tan_sub_pi

theorem tan_pi_sub (x : ℝ) : tan (π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.sub_eq'
#align real.tan_pi_sub Real.tan_pi_sub

theorem tan_pi_div_two_sub (x : ℝ) : tan (π / 2 - x) = (tan x)⁻¹ := by
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, inv_div, sin_pi_div_two_sub, cos_pi_div_two_sub]
#align real.tan_pi_div_two_sub Real.tan_pi_div_two_sub

theorem tan_nat_mul_pi (n : ℕ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.nat_mul_eq n
#align real.tan_nat_mul_pi Real.tan_nat_mul_pi

theorem tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.int_mul_eq n
#align real.tan_int_mul_pi Real.tan_int_mul_pi

theorem tan_add_nat_mul_pi (x : ℝ) (n : ℕ) : tan (x + n * π) = tan x :=
  tan_periodic.nat_mul n x
#align real.tan_add_nat_mul_pi Real.tan_add_nat_mul_pi

theorem tan_add_int_mul_pi (x : ℝ) (n : ℤ) : tan (x + n * π) = tan x :=
  tan_periodic.int_mul n x
#align real.tan_add_int_mul_pi Real.tan_add_int_mul_pi

theorem tan_sub_nat_mul_pi (x : ℝ) (n : ℕ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_nat_mul_eq n
#align real.tan_sub_nat_mul_pi Real.tan_sub_nat_mul_pi

theorem tan_sub_int_mul_pi (x : ℝ) (n : ℤ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_int_mul_eq n
#align real.tan_sub_int_mul_pi Real.tan_sub_int_mul_pi

theorem tan_nat_mul_pi_sub (x : ℝ) (n : ℕ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.nat_mul_sub_eq n
#align real.tan_nat_mul_pi_sub Real.tan_nat_mul_pi_sub

theorem tan_int_mul_pi_sub (x : ℝ) (n : ℤ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.int_mul_sub_eq n
#align real.tan_int_mul_pi_sub Real.tan_int_mul_pi_sub

theorem tendsto_sin_pi_div_two : Tendsto sin (𝓝[<] (π / 2)) (𝓝 1) := by
  convert continuous_sin.continuousWithinAt.tendsto
  simp
#align real.tendsto_sin_pi_div_two Real.tendsto_sin_pi_div_two

theorem tendsto_cos_pi_div_two : Tendsto cos (𝓝[<] (π / 2)) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert continuous_cos.continuousWithinAt.tendsto
    simp
  · filter_upwards [Ioo_mem_nhdsWithin_Iio
        (right_mem_Ioc.mpr (neg_lt_self pi_div_two_pos))] with x hx using cos_pos_of_mem_Ioo hx
#align real.tendsto_cos_pi_div_two Real.tendsto_cos_pi_div_two

theorem tendsto_tan_pi_div_two : Tendsto tan (𝓝[<] (π / 2)) atTop := by
  convert tendsto_cos_pi_div_two.inv_tendsto_zero.atTop_mul zero_lt_one tendsto_sin_pi_div_two
    using 1
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
#align real.tendsto_tan_pi_div_two Real.tendsto_tan_pi_div_two

theorem tendsto_sin_neg_pi_div_two : Tendsto sin (𝓝[>] (-(π / 2))) (𝓝 (-1)) := by
  convert continuous_sin.continuousWithinAt.tendsto using 2
  simp
#align real.tendsto_sin_neg_pi_div_two Real.tendsto_sin_neg_pi_div_two

theorem tendsto_cos_neg_pi_div_two : Tendsto cos (𝓝[>] (-(π / 2))) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert continuous_cos.continuousWithinAt.tendsto
    simp
  · filter_upwards [Ioo_mem_nhdsWithin_Ioi
        (left_mem_Ico.mpr (neg_lt_self pi_div_two_pos))] with x hx using cos_pos_of_mem_Ioo hx
#align real.tendsto_cos_neg_pi_div_two Real.tendsto_cos_neg_pi_div_two

theorem tendsto_tan_neg_pi_div_two : Tendsto tan (𝓝[>] (-(π / 2))) atBot := by
  convert tendsto_cos_neg_pi_div_two.inv_tendsto_zero.atTop_mul_neg (by norm_num)
      tendsto_sin_neg_pi_div_two using 1
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
#align real.tendsto_tan_neg_pi_div_two Real.tendsto_tan_neg_pi_div_two

end Real

namespace Complex

open Real

theorem sin_eq_zero_iff_cos_eq {z : ℂ} : sin z = 0 ↔ cos z = 1 ∨ cos z = -1 := by
  rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq, sq, sq, ← sub_eq_iff_eq_add, sub_self]
  exact ⟨fun h => by rw [h, mul_zero], eq_zero_of_mul_self_eq_zero ∘ Eq.symm⟩
#align complex.sin_eq_zero_iff_cos_eq Complex.sin_eq_zero_iff_cos_eq

@[simp]
theorem cos_pi_div_two : cos (π / 2) = 0 :=
  calc
    cos (π / 2) = Real.cos (π / 2) := by rw [ofReal_cos]; simp
    _ = 0 := by simp
#align complex.cos_pi_div_two Complex.cos_pi_div_two

@[simp]
theorem sin_pi_div_two : sin (π / 2) = 1 :=
  calc
    sin (π / 2) = Real.sin (π / 2) := by rw [ofReal_sin]; simp
    _ = 1 := by simp
#align complex.sin_pi_div_two Complex.sin_pi_div_two

@[simp]
theorem sin_pi : sin π = 0 := by rw [← ofReal_sin, Real.sin_pi]; simp
#align complex.sin_pi Complex.sin_pi

@[simp]
theorem cos_pi : cos π = -1 := by rw [← ofReal_cos, Real.cos_pi]; simp
#align complex.cos_pi Complex.cos_pi

@[simp]
theorem sin_two_pi : sin (2 * π) = 0 := by simp [two_mul, sin_add]
#align complex.sin_two_pi Complex.sin_two_pi

@[simp]
theorem cos_two_pi : cos (2 * π) = 1 := by simp [two_mul, cos_add]
#align complex.cos_two_pi Complex.cos_two_pi

theorem sin_antiperiodic : Function.Antiperiodic sin π := by simp [sin_add]
#align complex.sin_antiperiodic Complex.sin_antiperiodic

theorem sin_periodic : Function.Periodic sin (2 * π) :=
  sin_antiperiodic.periodic_two_mul
#align complex.sin_periodic Complex.sin_periodic

theorem sin_add_pi (x : ℂ) : sin (x + π) = -sin x :=
  sin_antiperiodic x
#align complex.sin_add_pi Complex.sin_add_pi

theorem sin_add_two_pi (x : ℂ) : sin (x + 2 * π) = sin x :=
  sin_periodic x
#align complex.sin_add_two_pi Complex.sin_add_two_pi

theorem sin_sub_pi (x : ℂ) : sin (x - π) = -sin x :=
  sin_antiperiodic.sub_eq x
#align complex.sin_sub_pi Complex.sin_sub_pi

theorem sin_sub_two_pi (x : ℂ) : sin (x - 2 * π) = sin x :=
  sin_periodic.sub_eq x
#align complex.sin_sub_two_pi Complex.sin_sub_two_pi

theorem sin_pi_sub (x : ℂ) : sin (π - x) = sin x :=
  neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'
#align complex.sin_pi_sub Complex.sin_pi_sub

theorem sin_two_pi_sub (x : ℂ) : sin (2 * π - x) = -sin x :=
  sin_neg x ▸ sin_periodic.sub_eq'
#align complex.sin_two_pi_sub Complex.sin_two_pi_sub

theorem sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
  sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n
#align complex.sin_nat_mul_pi Complex.sin_nat_mul_pi

theorem sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
  sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n
#align complex.sin_int_mul_pi Complex.sin_int_mul_pi

theorem sin_add_nat_mul_two_pi (x : ℂ) (n : ℕ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.nat_mul n x
#align complex.sin_add_nat_mul_two_pi Complex.sin_add_nat_mul_two_pi

theorem sin_add_int_mul_two_pi (x : ℂ) (n : ℤ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.int_mul n x
#align complex.sin_add_int_mul_two_pi Complex.sin_add_int_mul_two_pi

theorem sin_sub_nat_mul_two_pi (x : ℂ) (n : ℕ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_nat_mul_eq n
#align complex.sin_sub_nat_mul_two_pi Complex.sin_sub_nat_mul_two_pi

theorem sin_sub_int_mul_two_pi (x : ℂ) (n : ℤ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_int_mul_eq n
#align complex.sin_sub_int_mul_two_pi Complex.sin_sub_int_mul_two_pi

theorem sin_nat_mul_two_pi_sub (x : ℂ) (n : ℕ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.nat_mul_sub_eq n
#align complex.sin_nat_mul_two_pi_sub Complex.sin_nat_mul_two_pi_sub

theorem sin_int_mul_two_pi_sub (x : ℂ) (n : ℤ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.int_mul_sub_eq n
#align complex.sin_int_mul_two_pi_sub Complex.sin_int_mul_two_pi_sub

theorem cos_antiperiodic : Function.Antiperiodic cos π := by simp [cos_add]
#align complex.cos_antiperiodic Complex.cos_antiperiodic

theorem cos_periodic : Function.Periodic cos (2 * π) :=
  cos_antiperiodic.periodic_two_mul
#align complex.cos_periodic Complex.cos_periodic

theorem cos_add_pi (x : ℂ) : cos (x + π) = -cos x :=
  cos_antiperiodic x
#align complex.cos_add_pi Complex.cos_add_pi

theorem cos_add_two_pi (x : ℂ) : cos (x + 2 * π) = cos x :=
  cos_periodic x
#align complex.cos_add_two_pi Complex.cos_add_two_pi

theorem cos_sub_pi (x : ℂ) : cos (x - π) = -cos x :=
  cos_antiperiodic.sub_eq x
#align complex.cos_sub_pi Complex.cos_sub_pi

theorem cos_sub_two_pi (x : ℂ) : cos (x - 2 * π) = cos x :=
  cos_periodic.sub_eq x
#align complex.cos_sub_two_pi Complex.cos_sub_two_pi

theorem cos_pi_sub (x : ℂ) : cos (π - x) = -cos x :=
  cos_neg x ▸ cos_antiperiodic.sub_eq'
#align complex.cos_pi_sub Complex.cos_pi_sub

theorem cos_two_pi_sub (x : ℂ) : cos (2 * π - x) = cos x :=
  cos_neg x ▸ cos_periodic.sub_eq'
#align complex.cos_two_pi_sub Complex.cos_two_pi_sub

theorem cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.nat_mul_eq n).trans cos_zero
#align complex.cos_nat_mul_two_pi Complex.cos_nat_mul_two_pi

theorem cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.int_mul_eq n).trans cos_zero
#align complex.cos_int_mul_two_pi Complex.cos_int_mul_two_pi

theorem cos_add_nat_mul_two_pi (x : ℂ) (n : ℕ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.nat_mul n x
#align complex.cos_add_nat_mul_two_pi Complex.cos_add_nat_mul_two_pi

theorem cos_add_int_mul_two_pi (x : ℂ) (n : ℤ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.int_mul n x
#align complex.cos_add_int_mul_two_pi Complex.cos_add_int_mul_two_pi

theorem cos_sub_nat_mul_two_pi (x : ℂ) (n : ℕ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_nat_mul_eq n
#align complex.cos_sub_nat_mul_two_pi Complex.cos_sub_nat_mul_two_pi

theorem cos_sub_int_mul_two_pi (x : ℂ) (n : ℤ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_int_mul_eq n
#align complex.cos_sub_int_mul_two_pi Complex.cos_sub_int_mul_two_pi

theorem cos_nat_mul_two_pi_sub (x : ℂ) (n : ℕ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.nat_mul_sub_eq n
#align complex.cos_nat_mul_two_pi_sub Complex.cos_nat_mul_two_pi_sub

theorem cos_int_mul_two_pi_sub (x : ℂ) (n : ℤ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.int_mul_sub_eq n
#align complex.cos_int_mul_two_pi_sub Complex.cos_int_mul_two_pi_sub

theorem cos_nat_mul_two_pi_add_pi (n : ℕ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic
#align complex.cos_nat_mul_two_pi_add_pi Complex.cos_nat_mul_two_pi_add_pi

theorem cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic
#align complex.cos_int_mul_two_pi_add_pi Complex.cos_int_mul_two_pi_add_pi

theorem cos_nat_mul_two_pi_sub_pi (n : ℕ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic
#align complex.cos_nat_mul_two_pi_sub_pi Complex.cos_nat_mul_two_pi_sub_pi

theorem cos_int_mul_two_pi_sub_pi (n : ℤ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic
#align complex.cos_int_mul_two_pi_sub_pi Complex.cos_int_mul_two_pi_sub_pi

theorem sin_add_pi_div_two (x : ℂ) : sin (x + π / 2) = cos x := by simp [sin_add]
#align complex.sin_add_pi_div_two Complex.sin_add_pi_div_two

theorem sin_sub_pi_div_two (x : ℂ) : sin (x - π / 2) = -cos x := by simp [sub_eq_add_neg, sin_add]
#align complex.sin_sub_pi_div_two Complex.sin_sub_pi_div_two

theorem sin_pi_div_two_sub (x : ℂ) : sin (π / 2 - x) = cos x := by simp [sub_eq_add_neg, sin_add]
#align complex.sin_pi_div_two_sub Complex.sin_pi_div_two_sub

theorem cos_add_pi_div_two (x : ℂ) : cos (x + π / 2) = -sin x := by simp [cos_add]
#align complex.cos_add_pi_div_two Complex.cos_add_pi_div_two

theorem cos_sub_pi_div_two (x : ℂ) : cos (x - π / 2) = sin x := by simp [sub_eq_add_neg, cos_add]
#align complex.cos_sub_pi_div_two Complex.cos_sub_pi_div_two

theorem cos_pi_div_two_sub (x : ℂ) : cos (π / 2 - x) = sin x := by
  rw [← cos_neg, neg_sub, cos_sub_pi_div_two]
#align complex.cos_pi_div_two_sub Complex.cos_pi_div_two_sub

theorem tan_periodic : Function.Periodic tan π := by
  simpa only [tan_eq_sin_div_cos] using sin_antiperiodic.div cos_antiperiodic
#align complex.tan_periodic Complex.tan_periodic

theorem tan_add_pi (x : ℂ) : tan (x + π) = tan x :=
  tan_periodic x
#align complex.tan_add_pi Complex.tan_add_pi

theorem tan_sub_pi (x : ℂ) : tan (x - π) = tan x :=
  tan_periodic.sub_eq x
#align complex.tan_sub_pi Complex.tan_sub_pi

theorem tan_pi_sub (x : ℂ) : tan (π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.sub_eq'
#align complex.tan_pi_sub Complex.tan_pi_sub

theorem tan_pi_div_two_sub (x : ℂ) : tan (π / 2 - x) = (tan x)⁻¹ := by
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, inv_div, sin_pi_div_two_sub, cos_pi_div_two_sub]
#align complex.tan_pi_div_two_sub Complex.tan_pi_div_two_sub

theorem tan_nat_mul_pi (n : ℕ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.nat_mul_eq n
#align complex.tan_nat_mul_pi Complex.tan_nat_mul_pi

theorem tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.int_mul_eq n
#align complex.tan_int_mul_pi Complex.tan_int_mul_pi

theorem tan_add_nat_mul_pi (x : ℂ) (n : ℕ) : tan (x + n * π) = tan x :=
  tan_periodic.nat_mul n x
#align complex.tan_add_nat_mul_pi Complex.tan_add_nat_mul_pi

theorem tan_add_int_mul_pi (x : ℂ) (n : ℤ) : tan (x + n * π) = tan x :=
  tan_periodic.int_mul n x
#align complex.tan_add_int_mul_pi Complex.tan_add_int_mul_pi

theorem tan_sub_nat_mul_pi (x : ℂ) (n : ℕ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_nat_mul_eq n
#align complex.tan_sub_nat_mul_pi Complex.tan_sub_nat_mul_pi

theorem tan_sub_int_mul_pi (x : ℂ) (n : ℤ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_int_mul_eq n
#align complex.tan_sub_int_mul_pi Complex.tan_sub_int_mul_pi

theorem tan_nat_mul_pi_sub (x : ℂ) (n : ℕ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.nat_mul_sub_eq n
#align complex.tan_nat_mul_pi_sub Complex.tan_nat_mul_pi_sub

theorem tan_int_mul_pi_sub (x : ℂ) (n : ℤ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.int_mul_sub_eq n
#align complex.tan_int_mul_pi_sub Complex.tan_int_mul_pi_sub

theorem exp_antiperiodic : Function.Antiperiodic exp (π * I) := by simp [exp_add, exp_mul_I]
#align complex.exp_antiperiodic Complex.exp_antiperiodic

theorem exp_periodic : Function.Periodic exp (2 * π * I) :=
  (mul_assoc (2 : ℂ) π I).symm ▸ exp_antiperiodic.periodic_two_mul
#align complex.exp_periodic Complex.exp_periodic

theorem exp_mul_I_antiperiodic : Function.Antiperiodic (fun x => exp (x * I)) π := by
  simpa only [mul_inv_cancel_right₀ I_ne_zero] using exp_antiperiodic.mul_const I_ne_zero
set_option linter.uppercaseLean3 false in
#align complex.exp_mul_I_antiperiodic Complex.exp_mul_I_antiperiodic

theorem exp_mul_I_periodic : Function.Periodic (fun x => exp (x * I)) (2 * π) :=
  exp_mul_I_antiperiodic.periodic_two_mul
set_option linter.uppercaseLean3 false in
#align complex.exp_mul_I_periodic Complex.exp_mul_I_periodic

@[simp]
theorem exp_pi_mul_I : exp (π * I) = -1 :=
  exp_zero ▸ exp_antiperiodic.eq
set_option linter.uppercaseLean3 false in
#align complex.exp_pi_mul_I Complex.exp_pi_mul_I

@[simp]
theorem exp_two_pi_mul_I : exp (2 * π * I) = 1 :=
  exp_periodic.eq.trans exp_zero
set_option linter.uppercaseLean3 false in
#align complex.exp_two_pi_mul_I Complex.exp_two_pi_mul_I

@[simp]
theorem exp_nat_mul_two_pi_mul_I (n : ℕ) : exp (n * (2 * π * I)) = 1 :=
  (exp_periodic.nat_mul_eq n).trans exp_zero
set_option linter.uppercaseLean3 false in
#align complex.exp_nat_mul_two_pi_mul_I Complex.exp_nat_mul_two_pi_mul_I

@[simp]
theorem exp_int_mul_two_pi_mul_I (n : ℤ) : exp (n * (2 * π * I)) = 1 :=
  (exp_periodic.int_mul_eq n).trans exp_zero
set_option linter.uppercaseLean3 false in
#align complex.exp_int_mul_two_pi_mul_I Complex.exp_int_mul_two_pi_mul_I

@[simp]
theorem exp_add_pi_mul_I (z : ℂ) : exp (z + π * I) = -exp z :=
  exp_antiperiodic z
set_option linter.uppercaseLean3 false in
#align complex.exp_add_pi_mul_I Complex.exp_add_pi_mul_I

@[simp]
theorem exp_sub_pi_mul_I (z : ℂ) : exp (z - π * I) = -exp z :=
  exp_antiperiodic.sub_eq z
set_option linter.uppercaseLean3 false in
#align complex.exp_sub_pi_mul_I Complex.exp_sub_pi_mul_I

/-- A supporting lemma for the **Phragmen-Lindelöf principle** in a horizontal strip. If `z : ℂ`
belongs to a horizontal strip `|Complex.im z| ≤ b`, `b ≤ π / 2`, and `a ≤ 0`, then
$$\left|exp^{a\left(e^{z}+e^{-z}\right)}\right| \le e^{a\cos b \exp^{|re z|}}.$$
-/
theorem abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le {a b : ℝ} (ha : a ≤ 0) {z : ℂ} (hz : |z.im| ≤ b)
    (hb : b ≤ π / 2) :
    abs (exp (a * (exp z + exp (-z)))) ≤ Real.exp (a * Real.cos b * Real.exp |z.re|) := by
  simp only [abs_exp, Real.exp_le_exp, re_ofReal_mul, add_re, exp_re, neg_im, Real.cos_neg, ←
    add_mul, mul_assoc, mul_comm (Real.cos b), neg_re, ← Real.cos_abs z.im]
  have : Real.exp |z.re| ≤ Real.exp z.re + Real.exp (-z.re) :=
    apply_abs_le_add_of_nonneg (fun x => (Real.exp_pos x).le) z.re
  refine mul_le_mul_of_nonpos_left (mul_le_mul this ?_ ?_ ((Real.exp_pos _).le.trans this)) ha
  · exact
      Real.cos_le_cos_of_nonneg_of_le_pi (_root_.abs_nonneg _)
        (hb.trans <| half_le_self <| Real.pi_pos.le) hz
  · refine Real.cos_nonneg_of_mem_Icc ⟨?_, hb⟩
    exact (neg_nonpos.2 <| Real.pi_div_two_pos.le).trans ((_root_.abs_nonneg _).trans hz)
#align complex.abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le Complex.abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le

end Complex
