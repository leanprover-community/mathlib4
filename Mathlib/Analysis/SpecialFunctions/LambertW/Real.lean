/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.SpecialFunctions.LambertW.Basic

/-!
# TODO DOC

## References

* <https://en.wikipedia.org/wiki/Lambert_W_function>
* <https://dlmf.nist.gov/4.13>
* <https://en.wikipedia.org/wiki/Omega_constant>
-/

public noncomputable section

namespace Real

open Set

variable {x y : ℝ}

/-- TODO doc -/
@[pp_nodot, expose]
def lambertWZero : ℝ -> ℝ := fun x => (Complex.lambertW 0 x).re

/-- TODO doc -/
@[pp_nodot, expose]
def lambertWNegOne : ℝ -> ℝ := fun x => (Complex.lambertW (-1) x).re

@[inherit_doc] scoped[RealLambertW] notation "W₀" => Real.lambertWZero
recommended_spelling "lambertWZero" for "W₀" in [lambertWZero, RealLambertW.«termW₀»]

@[inherit_doc] scoped[RealLambertW] notation "W₋₁" => Real.lambertWNegOne
recommended_spelling "lambertWNegOne" for "W₋₁" in [lambertWNegOne, RealLambertW.«termW₋₁»]

open scoped RealLambertW

/-- TODO doc -/
@[wikidata Q2291098]
abbrev omegaConstant : ℝ := W₀ 1

@[inherit_doc] scoped[OmegaConstant] notation "Ω" => Real.omegaConstant

open scoped OmegaConstant

theorem _root_.Complex.LambertW.ofReal_mem_range_zero
    (hx : -1 ≤ y) : (y : ℂ) ∈ Complex.LambertW.range 0 := by
  simpa [Complex.LambertW.mem_range_zero_iff, hx] using Complex.arg_mem_Ioc y

theorem _root_.Complex.LambertW.ofReal_mem_range_neg_one
    (hx : y ≤ -1) : (y : ℂ) ∈ Complex.LambertW.range (-1) :=
  Or.inr ⟨hx, rfl⟩

theorem lambertWZero_mul_exp_of_le (hy : -1 ≤ y) : W₀ (y * rexp y) = y := by
  rw [lambertWZero, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.lambertW_mul_exp_of_mem_range (Complex.LambertW.ofReal_mem_range_zero hy),
    Complex.ofReal_re]

theorem lambertWNegOne_mul_exp_of_le (hy : y ≤ -1) : W₋₁ (y * rexp y) = y := by
  rw [lambertWNegOne, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.lambertW_mul_exp_of_mem_range (Complex.LambertW.ofReal_mem_range_neg_one hy),
    Complex.ofReal_re]

private theorem exists_ge_neg_one_mul_exp_eq_of_le (hx : -(rexp 1)⁻¹ ≤ x) :
    ∃ y ≥ -1, y * rexp y = x := by
  have : -1 < -(rexp 1)⁻¹ := by simp [field]
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Icc (-1) (x + 1), y * rexp y = x :=
    intermediate_value_Icc (by grind) (by fun_prop)
      ⟨by simpa [exp_neg], by nlinarith [one_le_exp (show 0 ≤ x + 1 by grind)]⟩
  exact ⟨y, hy.left, hyx⟩

theorem invOn_lambertWZero_mul_exp :
    InvOn W₀ (fun y => y * rexp y) (Ici (-1)) (Ici (-(rexp 1)⁻¹)) := by
  refine ⟨fun y => lambertWZero_mul_exp_of_le, fun x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ : ∃ y ≥ -1, y * rexp y = x := exists_ge_neg_one_mul_exp_eq_of_le hx
  rw [← hyx, lambertWZero_mul_exp_of_le hy]

theorem invOn_mul_exp_lambertWZero :
    InvOn (fun x => x * rexp x) W₀ (Ici (-(rexp 1)⁻¹)) (Ici (-1)) :=
  invOn_lambertWZero_mul_exp.symm

theorem invOn_lambertWNegOne_mul_exp :
    InvOn W₋₁ (fun x => x * rexp x) (Iic (-1)) (Ico (-(rexp 1)⁻¹) 0) := by
  refine ⟨fun y => lambertWNegOne_mul_exp_of_le, fun x hx => ?_⟩
  obtain ⟨y, ⟨hy, hyx⟩, -⟩ : ∃! y ≤ -1, y * rexp y = x :=
    existsUnique_mem_Iic_mul_exp_eq_of_mem_Ico hx
  rw [← hyx, lambertWNegOne_mul_exp_of_le hy]

theorem invOn_mul_exp_lambertWNegOne :
    InvOn (fun x => x * rexp x) W₋₁ (Ico (-(rexp 1)⁻¹) 0) (Iic (-1)) :=
  invOn_lambertWNegOne_mul_exp.symm

theorem bijOn_lambertWZero : BijOn W₀ (Ici (-(rexp 1)⁻¹)) (Ici (-1)) := by
  refine invOn_mul_exp_lambertWZero.bijOn (fun x hx => ?_) fun y _ => neg_exp_one_inv_le_mul_exp y
  obtain ⟨y, hy, hyx⟩ := exists_ge_neg_one_mul_exp_eq_of_le hx
  rwa [← hyx, lambertWZero_mul_exp_of_le hy]

theorem bijOn_lambertWNegOne : BijOn W₋₁ (Ico (-(rexp 1)⁻¹) 0) (Iic (-1)) := by
  refine invOn_mul_exp_lambertWNegOne.bijOn (fun x hx => ?_) fun y hy =>
    ⟨neg_exp_one_inv_le_mul_exp y, mul_neg_of_neg_of_pos (by grind) (exp_pos y)⟩
  obtain ⟨y, ⟨hy, hyx⟩, -⟩ := existsUnique_mem_Iic_mul_exp_eq_of_mem_Ico hx
  rwa [← hyx, lambertWNegOne_mul_exp_of_le hy]

theorem lambertWZero_mul_exp_lambertWZero_of_le (hx : -(rexp 1)⁻¹ ≤ y) :
    W₀ y * rexp (W₀ y) = y :=
  invOn_mul_exp_lambertWZero.left hx

theorem lambertWNegOne_mul_exp_lambertWNegOne_of_mem_Ico (hx : y ∈ Ico (-(rexp 1)⁻¹) 0) :
    W₋₁ y * rexp (W₋₁ y) = y :=
  invOn_mul_exp_lambertWNegOne.left hx

theorem strictMonoOn_lambertWZero : StrictMonoOn W₀ (Ici (-(rexp 1)⁻¹)) := by
  apply Function.strictMonoOn_of_rightInvOn_of_mapsTo ?_
    invOn_mul_exp_lambertWZero.left bijOn_lambertWZero.mapsTo
  exact (mul_log_strictMonoOn.comp (exp_strictMono.strictMonoOn (Ici (-1)))
    fun x => exp_le_exp.mpr).congr fun x hx => by simp [mul_comm]

theorem strictAntiOn_lambertWNegOne : StrictAntiOn W₋₁ (Ico (-(rexp 1)⁻¹) 0) := by
  apply Function.strictAntiOn_of_rightInvOn_of_mapsTo ?_
    invOn_mul_exp_lambertWNegOne.left bijOn_lambertWNegOne.mapsTo
  exact (mul_log_strictAntiOn.comp_strictMonoOn (exp_strictMono.strictMonoOn (Iic (-1))) fun x hx =>
    ⟨exp_pos x |>.le, exp_le_exp.mpr hx⟩).congr fun x hx => by simp [mul_comm]

theorem existsUnique_ge_mul_exp_eq_of_le (hx : -(rexp 1)⁻¹ ≤ x) :
    ∃! y ≥ -1, y * rexp y = x :=
  ⟨W₀ x, ⟨bijOn_lambertWZero.mapsTo hx, invOn_lambertWZero_mul_exp.right hx⟩,
    fun _y' ⟨hy', hy'x⟩ => hy'x ▸ (invOn_lambertWZero_mul_exp.left hy').symm⟩

@[simp]
theorem lambertWZero_zero : W₀ 0 = 0 := by
  nth_rw 1 [← zero_mul, lambertWZero_mul_exp_of_le neg_one_lt_zero.le]

theorem lambertWZero_pos_of_pos (hx : 0 < y) : 0 < W₀ y := by
  have : -(rexp 1)⁻¹ ≤ 0 := by simpa using exp_nonneg 1
  exact lambertWZero_zero ▸ strictMonoOn_lambertWZero this (this.trans hx.le) hx

theorem lambertWZero_nonneg_of_nonneg (hx : 0 ≤ y) : 0 ≤ W₀ y := by
  have : -(rexp 1)⁻¹ ≤ 0 := by simpa using exp_nonneg 1
  exact lambertWZero_zero ▸ strictMonoOn_lambertWZero.monotoneOn this (this.trans hx) hx

theorem omegaConstant_eq : Ω = W₀ 1 := rfl

theorem omegaConstant_mul_exp : Ω * rexp Ω = 1 := by
  apply lambertWZero_mul_exp_lambertWZero_of_le
  simp [field, neg_one_lt_zero.le.trans <| exp_nonneg _]

theorem omegaConstant_eq_exp_neg : Ω = rexp (-Ω) := by
  grind [omegaConstant_mul_exp, exp_neg]

theorem omegaConstant_lt_one : Ω < 1 := by
  rw [omegaConstant_eq]
  nth_rw 2 [← lambertWZero_mul_exp_of_le (show -1 ≤ 1 by norm_num)]
  apply strictMonoOn_lambertWZero <;> simp [field, neg_one_lt_zero.le.trans <| exp_nonneg _]

open Qq Mathlib.Meta.Positivity in
/-- TODO doc -/
@[positivity Real.lambertWZero _]
meta def _root_.Mathlib.Meta.Positivity.evalLambertWZero :
    PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(W₀ $a) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa => pure <| .positive q(lambertWZero_pos_of_pos $pa)
    | .nonnegative pa => pure <| .nonnegative q(lambertWZero_nonneg_of_nonneg $pa)
    | _ => pure .none
  | _, _, _ => throwError "not Real.lambertWZero"

theorem omegaConstant_pos : 0 < Ω := by
  positivity

end Real
