/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.NumberTheory.IntervalSums

/-!
# Eisenstein Series E2

We define the Eisenstein series `E2` of weight `2` and level `1` as a limit of partial sums
over non-symmetric intervals.

-/

open UpperHalfPlane hiding I

open ModularForm EisensteinSeries Matrix.SpecialLinearGroup Filter Complex MatrixGroups
  SummationFilter Real

noncomputable section

namespace EisensteinSeries

/-- This is an auxilary summand used to define the Eisenstein serires `G2`. -/
def e2Summand (m : ℤ) (z : ℍ) : ℂ := ∑' n, eisSummand 2 ![m, n] z

lemma e2Summand_summable (m : ℤ) (z : ℍ) : Summable (fun n ↦ eisSummand 2 ![m, n] z) := by
  apply (linear_right_summable z m (k := 2) (by grind)).congr
  simp [eisSummand]

@[simp]
lemma e2Summand_zero_eq_two_riemannZeta_two (z : ℍ) : e2Summand 0 z = 2 * riemannZeta 2 := by
  simpa [e2Summand, eisSummand] using
    (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) (by grind) (by simp)).symm

lemma e2Summand_even (z : ℍ) : (e2Summand · z).Even := by
  intro n
  simp only [e2Summand, ← tsum_comp_neg (fun a ↦ eisSummand 2 ![-n, a] z)]
  apply tsum_congr (fun b ↦  ?_)
  simp only [eisSummand, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.reduceNeg, zpow_neg, Int.cast_neg, neg_mul, inv_inj]
  rw_mod_cast [Int.cast_neg]
  ring

/-- The Eisenstein series of weight `2` and level `1` defined as the limit as `N` tends to
infinity of the partial sum of `m` in `[N,N]` of `e2Summand m`. This sum over symmetric
intervals is handy in showing it is Summable. -/
def G2 : ℍ → ℂ := fun z ↦ ∑'[symCondInt] m, e2Summand m z

/-- The normalised Eisenstein series of weight `2` and level `1`. Defined as `G2 / 2 * ζ(2)`. -/
def E2 : ℍ → ℂ := (1 / (2 * riemannZeta 2)) •  G2

/-- This function measures the defect in `G2` being a modular form. -/
def D2 (γ : SL(2, ℤ)) : ℍ → ℂ := fun z ↦ (2 * π * I * γ 1 0) / (denom γ z)

lemma D2_one : D2 1 = 0 := by
  ext z
  simp [D2]

private lemma denom_aux (A B : SL(2, ℤ)) (z : ℍ) : ((A * B) 1 0) * (denom B z) =
    (A 1 0) * B.1.det + (B 1 0) * denom (A * B) z := by
  have h0 := Matrix.two_mul_expl A.1 B.1
  simp only [Fin.isValue, coe_mul, h0.2.2.1, Int.cast_add, Int.cast_mul, ModularGroup.denom_apply,
    Matrix.det_fin_two B.1, Int.cast_sub, ← map_mul, h0.2.2.2]
  ring

lemma D2_mul (A B : SL(2, ℤ)) : D2 (A * B) = (D2 A) ∣[(2 : ℤ)] B + D2 B := by
  ext z
  simp only [D2, mul_assoc, Fin.isValue, coe_mul, map_mul, ← mul_div,
    SL_slash_def, ModularGroup.sl_moeb, Int.reduceNeg, zpow_neg, Pi.add_apply, ← mul_add,
    mul_eq_mul_left_iff, I_ne_zero, or_false, ofReal_eq_zero, Real.pi_ne_zero, OfNat.ofNat_ne_zero]
  have hde := denom_ne_zero B z
  have hd := denom_aux A B z
  simp only [Fin.isValue, coe_mul, det_coe, Int.cast_one, mul_one, ← sub_eq_iff_eq_add] at hd
  have : denom A (num B z / denom B z) = denom A ↑(↑B • z) := by
    simp only [specialLinearGroup_apply, algebraMap_int_eq, Fin.isValue, eq_intCast, ofReal_intCast,
      UpperHalfPlane.coe_mk]
    rfl
  field_simp
  simp only [Fin.isValue, pow_two, ← mul_assoc, denom_cocycle A B z.im_ne_zero,
    mul_div_mul_right _ _ hde, ← hd, sub_div, Fin.isValue, this, ModularGroup.sl_moeb]
  nth_rw 3 [mul_comm]
  rw [← mul_assoc,  mul_div_cancel_right₀]
  · ring
  · exact denom_ne_zero A (B • z)

lemma D2_inv (A : SL(2, ℤ)) : (D2 A)∣[(2 : ℤ)] A⁻¹ = - D2 A⁻¹ := by
  have := D2_mul A A⁻¹
  simp only [mul_inv_cancel, SL_slash, D2_one] at this
  exact eq_neg_of_add_eq_zero_left (_root_.id (this.symm))

lemma D2_T : D2 ModularGroup.T = 0 := by
  ext z
  simp [D2, ModularGroup.T]

lemma D2_S (z : ℍ) : D2 ModularGroup.S z = 2 * π * I / z := by
  simp [D2, ModularGroup.S, ModularGroup.denom_apply]

end EisensteinSeries
