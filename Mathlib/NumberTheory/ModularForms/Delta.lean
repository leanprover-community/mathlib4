/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# The modular discriminant Δ

This file defines the modular discriminant `Δ(z) = η(z) ^ 24`, where `η` is the Dedekind eta
function, and proves its key properties including invariance under the generators of `SL(2, ℤ)`.

## Main definitions

* `ModularForm.Delta`: The modular discriminant function `Δ(z) = η(z) ^ 24`, which can also be
  expressed as `q * ∏' (1 - q ^ (n + 1)) ^ 24` where `q = e ^ (2πiz)`.

## Main results

* `ModularForm.Delta_ne_zero`: The discriminant is non-vanishing on the upper half-plane.
* `ModularForm.Discriminant_T_invariant`: Invariance under the translation `T : z ↦ z + 1`.
* `ModularForm.Discriminant_S_invariant`: Invariance under the inversion `S : z ↦ -1 / z`,
  showing `Δ(-1 / z) = z ^ 12 · Δ(z)`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/


open TopologicalSpace Set MeasureTheory intervalIntegral
 Metric Filter Function Complex

open UpperHalfPlane hiding I

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

noncomputable section

namespace ModularForm

/-- The modular discriminant `Δ(z) = η(z) ^ 24`, a weight 12 modular form for `SL(2, ℤ)`. -/
public def Delta (z : ℍ) := (eta z) ^ 24

local notation "Δ" => Delta

local notation "η" => eta

local notation "𝕢" => Periodic.qParam
section auxiliary

noncomputable abbrev csqrt : ℂ → ℂ := fun a : ℂ ↦ a ^ (1 / (2 : ℂ))

lemma csqrt_eq {z : ℂ} (hz : z ≠ 0) : csqrt z = cexp ((Complex.log z) * (1 / 2)) := by
  unfold csqrt
  rw [Complex.cpow_def]
  simp [one_div, hz]

lemma csqrt_deriv {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (csqrt) z = (2 : ℂ)⁻¹ * ( z ^ (- 1 / (2 : ℂ))):= by
  have := Complex.deriv_cpow_const (c := 1 / 2) hz
  unfold csqrt
  norm_num at *
  simpa

lemma csqrt_differentiableAt {z : ℂ} (hz : z ∈ slitPlane) : DifferentiableAt ℂ csqrt z := by
  exact DifferentiableAt.cpow_const (by fun_prop) hz

lemma upperHalfPlane_mem_slitPlane (z : ℍ) : z.1 ∈ slitPlane := by
  simp [slitPlane, im_ne_zero z]

lemma csqrt_I : (csqrt I) ^ 24  = 1 := by
  rw [csqrt_eq (by simp), ← exp_nat_mul]
  ring_nf
  rw [show (log I * 12) = (12 : ℕ) * log I by ring, exp_nat_mul, exp_log (I_ne_zero)]
  simp [show I ^ 12 = (I ^ 4) ^ 3 by rw [← @pow_mul], I_pow_four]

lemma csqrt_pow_24_eq (z : ℂ) (hz : z ≠ 0) : (csqrt z) ^ 24 = z ^ 12 := by
  rw [csqrt_eq (by simp [hz]), ← Complex.exp_nat_mul]
  ring_nf
  rw [show (log z * 12) = (12 : ℕ) * log z by ring, Complex.exp_nat_mul, Complex.exp_log hz]

lemma logDeriv_eta_comp_div_eq (z : ℍ) :
    let Z := (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos)
    (logDeriv (η ∘ (fun z : ℂ ↦ -1 / z))) z = ((z : ℂ) ^ (2 : ℤ))⁻¹ * (logDeriv η) Z := by
  rw [logDeriv_comp, mul_comm]
  · congr
    · conv =>
        enter [1,1, z]
        rw [neg_div]
      norm_cast
      simp
    · grind
  · exact differentiableAt_eta_of_mem_upperHalfPlaneSet (by simpa using im_pnat_div_pos 1 z)
  · conv =>
      enter [2, z]
      simp [neg_div]
    exact ((differentiableAt_fun_id).inv (ne_zero z)).neg

lemma logDeriv_eta_comp_eq_logDeriv_csqrt_eta (z : ℍ) :
    logDeriv (η ∘ (fun z : ℂ ↦ -1 / z)) z = logDeriv (csqrt * η) z := by
  rw [logDeriv_eta_comp_div_eq z, show ((csqrt) * η) = (fun x ↦ (csqrt) x * η x) by rfl,
      logDeriv_mul _ (by simp [csqrt, ne_zero z]) (ModularForm.eta_ne_zero z.2)
      (csqrt_differentiableAt (upperHalfPlane_mem_slitPlane z))
      (differentiableAt_eta_of_mem_upperHalfPlaneSet z.2)]
  nth_rw 2 [logDeriv_apply]
  have EE := congrFun (EisensteinSeries.E2_slash_action  ModularGroup.S) z
  simp only [one_div, SL_slash_def, modular_S_smul, ModularGroup.denom_S,
    Int.reduceNeg, zpow_neg, riemannZeta_two, mul_inv_rev, inv_div, Pi.sub_apply, Pi.smul_apply,
    EisensteinSeries.D2, Fin.isValue, ModularGroup.denom_S, smul_eq_mul] at EE
  rw [csqrt_deriv (upperHalfPlane_mem_slitPlane z), div_eq_mul_inv, logDeriv_eta_eq_E2 z,
    logDeriv_eta_eq_E2 (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos), ← mul_assoc, mul_comm,
     ← mul_assoc, EE]
  have H : (z : ℂ) * z ^ (- 1 / (2 : ℂ)) = z ^ (1 - (1 / 2 : ℂ)) := by
    simp [cpow_sub _ _ (ne_zero z), div_eq_mul_inv, neg_mul, one_mul, cpow_one, ← cpow_neg]
  field_simp [I_ne_zero, ne_zero z, Real.pi_ne_zero]
  ring_nf
  simp [H, ModularGroup.S]
  grind

lemma eta_comp_eqOn_const_mul_csqrt_eta :
    ∃ z : ℂ, z ≠ 0 ∧ upperHalfPlaneSet.EqOn (η ∘ (fun z : ℂ ↦ -1 / z)) (z • ((csqrt) * η)) := by
  rw [← logDeriv_eqOn_iff]
  · apply fun z hz ↦ logDeriv_eta_comp_eq_logDeriv_csqrt_eta ⟨z, hz⟩
  · apply DifferentiableOn.comp (t := upperHalfPlaneSet)
    · exact fun x hx ↦ (differentiableAt_eta_of_mem_upperHalfPlaneSet hx).differentiableWithinAt
    · exact DifferentiableOn.div (by fun_prop) (by fun_prop) (fun x hx ↦ ne_zero (⟨x, hx⟩ : ℍ))
    · exact fun y hy ↦ by simpa using im_pnat_div_pos 1 (⟨y, hy⟩ : ℍ)
  · intro x hx
    apply DifferentiableAt.differentiableWithinAt (x := x)
    exact ((csqrt_differentiableAt (z := x) (upperHalfPlane_mem_slitPlane ⟨x, hx⟩))).mul
     (differentiableAt_eta_of_mem_upperHalfPlaneSet (z := x) hx)
  · exact isOpen_lt continuous_const Complex.continuous_im
  · exact Convex.isPreconnected (convex_halfSpace_im_gt 0)
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    exact ⟨by simp [ne_zero ⟨x, hx⟩] , eta_ne_zero hx⟩
  · intro x hx
    simpa using eta_ne_zero (z := -1 / x) (by simpa using im_pnat_div_pos 1 ⟨x, hx⟩)

lemma exp_periodo (z : ℍ) :
    cexp (2 * ↑π * I  * (1 + ↑z)) = cexp (2 * ↑π * I * ↑z) := by
  rw [mul_add, ← exp_periodic (2 * π * I * z)]
  congr 1
  ring

end auxiliary
@[expose] public section

/-- The discriminant expressed as a q-expansion: `Δ(z) = q * ∏' (1 - q ^ (n + 1)) ^ 24`. -/
lemma Delta_eq_q_prod (z : ℍ) : Δ z = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24 := by
  simp only [Delta, eta, mul_pow]
  congr
  · simp [Periodic.qParam]
    simp only [← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    grind
  · rw [Multipliable.tprod_pow]
    exact multipliableLocallyUniformlyOn_eta.multipliable z.2

/-- The modular discriminant is non-vanishing on the upper half-plane. -/
lemma Delta_ne_zero (z : ℍ) : Δ z ≠ 0 := by
  simpa [Delta] using eta_ne_zero z.2

/-- The discriminant is invariant under `T : z ↦ z + 1`, i.e., `Δ(z + 1) = Δ(z)`. -/
lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_T_smul, ModularGroup.T]
  simp [Delta_eq_q_prod, eta_q,  Periodic.qParam, exp_periodo z]

/-- The transformation formula for `η` under `S : z ↦ -1/z`: we have
`η(-1/z) = (√I)⁻¹ · √z · η(z)` on the upper half-plane. -/
lemma eta_comp_eq_csqrt_I_inv : upperHalfPlaneSet.EqOn
    (η ∘ (fun z : ℂ ↦ -1 / z)) ((I ^ (1 / 2 : ℂ))⁻¹ • ((· ^ (1 / 2 : ℂ)) * η)) := by
  obtain ⟨z, hz, h⟩ := eta_comp_eqOn_const_mul_csqrt_eta
  intro x hx
  have hI : I ∈ upperHalfPlaneSet := by simp
  have h3 := h hI
  simp only [comp_apply, div_I, neg_mul, one_mul, neg_neg, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul, ← mul_assoc] at h3
  have hcd := (mul_eq_right₀ (eta_ne_zero (mem_setOf.mpr hI))).mp h3.symm
  grind

/-- The discriminant satisfies the modular transformation for `S : z ↦ -1 / z`:
we have `Δ(-1/z) = z ^ 12 · Δ(z)`. -/
lemma Discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  ext z
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_S_smul]
  have he := eta_comp_eq_csqrt_I_inv z.2
  have hi : -1 / (z : ℂ) = -((z : ℂ))⁻¹ := by simp [neg_div]
  simp only [comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Delta, inv_neg, ModularGroup.S,
    Int.reduceNeg, Fin.isValue, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Int.cast_one, ofReal_one, one_mul, Int.cast_zero,
    ofReal_zero, add_zero, zpow_neg, hi] at *
  rw [he, mul_pow, mul_pow, inv_pow, csqrt_I, inv_one, one_mul,mul_comm,
    csqrt_pow_24_eq z.1 (ne_zero z), ← mul_assoc]
  field_simp [ne_zero z]

end

end ModularForm
