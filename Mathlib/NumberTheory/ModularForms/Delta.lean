/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# Delta function

## Main definitions

* We define the Delta function as the infinite product
`η(z) = q * ∏' (1 - q ^ (n + 1)) ^ 24 ` where `q = e ^ (2πiz)` and `z` is in the upper half-plane.
The product is taken over all non-negative integers `n`. We then show it is modular form and
non-vanishing.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/


open TopologicalSpace Set MeasureTheory intervalIntegral
 Metric Filter Function Complex

open UpperHalfPlane hiding I

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

noncomputable section

local notation "𝕢" => Periodic.qParam

local notation "ℍₒ" => upperHalfPlaneSet

@[expose] public section

namespace ModularForm

def Delta (z : ℍ) := (eta z) ^ 24

local notation "Δ" => Delta

local notation "η" => eta

lemma Delta_eq_q_prod (z : ℍ) : Δ z = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24 := by
  simp only [Delta, eta, mul_pow]
  congr
  · simp [Periodic.qParam]
    simp only [← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    grind
  · rw [Multipliable.tprod_pow]
    exact multipliableLocallyUniformlyOn_eta.multipliable z.2

/-This should be easy from the definition and the Mulitpliable bit. -/
lemma Delta_ne_zero (z : ℍ) : Δ z ≠ 0 := by
  simpa [Delta] using eta_ne_zero z.2

lemma exp_periodo (z : ℍ) :
    cexp (2 * ↑π * I  * (1 + ↑z)) = cexp (2 * ↑π * I * ↑z) := by
  rw [mul_add, ← exp_periodic (2 * π * I * z)]
  congr 1
  ring

lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_T_smul, ModularGroup.T]
  simp [Delta_eq_q_prod, eta_q,  Periodic.qParam, exp_periodo z]

noncomputable abbrev csqrt : ℂ → ℂ := fun a : ℂ => cexp ((1 / 2) * log a)


lemma csqrt_deriv {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (csqrt) z = (2 : ℂ)⁻¹ * ( cexp (-(1 / 2) * log z)):= by
  have : csqrt =  cexp ∘ (fun a ↦ (1 / 2 * Complex.log a)) := by
    ext z
    simp [csqrt]
  rw [eq_inv_mul_iff_mul_eq₀ (by simp), this, deriv_comp _ (by fun_prop)
    ((Complex.differentiableAt_log hz).const_mul (1 / 2)), one_div, Complex.deriv_exp,
    deriv_const_mul_field', neg_mul, exp_neg, ← mul_eq_one_iff_eq_inv₀ (by simp)]
  ring_nf
  simp only [← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
  ring_nf
  rw [Complex.exp_log (slitPlane_ne_zero hz), (Complex.hasDerivAt_log  hz).deriv]
  grind [(slitPlane_ne_zero hz)]

lemma csqrt_differentiableAt (z : ℂ) (hz : z ∈ slitPlane) : DifferentiableAt ℂ csqrt z := by
  exact DifferentiableAt.cexp (DifferentiableAt.const_mul (differentiableAt_log hz) (1 / 2))

lemma upperHalfPlane_mem_slitPlane (z : ℍ) : z.1 ∈ slitPlane := by
  simp [slitPlane, im_ne_zero z]

private lemma csqrt_I : (csqrt I) ^ 24  = 1 := by
  rw [← exp_nat_mul]
  ring_nf
  rw [show (log I * 12) = (12 : ℕ) * log I by ring, exp_nat_mul, exp_log (I_ne_zero)]
  have : I ^ 12 = (I ^ 4) ^ 3 :=by
    rw [← @pow_mul]
  simp [this, I_pow_four]

private lemma csqrt_pow_24 (z : ℂ) (hz : z ≠ 0) : (csqrt z) ^ 24 = z ^ 12 := by
  rw [← Complex.exp_nat_mul]
  ring_nf
  rw [show (log z * 12) = (12 : ℕ) * log z by ring, Complex.exp_nat_mul, Complex.exp_log hz]

lemma eta_logDeriv_eql (z : ℍ) :
    (logDeriv (η ∘ (fun z : ℂ => -1 / z))) z = (logDeriv (csqrt * η)) z := by
  let Z := (⟨_ , by simpa using im_pnat_div_pos 1 z⟩ : ℍ)
  have h0 : (logDeriv (η ∘ (fun z : ℂ => -1 / z))) z = ((z : ℂ) ^ (2 : ℤ))⁻¹ * (logDeriv η) Z := by
    rw [logDeriv_comp, mul_comm]
    congr
    · conv =>
        enter [1,1, z]
        simp [neg_div]
      simp only [deriv.fun_neg', deriv_inv', neg_neg, inv_inj]
      norm_cast
    · simpa only using
      differentiableAt_eta_of_mem_upperHalfPlaneSet (by simpa using im_pnat_div_pos 1 z)
    conv =>
      enter [2]
      ext z
      rw [neg_div]
      simp
    apply DifferentiableAt.neg
    apply DifferentiableAt.inv
    simp only [differentiableAt_fun_id]
    exact ne_zero z
  rw [h0, show ((csqrt) * η) = (fun x => (csqrt) x * η x) by rfl, logDeriv_mul]
  nth_rw 2 [logDeriv_apply]
  unfold csqrt
  have := csqrt_deriv (upperHalfPlane_mem_slitPlane z)
  rw [this]
  simp only [one_div, neg_mul,Z, smul_eq_mul]
  nth_rw 2 [div_eq_mul_inv]
  rw [← Complex.exp_neg, show 2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
   (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)))* 2⁻¹ by ring, ← Complex.exp_add,
   ← sub_eq_add_neg, show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring,
    Complex.exp_neg, Complex.exp_log, logDeriv_eta_eq_E2 z]
  have Rb := logDeriv_eta_eq_E2 Z
  simp only [coe_mk_subtype] at Rb
  rw [Rb]
  have E := EisensteinSeries.E2_slash_action  ModularGroup.S
  have EE := congrFun E z
  simp only [one_div, neg_mul, smul_eq_mul, SL_slash_def, modular_S_smul, ModularGroup.denom_S,
    Int.reduceNeg, zpow_neg] at *
  have h00 :  (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) = Z := by
    simp [Z ]
    ring_nf
  rw [h00] at EE
  rw [← mul_assoc, mul_comm, ← mul_assoc]
  simp  [UpperHalfPlane.coe] at *
  rw [EE]
  congr 1
  have hzne := ne_zero z
  have hI : Complex.I ≠ 0 := by
    exact I_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by
    simp only [ne_eq, ofReal_eq_zero]
    exact Real.pi_ne_zero
  simp [ EisensteinSeries.D2, riemannZeta_two ] at *
  field_simp
  ring
  simp [add_comm, ModularGroup.S]
  · exact ne_zero z
  · simp only [csqrt, one_div, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  · apply ModularForm.eta_ne_zero z.2
  · apply csqrt_differentiableAt upperHalfPlane_mem_slitPlane
  · apply differentiableAt_eta_of_mem_upperHalfPlaneSet z.2


lemma eta_logderivs : {z : ℂ | 0 < z.im}.EqOn (logDeriv (η ∘ (fun z : ℂ => -1/z)))
  (logDeriv ((csqrt) * η)) := by
  intro z hz
  have := eta_logDeriv_eql ⟨z, hz⟩
  exact this


lemma eta_logderivs_const : ∃ z : ℂ, z ≠ 0 ∧ {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
  (z • ((csqrt) * η)) := by
  have h := eta_logderivs
  rw [logDeriv_eqOn_iff] at h
  · exact h
  · apply DifferentiableOn.comp
    pick_goal 4
    · use ({z : ℂ | 0 < z.im})
    · rw [DifferentiableOn]
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      apply differentiableAt_eta_of_mem_upperHalfPlaneSet hx
    · apply DifferentiableOn.div
      fun_prop
      fun_prop
      intro x hx
      have hx2 := ne_zero (⟨x, hx⟩ : ℍ)
      norm_cast at *
    · intro y hy
      simp
      have := UpperHalfPlane.im_inv_neg_coe_pos (⟨y, hy⟩ : ℍ)
      conv =>
        enter [2,1]
        rw [neg_div]
        rw [div_eq_mul_inv]
        simp
      simp at *
      exact this
  · apply DifferentiableOn.mul
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (csqrt_differentiableAt upperHalfPlane_mem_slitPlane hx).differentiableWithinAt
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (differentiableAt_eta_of_mem_upperHalfPlaneSet hx).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_im
  · refine Convex.isPreconnected ?_
    exact convex_halfSpace_im_gt 0
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    refine ⟨ ?_ , by apply ModularForm.eta_ne_zero hx⟩
    unfold csqrt
    simp only [one_div, Complex.exp_ne_zero, not_false_eq_true]
  · intro x hx
    simp only [comp_apply, ne_eq]
    have := ModularForm.eta_ne_zero (z := -1 / x) (by sorry)
    simpa only [ne_eq, coe_mk_subtype] using this

lemma eta_equality : {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
   ((csqrt (Complex.I))⁻¹ • ((csqrt) * η)) := by
  have h := eta_logderivs_const
  obtain ⟨z, hz, h⟩ := h
  intro x hx
  have h2 := h hx
  have hI : (Complex.I) ∈ {z : ℂ | 0 < z.im} := by
    simp only [mem_setOf_eq, Complex.I_im, zero_lt_one]
  have h3 := h hI
  simp at h3
  conv at h3 =>
    enter [2]
    rw [← mul_assoc]
  have he : η Complex.I ≠ 0 := by
    have h:=  ModularForm.eta_ne_zero (z := UpperHalfPlane.I) (by exact mem_setOf.mpr hI)
    convert h
  have hcd := (mul_eq_right₀ he).mp (_root_.id (Eq.symm h3))
  rw [mul_eq_one_iff_inv_eq₀ hz] at hcd
  rw [@inv_eq_iff_eq_inv] at hcd
  rw [hcd] at h2
  exact h2


lemma Discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  ext z
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_S_smul]
  simp [ModularGroup.S]
  simp_rw [ Delta]
  have he := eta_equality z.2
  simp only [comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, UpperHalfPlane.coe_mk,
    Int.reduceNeg, zpow_neg] at *
  have hi :  -1/(z.1 : ℂ) = (-(z : ℂ))⁻¹ := by
    rw [neg_div]
    rw [← neg_inv]
    simp [UpperHalfPlane.coe]
  rw [hi] at he
  simp at he
  rw [he, mul_pow, mul_pow, inv_pow, csqrt_I]
  simp only [inv_one, one_mul, UpperHalfPlane.coe]
  rw [mul_comm]
  have hzz := csqrt_pow_24 z.1 (ne_zero z)
  rw [hzz, ← mul_assoc]
  have hz := ne_zero z
  simp only [UpperHalfPlane.coe, ne_eq] at hz
  norm_cast
  field_simp

end ModularForm
