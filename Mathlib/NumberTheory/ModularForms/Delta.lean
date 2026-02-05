/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Basic

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



noncomputable def csqrt : ℂ → ℂ :=  (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a)))

lemma csqrt_deriv (z : ℍ) : deriv (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a))) z =
    (2 : ℂ)⁻¹ • (fun a : ℂ => cexp (-(1 / (2 : ℂ)) * (log a))) z:= by
  have :  (fun a ↦ cexp (1 / 2 * Complex.log a)) =  cexp ∘ (fun a ↦ (1 / 2 * Complex.log a)) := by
    ext z
    simp
  have hzz : ↑z ∈ slitPlane := by
    rw [@mem_slitPlane_iff]
    right
    have hz := z.2
    simp at hz
    exact Ne.symm (ne_of_lt hz)
  rw [this, deriv_comp]
  simp
  rw [Complex.exp_neg]

  field_simp
  rw [← exp_nsmul]
  simp
  ring_nf
  rw [Complex.exp_log]
  have hl := (Complex.hasDerivAt_log (z := z) hzz).deriv
  rw [hl]
  field_simp [ne_zero z]
  · apply ne_zero z
  · fun_prop
  · apply DifferentiableAt.const_mul
    refine Complex.differentiableAt_log hzz

lemma csqrt_differentiableAt (z : ℍ) : DifferentiableAt ℂ csqrt z := by
  unfold csqrt
  apply DifferentiableAt.cexp
  apply DifferentiableAt.const_mul
  apply Complex.differentiableAt_log
  rw [@mem_slitPlane_iff]
  right
  have hz := z.2
  simp at hz
  exact Ne.symm (ne_of_lt hz)


lemma csqrt_I : (csqrt (Complex.I)) ^ 24  = 1 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1,1]
    rw [← mul_assoc]
    rw [show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by
      field_simp; ring]
  rw [Complex.exp_nat_mul]
  rw [Complex.exp_log]
  have hi4 := Complex.I_pow_four
  have : Complex.I ^ 12 = (Complex.I ^ 4) ^ 3 :=by
    rw [← @pow_mul]
  rw [this, hi4]
  simp
  exact I_ne_zero

lemma csqrt_pow_24 (z : ℂ) (hz : z ≠ 0) : (csqrt z) ^ 24 = z ^ 12 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1,1]
    rw [← mul_assoc]
    rw [show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by
      field_simp; ring]
  rw [Complex.exp_nat_mul, Complex.exp_log hz]


lemma eta_logDeriv_eql (z : ℍ) : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z =
  (logDeriv ((csqrt) * η)) z := by
  have h0 : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z = ((z :ℂ)^(2 : ℤ))⁻¹ * (logDeriv η) (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    rw [logDeriv_comp, mul_comm]
    congr
    conv =>
      enter [1,1]
      intro z
      rw [neg_div]
      simp
    simp only [deriv.fun_neg', deriv_inv', neg_neg, inv_inj]
    norm_cast
    · simpa only using
      differentiableAt_eta_of_mem_upperHalfPlaneSet (z := -1 / z) (by sorry)
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
  have := csqrt_deriv z
  rw [this]
  simp only [one_div, neg_mul, smul_eq_mul]
  nth_rw 2 [div_eq_mul_inv]
  rw [← Complex.exp_neg, show 2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
   (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)))* 2⁻¹ by ring, ← Complex.exp_add,
   ← sub_eq_add_neg, show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring, Complex.exp_neg, Complex.exp_log, eta_logDeriv z]
  have Rb := eta_logDeriv (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
  simp only [coe_mk_subtype] at Rb
  rw [Rb]
  have E := E₂_transform z
  simp only [one_div, neg_mul, smul_eq_mul, SL_slash_def, modular_S_smul, ModularGroup.denom_S,
    Int.reduceNeg, zpow_neg] at *
  have h00 :  (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) = (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    simp [UpperHalfPlane.mk]
    ring_nf
  rw [h00] at E
  rw [← mul_assoc, mul_comm, ← mul_assoc]
  simp only [UpperHalfPlane.coe] at *
  rw [E, add_mul, add_comm]
  congr 1
  have hzne := ne_zero z
  have hI : Complex.I ≠ 0 := by
    exact I_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by
    simp only [ne_eq, ofReal_eq_zero]
    exact Real.pi_ne_zero
  simp [UpperHalfPlane.coe] at hzne ⊢
  field_simp
  ring
  rw [mul_comm]
  · simpa only [UpperHalfPlane.coe, ne_eq] using (ne_zero z)
  · simp only [csqrt, one_div, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  · apply eta_nonzero_on_UpperHalfPlane z
  · unfold csqrt
    rw [show (fun a ↦ cexp (1 / 2 * Complex.log a)) = cexp ∘ (fun a ↦ 1 / 2 * Complex.log a) by rfl]
    apply DifferentiableAt.comp
    simp
    apply DifferentiableAt.const_mul
    apply Complex.differentiableAt_log
    rw [@mem_slitPlane_iff]
    right
    have hz := z.2
    simp only at hz
    exact Ne.symm (ne_of_lt hz)
  · apply eta_DifferentiableAt_UpperHalfPlane z

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
      apply eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩
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
    apply (csqrt_differentiableAt ⟨x, hx⟩).differentiableWithinAt
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_im
  · refine Convex.isPreconnected ?_
    exact convex_halfSpace_im_gt 0
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    refine ⟨ ?_ , by apply eta_nonzero_on_UpperHalfPlane ⟨x, hx⟩⟩
    unfold csqrt
    simp only [one_div, Complex.exp_ne_zero, not_false_eq_true]
  · intro x hx
    simp only [comp_apply, ne_eq]
    have := eta_nonzero_on_UpperHalfPlane ⟨-1 / x, by simpa using pnat_div_upper 1 ⟨x, hx⟩⟩
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
    have h:=  eta_nonzero_on_UpperHalfPlane UpperHalfPlane.I
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
