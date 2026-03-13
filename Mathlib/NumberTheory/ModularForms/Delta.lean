/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# The modular discriminant Δ

This file defines the modular discriminant `Δ(z) = η(z) ^ 24`, where `η` is the Dedekind eta
function, and proves its key properties including invariance under the generators of `SL(2, ℤ)`.

## Main definitions

* `ModularForm.delta`: The modular discriminant function `Δ(z) = η(z) ^ 24`, which can also be
  expressed as `q * ∏' (1 - q ^ (n + 1)) ^ 24` where `q = e ^ (2πiz)`.

## Main results

* `ModularForm.delta_ne_zero`: The discriminant is non-vanishing on the upper half-plane.
* `ModularForm.delta_T_invariant`: Invariance under the translation `T : z ↦ z + 1`.
* `ModularForm.delta_S_invariant`: Invariance under the inversion `S : z ↦ -1 / z`,
  showing `Δ(-1 / z) = z ^ 12 · Δ(z)`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/

open Set Function Complex

open UpperHalfPlane hiding I

open scoped Real

noncomputable section

namespace ModularForm

/-- The modular discriminant `Δ(z) = η(z) ^ 24`, where `η` is the Dedekind eta function. -/
@[expose] public def delta (z : ℍ) := (eta z) ^ 24

local notation "Δ" => delta

local notation "𝕢" => Periodic.qParam

section auxiliary

lemma csqrt_pow_24_eq {z : ℂ} (hz : z ≠ 0) : sqrt z ^ 24 = z ^ 12 := by
  rw [sqrt_eq_exp hz, ← exp_nat_mul]
  ring_nf
  rw [show (log z * 12) = (12 : ℕ) * log z by ring, exp_nat_mul, exp_log hz]

lemma csqrt_I_pow_24 : sqrt I ^ 24 = 1 := by
  rw [csqrt_pow_24_eq I_ne_zero, show 12 = 4 * 3 by lia, pow_mul, I_pow_four, one_pow]

lemma logDeriv_eta_comp_div_eq (z : ℍ) :
    logDeriv (η ∘ (-1 / ·)) z = ((z : ℂ) ^ (2 : ℤ))⁻¹ * logDeriv η (-z)⁻¹ := by
  simp only [neg_div, one_div, inv_neg]
  rw [logDeriv_comp, mul_comm]
  · simp [zpow_ofNat]
  · exact differentiableAt_eta_of_mem_upperHalfPlaneSet (by grind [im_pnat_div_pos 1 z])
  · fun_prop (disch := exact z.ne_zero)

open EisensteinSeries in
lemma logDeriv_eta_comp_eq_logDeriv_csqrt_eta (z : ℍ) :
    logDeriv (η ∘ (-1 / ·)) z = logDeriv (sqrt * η) z := by
  rw [logDeriv_eta_comp_div_eq z, Pi.mul_def,
      logDeriv_mul _ (by simp [sqrt, ne_zero z]) (eta_ne_zero z.2)
      (differentiableAt_sqrt (mem_slitPlane z))
      (differentiableAt_eta_of_mem_upperHalfPlaneSet z.2), logDeriv_apply sqrt]
  have hE2 := congrFun (E2_slash_action ModularGroup.S) z
  simp only [one_div, SL_slash_def, modular_S_smul, ModularGroup.denom_S,
    Int.reduceNeg, zpow_neg, riemannZeta_two, mul_inv_rev, inv_div, Pi.sub_apply, Pi.smul_apply,
    D2, ModularGroup.denom_S, smul_eq_mul] at hE2
  rw [deriv_sqrt (mem_slitPlane z), div_eq_mul_inv, logDeriv_eta_eq_E2 z,
    logDeriv_eta_eq_E2 (.mk _ z.im_inv_neg_coe_pos),  ← mul_assoc, mul_comm, ← mul_assoc, hE2, sqrt,
    show ModularGroup.S 1 0 = 1 by simp [ModularGroup.S]]
  transitivity 1 / z / 2 + π * I / 12 * E2 z
  · field_simp
    grind [I_sq]
  · rw [div_mul_eq_mul_div₀ _ _ (2 : ℂ), neg_div, cpow_neg, ← mul_inv, ← cpow_add _ _ z.ne_zero]
    norm_num

lemma eta_comp_eqOn_const_mul_csqrt_eta :
    ∃ c : ℂ, c ≠ 0 ∧ upperHalfPlaneSet.EqOn (η ∘ (fun z : ℂ ↦ -1 / z)) (c • (sqrt * η)) := by
  rw [← logDeriv_eqOn_iff]
  · exact fun z hz ↦ logDeriv_eta_comp_eq_logDeriv_csqrt_eta ⟨z, hz⟩
  · apply DifferentiableOn.comp (t := upperHalfPlaneSet)
    · exact fun x hx ↦ (differentiableAt_eta_of_mem_upperHalfPlaneSet hx).differentiableWithinAt
    · exact DifferentiableOn.div (by fun_prop) (by fun_prop)
        (fun x hx ↦ ne_zero (⟨x, hx⟩ : ℍ))
    · exact fun y hy ↦ by grind [im_pnat_div_pos 1 (⟨y, hy⟩ : ℍ)]
  · exact fun x hx ↦ ((differentiableAt_sqrt (mem_slitPlane ⟨x, hx⟩)).mul
     (differentiableAt_eta_of_mem_upperHalfPlaneSet hx)).differentiableWithinAt
  · exact isOpen_upperHalfPlaneSet
  · exact Convex.isPreconnected (convex_halfSpace_im_gt 0)
  · exact fun x hx ↦ mul_ne_zero (by simp [sqrt, ne_zero ⟨x, hx⟩]) (eta_ne_zero hx)
  · exact fun x hx ↦ eta_ne_zero (by grind [im_pnat_div_pos 1 ⟨x, hx⟩])

end auxiliary

public section

/-- The discriminant expressed as a q-expansion: `Δ(z) = q * ∏' (1 - q ^ (n + 1)) ^ 24`. -/
lemma delta_eq_q_prod (z : ℍ) : Δ z = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24 := by
  simp only [delta, eta, mul_pow]
  congr
  · simp [Periodic.qParam, ← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    grind
  · exact ((multipliableLocallyUniformlyOn_eta.multipliable z.2).tprod_pow _).symm

/-- The modular discriminant is non-vanishing on the upper half-plane. -/
lemma delta_ne_zero (z : ℍ) : Δ z ≠ 0 := by
  simpa [delta] using eta_ne_zero z.2

/-- The discriminant is invariant under `T : z ↦ z + 1`, i.e., `Δ(z + 1) = Δ(z)`. -/
lemma delta_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_T_smul, ModularGroup.T]
  simp [delta_eq_q_prod, eta_q, Periodic.qParam, ← exp_periodic (2 * π * I * z)]
  ring_nf

/-- The transformation formula for `η` under `S : z ↦ -1 / z`: we have
`η(-1 / z) = (√I)⁻¹ · √z · η(z)` on the upper half-plane. -/
lemma eta_comp_eq_csqrt_I_inv : upperHalfPlaneSet.EqOn
    (η ∘ (-1 / ·)) ((sqrt I)⁻¹ • (sqrt * η)) := by
  obtain ⟨z, hz, h⟩ := eta_comp_eqOn_const_mul_csqrt_eta
  have h3 :  η I = z * sqrt I * η I := by simpa [← mul_assoc] using h (show I ∈ _ by simp)
  grind [sqrt, eta_ne_zero (show 0 < I.im by simp)]

/-- The discriminant satisfies the modular transformation for `S : z ↦ -1 / z`:
we have `Δ(-1 / z) = z ^ 12 · Δ(z)`. -/
lemma delta_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  ext z
  suffices η (-(↑z)⁻¹) ^ 24 * ((z : ℂ) ^ 12)⁻¹ = η z ^ 24 by
    rw [SL_slash_apply, UpperHalfPlane.modular_S_smul]
    simpa [denom, ModularGroup.S]
  have he : η (-(↑z)⁻¹) = (sqrt I)⁻¹ * (sqrt z * η z) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv z.2
  simp only [he, mul_pow, mul_pow, inv_pow, csqrt_I_pow_24, csqrt_pow_24_eq (ne_zero z)]
  field_simp [z.ne_zero]

end

end ModularForm
