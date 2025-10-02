/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.NormedSpace.MultipliableUniformlyOn

/-!
# Dedekind eta function

## Main definitions

* We define the Dedekind eta function as the infinite product
`η(z) = q ^ 1/24 * ∏' (1 - q ^ (n + 1))` where `q = e ^ (2πiz)` and `z` is in the upper half-plane.
The product is taken over all non-negative integers `n`. We then show it is non-vanishing and
differentiable on the upper half-plane.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/

open TopologicalSpace Set MeasureTheory intervalIntegral
 Metric Filter Function Complex

open UpperHalfPlane hiding I

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

local notation "𝕢" => Periodic.qParam

local notation "ℍₒ" => upperHalfPlaneSet

namespace ModularForm

/-- The q term inside the product defining the eta function. It is defined as
`eta_q n z = e ^ (2 π i (n + 1) z)`. -/
noncomputable abbrev eta_q (n : ℕ) (z : ℂ) := (𝕢 1 z) ^ (n + 1)

lemma eta_q_eq_cexp (n : ℕ) (z : ℂ) : eta_q n z = cexp (2 * π * I * (n + 1) * z) := by
  simp [eta_q, Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf

lemma eta_q_eq_pow (n : ℕ) (z : ℂ) : eta_q n z = cexp (2 * π * I * z) ^ (n + 1) := by
  simp [eta_q, Periodic.qParam]

lemma one_sub_eta_q_ne_zero (n : ℕ) {z : ℂ} (hz : z ∈ ℍₒ) : 1 - eta_q n z ≠ 0 := by
  rw [eta_q_eq_cexp, sub_ne_zero]
  intro h
  simpa [← mul_assoc, ← h] using norm_exp_two_pi_I_lt_one ⟨(n + 1) • z, by
    simpa [(show 0 < (n + 1 : ℝ) by positivity)] using hz⟩

/-- The eta function, whose value at z is `q^ 1 / 24 * ∏' 1 - q ^ (n + 1)` for `q = e ^ 2 π i z`. -/
noncomputable def eta (z : ℂ) := 𝕢 24 z * ∏' n, (1 - eta_q n z)

local notation "η" => eta

theorem summable_eta_q (z : ℍ) : Summable fun n ↦ ‖-eta_q n z‖ := by
  simp [eta_q, eta_q_eq_pow, summable_nat_add_iff 1, norm_exp_two_pi_I_lt_one z]

lemma multipliableLocallyUniformlyOn_eta :
    MultipliableLocallyUniformlyOn (fun n a ↦ 1 - eta_q n a) ℍₒ:= by
  use fun z ↦ ∏' n, (1 - eta_q n z)
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_upperHalfPlaneSet
  intro K hK hcK
  by_cases hN : K.Nonempty
  · have hc : ContinuousOn (fun x ↦ ‖cexp (2 * π * I * x)‖) K := by fun_prop
    obtain ⟨z, hz, hB, HB⟩ := hcK.exists_sSup_image_eq_and_ge hN hc
    apply (summable_eta_q ⟨z, hK hz⟩).hasProdUniformlyOn_nat_one_add hcK
    · filter_upwards with n x hx
      simpa [eta_q, eta_q_eq_pow] using pow_le_pow_left₀ (by simp [norm_nonneg]) (HB x hx) _
    · simp_rw [eta_q, Periodic.qParam]
      fun_prop
  · rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    simpa [not_nonempty_iff_eq_empty.mp hN] using tendstoUniformlyOn_empty

/-- Eta is non-vanishing on the upper half plane. -/
lemma eta_ne_zero {z : ℂ} (hz : z ∈ ℍₒ) : η z ≠ 0 := by
  apply mul_ne_zero (Periodic.qParam_ne_zero z)
  refine tprod_one_add_ne_zero_of_summable (f := fun n ↦ -eta_q n z)  ?_ ?_
  · exact fun i ↦ by simpa using one_sub_eta_q_ne_zero i hz
  · simpa [eta_q, ← summable_norm_iff] using summable_eta_q ⟨z, hz⟩

lemma logDeriv_one_sub_cexp (r : ℂ) : logDeriv (fun z ↦ 1 - r * cexp z) =
    fun z ↦ -r * cexp z / (1 - r * cexp z) := by
  ext z
  simp [logDeriv]

lemma logDeriv_one_sub_mul_cexp_comp (r : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    logDeriv ((fun z ↦ 1 - r * cexp z) ∘ g) =
    fun z ↦ -r * (deriv g z) * cexp (g z) / (1 - r * cexp (g z)) := by
  ext y
  rw [logDeriv_comp (by fun_prop) (hg y), logDeriv_one_sub_cexp]
  ring

private theorem one_sub_eta_logDeriv_eq (z : ℂ) (n : ℕ) :
    logDeriv (1 - eta_q n ·) z = 2 * π * I * (n + 1) * -eta_q n z / (1 - eta_q n z) := by
  have h2 : (fun x ↦ 1 - cexp (2 * ↑π * I * (n + 1) * x)) =
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * I * (n + 1) * x) := by aesop
  have h3 : deriv (fun x : ℂ ↦ (2 * π * I * (n + 1) * x)) =
      fun _ ↦ 2 * π * I * (n + 1) := by
    ext y
    simpa using deriv_const_mul (2 * π * I * (n + 1)) (d := fun (x : ℂ) ↦ x) (x := y)
  simp_rw [eta_q_eq_cexp, h2, logDeriv_one_sub_mul_cexp_comp 1
    (g := fun x ↦ (2 * π * I * (n + 1) * x)) (by fun_prop), h3]
  simp

lemma tsum_logDeriv_eta_q (z : ℂ) : ∑' n, logDeriv (fun x ↦ 1 - eta_q n x) z =
    (2 * π * I) * ∑' n, (n + 1) * (-eta_q n z) / (1 - eta_q n z) := by
  rw [tsum_congr (one_sub_eta_logDeriv_eq z), ← tsum_mul_left]
  grind

theorem differentiableAt_eta_of_mem_upperHalfPlaneSet {z : ℂ} (hz : z ∈ ℍₒ) :
    DifferentiableAt ℂ eta z := by
  apply DifferentiableAt.mul (by fun_prop)
  refine (multipliableLocallyUniformlyOn_eta.hasProdLocallyUniformlyOn.differentiableOn ?_
    isOpen_upperHalfPlaneSet z hz).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz)
  filter_upwards with b
  simpa [Finset.prod_fn] using DifferentiableOn.finset_prod (by fun_prop)

end ModularForm
