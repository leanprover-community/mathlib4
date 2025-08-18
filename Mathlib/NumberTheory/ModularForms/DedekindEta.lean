/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.NormedSpace.MultipliableUniformlyOn
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2

/-!
# Dedekind eta function

## Main definitions

* We define the Dedekind eta function as the infinite product
`η(z) = q ^ 1/24 * ∏' (1 - q ^ (n + 1))` where `q = e ^ (2πiz)` and `z` is in the upper half-plane.
The product is taken over all non-negative integers `n`. We then show it is non-vanishing and
differentiable on the upper half-plane.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005]
-/

open UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
 Metric Filter Function Complex ArithmeticFunction

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

local notation "𝕢" => Periodic.qParam

local notation "ℍₒ" => complexUpperHalfPlane

/-- The q term inside the product defining the eta function. It is defined as
`eta_q n z = e ^ (2 π i (n + 1) z)`. -/
noncomputable abbrev eta_q (n : ℕ) (z : ℂ) := (𝕢 1 z) ^ (n + 1)

lemma eta_q_eq_cexp (n : ℕ) (z : ℂ) : eta_q n z = cexp (2 * π * Complex.I * (n + 1) * z) := by
  simp [eta_q, Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf

lemma eta_q_eq_pow (n : ℕ) (z : ℂ) : eta_q n z = cexp (2 * π * Complex.I * z) ^ (n + 1) := by
  simp [eta_q, Periodic.qParam]

lemma one_add_eta_q_ne_zero (n : ℕ) (z : ℍ) : 1 - eta_q n z ≠ 0 := by
  rw [eta_q_eq_cexp, sub_ne_zero]
  intro h
  have := norm_exp_two_pi_I_lt_one ⟨(n + 1) • z, by
    have : 0 < (n + 1 : ℝ) := by linarith
    simpa [this] using z.2⟩
  simp [← mul_assoc, ← h] at *

/-- The product term in the eta function, defined as `∏' 1 - q ^ (n + 1)` for `q = e ^ 2 π i z`. -/
noncomputable abbrev etaProdTerm (z : ℂ) := ∏' (n : ℕ), (1 - eta_q n z)

local notation "ηₚ" => etaProdTerm

/-- The eta function, whose value at z is `q^ 1 / 24 * ∏' 1 - q ^ (n + 1)` for `q = e ^ 2 π i z`. -/
noncomputable def ModularForm.eta (z : ℂ) := 𝕢 24 z * ηₚ z

local notation "η" => ModularForm.eta

open ModularForm

theorem Summable_eta_q (z : ℍ) : Summable fun n ↦ ‖-eta_q n z‖ := by
  simp [eta_q, eta_q_eq_pow, summable_nat_add_iff 1, norm_exp_two_pi_I_lt_one z]

lemma hasProdLocallyUniformlyOn_eta : HasProdLocallyUniformlyOn (fun n a ↦ 1 - eta_q n a) ηₚ ℍₒ:= by
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact complexUpperHalPlane_isOpen
  intro K hK hcK
  by_cases hN : K.Nonempty
  · have hc : ContinuousOn (fun x ↦ ‖cexp (2 * π * Complex.I * x)‖) K := by fun_prop
    obtain ⟨z, hz, hB, HB⟩ := hcK.exists_sSup_image_eq_and_ge hN hc
    apply (Summable_eta_q ⟨z, by simpa using (hK hz)⟩).hasProdUniformlyOn_nat_one_add hcK
    · filter_upwards with n x hx
      simpa only [eta_q, eta_q_eq_pow n x, norm_neg, norm_pow, coe_mk_subtype,
          eta_q_eq_pow n (⟨z, hK hz⟩ : ℍ)] using
          pow_le_pow_left₀ (by simp [norm_nonneg]) (HB x hx) (n + 1)
    · simp_rw [eta_q, Periodic.qParam]
      fun_prop
  · rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    simpa [not_nonempty_iff_eq_empty.mp hN] using tendstoUniformlyOn_empty

theorem etaProdTerm_ne_zero (z : ℍ) : ηₚ z ≠ 0 := by
  simp only [etaProdTerm, eta_q, ne_eq]
  refine tprod_one_add_ne_zero_of_summable z (f := fun n x ↦ -eta_q n x) ?_ ?_
  · refine fun i x ↦ by simpa using one_add_eta_q_ne_zero i x
  · intro x
    simpa [eta_q, ← summable_norm_iff] using Summable_eta_q x

/-- Eta is non-vanishing on the upper half plane. -/
lemma eta_ne_zero_on_UpperHalfPlane (z : ℍ) : η z ≠ 0 := by
  simpa [ModularForm.eta, Periodic.qParam] using etaProdTerm_ne_zero z

lemma logDeriv_one_sub_cexp (r : ℂ) : logDeriv (fun z ↦ 1 - r * cexp z) =
    fun z ↦ -r * cexp z / (1 - r * cexp z) := by
  ext z
  simp [logDeriv]

lemma logDeriv_z_term (z : ℍ) : logDeriv (𝕢 24) ↑z  =  2 * ↑π * Complex.I / 24 := by
  have : (𝕢 24) = (fun z ↦ cexp (z)) ∘ (fun z => (2 * ↑π * Complex.I / 24) * z)  := by
    ext y
    simp only [Periodic.qParam, ofReal_ofNat, comp_apply]
    ring_nf
  rw [this, logDeriv_comp (by fun_prop) (by fun_prop), deriv_const_mul _ (by fun_prop)]
  simp only [LogDeriv_exp, Pi.one_apply, deriv_id'', mul_one, one_mul]

lemma logDeriv_one_sub_mul_cexp_comp (r : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    logDeriv ((fun z ↦ 1 - r * cexp z) ∘ g) =
    fun z ↦ -r * (deriv g z) * cexp (g z) / (1 - r * cexp (g z)) := by
  ext y
  rw [logDeriv_comp (by fun_prop) (hg y), logDeriv_one_sub_cexp]
  ring

private theorem one_sub_eta_logDeriv_eq (z : ℂ) (i : ℕ) : logDeriv (fun x ↦ 1 - eta_q i x) z =
    2 * π * Complex.I * (i + 1) * -eta_q i z / (1 - eta_q i z) := by
  have h2 : (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) =
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by aesop
  have h3 : deriv (fun x : ℂ ↦ (2 * π * Complex.I * (i + 1) * x)) =
      fun _ ↦ 2 * π * Complex.I * (i + 1) := by
    ext y
    simpa using deriv_const_mul (2 * π * Complex.I * (i + 1)) (d := fun (x : ℂ) ↦ x) (x := y)
  simp_rw [eta_q_eq_cexp, h2, logDeriv_one_sub_mul_cexp_comp 1
    (g := fun x ↦ (2 * π * Complex.I * (i + 1) * x)) (by fun_prop), h3]
  simp

lemma tsum_log_deriv_eta_q (z : ℂ) : ∑' (i : ℕ), logDeriv (fun x ↦ 1 - eta_q i x) z =
  (2 * π * Complex.I) * ∑' n : ℕ, (n + 1) * (-eta_q n z) / (1 - eta_q n z) := by
  suffices ∑' (i : ℕ), logDeriv (fun x ↦ 1 - eta_q i x) z =
  ∑' n : ℕ, (2 * ↑π * Complex.I * (n + 1)) * (-eta_q n z) / (1 - eta_q n z) by
    rw [this, ← tsum_mul_left]
    congr 1
    ext i
    ring
  exact tsum_congr (fun i ↦ one_sub_eta_logDeriv_eq z i)

theorem etaProdTerm_differentiableAt (z : ℍ) : DifferentiableAt ℂ ηₚ z := by
  have hD := hasProdLocallyUniformlyOn_eta.tendstoLocallyUniformlyOn_finsetRange.differentiableOn ?_
    complexUpperHalPlane_isOpen
  · exact (hD z z.2).differentiableAt (complexUpperHalPlane_isOpen.mem_nhds z.2)
  · filter_upwards with b y
    apply (DifferentiableOn.finset_prod (u := Finset.range b) (f := fun i x ↦ 1 - eta_q i x)
      (by fun_prop)).congr
    simp

lemma eta_DifferentiableAt_UpperHalfPlane (z : ℍ) : DifferentiableAt ℂ eta z :=
  DifferentiableAt.mul (by fun_prop) (etaProdTerm_differentiableAt z)

lemma tsum_eq_tsum_sigma (z : ℍ) : ∑' n : ℕ+,
    n * cexp (2 * π * Complex.I * z) ^ (n : ℕ) / (1 - cexp (2 * π *  Complex.I * z) ^ (n : ℕ)) =
    ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * z) ^ (n : ℕ) := by
  have :=  fun m : ℕ+ => tsum_choose_mul_geometric_of_norm_lt_one
      (r := (cexp (2 * ↑π * Complex.I * z))^(m : ℕ)) 0 ?_
  · simp only [add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add, pow_one,
      one_div] at this
    conv =>
      enter [1,1]
      ext n
      rw [div_eq_mul_one_div]
      simp only [one_div, ← this n, ← tsum_mul_left]
      conv =>
        enter [1]
        ext m
        rw [mul_assoc, ← pow_succ' (cexp (2 * ↑π * Complex.I * ↑z) ^ (n : ℕ)) m ]
    have h00 := tsum_prod_pow_cexp_eq_tsum_sigma z (k := 1)
    rw [Summable.tsum_comm (by apply summable_prod_aux (k := 1) z)] at h00
    rw [← h00]
    apply tsum_congr
    intro b
    rw [← tsum_pnat_eq_tsum_succ
      (fun n =>  b * (cexp (2 * π * Complex.I  * z) ^ (b : ℕ)) ^ (n : ℕ))]
    apply tsum_congr
    intro c
    simp only [← exp_nsmul, nsmul_eq_mul, pow_one, mul_eq_mul_left_iff, Nat.cast_eq_zero,
      PNat.ne_zero, or_false]
    ring_nf
  · simpa using
      pow_lt_one₀ (by simp) (UpperHalfPlane.norm_exp_two_pi_I_lt_one z) (by apply PNat.ne_zero)

lemma summable_mul_tendsto_const {F ι : Type*} [NontriviallyNormedField F] [CompleteSpace F]
    {f g : ι → F} (hf : Summable fun n => ‖f n‖) {c : F} (hg : Tendsto g cofinite (𝓝 c)) :
    Summable fun n : ι ↦ f n * g n := by
  apply summable_of_isBigO hf
  have h0 : g =O[cofinite] fun _x ↦ (1 : F) := by
    apply Filter.Tendsto.isBigO_one
    exact hg
  simpa using ((Asymptotics.isBigO_const_mul_self 1 f cofinite).mul h0)

lemma logDeriv_q_expo_summable {F : Type*} [NontriviallyNormedField F]
    [CompleteSpace F] {r : F} (hr : ‖r‖ < 1) : Summable fun n : ℕ => (n * r ^ n / (1 - r ^ n)) := by
  rw [show (fun n : ℕ => (n * r ^ n / (1 - r ^ n))) =
    fun n : ℕ => ((n * r ^ n) * (1 / (1 - r ^ n))) by grind]
  apply summable_mul_tendsto_const (c := 1 / (1 - 0))
  · rw [Nat.cofinite_eq_atTop]
    have : Tendsto (fun n : ℕ => 1 - r ^ n) atTop (𝓝 (1 - 0)) :=
      Filter.Tendsto.sub (by simp) (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr)
    have h1 : Tendsto (fun n : ℕ => (1 : F)) atTop (𝓝 1) := by simp only [tendsto_const_nhds_iff]
    apply (Filter.Tendsto.div h1 this (by simp)).congr
    simp
  · simpa using (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hr)


lemma eta_logDeriv (z : ℍ) : logDeriv ModularForm.eta z = (π * Complex.I / 12) * E2 z := by
  unfold ModularForm.eta etaProdTerm
  rw [logDeriv_mul (UpperHalfPlane.coe z) (by simp [ne_eq, exp_ne_zero, not_false_eq_true,
    Periodic.qParam]) (etaProdTerm_ne_zero z) (by fun_prop) (etaProdTerm_differentiableAt z) ]
  have HG := logDeriv_tprod_eq_tsum (isOpen_lt continuous_const Complex.continuous_im) (x := z)
    (f := fun n x => 1 - eta_q n x) (fun i ↦ one_add_eta_q_ne_zero i z) ?_ ?_ ?_
    (etaProdTerm_ne_zero z)
  · rw [show z.1 = UpperHalfPlane.coe z by rfl] at HG
    rw [HG]
    simp only [logDeriv_z_term z, tsum_log_deriv_eta_q z, mul_neg, E2, one_div, mul_inv_rev,
    Pi.smul_apply, smul_eq_mul]
    rw [G2_q_exp, riemannZeta_two, ← (tsum_eq_tsum_sigma z),  mul_sub, sub_eq_add_neg, mul_add]
    conv =>
      enter [1,2,2,1]
      ext n
      rw [neg_div, neg_eq_neg_one_mul]
    rw [tsum_mul_left]
    congr 1
    · field_simp
      ring
    · have := tsum_pnat_eq_tsum_succ (f := fun n => ( n) * cexp (2 * ↑π * Complex.I * ↑z ) ^ (n)
        / (1 - cexp (2 * ↑π * Complex.I * ↑z) ^ n ))
      simp at this
      rw [this]
      field_simp [Periodic.qParam, eta_q_eq_pow]
      ring_nf
      congr
      ext n
      ring_nf
  · intro i x hx
    simp_rw [eta_q_eq_pow]
    fun_prop
  · simp only [mem_setOf_eq, one_sub_eta_logDeriv_eq]
    apply ((summable_nat_add_iff 1).mpr ((logDeriv_q_expo_summable (r := 𝕢 1 z)
      (by simpa [Periodic.qParam] using UpperHalfPlane.norm_exp_two_pi_I_lt_one z)).mul_left
      (-2 * π * Complex.I))).congr
    intro b
    have := one_add_eta_q_ne_zero b z
    simp only [UpperHalfPlane.coe, ne_eq, neg_mul, Nat.cast_add, Nat.cast_one, mul_neg] at *
    field_simp
    left
    ring
  · use ηₚ
    apply (hasProdLocallyUniformlyOn_eta).congr
    exact fun n x hx ↦ Eq.refl ((fun b ↦ ∏ i ∈ n, (fun n a ↦ 1 - eta_q n a) i b) x)
