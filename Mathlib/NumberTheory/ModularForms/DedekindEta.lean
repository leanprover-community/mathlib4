/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Dedekind eta function

## Main definitions

* We define the Dedekind eta function as the infinite product
  `η(z) = q ^ 1/24 * ∏' (1 - q ^ (n + 1))` where `q = e ^ (2πiz)` and `z` is in the upper
  half-plane. The product is taken over all non-negative integers `n`. We then show it is
  non-vanishing and differentiable on the upper half-plane. Lastly, we compute its logarithmic
  derivative and show that it is a multiple of the Eisenstein series `E2`.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/

@[expose] public section

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

/-- Notation for the Dedekind eta function. -/
scoped[ModularForm] notation "η" => eta

/-! ### q-coordinate facts about `∏ (1 - q^(n+1))`

The following lemmas describe the analytic behaviour of the infinite product
`∏' n, (1 - q^(n+1))` viewed as a function of `q` on the open unit disc, including the
behaviour at `q = 0` (the cusp at infinity). The eta-side lemmas below derive from these
by pulling back along `qParam 1 : ℍₒ → 𝔻 \ {0}`.
-/

/-- For `‖q‖ < 1`, the infinite product `∏ (1 - q^(n+1))` is multipliable. -/
lemma multipliable_one_sub_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) := by
  rw [show (fun n : ℕ ↦ 1 - q ^ (n + 1)) = (fun n ↦ 1 + (-q ^ (n + 1))) from by ext; ring]
  apply multipliable_one_add_of_summable
  simp only [norm_neg, norm_pow]
  exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)

/-- The infinite product `∏ (1 - q^(n+1))` converges locally uniformly on the open unit disc,
with limit `q ↦ ∏' n, (1 - q^(n+1))`. -/
lemma multipliableLocallyUniformlyOn_one_sub_pow :
    MultipliableLocallyUniformlyOn (fun n q ↦ 1 - q ^ (n + 1)) (Metric.ball (0 : ℂ) 1) := by
  use fun q ↦ ∏' n, (1 - q ^ (n + 1))
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
  intro K hK hcK
  by_cases hN : K.Nonempty
  · have hc : ContinuousOn (fun q : ℂ ↦ ‖q‖) K := by fun_prop
    obtain ⟨q₀, hq₀, _, HB⟩ := hcK.exists_sSup_image_eq_and_ge hN hc
    have hq₀_lt : ‖q₀‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hK hq₀
    have hsum : Summable fun n : ℕ ↦ ‖q₀‖ ^ (n + 1) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq₀_lt)
    refine hsum.hasProdUniformlyOn_nat_one_add hcK (.of_forall fun n x hx ↦ ?_)
      (fun _ ↦ by fun_prop)
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (HB x hx) (n + 1)
  · rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    simpa [not_nonempty_iff_eq_empty.mp hN] using tendstoUniformlyOn_empty

/-- The infinite product `q ↦ ∏' n, (1 - q^(n+1))` is differentiable on the open unit disc. -/
lemma differentiableOn_tprod_one_sub_pow :
    DifferentiableOn ℂ (fun q ↦ ∏' n, (1 - q ^ (n + 1))) (Metric.ball (0 : ℂ) 1) := by
  apply multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.differentiableOn
    ?_ Metric.isOpen_ball
  filter_upwards with n
  simpa [Finset.prod_fn] using DifferentiableOn.finset_prod (fun _ _ ↦ by fun_prop)

/-- For any `k`, the function `q ↦ ∏' n, (1 - q^(n+1))^k` is differentiable on the
open unit disc. -/
lemma differentiableOn_tprod_one_sub_pow_pow (k : ℕ) :
    DifferentiableOn ℂ (fun q ↦ ∏' n, (1 - q ^ (n + 1)) ^ k) (Metric.ball (0 : ℂ) 1) := by
  refine (differentiableOn_tprod_one_sub_pow.fun_pow k).congr fun q hq ↦ ?_
  have hq_lt : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  exact (multipliable_one_sub_pow hq_lt).tprod_pow k

theorem summable_eta_q (z : ℍ) : Summable fun n ↦ ‖-eta_q n z‖ := by
  have hq : ‖(𝕢 (1 : ℝ) ↑z : ℂ)‖ < 1 := by exact_mod_cast norm_qParam_lt_one 1 z
  simpa only [norm_neg, eta_q, norm_pow] using
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)

lemma multipliableLocallyUniformlyOn_eta :
    MultipliableLocallyUniformlyOn (fun n a ↦ 1 - eta_q n a) ℍₒ :=
  ⟨_, (multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn :
      TendstoLocallyUniformlyOn _ _ _ _).comp (Periodic.qParam 1)
    (fun z hz ↦ by simpa [Metric.mem_ball, dist_zero_right] using
      (by exact_mod_cast norm_qParam_lt_one 1 ⟨z, hz⟩ : ‖(𝕢 (1 : ℝ) z : ℂ)‖ < 1))
      (by fun_prop)⟩

lemma eta_tprod_ne_zero {z : ℂ} (hz : z ∈ ℍₒ) : ∏' n, (1 - eta_q n z) ≠ 0 := by
  refine tprod_one_add_ne_zero_of_summable (f := fun n ↦ -eta_q n z) ?_ ?_
  · exact fun i ↦ by simpa using one_sub_eta_q_ne_zero i hz
  · simpa [eta_q, ← summable_norm_iff] using summable_eta_q ⟨z, hz⟩

/-- Eta is non-vanishing on the upper half plane. -/
lemma eta_ne_zero {z : ℂ} (hz : z ∈ ℍₒ) : η z ≠ 0 :=
  mul_ne_zero (Periodic.qParam_ne_zero z) (eta_tprod_ne_zero hz)

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
  simp_rw [eta_q_eq_cexp, h2, logDeriv_one_sub_mul_cexp_comp 1
    (g := fun x ↦ (2 * π * I * (n + 1) * x)) (by fun_prop), deriv_const_mul_id]
  simp

lemma tsum_logDeriv_eta_q (z : ℂ) : ∑' n, logDeriv (fun x ↦ 1 - eta_q n x) z =
    (2 * π * I) * ∑' n, (n + 1) * (-eta_q n z) / (1 - eta_q n z) := by
  rw [tsum_congr (one_sub_eta_logDeriv_eq z), ← tsum_mul_left]
  grind

lemma differentiableAt_eta_tprod {z : ℂ} (hz : z ∈ ℍₒ) :
    DifferentiableAt ℂ (fun x ↦ ∏' n, (1 - eta_q n x)) z := by
  have hq : (𝕢 (1 : ℝ) z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using
      (by exact_mod_cast norm_qParam_lt_one 1 ⟨z, hz⟩ : ‖(𝕢 (1 : ℝ) z : ℂ)‖ < 1)
  exact (((differentiableOn_tprod_one_sub_pow).differentiableAt
    (Metric.isOpen_ball.mem_nhds hq)).comp z (by fun_prop : DifferentiableAt ℂ (𝕢 (1 : ℝ)) z))

theorem differentiableAt_eta_of_mem_upperHalfPlaneSet {z : ℂ} (hz : z ∈ ℍₒ) :
    DifferentiableAt ℂ eta z :=
  .mul (by fun_prop) (differentiableAt_eta_tprod hz)

lemma logDeriv_qParam (h : ℝ) (z : ℂ) : logDeriv (𝕢 h) z = 2 * π * I / h := by
  have : 𝕢 h = cexp ∘ ((2 * π * I / h) * ·) := by
    ext
    grind [Periodic.qParam]
  rw [this, logDeriv_comp (by fun_prop) (by fun_prop), deriv_const_mul_id]
  simp [logDeriv_exp]

lemma summable_logDeriv_one_sub_eta_q {z : ℂ} (hz : z ∈ ℍₒ) :
    Summable fun i ↦ logDeriv (1 - eta_q i ·) z := by
  have := summable_norm_pow_mul_geometric_div_one_sub 1 (norm_qParam_lt_one 1 ⟨z, hz⟩)
  convert ((summable_nat_add_iff 1).mpr this).mul_left (-2 * π * I) using 1 with n
  grind [one_sub_eta_logDeriv_eq]

open EisensteinSeries in
lemma logDeriv_eta_eq_E2 (z : ℍ) : logDeriv eta z = (π * I / 12) * E2 z := by
  unfold eta
  rw [logDeriv_mul _ (Periodic.qParam_ne_zero _) (eta_tprod_ne_zero z.2) (by fun_prop)
    (differentiableAt_eta_tprod z.2)]
  have HG := logDeriv_tprod_eq_tsum isOpen_upperHalfPlaneSet z.2
    (one_sub_eta_q_ne_zero · z.2) (by fun_prop) (summable_logDeriv_one_sub_eta_q z.2)
    multipliableLocallyUniformlyOn_eta (eta_tprod_ne_zero z.2)
  simp only [logDeriv_qParam 24 z, HG, tsum_logDeriv_eta_q z, E2, one_div,
    mul_inv_rev, Pi.smul_apply, smul_eq_mul]
  rw [G2_eq_tsum_cexp, riemannZeta_two, ← tsum_pow_div_one_sub_eq_tsum_sigma
    (norm_exp_two_pi_I_lt_one z), mul_sub, sub_eq_add_neg, mul_add]
  simp [eta_q_eq_pow, ← tsum_mul_left, tsum_pnat_eq_tsum_succ (f := fun n ↦
        n * cexp (2 * π * I * z) ^ n / (1 - cexp (2 * π * I * z) ^ n)), ← tsum_neg]
  grind

end ModularForm
