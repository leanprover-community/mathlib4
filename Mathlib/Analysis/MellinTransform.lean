/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module analysis.mellin_transform
! leanprover-community/mathlib commit 917c3c072e487b3cccdbfeff17e75b40e45f66cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.ImproperIntegrals
import Mathbin.Analysis.Calculus.ParametricIntegral
import Mathbin.MeasureTheory.Measure.Haar.NormedSpace

/-! # The Mellin transform

We define the Mellin transform of a locally integrable function on `Ioi 0`, and show it is
differentiable in a suitable vertical strip.

## Main statements

- `mellin` : the Mellin transform `∫ (t : ℝ) in Ioi 0, t ^ (s - 1) • f t`,
  where `s` is a complex number.
- `has_mellin`: shorthand asserting that the Mellin transform exists and has a given value
  (analogous to `has_sum`).
- `mellin_differentiable_at_of_is_O_rpow` : if `f` is `O(x ^ (-a))` at infinity, and
  `O(x ^ (-b))` at 0, then `mellin f` is holomorphic on the domain `b < re s < a`.

-/


open MeasureTheory Set Filter Asymptotics TopologicalSpace

namespace Complex

-- Porting note: move this to `analysis.special_functions.pow.complex`
theorem cpow_mul_of_real_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (z : ℂ) :
    (x : ℂ) ^ (↑y * z) = (↑(x ^ y) : ℂ) ^ z :=
  by
  rw [cpow_mul, of_real_cpow hx]
  · rw [← of_real_log hx, ← of_real_mul, of_real_im, neg_lt_zero]; exact Real.pi_pos
  · rw [← of_real_log hx, ← of_real_mul, of_real_im]; exact real.pi_pos.le
#align complex.cpow_mul_of_real_nonneg Complex.cpow_mul_of_real_nonneg

end Complex

open Real

open Complex hiding exp log abs_of_nonneg

open scoped Topology

noncomputable section

section Defs

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Predicate on `f` and `s` asserting that the Mellin integral is well-defined. -/
def MellinConvergent (f : ℝ → E) (s : ℂ) : Prop :=
  IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (Ioi 0)
#align mellin_convergent MellinConvergent

theorem MellinConvergent.const_smul {f : ℝ → E} {s : ℂ} (hf : MellinConvergent f s) {𝕜 : Type _}
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E] (c : 𝕜) :
    MellinConvergent (fun t => c • f t) s := by
  simpa only [MellinConvergent, smul_comm] using hf.smul c
#align mellin_convergent.const_smul MellinConvergent.const_smul

theorem MellinConvergent.cpow_smul {f : ℝ → E} {s a : ℂ} :
    MellinConvergent (fun t => (t : ℂ) ^ a • f t) s ↔ MellinConvergent f (s + a) :=
  by
  refine' integrable_on_congr_fun (fun t ht => _) measurableSet_Ioi
  simp_rw [← sub_add_eq_add_sub, cpow_add _ _ (of_real_ne_zero.2 <| ne_of_gt ht), mul_smul]
#align mellin_convergent.cpow_smul MellinConvergent.cpow_smul

theorem MellinConvergent.div_const {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) (a : ℂ) :
    MellinConvergent (fun t => f t / a) s := by
  simpa only [MellinConvergent, smul_eq_mul, ← mul_div_assoc] using hf.div_const a
#align mellin_convergent.div_const MellinConvergent.div_const

theorem MellinConvergent.comp_mul_left {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 < a) :
    MellinConvergent (fun t => f (a * t)) s ↔ MellinConvergent f s :=
  by
  have := integrable_on_Ioi_comp_mul_left_iff (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) 0 ha
  rw [MulZeroClass.mul_zero] at this 
  have h1 :
    eq_on (fun t : ℝ => (↑(a * t) : ℂ) ^ (s - 1) • f (a * t))
      ((a : ℂ) ^ (s - 1) • fun t : ℝ => (t : ℂ) ^ (s - 1) • f (a * t)) (Ioi 0) :=
    by
    intro t ht
    simp only [of_real_mul, mul_cpow_of_real_nonneg ha.le (le_of_lt ht), mul_smul, Pi.smul_apply]
  have h2 : (a : ℂ) ^ (s - 1) ≠ 0 := by rw [Ne.def, cpow_eq_zero_iff, not_and_or, of_real_eq_zero];
    exact Or.inl ha.ne'
  simp_rw [MellinConvergent, ← this, integrable_on_congr_fun h1 measurableSet_Ioi, integrable_on,
    integrable_smul_iff h2]
#align mellin_convergent.comp_mul_left MellinConvergent.comp_mul_left

theorem MellinConvergent.comp_rpow {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : a ≠ 0) :
    MellinConvergent (fun t => f (t ^ a)) s ↔ MellinConvergent f (s / a) :=
  by
  simp_rw [MellinConvergent]
  letI u : NormedSpace ℝ E := NormedSpace.complexToReal
  -- why isn't this automatic?
  conv_rhs => rw [← @integrable_on_Ioi_comp_rpow_iff' _ _ u _ a ha]
  refine' integrable_on_congr_fun (fun t ht => _) measurableSet_Ioi
  dsimp only [Pi.smul_apply]
  rw [← Complex.coe_smul (t ^ (a - 1)), ← mul_smul, ← cpow_mul_of_real_nonneg (le_of_lt ht),
    of_real_cpow (le_of_lt ht), ← cpow_add _ _ (of_real_ne_zero.mpr (ne_of_gt ht)), of_real_sub,
    of_real_one, mul_sub, mul_div_cancel' _ (of_real_ne_zero.mpr ha), mul_one, add_comm, ←
    add_sub_assoc, sub_add_cancel]
#align mellin_convergent.comp_rpow MellinConvergent.comp_rpow

variable [CompleteSpace E]

/-- The Mellin transform of a function `f` (for a complex exponent `s`), defined as the integral of
`t ^ (s - 1) • f` over `Ioi 0`. -/
def mellin (f : ℝ → E) (s : ℂ) : E :=
  ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • f t
#align mellin mellin

-- next few lemmas don't require convergence of the Mellin transform (they are just 0 = 0 otherwise)
theorem mellin_cpow_smul (f : ℝ → E) (s a : ℂ) :
    mellin (fun t => (t : ℂ) ^ a • f t) s = mellin f (s + a) :=
  by
  refine' set_integral_congr measurableSet_Ioi fun t ht => _
  simp_rw [← sub_add_eq_add_sub, cpow_add _ _ (of_real_ne_zero.2 <| ne_of_gt ht), mul_smul]
#align mellin_cpow_smul mellin_cpow_smul

theorem mellin_const_smul (f : ℝ → E) (s : ℂ) {𝕜 : Type _} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E] (c : 𝕜) :
    mellin (fun t => c • f t) s = c • mellin f s := by simp only [mellin, smul_comm, integral_smul]
#align mellin_const_smul mellin_const_smul

theorem mellin_div_const (f : ℝ → ℂ) (s a : ℂ) : mellin (fun t => f t / a) s = mellin f s / a := by
  simp_rw [mellin, smul_eq_mul, ← mul_div_assoc, integral_div]
#align mellin_div_const mellin_div_const

theorem mellin_comp_rpow (f : ℝ → E) (s : ℂ) {a : ℝ} (ha : a ≠ 0) :
    mellin (fun t => f (t ^ a)) s = (|a|)⁻¹ • mellin f (s / a) :=
  by
  -- note: this is also true for a = 0 (both sides are zero), but this is mathematically
  -- uninteresting and rather time-consuming to check
  simp_rw [mellin]
  conv_rhs => rw [← integral_comp_rpow_Ioi _ ha, ← integral_smul]
  refine' set_integral_congr measurableSet_Ioi fun t ht => _
  dsimp only
  rw [← mul_smul, ← mul_assoc, inv_mul_cancel, one_mul, ← smul_assoc, real_smul]
  show |a| ≠ 0; · contrapose! ha; exact abs_eq_zero.mp ha
  rw [of_real_cpow (le_of_lt ht), ← cpow_mul_of_real_nonneg (le_of_lt ht), ←
    cpow_add _ _ (of_real_ne_zero.mpr <| ne_of_gt ht), of_real_sub, of_real_one, mul_sub,
    mul_div_cancel' _ (of_real_ne_zero.mpr ha), add_comm, ← add_sub_assoc, mul_one, sub_add_cancel]
#align mellin_comp_rpow mellin_comp_rpow

theorem mellin_comp_mul_left (f : ℝ → E) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    mellin (fun t => f (a * t)) s = (a : ℂ) ^ (-s) • mellin f s :=
  by
  simp_rw [mellin]
  have :
    eq_on (fun t : ℝ => (t : ℂ) ^ (s - 1) • f (a * t))
      (fun t : ℝ => (a : ℂ) ^ (1 - s) • (fun u : ℝ => (u : ℂ) ^ (s - 1) • f u) (a * t)) (Ioi 0) :=
    by
    intro t ht
    dsimp only
    rw [of_real_mul, mul_cpow_of_real_nonneg ha.le (le_of_lt ht), ← mul_smul,
      (by ring : 1 - s = -(s - 1)), cpow_neg, inv_mul_cancel_left₀]
    rw [Ne.def, cpow_eq_zero_iff, of_real_eq_zero, not_and_or]
    exact Or.inl ha.ne'
  rw [set_integral_congr measurableSet_Ioi this, integral_smul, integral_comp_mul_left_Ioi _ _ ha,
    MulZeroClass.mul_zero, ← Complex.coe_smul, ← mul_smul, sub_eq_add_neg,
    cpow_add _ _ (of_real_ne_zero.mpr ha.ne'), cpow_one, abs_of_pos (inv_pos.mpr ha), of_real_inv,
    mul_assoc, mul_comm, inv_mul_cancel_right₀ (of_real_ne_zero.mpr ha.ne')]
#align mellin_comp_mul_left mellin_comp_mul_left

theorem mellin_comp_mul_right (f : ℝ → E) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    mellin (fun t => f (t * a)) s = (a : ℂ) ^ (-s) • mellin f s := by
  simpa only [mul_comm] using mellin_comp_mul_left f s ha
#align mellin_comp_mul_right mellin_comp_mul_right

theorem mellin_comp_inv (f : ℝ → E) (s : ℂ) : mellin (fun t => f t⁻¹) s = mellin f (-s) := by
  simp_rw [← rpow_neg_one, mellin_comp_rpow _ _ (neg_ne_zero.mpr one_ne_zero), abs_neg, abs_one,
    inv_one, one_smul, of_real_neg, of_real_one, div_neg, div_one]
#align mellin_comp_inv mellin_comp_inv

/-- Predicate standing for "the Mellin transform of `f` is defined at `s` and equal to `m`". This
shortens some arguments. -/
def HasMellin (f : ℝ → E) (s : ℂ) (m : E) : Prop :=
  MellinConvergent f s ∧ mellin f s = m
#align has_mellin HasMellin

theorem hasMellin_add {f g : ℝ → E} {s : ℂ} (hf : MellinConvergent f s)
    (hg : MellinConvergent g s) : HasMellin (fun t => f t + g t) s (mellin f s + mellin g s) :=
  ⟨by simpa only [MellinConvergent, smul_add] using hf.add hg, by
    simpa only [mellin, smul_add] using integral_add hf hg⟩
#align has_mellin_add hasMellin_add

theorem hasMellin_sub {f g : ℝ → E} {s : ℂ} (hf : MellinConvergent f s)
    (hg : MellinConvergent g s) : HasMellin (fun t => f t - g t) s (mellin f s - mellin g s) :=
  ⟨by simpa only [MellinConvergent, smul_sub] using hf.sub hg, by
    simpa only [mellin, smul_sub] using integral_sub hf hg⟩
#align has_mellin_sub hasMellin_sub

end Defs

variable {E : Type _} [NormedAddCommGroup E]

section MellinConvergent

/-! ## Convergence of Mellin transform integrals -/


/-- Auxiliary lemma to reduce convergence statements from vector-valued functions to real
scalar-valued functions. -/
theorem mellin_convergent_iff_norm [NormedSpace ℂ E] {f : ℝ → E} {T : Set ℝ} (hT : T ⊆ Ioi 0)
    (hT' : MeasurableSet T) (hfc : AEStronglyMeasurable f <| volume.restrict <| Ioi 0) {s : ℂ} :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) T ↔
      IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * ‖f t‖) T :=
  by
  have : ae_strongly_measurable (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (volume.restrict T) :=
    by
    refine' ((ContinuousAt.continuousOn _).AEStronglyMeasurable hT').smul (hfc.mono_set hT)
    exact fun t ht => continuous_at_of_real_cpow_const _ _ (Or.inr <| ne_of_gt (hT ht))
  rw [integrable_on, ← integrable_norm_iff this, ← integrable_on]
  refine' integrable_on_congr_fun (fun t ht => _) hT'
  simp_rw [norm_smul, Complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos (hT ht), sub_re, one_re]
#align mellin_convergent_iff_norm mellin_convergent_iff_norm

/-- If `f` is a locally integrable real-valued function which is `O(x ^ (-a))` at `∞`, then for any
`s < a`, its Mellin transform converges on some neighbourhood of `+∞`. -/
theorem mellin_convergent_top_of_isBigO {f : ℝ → ℝ}
    (hfc : AEStronglyMeasurable f <| volume.restrict (Ioi 0)) {a s : ℝ}
    (hf : IsBigO atTop f fun t => t ^ (-a)) (hs : s < a) :
    ∃ c : ℝ, 0 < c ∧ IntegrableOn (fun t : ℝ => t ^ (s - 1) * f t) (Ioi c) :=
  by
  obtain ⟨d, hd, hd'⟩ := hf.exists_pos
  simp_rw [is_O_with, eventually_at_top] at hd' 
  obtain ⟨e, he⟩ := hd'
  have he' : 0 < max e 1 := zero_lt_one.trans_le (le_max_right _ _)
  refine' ⟨max e 1, he', _, _⟩
  · refine' ae_strongly_measurable.mul _ (hfc.mono_set (Ioi_subset_Ioi he'.le))
    refine' (ContinuousAt.continuousOn fun t ht => _).AEStronglyMeasurable measurableSet_Ioi
    exact continuous_at_rpow_const _ _ (Or.inl <| (he'.trans ht).ne')
  · have : ∀ᵐ t : ℝ ∂volume.restrict (Ioi <| max e 1), ‖t ^ (s - 1) * f t‖ ≤ t ^ (s - 1 + -a) * d :=
      by
      refine' (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => _)
      have ht' : 0 < t := he'.trans ht
      rw [norm_mul, rpow_add ht', ← norm_of_nonneg (rpow_nonneg_of_nonneg ht'.le (-a)), mul_assoc,
        mul_comm _ d, norm_of_nonneg (rpow_nonneg_of_nonneg ht'.le _)]
      exact
        mul_le_mul_of_nonneg_left (he t ((le_max_left e 1).trans_lt ht).le)
          (rpow_pos_of_pos ht' _).le
    refine' (has_finite_integral.mul_const _ _).mono' this
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) he').HasFiniteIntegral
#align mellin_convergent_top_of_is_O mellin_convergent_top_of_isBigO

/-- If `f` is a locally integrable real-valued function which is `O(x ^ (-b))` at `0`, then for any
`b < s`, its Mellin transform converges on some right neighbourhood of `0`. -/
theorem mellin_convergent_zero_of_isBigO {b : ℝ} {f : ℝ → ℝ}
    (hfc : AEStronglyMeasurable f <| volume.restrict (Ioi 0))
    (hf : IsBigO (𝓝[>] 0) f fun t => t ^ (-b)) {s : ℝ} (hs : b < s) :
    ∃ c : ℝ, 0 < c ∧ IntegrableOn (fun t : ℝ => t ^ (s - 1) * f t) (Ioc 0 c) :=
  by
  obtain ⟨d, hd, hd'⟩ := hf.exists_pos
  simp_rw [is_O_with, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, gt_iff_lt] at hd' 
  obtain ⟨ε, hε, hε'⟩ := hd'
  refine' ⟨ε, hε, integrable_on_Ioc_iff_integrable_on_Ioo.mpr ⟨_, _⟩⟩
  · refine' ae_strongly_measurable.mul _ (hfc.mono_set Ioo_subset_Ioi_self)
    refine' (ContinuousAt.continuousOn fun t ht => _).AEStronglyMeasurable measurableSet_Ioo
    exact continuous_at_rpow_const _ _ (Or.inl ht.1.ne')
  · apply has_finite_integral.mono'
    · show has_finite_integral (fun t => d * t ^ (s - b - 1)) _
      refine' (integrable.has_finite_integral _).const_mul _
      rw [← integrable_on, ← integrableOn_Ioc_iff_integrableOn_Ioo, ←
        intervalIntegrable_iff_integrable_Ioc_of_le hε.le]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    · refine' (ae_restrict_iff' measurableSet_Ioo).mpr (eventually_of_forall fun t ht => _)
      rw [mul_comm, norm_mul]
      specialize hε' _ ht.1
      · rw [dist_eq_norm, sub_zero, norm_of_nonneg (le_of_lt ht.1)]
        exact ht.2
      · refine' (mul_le_mul_of_nonneg_right hε' (norm_nonneg _)).trans _
        simp_rw [norm_of_nonneg (rpow_nonneg_of_nonneg (le_of_lt ht.1) _), mul_assoc]
        refine' mul_le_mul_of_nonneg_left (le_of_eq _) hd.le
        rw [← rpow_add ht.1]
        congr 1
        abel
#align mellin_convergent_zero_of_is_O mellin_convergent_zero_of_isBigO

/-- If `f` is a locally integrable real-valued function on `Ioi 0` which is `O(x ^ (-a))` at `∞`
and `O(x ^ (-b))` at `0`, then its Mellin transform integral converges for `b < s < a`. -/
theorem mellin_convergent_of_isBigO_scalar {a b : ℝ} {f : ℝ → ℝ} {s : ℝ}
    (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : IsBigO atTop f fun t => t ^ (-a))
    (hs_top : s < a) (hf_bot : IsBigO (𝓝[>] 0) f fun t => t ^ (-b)) (hs_bot : b < s) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) * f t) (Ioi 0) :=
  by
  obtain ⟨c1, hc1, hc1'⟩ := mellin_convergent_top_of_isBigO hfc.ae_strongly_measurable hf_top hs_top
  obtain ⟨c2, hc2, hc2'⟩ :=
    mellin_convergent_zero_of_isBigO hfc.ae_strongly_measurable hf_bot hs_bot
  have : Ioi 0 = Ioc 0 c2 ∪ Ioc c2 c1 ∪ Ioi c1 := by
    rw [union_assoc, Ioc_union_Ioi (le_max_right _ _),
      Ioc_union_Ioi ((min_le_left _ _).trans (le_max_right _ _)), min_eq_left (lt_min hc2 hc1).le]
  rw [this, integrable_on_union, integrable_on_union]
  refine' ⟨⟨hc2', integrable_on_Icc_iff_integrable_on_Ioc.mp _⟩, hc1'⟩
  refine'
    (hfc.continuous_on_mul _ isOpen_Ioi).integrableOn_compact_subset
      (fun t ht => (hc2.trans_le ht.1 : 0 < t)) is_compact_Icc
  exact ContinuousAt.continuousOn fun t ht => continuous_at_rpow_const _ _ <| Or.inl <| ne_of_gt ht
#align mellin_convergent_of_is_O_scalar mellin_convergent_of_isBigO_scalar

theorem mellinConvergent_of_isBigO_rpow [NormedSpace ℂ E] {a b : ℝ} {f : ℝ → E} {s : ℂ}
    (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : IsBigO atTop f fun t => t ^ (-a))
    (hs_top : s.re < a) (hf_bot : IsBigO (𝓝[>] 0) f fun t => t ^ (-b)) (hs_bot : b < s.re) :
    MellinConvergent f s :=
  by
  rw [MellinConvergent,
    mellin_convergent_iff_norm (subset_refl _) measurableSet_Ioi hfc.ae_strongly_measurable]
  exact mellin_convergent_of_isBigO_scalar hfc.norm hf_top.norm_left hs_top hf_bot.norm_left hs_bot
#align mellin_convergent_of_is_O_rpow mellinConvergent_of_isBigO_rpow

end MellinConvergent

section MellinDiff

/-- If `f` is `O(x ^ (-a))` as `x → +∞`, then `log • f` is `O(x ^ (-b))` for every `b < a`. -/
theorem isBigO_rpow_top_log_smul [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E} (hab : b < a)
    (hf : IsBigO atTop f fun t => t ^ (-a)) :
    IsBigO atTop (fun t : ℝ => log t • f t) fun t => t ^ (-b) :=
  by
  refine'
    ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).IsBigO.smul hf).congr'
      (eventually_of_forall fun t => by rfl)
      ((eventually_gt_at_top 0).mp (eventually_of_forall fun t ht => _))
  rw [smul_eq_mul, ← rpow_add ht, ← sub_eq_add_neg, sub_eq_add_neg a, add_sub_cancel']
#align is_O_rpow_top_log_smul isBigO_rpow_top_log_smul

/-- If `f` is `O(x ^ (-a))` as `x → 0`, then `log • f` is `O(x ^ (-b))` for every `a < b`. -/
theorem isBigO_rpow_zero_log_smul [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E} (hab : a < b)
    (hf : IsBigO (𝓝[>] 0) f fun t => t ^ (-a)) :
    IsBigO (𝓝[>] 0) (fun t : ℝ => log t • f t) fun t => t ^ (-b) :=
  by
  have : is_o (𝓝[>] 0) log fun t : ℝ => t ^ (a - b) :=
    by
    refine'
      ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).neg_left.comp_tendsto
            tendsto_inv_zero_atTop).congr'
        (eventually_nhds_within_iff.mpr <| eventually_of_forall fun t ht => _)
        (eventually_nhds_within_iff.mpr <| eventually_of_forall fun t ht => _)
    ·
      simp_rw [Function.comp_apply, ← one_div, log_div one_ne_zero (ne_of_gt ht), Real.log_one,
        zero_sub, neg_neg]
    · simp_rw [Function.comp_apply, inv_rpow (le_of_lt ht), ← rpow_neg (le_of_lt ht), neg_sub]
  refine'
    (this.is_O.smul hf).congr' (eventually_of_forall fun t => by rfl)
      (eventually_nhds_within_iff.mpr (eventually_of_forall fun t ht => _))
  simp_rw [smul_eq_mul, ← rpow_add ht]
  congr 1
  abel
#align is_O_rpow_zero_log_smul isBigO_rpow_zero_log_smul

/-- Suppose `f` is locally integrable on `(0, ∞)`, is `O(x ^ (-a))` as `x → ∞`, and is
`O(x ^ (-b))` as `x → 0`. Then its Mellin transform is differentiable on the domain `b < re s < a`,
with derivative equal to the Mellin transform of `log • f`. -/
theorem mellin_has_deriv_of_isBigO_rpow [CompleteSpace E] [NormedSpace ℂ E] {a b : ℝ} {f : ℝ → E}
    {s : ℂ} (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : IsBigO atTop f fun t => t ^ (-a))
    (hs_top : s.re < a) (hf_bot : IsBigO (𝓝[>] 0) f fun t => t ^ (-b)) (hs_bot : b < s.re) :
    MellinConvergent (fun t => log t • f t) s ∧
      HasDerivAt (mellin f) (mellin (fun t => log t • f t) s) s :=
  by
  let F : ℂ → ℝ → E := fun z t => (t : ℂ) ^ (z - 1) • f t
  let F' : ℂ → ℝ → E := fun z t => ((t : ℂ) ^ (z - 1) * log t) • f t
  have hab : b < a := hs_bot.trans hs_top
  -- A convenient radius of ball within which we can uniformly bound the derivative.
  obtain ⟨v, hv0, hv1, hv2⟩ : ∃ v : ℝ, 0 < v ∧ v < s.re - b ∧ v < a - s.re :=
    by
    obtain ⟨w, hw1, hw2⟩ := exists_between (sub_pos.mpr hs_top)
    obtain ⟨w', hw1', hw2'⟩ := exists_between (sub_pos.mpr hs_bot)
    exact
      ⟨min w w', lt_min hw1 hw1', (min_le_right _ _).trans_lt hw2', (min_le_left _ _).trans_lt hw2⟩
  let bound : ℝ → ℝ := fun t : ℝ => (t ^ (s.re + v - 1) + t ^ (s.re - v - 1)) * |log t| * ‖f t‖
  have h1 : ∀ᶠ z : ℂ in 𝓝 s, ae_strongly_measurable (F z) (volume.restrict <| Ioi 0) :=
    by
    refine' eventually_of_forall fun z => ae_strongly_measurable.smul _ hfc.ae_strongly_measurable
    refine' ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    refine' ContinuousAt.continuousOn fun t ht => _
    exact continuous_at_of_real_cpow_const _ _ (Or.inr <| ne_of_gt ht)
  have h2 : integrable_on (F s) (Ioi 0) :=
    mellinConvergent_of_isBigO_rpow hfc hf_top hs_top hf_bot hs_bot
  have h3 : ae_strongly_measurable (F' s) (volume.restrict <| Ioi 0) :=
    by
    apply locally_integrable_on.ae_strongly_measurable
    refine' hfc.continuous_on_smul isOpen_Ioi ((ContinuousAt.continuousOn fun t ht => _).mul _)
    · exact continuous_at_of_real_cpow_const _ _ (Or.inr <| ne_of_gt ht)
    · refine' continuous_of_real.comp_continuous_on _
      exact continuous_on_log.mono (subset_compl_singleton_iff.mpr not_mem_Ioi_self)
  have h4 : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ z : ℂ, z ∈ Metric.ball s v → ‖F' z t‖ ≤ bound t :=
    by
    refine' (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht z hz => _)
    simp_rw [bound, F', norm_smul, norm_mul, Complex.norm_eq_abs (log _), Complex.abs_ofReal,
      mul_assoc]
    refine' mul_le_mul_of_nonneg_right _ (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    rw [Complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos ht]
    rcases le_or_lt 1 t with ⟨⟩
    · refine'
        le_add_of_le_of_nonneg (rpow_le_rpow_of_exponent_le h _)
          (rpow_nonneg_of_nonneg (zero_le_one.trans h) _)
      rw [sub_re, one_re, sub_le_sub_iff_right]
      rw [mem_ball_iff_norm, Complex.norm_eq_abs] at hz 
      have hz' := (re_le_abs _).trans hz.le
      rwa [sub_re, sub_le_iff_le_add'] at hz' 
    · refine'
        le_add_of_nonneg_of_le (rpow_pos_of_pos ht _).le (rpow_le_rpow_of_exponent_ge ht h.le _)
      rw [sub_re, one_re, sub_le_iff_le_add, sub_add_cancel]
      rw [mem_ball_iff_norm', Complex.norm_eq_abs] at hz 
      have hz' := (re_le_abs _).trans hz.le
      rwa [sub_re, sub_le_iff_le_add, ← sub_le_iff_le_add'] at hz' 
  have h5 : integrable_on bound (Ioi 0) :=
    by
    simp_rw [bound, add_mul, mul_assoc]
    suffices
      ∀ {j : ℝ} (hj : b < j) (hj' : j < a),
        integrable_on (fun t : ℝ => t ^ (j - 1) * (|log t| * ‖f t‖)) (Ioi 0) volume
      by
      refine' integrable.add (this _ _) (this _ _)
      all_goals linarith
    · intro j hj hj'
      obtain ⟨w, hw1, hw2⟩ := exists_between hj
      obtain ⟨w', hw1', hw2'⟩ := exists_between hj'
      refine' mellin_convergent_of_isBigO_scalar _ _ hw1' _ hw2
      · simp_rw [mul_comm]
        refine' hfc.norm.mul_continuous_on _ isOpen_Ioi
        refine' Continuous.comp_continuousOn continuous_abs (continuous_on_log.mono _)
        exact subset_compl_singleton_iff.mpr not_mem_Ioi_self
      · refine' (isBigO_rpow_top_log_smul hw2' hf_top).norm_left.congr' _ (eventually_eq.refl _ _)
        refine' (eventually_gt_at_top 0).mp (eventually_of_forall fun t ht => _)
        simp only [norm_smul, Real.norm_eq_abs]
      · refine' (isBigO_rpow_zero_log_smul hw1 hf_bot).norm_left.congr' _ (eventually_eq.refl _ _)
        refine' eventually_nhds_within_iff.mpr (eventually_of_forall fun t ht => _)
        simp only [norm_smul, Real.norm_eq_abs]
  have h6 :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ∀ y : ℂ, y ∈ Metric.ball s v → HasDerivAt (fun z : ℂ => F z t) (F' y t) y :=
    by
    dsimp only [F, F']
    refine' (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht y hy => _)
    have ht' : (t : ℂ) ≠ 0 := of_real_ne_zero.mpr (ne_of_gt ht)
    have u1 : HasDerivAt (fun z : ℂ => (t : ℂ) ^ (z - 1)) (t ^ (y - 1) * log t) y :=
      by
      convert ((hasDerivAt_id' y).sub_const 1).const_cpow (Or.inl ht') using 1
      rw [of_real_log (le_of_lt ht)]
      ring
    exact u1.smul_const (f t)
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le hv0 h1 h2 h3 h4 h5 h6
  exact ⟨by simpa only [F', mul_smul] using main.1, by simpa only [F', mul_smul] using main.2⟩
#align mellin_has_deriv_of_is_O_rpow mellin_has_deriv_of_isBigO_rpow

/-- Suppose `f` is locally integrable on `(0, ∞)`, is `O(x ^ (-a))` as `x → ∞`, and is
`O(x ^ (-b))` as `x → 0`. Then its Mellin transform is differentiable on the domain `b < re s < a`.
-/
theorem mellin_differentiableAt_of_isBigO_rpow [CompleteSpace E] [NormedSpace ℂ E] {a b : ℝ}
    {f : ℝ → E} {s : ℂ} (hfc : LocallyIntegrableOn f <| Ioi 0)
    (hf_top : IsBigO atTop f fun t => t ^ (-a)) (hs_top : s.re < a)
    (hf_bot : IsBigO (𝓝[>] 0) f fun t => t ^ (-b)) (hs_bot : b < s.re) :
    DifferentiableAt ℂ (mellin f) s :=
  (mellin_has_deriv_of_isBigO_rpow hfc hf_top hs_top hf_bot hs_bot).2.DifferentiableAt
#align mellin_differentiable_at_of_is_O_rpow mellin_differentiableAt_of_isBigO_rpow

end MellinDiff

section ExpDecay

/-- If `f` is locally integrable, decays exponentially at infinity, and is `O(x ^ (-b))` at 0, then
its Mellin transform converges for `b < s.re`. -/
theorem mellinConvergent_of_isBigO_rpow_exp [NormedSpace ℂ E] {a b : ℝ} (ha : 0 < a) {f : ℝ → E}
    {s : ℂ} (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : IsBigO atTop f fun t => exp (-a * t))
    (hf_bot : IsBigO (𝓝[>] 0) f fun t => t ^ (-b)) (hs_bot : b < s.re) : MellinConvergent f s :=
  mellinConvergent_of_isBigO_rpow hfc (hf_top.trans (isLittleO_exp_neg_mul_rpow_atTop ha _).IsBigO)
    (lt_add_one _) hf_bot hs_bot
#align mellin_convergent_of_is_O_rpow_exp mellinConvergent_of_isBigO_rpow_exp

/-- If `f` is locally integrable, decays exponentially at infinity, and is `O(x ^ (-b))` at 0, then
its Mellin transform is holomorphic on `b < s.re`. -/
theorem mellin_differentiableAt_of_isBigO_rpow_exp [CompleteSpace E] [NormedSpace ℂ E] {a b : ℝ}
    (ha : 0 < a) {f : ℝ → E} {s : ℂ} (hfc : LocallyIntegrableOn f <| Ioi 0)
    (hf_top : IsBigO atTop f fun t => exp (-a * t)) (hf_bot : IsBigO (𝓝[>] 0) f fun t => t ^ (-b))
    (hs_bot : b < s.re) : DifferentiableAt ℂ (mellin f) s :=
  mellin_differentiableAt_of_isBigO_rpow hfc
    (hf_top.trans (isLittleO_exp_neg_mul_rpow_atTop ha _).IsBigO) (lt_add_one _) hf_bot hs_bot
#align mellin_differentiable_at_of_is_O_rpow_exp mellin_differentiableAt_of_isBigO_rpow_exp

end ExpDecay

section MellinIoc

/-!
## Mellin transforms of functions on `Ioc 0 1`
-/


/-- The Mellin transform of the indicator function of `Ioc 0 1`. -/
theorem hasMellin_one_Ioc {s : ℂ} (hs : 0 < re s) :
    HasMellin (indicator (Ioc 0 1) (fun t => 1 : ℝ → ℂ)) s (1 / s) :=
  by
  have aux1 : -1 < (s - 1).re := by
    simpa only [sub_re, one_re, sub_eq_add_neg] using lt_add_of_pos_left _ hs
  have aux2 : s ≠ 0 := by contrapose! hs; rw [hs, zero_re]
  have aux3 : MeasurableSet (Ioc (0 : ℝ) 1) := measurableSet_Ioc
  simp_rw [HasMellin, mellin, MellinConvergent, ← indicator_smul, integrable_on,
    integrable_indicator_iff aux3, smul_eq_mul, integral_indicator aux3, mul_one, integrable_on,
    measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
  rw [← integrable_on, ← intervalIntegrable_iff_integrable_Ioc_of_le zero_le_one]
  refine' ⟨intervalIntegral.intervalIntegrable_cpow' aux1, _⟩
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl aux1), sub_add_cancel,
    of_real_zero, of_real_one, one_cpow, zero_cpow aux2, sub_zero]
#align has_mellin_one_Ioc hasMellin_one_Ioc

/-- The Mellin transform of a power function restricted to `Ioc 0 1`. -/
theorem hasMellin_cpow_Ioc (a : ℂ) {s : ℂ} (hs : 0 < re s + re a) :
    HasMellin (indicator (Ioc 0 1) (fun t => ↑t ^ a : ℝ → ℂ)) s (1 / (s + a)) :=
  by
  have := hasMellin_one_Ioc (by rwa [add_re] : 0 < (s + a).re)
  simp_rw [HasMellin, ← MellinConvergent.cpow_smul, ← mellin_cpow_smul, ← indicator_smul,
    smul_eq_mul, mul_one] at this 
  exact this
#align has_mellin_cpow_Ioc hasMellin_cpow_Ioc

end MellinIoc

