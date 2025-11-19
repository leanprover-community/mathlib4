/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Jensen's Formula of Complex Analysis

If a function `g : ℂ → ℂ` is analytic without zero on the closed ball with center `c` and radius
`R`, then `log ‖g ·‖` is harmonic, and the mean value theorem of harmonic functions asserts that the
circle average `circleAverage (log ‖g ·‖) c R` equals `log ‖g c‖`.  Note that `g c` equals
`meromorphicTrailingCoeffAt g c` and see `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero` for the
precise statement.

Jensen's Formula, formulated in `MeromorphicOn.circleAverage_log_norm` below, generalizes this to
the setting where `g` is merely meromorphic. In that case, the `circleAverage (log ‖g ·‖) c R`
equals `log ‖meromorphicTrailingCoeffAt g c‖` plus a correction term that accounts for the zeros and
poles of `g` within the ball.
-/

@[expose] public section

open Filter MeromorphicAt MeromorphicOn Metric Real

/-!
## Preparatory Material

In preparation to the proof of Jensen's formula, compute several circle averages and reformulate
some of the terms that appear in the formula and its proof.
-/

/--
Let `D : ℂ → ℤ` be a function with locally finite support within the closed ball with center `c` and
radius `R`, such as the zero- and pole divisor of a meromorphic function.  Then, the circle average
of the function `∑ᶠ u, (D u * log ‖· - u‖)` over the boundary of the ball equals
`∑ᶠ u, D u * log R`.
-/
@[simp]
lemma circleAverage_log_norm_factorizedRational {R : ℝ} {c : ℂ}
    (D : Function.locallyFinsuppWithin (closedBall c |R|) ℤ) :
    circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R = ∑ᶠ u, D u * log R := by
  have h := D.finiteSupport (isCompact_closedBall c |R|)
  calc circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R
  _ = circleAverage (∑ u ∈ h.toFinset, (D u * log ‖· - u‖)) c R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    contrapose
    aesop
  _ = ∑ i ∈ h.toFinset, circleAverage (fun x ↦ D i * log ‖x - i‖) c R := by
    rw [circleAverage_sum]
    intro u hu
    apply IntervalIntegrable.const_mul
    apply circleIntegrable_log_norm_meromorphicOn (f := (· - u))
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
  _ = ∑ u ∈ h.toFinset, D u * log R := by
    apply Finset.sum_congr rfl
    intro u hu
    simp_rw [← smul_eq_mul, circleAverage_fun_smul]
    congr
    rw [circleAverage_log_norm_sub_const_of_mem_closedBall]
    apply D.supportWithinDomain
    simp_all
  _ = ∑ᶠ u, D u * log R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    aesop

/--
If  `g : ℂ → ℂ` is analytic without zero on the closed ball with center `c` and radius `R`, then the
circle average `circleAverage (log ‖g ·‖) c R` equals `log ‖g c‖`.
-/
@[simp]
lemma AnalyticOnNhd.circleAverage_log_norm_of_ne_zero {R : ℝ} {c : ℂ} {g : ℂ → ℂ}
    (h₁g : AnalyticOnNhd ℂ g (closedBall c |R|)) (h₂g : ∀ u ∈ closedBall c |R|, g u ≠ 0) :
    circleAverage (Real.log ‖g ·‖) c R = Real.log ‖g c‖ :=
  HarmonicOnNhd.circleAverage_eq (fun x hx ↦ (h₁g x hx).harmonicAt_log_norm (h₂g x hx))

/--
Reformulation of a finsum that appears in Jensen's formula and in the definition of the counting
function of Value Distribution Theory, as discussed in
`Mathlib/Analysis/Complex/ValueDistribution/CountingFunction.lean`.
-/
lemma countingFunction_finsum_eq_finsum_add {c : ℂ} {R : ℝ} {D : ℂ → ℤ} (hR : R ≠ 0)
    (hD : D.support.Finite) :
    ∑ᶠ u, D u * (log R - log ‖c - u‖) = ∑ᶠ u, D u * log (R * ‖c - u‖⁻¹) + D c * log R := by
  by_cases h : c ∈ D.support
  · have {g : ℂ → ℝ} : (fun u ↦ D u * g u).support ⊆ hD.toFinset :=
      fun x ↦ by simp +contextual
    simp only [finsum_eq_sum_of_support_subset _ this,
      Finset.sum_eq_sum_diff_singleton_add ((Set.Finite.mem_toFinset hD).mpr h), sub_self,
      norm_zero, log_zero, sub_zero, inv_zero, mul_zero, add_zero, add_left_inj]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [Finset.mem_sdiff, Finset.notMem_singleton] at hx
    rw [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr (sub_eq_zero.not.2 hx.2.symm))), log_inv]
    ring
  · simp_all only [Function.mem_support, Decidable.not_not, Int.cast_zero, zero_mul, add_zero]
    refine finsum_congr fun x ↦ ?_
    by_cases h₁ : c = x
    · simp_all
    · rw [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr (sub_eq_zero.not.2 h₁))), log_inv]
      ring

/-!
## Jensen's Formula
-/

/-!
**Jensen's Formula**: If `f : ℂ → ℂ` is meromorphic on the closed ball with center `c` and radius
`R`, then the `circleAverage (log ‖f ·‖) c R` equals `log ‖meromorphicTrailingCoeffAt f c‖` plus a
correction term that accounts for the zeros and poles of `f` within the ball.

See `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const` for a
reformulation in terms of the logarithmic counting function of Value Distribution Theory.
-/
theorem MeromorphicOn.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0)
    (h₁f : MeromorphicOn f (closedBall c |R|)) :
    circleAverage (log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * log (R * ‖c - u‖⁻¹)
        + divisor f (closedBall c |R|) c * log R + log ‖meromorphicTrailingCoeffAt f c‖ := by
  -- Shorthand notation to keep line size in check
  let CB := closedBall c |R|
  by_cases h₂f : ∀ u ∈ CB, meromorphicOrderAt f u ≠ ⊤
  · have h₃f := (divisor f CB).finiteSupport (isCompact_closedBall c |R|)
    -- Extract zeros & poles and compute
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extract_zeros_poles (by simp_all) h₃f
    calc circleAverage (log ‖f ·‖) c R
    _ = circleAverage ((∑ᶠ u, (divisor f CB u * log ‖· - u‖)) + (log ‖g ·‖)) c R := by
      have h₄g := extract_zeros_poles_log h₂g h₃g
      rw [circleAverage_congr_codiscreteWithin (codiscreteWithin.mono sphere_subset_closedBall h₄g)
        hR]
    _ = circleAverage (∑ᶠ u, (divisor f CB u * log ‖· - u‖)) c R + circleAverage (log ‖g ·‖) c R :=
      circleAverage_add (circleIntegrable_log_norm_factorizedRational (divisor f CB))
        (circleIntegrable_log_norm_meromorphicOn (h₁g.mono sphere_subset_closedBall).meromorphicOn)
    _ = ∑ᶠ u, divisor f CB u * log R + log ‖g c‖ := by
      simp [h₁g]
      rw [h₁g.circleAverage_log_norm_of_ne_zero]
      exact fun u hu ↦ h₂g ⟨u, hu⟩
    _ = ∑ᶠ u, divisor f CB u * log R
      + (log ‖meromorphicTrailingCoeffAt f c‖ - ∑ᶠ u, divisor f CB u * log ‖c - u‖) := by
      have t₀ : c ∈ CB := by simp [CB]
      have t₁ : AccPt c (𝓟 CB) := by
        apply accPt_iff_frequently_nhdsNE.mpr
        apply compl_notMem
        apply mem_nhdsWithin.mpr
        use ball c |R|
        simpa [hR] using fun _ ⟨h, _⟩ ↦ ball_subset_closedBall h
      simp [MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles h₃f t₀ t₁
        (h₁f c t₀) (h₁g c t₀) (h₂g ⟨c, t₀⟩) h₃g]
    _ = ∑ᶠ u, divisor f CB u * log R - ∑ᶠ u, divisor f CB u * log ‖c - u‖
      + log ‖meromorphicTrailingCoeffAt f c‖ := by
      ring
    _ = (∑ᶠ u, divisor f CB u * (log R - log ‖c - u‖)) + log ‖meromorphicTrailingCoeffAt f c‖ := by
      rw [← finsum_sub_distrib]
      · simp_rw [← mul_sub]
      repeat apply h₃f.subset (fun _ ↦ (by simp_all))
    _ = ∑ᶠ u, divisor f CB u * log (R * ‖c - u‖⁻¹) + divisor f CB c * log R
      + log ‖meromorphicTrailingCoeffAt f c‖ := by
      rw [countingFunction_finsum_eq_finsum_add hR h₃f]
  · -- Trivial case: `f` vanishes on a codiscrete set
    have h₂f : ¬∀ (u : ↑(closedBall c |R|)), meromorphicOrderAt f ↑u ≠ ⊤ := by aesop
    rw [← h₁f.exists_meromorphicOrderAt_ne_top_iff_forall
      ⟨nonempty_closedBall.mpr (abs_nonneg R), (convex_closedBall c |R|).isPreconnected⟩] at h₂f
    push_neg at h₂f
    have : divisor f CB = 0 := by
      ext x
      by_cases h : x ∈ CB
      <;> simp_all [CB]
    simp only [CB, this, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero,
      zero_mul, finsum_zero, add_zero, zero_add]
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top (by aesop), norm_zero, log_zero]
    have : f =ᶠ[codiscreteWithin CB] 0 := by
      filter_upwards [h₁f.meromorphicNFAt_mem_codiscreteWithin, self_mem_codiscreteWithin CB]
        with z h₁z h₂z
      simpa [h₂f ⟨z, h₂z⟩] using (not_iff_not.2 h₁z.meromorphicOrderAt_eq_zero_iff)
    rw [circleAverage_congr_codiscreteWithin (f₂ := 0) _ hR]
    · simp only [circleAverage, mul_inv_rev, Pi.zero_apply, intervalIntegral.integral_zero,
        smul_eq_mul, mul_zero]
    apply Filter.codiscreteWithin.mono (U := CB) sphere_subset_closedBall
    filter_upwards [this] with z hz
    simp_all
