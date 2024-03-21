/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

#align_import analysis.convolution from "leanprover-community/mathlib"@"8905e5ed90859939681a725b00f6063e65096d95"

/-!
# Convolution with a bump function

In this file we prove lemmas about convolutions `(φ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x₀`,
where `φ : ContDiffBump 0` is a smooth bump function.

We prove that this convolution is equal to `g x₀`
if `g` is a constant on `Metric.ball x₀ φ.rOut`.
We also provide estimates in the case if `g x` is close to `g x₀` on this ball.

## Main results

- `ContDiffBump.convolution_tendsto_right_of_continuous`:
  Let `g` be a continuous function; let `φ i` be a family of `ContDiffBump 0` functions with.
  If `(φ i).rOut` tends to zero along a filter `l`,
  then `((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x₀` tends to `g x₀` along the same filter.
- `ContDiffBump.convolution_tendsto_right`: generalization of the above lemma.
- `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`: let `g` be a locally
  integrable function. Then the convolution of `g` with a family of bump functions with
  support tending to `0` converges almost everywhere to `g`.

## Keywords

convolution, smooth function, bump function
-/

universe uG uE'

open ContinuousLinearMap Metric MeasureTheory Filter Function Measure Set
open scoped Convolution Topology

namespace ContDiffBump

variable {G : Type uG} {E' : Type uE'} [NormedAddCommGroup E'] {g : G → E'} [MeasurableSpace G]
  {μ : MeasureTheory.Measure G} [NormedSpace ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [HasContDiffBump G] [CompleteSpace E'] {φ : ContDiffBump (0 : G)} {x₀ : G}

/-- If `φ` is a bump function, compute `(φ ⋆ g) x₀`
if `g` is constant on `Metric.ball x₀ φ.rOut`. -/
theorem convolution_eq_right {x₀ : G} (hg : ∀ x ∈ ball x₀ φ.rOut, g x = g x₀) :
    (φ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = integral μ φ • g x₀ := by
  simp_rw [convolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]
#align cont_diff_bump.convolution_eq_right ContDiffBump.convolution_eq_right

variable [BorelSpace G]
variable [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
variable [FiniteDimensional ℝ G]

/-- If `φ` is a normed bump function, compute `φ ⋆ g`
if `g` is constant on `Metric.ball x₀ φ.rOut`. -/
theorem normed_convolution_eq_right {x₀ : G} (hg : ∀ x ∈ ball x₀ φ.rOut, g x = g x₀) :
    (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = g x₀ := by
  rw [convolution_eq_right' _ φ.support_normed_eq.subset hg]
  exact integral_normed_smul φ μ (g x₀)
#align cont_diff_bump.normed_convolution_eq_right ContDiffBump.normed_convolution_eq_right

variable [μ.IsAddLeftInvariant]

/-- If `φ` is a normed bump function, approximate `(φ ⋆ g) x₀`
if `g` is near `g x₀` on a ball with radius `φ.rOut` around `x₀`. -/
theorem dist_normed_convolution_le {x₀ : G} {ε : ℝ} (hmg : AEStronglyMeasurable g μ)
    (hg : ∀ x ∈ ball x₀ φ.rOut, dist (g x) (g x₀) ≤ ε) :
    dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
  dist_convolution_le (by simp_rw [← dist_self (g x₀), hg x₀ (mem_ball_self φ.rOut_pos)])
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hmg hg
#align cont_diff_bump.dist_normed_convolution_le ContDiffBump.dist_normed_convolution_le

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of normed bump functions
  such that `(φ i).rOut` tends to `0` as `i` tends to `l`;
* `g i` is `μ`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ˢ 𝓝 x₀`;
* `k i` tends to `x₀`. -/
nonrec theorem convolution_tendsto_right {ι} {φ : ι → ContDiffBump (0 : G)} {g : ι → G → E'}
    {k : ι → G} {x₀ : G} {z₀ : E'} {l : Filter ι} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hig : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ) (hcg : Tendsto (uncurry g) (l ×ˢ 𝓝 x₀) (𝓝 z₀))
    (hk : Tendsto k l (𝓝 x₀)) :
    Tendsto (fun i => ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g i) (k i)) l (𝓝 z₀) :=
  convolution_tendsto_right (eventually_of_forall fun i => (φ i).nonneg_normed)
    (eventually_of_forall fun i => (φ i).integral_normed) (tendsto_support_normed_smallSets hφ) hig
    hcg hk
#align cont_diff_bump.convolution_tendsto_right ContDiffBump.convolution_tendsto_right

/-- Special case of `ContDiffBump.convolution_tendsto_right` where `g` is continuous,
  and the limit is taken only in the first function. -/
theorem convolution_tendsto_right_of_continuous {ι} {φ : ι → ContDiffBump (0 : G)} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hg : Continuous g) (x₀ : G) :
    Tendsto (fun i => ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x₀) l (𝓝 (g x₀)) :=
  convolution_tendsto_right hφ (eventually_of_forall fun _ => hg.aestronglyMeasurable)
    ((hg.tendsto x₀).comp tendsto_snd) tendsto_const_nhds
#align cont_diff_bump.convolution_tendsto_right_of_continuous ContDiffBump.convolution_tendsto_right_of_continuous

/-- If a function `g` is locally integrable, then the convolution `φ i * g` converges almost
everywhere to `g` if `φ i` is a sequence of bump functions with support tending to `0`, provided
that the ratio between the inner and outer radii of `φ i` remains bounded. -/
theorem ae_convolution_tendsto_right_of_locallyIntegrable
    {ι} {φ : ι → ContDiffBump (0 : G)} {l : Filter ι} {K : ℝ}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (h'φ : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn) (hg : LocallyIntegrable g μ) : ∀ᵐ x₀ ∂μ,
    Tendsto (fun i ↦ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x₀) l (𝓝 (g x₀)) := by
  have : IsAddHaarMeasure μ := ⟨⟩
  -- By Lebesgue differentiation theorem, the average of `g` on a small ball converges
  -- almost everywhere to the value of `g` as the radius shrinks to zero.
  -- We will see that this set of points satisfies the desired conclusion.
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average_norm_sub hg] with x₀ h₀
  simp only [convolution_eq_swap, lsmul_apply]
  have hφ' : Tendsto (fun i ↦ (φ i).rOut) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hφ, eventually_of_forall (fun i ↦ (φ i).rOut_pos)⟩
  have := (h₀.comp (Besicovitch.tendsto_filterAt μ x₀)).comp hφ'
  simp only [Function.comp] at this
  apply tendsto_integral_smul_of_tendsto_average_norm_sub (K ^ (FiniteDimensional.finrank ℝ G)) this
  · filter_upwards with i using
      hg.integrableOn_isCompact (isCompact_closedBall _ _)
  · apply tendsto_const_nhds.congr (fun i ↦ ?_)
    rw [← integral_neg_eq_self]
    simp only [sub_neg_eq_add, integral_add_left_eq_self, integral_normed]
  · filter_upwards with i
    change support ((ContDiffBump.normed (φ i) μ) ∘ (fun y ↦ x₀ - y)) ⊆ closedBall x₀ (φ i).rOut
    simp only [support_comp_eq_preimage, support_normed_eq]
    intro x hx
    simp only [mem_preimage, mem_ball, dist_zero_right] at hx
    simpa [dist_eq_norm_sub'] using hx.le
  · filter_upwards [h'φ] with i hi x
    rw [abs_of_nonneg (nonneg_normed _ _), addHaar_closedBall_center]
    exact (φ i).normed_le_div_measure_closedBall_rOut _ _ hi _

end ContDiffBump
