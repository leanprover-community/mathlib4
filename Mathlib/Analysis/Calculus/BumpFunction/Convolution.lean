import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed

universe uG uE'

open ContinuousLinearMap Metric MeasureTheory Filter Function
open scoped Convolution Topology

namespace ContDiffBump

variable {G : Type uG} {E' : Type uE'} [NormedAddCommGroup E'] {g : G → E'} [MeasurableSpace G]
  {μ : MeasureTheory.Measure G} [NormedSpace ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [HasContDiffBump G] [CompleteSpace E'] {φ : ContDiffBump (0 : G)} {x₀ : G}

/-- If `φ` is a bump function, compute `(φ ⋆ g) x₀` if `g` is constant on `Metric.ball x₀ φ.R`. -/
theorem convolution_eq_right {x₀ : G} (hg : ∀ x ∈ ball x₀ φ.rOut, g x = g x₀) :
    (φ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = integral μ φ • g x₀ := by
  simp_rw [convolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]
#align cont_diff_bump.convolution_eq_right ContDiffBump.convolution_eq_right

variable [BorelSpace G]
variable [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

variable [FiniteDimensional ℝ G]

/-- If `φ` is a normed bump function, compute `φ ⋆ g` if `g` is constant on `Metric.ball x₀ φ.R`. -/
theorem normed_convolution_eq_right {x₀ : G} (hg : ∀ x ∈ ball x₀ φ.rOut, g x = g x₀) :
    (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = g x₀ := by
  rw [convolution_eq_right' _ φ.support_normed_eq.subset hg]
  exact integral_normed_smul φ μ (g x₀)
#align cont_diff_bump.normed_convolution_eq_right ContDiffBump.normed_convolution_eq_right

variable [μ.IsAddLeftInvariant]

/-- If `φ` is a normed bump function, approximate `(φ ⋆ g) x₀` if `g` is near `g x₀` on a ball with
radius `φ.R` around `x₀`. -/
theorem dist_normed_convolution_le {x₀ : G} {ε : ℝ} (hmg : AEStronglyMeasurable g μ)
    (hg : ∀ x ∈ ball x₀ φ.rOut, dist (g x) (g x₀) ≤ ε) :
    dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
  dist_convolution_le (by simp_rw [← dist_self (g x₀), hg x₀ (mem_ball_self φ.rOut_pos)])
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hmg hg
#align cont_diff_bump.dist_normed_convolution_le ContDiffBump.dist_normed_convolution_le

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of normed bump functions such that `(φ i).R` tends to `0` as `i` tends to `l`;
* `g i` is `mu`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ˢ 𝓝 x₀`;
* `k i` tends to `x₀`. -/
nonrec theorem convolution_tendsto_right {ι} {φ : ι → ContDiffBump (0 : G)} {g : ι → G → E'}
    {k : ι → G} {x₀ : G} {z₀ : E'} {l : Filter ι} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hig : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ) (hcg : Tendsto (uncurry g) (l ×ˢ 𝓝 x₀) (𝓝 z₀))
    (hk : Tendsto k l (𝓝 x₀)) :
    Tendsto (fun i => ((fun x => (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀) :=
  convolution_tendsto_right (eventually_of_forall fun i => (φ i).nonneg_normed)
    (eventually_of_forall fun i => (φ i).integral_normed) (tendsto_support_normed_smallSets hφ) hig
    hcg hk
#align cont_diff_bump.convolution_tendsto_right ContDiffBump.convolution_tendsto_right

/-- Special case of `ContDiffBump.convolution_tendsto_right` where `g` is continuous,
  and the limit is taken only in the first function. -/
theorem convolution_tendsto_right_of_continuous {ι} {φ : ι → ContDiffBump (0 : G)} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hg : Continuous g) (x₀ : G) :
    Tendsto (fun i => ((fun x => (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
  convolution_tendsto_right hφ (eventually_of_forall fun _ => hg.aestronglyMeasurable)
    ((hg.tendsto x₀).comp tendsto_snd) tendsto_const_nhds
#align cont_diff_bump.convolution_tendsto_right_of_continuous ContDiffBump.convolution_tendsto_right_of_continuous

end ContDiffBump
