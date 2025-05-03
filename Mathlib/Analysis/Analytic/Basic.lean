/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Bound.Attribute
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Analytic functions

A function is analytic in one dimension around `0` if it can be written as a converging power series
`Σ pₙ zⁿ`. This definition can be extended to any dimension (even in infinite dimension) by
requiring that `pₙ` is a continuous `n`-multilinear map. In general, `pₙ` is not unique (in two
dimensions, taking `p₂ (x, y) (x', y') = x y'` or `y x'` gives the same map when applied to a
vector `(x, y) (x, y)`). A way to guarantee uniqueness is to take a symmetric `pₙ`, but this is not
always possible in nonzero characteristic (in characteristic 2, the previous example has no
symmetric representative). Therefore, we do not insist on symmetry or uniqueness in the definition,
and we only require the existence of a converging series.

The general framework is important to say that the exponential map on bounded operators on a Banach
space is analytic, as well as the inverse on invertible operators.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `p.radius`: the largest `r : ℝ≥0∞` such that `‖p n‖ * r^n` grows subexponentially.
* `p.le_radius_of_bound`, `p.le_radius_of_bound_nnreal`, `p.le_radius_of_isBigO`: if `‖p n‖ * r ^ n`
  is bounded above, then `r ≤ p.radius`;
* `p.isLittleO_of_lt_radius`, `p.norm_mul_pow_le_mul_pow_of_lt_radius`,
  `p.isLittleO_one_of_lt_radius`,
  `p.norm_mul_pow_le_of_lt_radius`, `p.nnnorm_mul_pow_le_of_lt_radius`: if `r < p.radius`, then
  `‖p n‖ * r ^ n` tends to zero exponentially;
* `p.lt_radius_of_isBigO`: if `r ≠ 0` and `‖p n‖ * r ^ n = O(a ^ n)` for some `-1 < a < 1`, then
  `r < p.radius`;
* `p.partialSum n x`: the sum `∑_{i = 0}^{n-1} pᵢ xⁱ`.
* `p.sum x`: the sum `∑'_{i = 0}^{∞} pᵢ xⁱ`.

Additionally, let `f` be a function from `E` to `F`.

* `HasFPowerSeriesOnBall f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₙ yⁿ`.
* `HasFPowerSeriesAt f p x`: on some ball of center `x` with positive radius, holds
  `HasFPowerSeriesOnBall f p x r`.
* `AnalyticAt 𝕜 f x`: there exists a power series `p` such that holds `HasFPowerSeriesAt f p x`.
* `AnalyticOnNhd 𝕜 f s`: the function `f` is analytic at every point of `s`.

We also define versions of `HasFPowerSeriesOnBall`, `AnalyticAt`, and `AnalyticOnNhd` restricted to
a set, similar to `ContinuousWithinAt`. See `Mathlib.Analysis.Analytic.Within` for basic properties.

* `AnalyticWithinAt 𝕜 f s x` means a power series at `x` converges to `f` on `𝓝[s ∪ {x}] x`.
* `AnalyticOn 𝕜 f s t` means `∀ x ∈ t, AnalyticWithinAt 𝕜 f s x`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `HasFPowerSeriesOnBall.continuousOn` and `HasFPowerSeriesAt.continuousAt` and
  `AnalyticAt.continuousAt`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `FormalMultilinearSeries.hasFPowerSeriesOnBall`.

## Implementation details

We only introduce the radius of convergence of a power series, as `p.radius`.
For a power series in finitely many dimensions, there is a finer (directional, coordinate-dependent)
notion, describing the polydisk of convergence. This notion is more specific, and not necessary to
build the general theory. We do not define it here.
-/

noncomputable section

variable {𝕜 E F G : Type*}

open Topology NNReal Filter ENNReal Set Asymptotics
open scoped Pointwise

namespace FormalMultilinearSeries

variable [Semiring 𝕜] [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]
variable [TopologicalSpace E] [TopologicalSpace F]
variable [ContinuousAdd E] [ContinuousAdd F]
variable [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F]

/-- Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A
priori, it only behaves well when `‖x‖ < p.radius`. -/
protected def sum (p : FormalMultilinearSeries 𝕜 E F) (x : E) : F :=
  ∑' n : ℕ, p n fun _ => x

/-- Given a formal multilinear series `p` and a vector `x`, then `p.partialSum n x` is the sum
`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/
def partialSum (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (x : E) : F :=
  ∑ k ∈ Finset.range n, p k fun _ : Fin k => x

/-- The partial sums of a formal multilinear series are continuous. -/
theorem partialSum_continuous (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
    Continuous (p.partialSum n) := by
  unfold partialSum
  fun_prop

end FormalMultilinearSeries

/-! ### The radius of a formal multilinear series -/

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}

/-- The radius of a formal multilinear series is the largest `r` such that the sum `Σ ‖pₙ‖ ‖y‖ⁿ`
converges for all `‖y‖ < r`. This implies that `Σ pₙ yⁿ` converges for all `‖y‖ < r`, but these
definitions are *not* equivalent in general. -/
def radius (p : FormalMultilinearSeries 𝕜 E F) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (C : ℝ) (_ : ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C), (r : ℝ≥0∞)

/-- If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound (C : ℝ) {r : ℝ≥0} (h : ∀ n : ℕ, ‖p n‖ * (r : ℝ) ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ p.radius :=
  le_iSup_of_le r <| le_iSup_of_le C <| le_iSup (fun _ => (r : ℝ≥0∞)) h

/-- If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound_nnreal (C : ℝ≥0) {r : ℝ≥0} (h : ∀ n : ℕ, ‖p n‖₊ * r ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ p.radius :=
  p.le_radius_of_bound C fun n => mod_cast h n

/-- If `‖pₙ‖ rⁿ = O(1)`, as `n → ∞`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_isBigO (h : (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] fun _ => (1 : ℝ)) :
    ↑r ≤ p.radius :=
  Exists.elim (isBigO_one_nat_atTop_iff.1 h) fun C hC =>
    p.le_radius_of_bound C fun n => (le_abs_self _).trans (hC n)

theorem le_radius_of_eventually_le (C) (h : ∀ᶠ n in atTop, ‖p n‖ * (r : ℝ) ^ n ≤ C) :
    ↑r ≤ p.radius :=
  p.le_radius_of_isBigO <| IsBigO.of_bound C <| h.mono fun n hn => by simpa

theorem le_radius_of_summable_nnnorm (h : Summable fun n => ‖p n‖₊ * r ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_bound_nnreal (∑' n, ‖p n‖₊ * r ^ n) fun _ => h.le_tsum' _

theorem le_radius_of_summable (h : Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_summable_nnnorm <| by
    simp only [← coe_nnnorm] at h
    exact mod_cast h

theorem radius_eq_top_of_forall_nnreal_isBigO
    (h : ∀ r : ℝ≥0, (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] fun _ => (1 : ℝ)) : p.radius = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_isBigO (h r)

theorem radius_eq_top_of_eventually_eq_zero (h : ∀ᶠ n in atTop, p n = 0) : p.radius = ∞ :=
  p.radius_eq_top_of_forall_nnreal_isBigO fun r =>
    (isBigO_zero _ _).congr' (h.mono fun n hn => by simp [hn]) EventuallyEq.rfl

theorem radius_eq_top_of_forall_image_add_eq_zero (n : ℕ) (hn : ∀ m, p (m + n) = 0) :
    p.radius = ∞ :=
  p.radius_eq_top_of_eventually_eq_zero <|
    mem_atTop_sets.2 ⟨n, fun _ hk => tsub_add_cancel_of_le hk ▸ hn _⟩

@[simp]
theorem constFormalMultilinearSeries_radius {v : F} :
    (constFormalMultilinearSeries 𝕜 E v).radius = ⊤ :=
  (constFormalMultilinearSeries 𝕜 E v).radius_eq_top_of_forall_image_add_eq_zero 1
    (by simp [constFormalMultilinearSeries])

/-- `0` has infinite radius of convergence -/
@[simp] lemma zero_radius : (0 : FormalMultilinearSeries 𝕜 E F).radius = ∞ := by
  rw [← constFormalMultilinearSeries_zero]
  exact constFormalMultilinearSeries_radius

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` tends to zero exponentially:
for some `0 < a < 1`, `‖p n‖ rⁿ = o(aⁿ)`. -/
theorem isLittleO_of_lt_radius (h : ↑r < p.radius) :
    ∃ a ∈ Ioo (0 : ℝ) 1, (fun n => ‖p n‖ * (r : ℝ) ^ n) =o[atTop] (a ^ ·) := by
  have := (TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 4
  rw [this]
  -- Porting note: was
  -- rw [(TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 4]
  simp only [radius, lt_iSup_iff] at h
  rcases h with ⟨t, C, hC, rt⟩
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at rt
  have : 0 < (t : ℝ) := r.coe_nonneg.trans_lt rt
  rw [← div_lt_one this] at rt
  refine ⟨_, rt, C, Or.inr zero_lt_one, fun n => ?_⟩
  calc
    |‖p n‖ * (r : ℝ) ^ n| = ‖p n‖ * (t : ℝ) ^ n * (r / t : ℝ) ^ n := by
      field_simp [mul_right_comm, abs_mul]
    _ ≤ C * (r / t : ℝ) ^ n := by gcongr; apply hC

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ = o(1)`. -/
theorem isLittleO_one_of_lt_radius (h : ↑r < p.radius) :
    (fun n => ‖p n‖ * (r : ℝ) ^ n) =o[atTop] (fun _ => 1 : ℕ → ℝ) :=
  let ⟨_, ha, hp⟩ := p.isLittleO_of_lt_radius h
  hp.trans <| (isLittleO_pow_pow_of_lt_left ha.1.le ha.2).congr (fun _ => rfl) one_pow

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` tends to zero exponentially:
for some `0 < a < 1` and `C > 0`, `‖p n‖ * r ^ n ≤ C * a ^ n`. -/
theorem norm_mul_pow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C * a ^ n := by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 5).mp
    (p.isLittleO_of_lt_radius h)
  rcases this with ⟨a, ha, C, hC, H⟩
  exact ⟨a, ha, C, hC, fun n => (le_abs_self _).trans (H n)⟩

/-- If `r ≠ 0` and `‖pₙ‖ rⁿ = O(aⁿ)` for some `-1 < a < 1`, then `r < p.radius`. -/
theorem lt_radius_of_isBigO (h₀ : r ≠ 0) {a : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hp : (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] (a ^ ·)) : ↑r < p.radius := by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 2 5)
  rcases this.mp ⟨a, ha, hp⟩ with ⟨a, ha, C, hC, hp⟩
  rw [← pos_iff_ne_zero, ← NNReal.coe_pos] at h₀
  lift a to ℝ≥0 using ha.1.le
  have : (r : ℝ) < r / a := by
    simpa only [div_one] using (div_lt_div_iff_of_pos_left h₀ zero_lt_one ha.1).2 ha.2
  norm_cast at this
  rw [← ENNReal.coe_lt_coe] at this
  refine this.trans_le (p.le_radius_of_bound C fun n => ?_)
  rw [NNReal.coe_div, div_pow, ← mul_div_assoc, div_le_iff₀ (pow_pos ha.1 n)]
  exact (le_abs_self _).trans (hp n)

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
theorem norm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C :=
  let ⟨_, ha, C, hC, h⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  ⟨C, hC, fun n => (h n).trans <| mul_le_of_le_one_right hC.lt.le (pow_le_one₀ ha.1.le ha.2.le)⟩

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
theorem norm_le_div_pow_of_pos_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h0 : 0 < r) (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖ ≤ C / (r : ℝ) ^ n :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨C, hC, fun n => Iff.mpr (le_div_iff₀ (pow_pos h0 _)) (hp n)⟩

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
theorem nnnorm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖₊ * r ^ n ≤ C :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨⟨C, hC.lt.le⟩, hC, mod_cast hp⟩

theorem le_radius_of_tendsto (p : FormalMultilinearSeries 𝕜 E F) {l : ℝ}
    (h : Tendsto (fun n => ‖p n‖ * (r : ℝ) ^ n) atTop (𝓝 l)) : ↑r ≤ p.radius :=
  p.le_radius_of_isBigO (h.isBigO_one _)

theorem le_radius_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_tendsto hs.tendsto_atTop_zero

theorem not_summable_norm_of_radius_lt_nnnorm (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (h : p.radius < ‖x‖₊) : ¬Summable fun n => ‖p n‖ * ‖x‖ ^ n :=
  fun hs => not_le_of_lt h (p.le_radius_of_summable_norm hs)

theorem summable_norm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0} (h : ↑r < p.radius) :
    Summable fun n : ℕ => ‖p n‖ * (r : ℝ) ^ n := by
  obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  exact .of_nonneg_of_le (fun _ ↦ by positivity)
    hp ((summable_geometric_of_lt_one ha.1.le ha.2).mul_left _)

theorem summable_norm_apply (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ EMetric.ball (0 : E) p.radius) : Summable fun n : ℕ => ‖p n fun _ => x‖ := by
  rw [mem_emetric_ball_zero_iff] at hx
  refine .of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (fun n ↦ ((p n).le_opNorm _).trans_eq ?_) (p.summable_norm_mul_pow hx)
  simp

theorem summable_nnnorm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0} (h : ↑r < p.radius) :
    Summable fun n : ℕ => ‖p n‖₊ * r ^ n := by
  rw [← NNReal.summable_coe]
  push_cast
  exact p.summable_norm_mul_pow h

protected theorem summable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ EMetric.ball (0 : E) p.radius) : Summable fun n : ℕ => p n fun _ => x :=
  (p.summable_norm_apply hx).of_norm

theorem radius_eq_top_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : ∀ r : ℝ≥0, Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : p.radius = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_summable_norm (hs r)

theorem radius_eq_top_iff_summable_norm (p : FormalMultilinearSeries 𝕜 E F) :
    p.radius = ∞ ↔ ∀ r : ℝ≥0, Summable fun n => ‖p n‖ * (r : ℝ) ^ n := by
  constructor
  · intro h r
    obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius
      (show (r : ℝ≥0∞) < p.radius from h.symm ▸ ENNReal.coe_lt_top)
    refine .of_norm_bounded
      (fun n ↦ (C : ℝ) * a ^ n) ((summable_geometric_of_lt_one ha.1.le ha.2).mul_left _) fun n ↦ ?_
    specialize hp n
    rwa [Real.norm_of_nonneg (by positivity)]
  · exact p.radius_eq_top_of_summable_norm

/-- If the radius of `p` is positive, then `‖pₙ‖` grows at most geometrically. -/
theorem le_mul_pow_of_radius_pos (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ n, ‖p n‖ ≤ C * r ^ n := by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨r, r0, rlt⟩
  have rpos : 0 < (r : ℝ) := by simp [ENNReal.coe_pos.1 r0]
  rcases norm_le_div_pow_of_pos_of_lt_radius p rpos rlt with ⟨C, Cpos, hCp⟩
  refine ⟨C, r⁻¹, Cpos, by simp only [inv_pos, rpos], fun n => ?_⟩
  rw [inv_pow, ← div_eq_mul_inv]
  exact hCp n

lemma radius_le_of_le {𝕜' E' F' : Type*}
    [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E'] [NormedSpace 𝕜' E']
    [NormedAddCommGroup F'] [NormedSpace 𝕜' F']
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜' E' F'}
    (h : ∀ n, ‖p n‖ ≤ ‖q n‖) : q.radius ≤ p.radius := by
  apply le_of_forall_nnreal_lt (fun r hr ↦ ?_)
  rcases norm_mul_pow_le_of_lt_radius _ hr with ⟨C, -, hC⟩
  apply le_radius_of_bound _ C (fun n ↦ ?_)
  apply le_trans _ (hC n)
  gcongr
  exact h n

/-- The radius of the sum of two formal series is at least the minimum of their two radii. -/
theorem min_radius_le_radius_add (p q : FormalMultilinearSeries 𝕜 E F) :
    min p.radius q.radius ≤ (p + q).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  rw [lt_min_iff] at hr
  have := ((p.isLittleO_one_of_lt_radius hr.1).add (q.isLittleO_one_of_lt_radius hr.2)).isBigO
  refine (p + q).le_radius_of_isBigO ((isBigO_of_le _ fun n => ?_).trans this)
  rw [← add_mul, norm_mul, norm_mul, norm_norm]
  exact mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (le_abs_self _)) (norm_nonneg _)

@[simp]
theorem radius_neg (p : FormalMultilinearSeries 𝕜 E F) : (-p).radius = p.radius := by
  simp only [radius, neg_apply, norm_neg]

theorem radius_le_smul {p : FormalMultilinearSeries 𝕜 E F} {c : 𝕜} : p.radius ≤ (c • p).radius := by
  simp only [radius, smul_apply]
  refine iSup_mono fun r ↦ iSup_mono' fun C ↦ ⟨‖c‖ * C, iSup_mono' fun h ↦ ?_⟩
  simp only [le_refl, exists_prop, and_true]
  intro n
  rw [norm_smul c (p n), mul_assoc]
  gcongr
  exact h n

theorem radius_smul_eq (p : FormalMultilinearSeries 𝕜 E F) {c : 𝕜} (hc : c ≠ 0) :
    (c • p).radius = p.radius := by
  apply eq_of_le_of_le _ radius_le_smul
  exact radius_le_smul.trans_eq (congr_arg _ <| inv_smul_smul₀ hc p)

@[simp]
theorem radius_shift (p : FormalMultilinearSeries 𝕜 E F) : p.shift.radius = p.radius := by
  simp only [radius, shift, Nat.succ_eq_add_one, ContinuousMultilinearMap.curryRight_norm]
  congr
  ext r
  apply eq_of_le_of_le
  · apply iSup_mono'
    intro C
    use ‖p 0‖ ⊔ (C * r)
    apply iSup_mono'
    intro h
    simp only [le_refl, le_sup_iff, exists_prop, and_true]
    intro n
    rcases n with - | m
    · simp
    right
    rw [pow_succ, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right (h m) zero_le_coe
  · apply iSup_mono'
    intro C
    use ‖p 1‖ ⊔ C / r
    apply iSup_mono'
    intro h
    simp only [le_refl, le_sup_iff, exists_prop, and_true]
    intro n
    cases eq_zero_or_pos r with
    | inl hr =>
      rw [hr]
      cases n <;> simp
    | inr hr =>
      right
      rw [← NNReal.coe_pos] at hr
      specialize h (n + 1)
      rw [le_div_iff₀ hr]
      rwa [pow_succ, ← mul_assoc] at h

@[simp]
theorem radius_unshift (p : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)) (z : F) :
    (p.unshift z).radius = p.radius := by
  rw [← radius_shift, unshift_shift]

protected theorem hasSum [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ EMetric.ball (0 : E) p.radius) : HasSum (fun n : ℕ => p n fun _ => x) (p.sum x) :=
  (p.summable hx).hasSum

theorem radius_le_radius_continuousLinearMap_comp (p : FormalMultilinearSeries 𝕜 E F)
    (f : F →L[𝕜] G) : p.radius ≤ (f.compFormalMultilinearSeries p).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  apply le_radius_of_isBigO
  apply (IsBigO.trans_isLittleO _ (p.isLittleO_one_of_lt_radius hr)).isBigO
  refine IsBigO.mul (@IsBigOWith.isBigO _ _ _ _ _ ‖f‖ _ _ _ ?_) (isBigO_refl _ _)
  refine IsBigOWith.of_bound (Eventually.of_forall fun n => ?_)
  simpa only [norm_norm] using f.norm_compContinuousMultilinearMap_le (p n)

end FormalMultilinearSeries

/-! ### Expanding a function as a power series -/


section

variable {f g : E → F} {p pf : FormalMultilinearSeries 𝕜 E F} {s t : Set E} {x : E} {r r' : ℝ≥0∞}

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series on the ball of radius `r > 0` around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `‖y‖ < r`.
-/
structure HasFPowerSeriesOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (r : ℝ≥0∞) :
    Prop where
  r_le : r ≤ p.radius
  r_pos : 0 < r
  hasSum :
    ∀ {y}, y ∈ EMetric.ball (0 : E) r → HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y))

/-- Analogue of `HasFPowerSeriesOnBall` where convergence is required only on a set `s`. We also
require convergence at `x` as the behavior of this notion is very bad otherwise. -/
structure HasFPowerSeriesWithinOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E)
    (x : E) (r : ℝ≥0∞) : Prop where
  /-- `p` converges on `ball 0 r` -/
  r_le : r ≤ p.radius
  /-- The radius of convergence is positive -/
  r_pos : 0 < r
  /-- `p converges to f` within `s` -/
  hasSum : ∀ {y}, x + y ∈ insert x s → y ∈ EMetric.ball (0 : E) r →
    HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y))

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a neighborhood of `0`. -/
def HasFPowerSeriesAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) :=
  ∃ r, HasFPowerSeriesOnBall f p x r

/-- Analogue of `HasFPowerSeriesAt` where convergence is required only on a set `s`. -/
def HasFPowerSeriesWithinAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E) (x : E) :=
  ∃ r, HasFPowerSeriesWithinOnBall f p s x r

-- Teach the `bound` tactic that power series have positive radius
attribute [bound_forward] HasFPowerSeriesOnBall.r_pos HasFPowerSeriesWithinOnBall.r_pos

variable (𝕜)

/-- Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a convergent power
series expansion around `x`. -/
@[fun_prop]
def AnalyticAt (f : E → F) (x : E) :=
  ∃ p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesAt f p x

/-- `f` is analytic within `s` at `x` if it has a power series at `x` that converges on `𝓝[s] x` -/
def AnalyticWithinAt (f : E → F) (s : Set E) (x : E) : Prop :=
  ∃ p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesWithinAt f p s x

/-- Given a function `f : E → F`, we say that `f` is analytic on a set `s` if it is analytic around
every point of `s`. -/
def AnalyticOnNhd (f : E → F) (s : Set E) :=
  ∀ x, x ∈ s → AnalyticAt 𝕜 f x

/-- `f` is analytic within `s` if it is analytic within `s` at each point of `s`.  Note that
this is weaker than `AnalyticOnNhd 𝕜 f s`, as `f` is allowed to be arbitrary outside `s`. -/
def AnalyticOn (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, AnalyticWithinAt 𝕜 f s x

/-!
### `HasFPowerSeriesOnBall` and `HasFPowerSeriesWithinOnBall`
-/

variable {𝕜}

theorem HasFPowerSeriesOnBall.hasFPowerSeriesAt (hf : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesAt f p x :=
  ⟨r, hf⟩

theorem HasFPowerSeriesAt.analyticAt (hf : HasFPowerSeriesAt f p x) : AnalyticAt 𝕜 f x :=
  ⟨p, hf⟩

theorem HasFPowerSeriesOnBall.analyticAt (hf : HasFPowerSeriesOnBall f p x r) : AnalyticAt 𝕜 f x :=
  hf.hasFPowerSeriesAt.analyticAt

theorem HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt
    (hf : HasFPowerSeriesWithinOnBall f p s x r) : HasFPowerSeriesWithinAt f p s x :=
  ⟨r, hf⟩

theorem HasFPowerSeriesWithinAt.analyticWithinAt (hf : HasFPowerSeriesWithinAt f p s x) :
    AnalyticWithinAt 𝕜 f s x := ⟨p, hf⟩

theorem HasFPowerSeriesWithinOnBall.analyticWithinAt (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    AnalyticWithinAt 𝕜 f s x :=
  hf.hasFPowerSeriesWithinAt.analyticWithinAt

/-- If a function `f` has a power series `p` around `x`, then the function `z ↦ f (z - y)` has the
same power series around `x + y`. -/
theorem HasFPowerSeriesOnBall.comp_sub (hf : HasFPowerSeriesOnBall f p x r) (y : E) :
    HasFPowerSeriesOnBall (fun z => f (z - y)) p (x + y) r :=
  { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {z} hz => by
      convert hf.hasSum hz using 2
      abel }

theorem HasFPowerSeriesWithinOnBall.comp_sub (hf : HasFPowerSeriesWithinOnBall f p s x r) (y : E) :
    HasFPowerSeriesWithinOnBall (fun z ↦ f (z - y)) p (s + {y}) (x + y) r where
  r_le := hf.r_le
  r_pos := hf.r_pos
  hasSum {z} hz1 hz2 := by
    have : x + z ∈ insert x s := by
      simp only [add_singleton, image_add_right, mem_insert_iff, add_eq_left, mem_preimage] at hz1 ⊢
      abel_nf at hz1
      assumption
    convert hf.hasSum this hz2 using 2
    abel

theorem HasFPowerSeriesAt.comp_sub (hf : HasFPowerSeriesAt f p x) (y : E) :
    HasFPowerSeriesAt (fun z ↦ f (z - y)) p (x + y) := by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩

theorem HasFPowerSeriesWithinAt.comp_sub (hf : HasFPowerSeriesWithinAt f p s x) (y : E) :
    HasFPowerSeriesWithinAt (fun z ↦ f (z - y)) p (s + {y}) (x + y) := by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩

theorem AnalyticAt.comp_sub (hf : AnalyticAt 𝕜 f x) (y : E) :
    AnalyticAt 𝕜 (fun z ↦ f (z - y)) (x + y) := by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩

theorem AnalyticOnNhd.comp_sub (hf : AnalyticOnNhd 𝕜 f s) (y : E) :
    AnalyticOnNhd 𝕜 (fun z ↦ f (z - y)) (s + {y}) := by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx using 1; abel)).comp_sub

theorem AnalyticWithinAt.comp_sub (hf : AnalyticWithinAt 𝕜 f s x) (y : E) :
    AnalyticWithinAt 𝕜 (fun z ↦ f (z - y)) (s + {y}) (x + y) := by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩

theorem AnalyticOn.comp_sub (hf : AnalyticOn 𝕜 f s) (y : E) :
    AnalyticOn 𝕜 (fun z ↦ f (z - y)) (s + {y}) := by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx using 1; abel)).comp_sub

theorem HasFPowerSeriesWithinOnBall.hasSum_sub (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
    (hy : y ∈ (insert x s) ∩ EMetric.ball x r) :
    HasSum (fun n : ℕ => p n fun _ => y - x) (f y) := by
  have : y - x ∈ EMetric.ball 0 r := by simpa [edist_eq_enorm_sub] using hy.2
  simpa only [add_sub_cancel] using hf.hasSum (by simpa only [add_sub_cancel] using hy.1) this

theorem HasFPowerSeriesOnBall.hasSum_sub (hf : HasFPowerSeriesOnBall f p x r) {y : E}
    (hy : y ∈ EMetric.ball x r) : HasSum (fun n : ℕ => p n fun _ => y - x) (f y) := by
  have : y - x ∈ EMetric.ball 0 r := by simpa [edist_eq_enorm_sub] using hy
  simpa only [add_sub_cancel] using hf.hasSum this

theorem HasFPowerSeriesOnBall.radius_pos (hf : HasFPowerSeriesOnBall f p x r) : 0 < p.radius :=
  lt_of_lt_of_le hf.r_pos hf.r_le

theorem HasFPowerSeriesWithinOnBall.radius_pos (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    0 < p.radius :=
  lt_of_lt_of_le hf.r_pos hf.r_le

theorem HasFPowerSeriesAt.radius_pos (hf : HasFPowerSeriesAt f p x) : 0 < p.radius :=
  let ⟨_, hr⟩ := hf
  hr.radius_pos

theorem HasFPowerSeriesWithinOnBall.of_le
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (r'_pos : 0 < r') (hr : r' ≤ r) :
    HasFPowerSeriesWithinOnBall f p s x r' :=
  ⟨le_trans hr hf.1, r'_pos, fun hy h'y => hf.hasSum hy (EMetric.ball_subset_ball hr h'y)⟩

theorem HasFPowerSeriesOnBall.mono (hf : HasFPowerSeriesOnBall f p x r) (r'_pos : 0 < r')
    (hr : r' ≤ r) : HasFPowerSeriesOnBall f p x r' :=
  ⟨le_trans hr hf.1, r'_pos, fun hy => hf.hasSum (EMetric.ball_subset_ball hr hy)⟩

lemma HasFPowerSeriesWithinOnBall.congr {f g : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {s : Set E} {x : E} {r : ℝ≥0∞} (h : HasFPowerSeriesWithinOnBall f p s x r)
    (h' : EqOn g f (s ∩ EMetric.ball x r)) (h'' : g x = f x) :
    HasFPowerSeriesWithinOnBall g p s x r := by
  refine ⟨h.r_le, h.r_pos, ?_⟩
  intro y hy h'y
  convert h.hasSum hy h'y using 1
  simp only [mem_insert_iff, add_eq_left] at hy
  rcases hy with rfl | hy
  · simpa using h''
  · apply h'
    refine ⟨hy, ?_⟩
    simpa [edist_eq_enorm_sub] using h'y

/-- Variant of `HasFPowerSeriesWithinOnBall.congr` in which one requests equality on `insert x s`
instead of separating `x` and `s`. -/
lemma HasFPowerSeriesWithinOnBall.congr' {f g : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {s : Set E} {x : E} {r : ℝ≥0∞} (h : HasFPowerSeriesWithinOnBall f p s x r)
    (h' : EqOn g f (insert x s ∩ EMetric.ball x r)) :
    HasFPowerSeriesWithinOnBall g p s x r := by
  refine ⟨h.r_le, h.r_pos, fun {y} hy h'y ↦ ?_⟩
  convert h.hasSum hy h'y using 1
  exact h' ⟨hy, by simpa [edist_eq_enorm_sub] using h'y⟩

lemma HasFPowerSeriesWithinAt.congr {f g : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E}
    {x : E} (h : HasFPowerSeriesWithinAt f p s x) (h' : g =ᶠ[𝓝[s] x] f) (h'' : g x = f x) :
    HasFPowerSeriesWithinAt g p s x := by
  rcases h with ⟨r, hr⟩
  obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, EMetric.ball x ε ∩ s ⊆ {y | g y = f y} :=
    EMetric.mem_nhdsWithin_iff.1 h'
  let r' := min r ε
  refine ⟨r', ?_⟩
  have := hr.of_le (r' := r') (by simp [r', εpos, hr.r_pos]) (min_le_left _ _)
  apply this.congr _ h''
  intro z hz
  exact hε ⟨EMetric.ball_subset_ball (min_le_right _ _) hz.2, hz.1⟩

theorem HasFPowerSeriesOnBall.congr (hf : HasFPowerSeriesOnBall f p x r)
    (hg : EqOn f g (EMetric.ball x r)) : HasFPowerSeriesOnBall g p x r :=
  { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {y} hy => by
      convert hf.hasSum hy using 1
      apply hg.symm
      simpa [edist_eq_enorm_sub] using hy }

theorem HasFPowerSeriesAt.congr (hf : HasFPowerSeriesAt f p x) (hg : f =ᶠ[𝓝 x] g) :
    HasFPowerSeriesAt g p x := by
  rcases hf with ⟨r₁, h₁⟩
  rcases EMetric.mem_nhds_iff.mp hg with ⟨r₂, h₂pos, h₂⟩
  exact ⟨min r₁ r₂,
    (h₁.mono (lt_min h₁.r_pos h₂pos) inf_le_left).congr
      fun y hy => h₂ (EMetric.ball_subset_ball inf_le_right hy)⟩

theorem HasFPowerSeriesWithinOnBall.unique (hf : HasFPowerSeriesWithinOnBall f p s x r)
    (hg : HasFPowerSeriesWithinOnBall g p s x r) :
    (insert x s ∩ EMetric.ball x r).EqOn f g := fun _ hy ↦
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)

theorem HasFPowerSeriesOnBall.unique (hf : HasFPowerSeriesOnBall f p x r)
    (hg : HasFPowerSeriesOnBall g p x r) : (EMetric.ball x r).EqOn f g := fun _ hy ↦
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)

protected theorem HasFPowerSeriesWithinAt.eventually (hf : HasFPowerSeriesWithinAt f p s x) :
    ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, HasFPowerSeriesWithinOnBall f p s x r :=
  let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.of_le hr'.1 hr'.2.le

protected theorem HasFPowerSeriesAt.eventually (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, HasFPowerSeriesOnBall f p x r :=
  let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.mono hr'.1 hr'.2.le

theorem HasFPowerSeriesOnBall.eventually_hasSum (hf : HasFPowerSeriesOnBall f p x r) :
    ∀ᶠ y in 𝓝 0, HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y)) := by
  filter_upwards [EMetric.ball_mem_nhds (0 : E) hf.r_pos] using fun _ => hf.hasSum

theorem HasFPowerSeriesAt.eventually_hasSum (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ y in 𝓝 0, HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y)) :=
  let ⟨_, hr⟩ := hf
  hr.eventually_hasSum

theorem HasFPowerSeriesOnBall.eventually_hasSum_sub (hf : HasFPowerSeriesOnBall f p x r) :
    ∀ᶠ y in 𝓝 x, HasSum (fun n : ℕ => p n fun _ : Fin n => y - x) (f y) := by
  filter_upwards [EMetric.ball_mem_nhds x hf.r_pos] with y using hf.hasSum_sub

theorem HasFPowerSeriesAt.eventually_hasSum_sub (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ y in 𝓝 x, HasSum (fun n : ℕ => p n fun _ : Fin n => y - x) (f y) :=
  let ⟨_, hr⟩ := hf
  hr.eventually_hasSum_sub

theorem HasFPowerSeriesOnBall.eventually_eq_zero
    (hf : HasFPowerSeriesOnBall f (0 : FormalMultilinearSeries 𝕜 E F) x r) :
    ∀ᶠ z in 𝓝 x, f z = 0 := by
  filter_upwards [hf.eventually_hasSum_sub] with z hz using hz.unique hasSum_zero

theorem HasFPowerSeriesAt.eventually_eq_zero
    (hf : HasFPowerSeriesAt f (0 : FormalMultilinearSeries 𝕜 E F) x) : ∀ᶠ z in 𝓝 x, f z = 0 :=
  let ⟨_, hr⟩ := hf
  hr.eventually_eq_zero

@[simp] lemma hasFPowerSeriesWithinOnBall_univ :
    HasFPowerSeriesWithinOnBall f p univ x r ↔ HasFPowerSeriesOnBall f p x r := by
  constructor
  · intro h
    refine ⟨h.r_le, h.r_pos, fun {y} m ↦ h.hasSum (by simp) m⟩
  · intro h
    exact ⟨h.r_le, h.r_pos, fun {y} _ m => h.hasSum m⟩

@[simp] lemma hasFPowerSeriesWithinAt_univ :
    HasFPowerSeriesWithinAt f p univ x ↔ HasFPowerSeriesAt f p x := by
  simp only [HasFPowerSeriesWithinAt, hasFPowerSeriesWithinOnBall_univ, HasFPowerSeriesAt]

lemma HasFPowerSeriesWithinOnBall.mono (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : t ⊆ s) :
    HasFPowerSeriesWithinOnBall f p t x r where
  r_le := hf.r_le
  r_pos := hf.r_pos
  hasSum hy h'y := hf.hasSum (insert_subset_insert h hy) h'y

lemma HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall (hf : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesWithinOnBall f p s x r := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.mono (subset_univ _)

lemma HasFPowerSeriesWithinAt.mono (hf : HasFPowerSeriesWithinAt f p s x) (h : t ⊆ s) :
    HasFPowerSeriesWithinAt f p t x := by
  obtain ⟨r, hp⟩ := hf
  exact ⟨r, hp.mono h⟩

lemma HasFPowerSeriesAt.hasFPowerSeriesWithinAt (hf : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesWithinAt f p s x := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  apply hf.mono (subset_univ _)

theorem HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin
    (h : HasFPowerSeriesWithinAt f p s x) (hst : s ∈ 𝓝[t] x) :
    HasFPowerSeriesWithinAt f p t x := by
  rcases h with ⟨r, hr⟩
  rcases EMetric.mem_nhdsWithin_iff.1 hst with ⟨r', r'_pos, hr'⟩
  refine ⟨min r r', ?_⟩
  have Z := hr.of_le (by simp [r'_pos, hr.r_pos]) (min_le_left r r')
  refine ⟨Z.r_le, Z.r_pos, fun {y} hy h'y ↦ ?_⟩
  apply Z.hasSum ?_ h'y
  simp only [mem_insert_iff, add_eq_left] at hy
  rcases hy with rfl | hy
  · simp
  apply mem_insert_of_mem _ (hr' ?_)
  simp only [EMetric.mem_ball, edist_eq_enorm_sub, sub_zero, lt_min_iff, mem_inter_iff,
    add_sub_cancel_left, hy, and_true] at h'y ⊢
  exact h'y.2

@[deprecated (since := "2024-10-31")]
alias HasFPowerSeriesWithinAt.mono_of_mem := HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin

@[simp] lemma hasFPowerSeriesWithinOnBall_insert_self :
    HasFPowerSeriesWithinOnBall f p (insert x s) x r ↔ HasFPowerSeriesWithinOnBall f p s x r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩  <;>
  exact ⟨h.r_le, h.r_pos, fun {y} ↦ by simpa only [insert_idem] using h.hasSum (y := y)⟩

@[simp] theorem hasFPowerSeriesWithinAt_insert {y : E} :
    HasFPowerSeriesWithinAt f p (insert y s) x ↔ HasFPowerSeriesWithinAt f p s x := by
  rcases eq_or_ne x y with rfl | hy
  · simp [HasFPowerSeriesWithinAt]
  · refine ⟨fun h ↦ h.mono (subset_insert _ _), fun h ↦ ?_⟩
    apply HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin h
    rw [nhdsWithin_insert_of_ne hy]
    exact self_mem_nhdsWithin

theorem HasFPowerSeriesWithinOnBall.coeff_zero (hf : HasFPowerSeriesWithinOnBall f pf s x r)
    (v : Fin 0 → E) : pf 0 v = f x := by
  have v_eq : v = fun i => 0 := Subsingleton.elim _ _
  have zero_mem : (0 : E) ∈ EMetric.ball (0 : E) r := by simp [hf.r_pos]
  have : ∀ i, i ≠ 0 → (pf i fun _ => 0) = 0 := by
    intro i hi
    have : 0 < i := pos_iff_ne_zero.2 hi
    exact ContinuousMultilinearMap.map_coord_zero _ (⟨0, this⟩ : Fin i) rfl
  have A := (hf.hasSum (by simp) zero_mem).unique (hasSum_single _ this)
  simpa [v_eq] using A.symm

theorem HasFPowerSeriesOnBall.coeff_zero (hf : HasFPowerSeriesOnBall f pf x r)
    (v : Fin 0 → E) : pf 0 v = f x := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.coeff_zero v

theorem HasFPowerSeriesWithinAt.coeff_zero (hf : HasFPowerSeriesWithinAt f pf s x) (v : Fin 0 → E) :
    pf 0 v = f x :=
  let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v

theorem HasFPowerSeriesAt.coeff_zero (hf : HasFPowerSeriesAt f pf x) (v : Fin 0 → E) :
    pf 0 v = f x :=
  let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v

/-!
### Analytic functions
-/

@[simp] theorem analyticOn_empty : AnalyticOn 𝕜 f ∅ := by intro; simp

@[simp] theorem analyticOnNhd_empty : AnalyticOnNhd 𝕜 f ∅ := by intro; simp

@[simp] lemma analyticWithinAt_univ :
    AnalyticWithinAt 𝕜 f univ x ↔ AnalyticAt 𝕜 f x := by
  simp [AnalyticWithinAt, AnalyticAt]

@[simp] lemma analyticOn_univ {f : E → F} :
    AnalyticOn 𝕜 f univ ↔ AnalyticOnNhd 𝕜 f univ := by
  simp only [AnalyticOn, analyticWithinAt_univ, AnalyticOnNhd]

lemma AnalyticWithinAt.mono (hf : AnalyticWithinAt 𝕜 f s x) (h : t ⊆ s) :
    AnalyticWithinAt 𝕜 f t x := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp.mono h⟩

lemma AnalyticAt.analyticWithinAt (hf : AnalyticAt 𝕜 f x) : AnalyticWithinAt 𝕜 f s x := by
  rw [← analyticWithinAt_univ] at hf
  apply hf.mono (subset_univ _)

lemma AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOn 𝕜 f s :=
  fun x hx ↦ (hf x hx).analyticWithinAt

lemma AnalyticWithinAt.congr_of_eventuallyEq {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : g =ᶠ[𝓝[s] x] f) (hx : g x = f x) :
    AnalyticWithinAt 𝕜 g s x := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p, hp.congr hs hx⟩

lemma AnalyticWithinAt.congr_of_eventuallyEq_insert {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : g =ᶠ[𝓝[insert x s] x] f) :
    AnalyticWithinAt 𝕜 g s x := by
  apply hf.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) hs)
  apply mem_of_mem_nhdsWithin (mem_insert x s) hs

lemma AnalyticWithinAt.congr {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : EqOn g f s) (hx : g x = f x) :
    AnalyticWithinAt 𝕜 g s x :=
  hf.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx

lemma AnalyticOn.congr {f g : E → F} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hs : EqOn g f s) :
    AnalyticOn 𝕜 g s :=
  fun x m ↦ (hf x m).congr hs (hs m)

theorem AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 g x :=
  let ⟨_, hpf⟩ := hf
  (hpf.congr hg).analyticAt

theorem analyticAt_congr (h : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 f x ↔ AnalyticAt 𝕜 g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

theorem AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd 𝕜 f t) (hst : s ⊆ t) :
    AnalyticOnNhd 𝕜 f s :=
  fun z hz => hf z (hst hz)

theorem AnalyticOnNhd.congr' (hf : AnalyticOnNhd 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g) :
    AnalyticOnNhd 𝕜 g s :=
  fun z hz => (hf z hz).congr (mem_nhdsSet_iff_forall.mp hg z hz)

theorem analyticOnNhd_congr' (h : f =ᶠ[𝓝ˢ s] g) : AnalyticOnNhd 𝕜 f s ↔ AnalyticOnNhd 𝕜 g s :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr' h.symm⟩

theorem AnalyticOnNhd.congr (hs : IsOpen s) (hf : AnalyticOnNhd 𝕜 f s) (hg : s.EqOn f g) :
    AnalyticOnNhd 𝕜 g s :=
  hf.congr' <| mem_nhdsSet_iff_forall.mpr
    (fun _ hz => eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hz, hg⟩)

theorem analyticOnNhd_congr (hs : IsOpen s) (h : s.EqOn f g) : AnalyticOnNhd 𝕜 f s ↔
    AnalyticOnNhd 𝕜 g s := ⟨fun hf => hf.congr hs h, fun hg => hg.congr hs h.symm⟩

theorem AnalyticWithinAt.mono_of_mem_nhdsWithin
    (h : AnalyticWithinAt 𝕜 f s x) (hst : s ∈ 𝓝[t] x) : AnalyticWithinAt 𝕜 f t x := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.mono_of_mem_nhdsWithin hst⟩

@[deprecated (since := "2024-10-31")]
alias AnalyticWithinAt.mono_of_mem := AnalyticWithinAt.mono_of_mem_nhdsWithin

lemma AnalyticOn.mono {f : E → F} {s t : Set E} (h : AnalyticOn 𝕜 f t)
    (hs : s ⊆ t) : AnalyticOn 𝕜 f s :=
  fun _ m ↦ (h _ (hs m)).mono hs

@[simp] theorem analyticWithinAt_insert {f : E → F} {s : Set E} {x y : E} :
    AnalyticWithinAt 𝕜 f (insert y s) x ↔ AnalyticWithinAt 𝕜 f s x := by
  simp [AnalyticWithinAt]

/-!
### Composition with linear maps
-/

/-- If a function `f` has a power series `p` on a ball within a set and `g` is linear,
then `g ∘ f` has the power series `g ∘ p` on the same ball. -/
theorem ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall (g : F →L[𝕜] G)
    (h : HasFPowerSeriesWithinOnBall f p s x r) :
    HasFPowerSeriesWithinOnBall (g ∘ f) (g.compFormalMultilinearSeries p) s x r where
  r_le := h.r_le.trans (p.radius_le_radius_continuousLinearMap_comp _)
  r_pos := h.r_pos
  hasSum hy h'y := by
    simpa only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] using
      g.hasSum (h.hasSum hy h'y)

/-- If a function `f` has a power series `p` on a ball and `g` is linear, then `g ∘ f` has the
power series `g ∘ p` on the same ball. -/
theorem ContinuousLinearMap.comp_hasFPowerSeriesOnBall (g : F →L[𝕜] G)
    (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (g ∘ f) (g.compFormalMultilinearSeries p) x r := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact g.comp_hasFPowerSeriesWithinOnBall h

/-- If a function `f` is analytic on a set `s` and `g` is linear, then `g ∘ f` is analytic
on `s`. -/
theorem ContinuousLinearMap.comp_analyticOn (g : F →L[𝕜] G) (h : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesWithinOnBall hp⟩

/-- If a function `f` is analytic on a set `s` and `g` is linear, then `g ∘ f` is analytic
on `s`. -/
theorem ContinuousLinearMap.comp_analyticOnNhd
    {s : Set E} (g : F →L[𝕜] G) (h : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesOnBall hp⟩

/-!
### Relation between analytic function and the partial sums of its power series
-/

theorem HasFPowerSeriesWithinOnBall.tendsto_partialSum
    (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E} (hy : y ∈ EMetric.ball (0 : E) r)
    (h'y : x + y ∈ insert x s) :
    Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) :=
  (hf.hasSum h'y hy).tendsto_sum_nat

theorem HasFPowerSeriesOnBall.tendsto_partialSum
    (hf : HasFPowerSeriesOnBall f p x r) {y : E} (hy : y ∈ EMetric.ball (0 : E) r) :
    Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) :=
  (hf.hasSum hy).tendsto_sum_nat

theorem HasFPowerSeriesAt.tendsto_partialSum
    (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ y in 𝓝 0, Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) := by
  rcases hf with ⟨r, hr⟩
  filter_upwards [EMetric.ball_mem_nhds (0 : E) hr.r_pos] with y hy
  exact hr.tendsto_partialSum hy

open Finset in
/-- If a function admits a power series expansion within a ball, then the partial sums
`p.partialSum n z` converge to `f (x + y)` as `n → ∞` and `z → y`. Note that `x + z` doesn't need
to belong to the set where the power series expansion holds. -/
theorem HasFPowerSeriesWithinOnBall.tendsto_partialSum_prod {y : E}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (hy : y ∈ EMetric.ball (0 : E) r)
    (h'y : x + y ∈ insert x s) :
    Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 z.2) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y))) := by
  have A : Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 y) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y))) := by
    apply (hf.tendsto_partialSum hy h'y).comp tendsto_fst
  suffices Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 z.2 - p.partialSum z.1 y)
    (atTop ×ˢ 𝓝 y) (𝓝 0) by simpa using A.add this
  apply Metric.tendsto_nhds.2 (fun ε εpos ↦ ?_)
  obtain ⟨r', yr', r'r⟩ : ∃ (r' : ℝ≥0), ‖y‖₊ < r' ∧ r' < r := by
    simp [edist_zero_eq_enorm] at hy
    simpa using ENNReal.lt_iff_exists_nnreal_btwn.1 hy
  have yr'_2 : ‖y‖ < r' := by simpa [← coe_nnnorm] using yr'
  have S : Summable fun n ↦ ‖p n‖ * ↑r' ^ n := p.summable_norm_mul_pow (r'r.trans_le hf.r_le)
  obtain ⟨k, hk⟩ : ∃ k, ∑' (n : ℕ), ‖p (n + k)‖ * ↑r' ^ (n + k) < ε / 4 := by
    have : Tendsto (fun k ↦ ∑' n, ‖p (n + k)‖ * ↑r' ^ (n + k)) atTop (𝓝 0) := by
      apply _root_.tendsto_sum_nat_add (f := fun n ↦ ‖p n‖ * ↑r' ^ n)
    exact ((tendsto_order.1 this).2 _ (by linarith)).exists
  have A : ∀ᶠ (z : ℕ × E) in atTop ×ˢ 𝓝 y,
      dist (p.partialSum k z.2) (p.partialSum k y) < ε / 4 := by
    have : ContinuousAt (fun z ↦ p.partialSum k z) y := (p.partialSum_continuous k).continuousAt
    exact tendsto_snd (Metric.tendsto_nhds.1 this.tendsto (ε / 4) (by linarith))
  have B : ∀ᶠ (z : ℕ × E) in atTop ×ˢ 𝓝 y, ‖z.2‖₊ < r' := by
    suffices ∀ᶠ (z : E) in 𝓝 y, ‖z‖₊ < r' from tendsto_snd this
    have : Metric.ball 0 r' ∈ 𝓝 y := Metric.isOpen_ball.mem_nhds (by simpa using yr'_2)
    filter_upwards [this] with a ha using by simpa [← coe_nnnorm] using ha
  have C : ∀ᶠ (z : ℕ × E) in atTop ×ˢ 𝓝 y, k ≤ z.1 := tendsto_fst (Ici_mem_atTop _)
  filter_upwards [A, B, C]
  rintro ⟨n, z⟩ hz h'z hkn
  simp only [dist_eq_norm, sub_zero] at hz ⊢
  have I (w : E) (hw : ‖w‖₊ < r') : ‖∑ i ∈ Ico k n, p i (fun _ ↦ w)‖ ≤ ε / 4 := calc
    ‖∑ i ∈ Ico k n, p i (fun _ ↦ w)‖
    _ = ‖∑ i ∈ range (n - k), p (i + k) (fun _ ↦ w)‖ := by
        rw [sum_Ico_eq_sum_range]
        congr with i
        rw [add_comm k]
    _ ≤ ∑ i ∈ range (n - k), ‖p (i + k) (fun _ ↦ w)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range (n - k), ‖p (i + k)‖ * ‖w‖ ^ (i + k) := by
        gcongr with i _hi; exact ((p (i + k)).le_opNorm _).trans_eq (by simp)
    _ ≤ ∑ i ∈ range (n - k), ‖p (i + k)‖ * ↑r' ^ (i + k) := by
        gcongr with i _hi; simpa [← coe_nnnorm] using hw.le
    _ ≤ ∑' i, ‖p (i + k)‖ * ↑r' ^ (i + k) := by
        apply Summable.sum_le_tsum _ (fun i _hi ↦ by positivity)
        apply ((_root_.summable_nat_add_iff k).2 S)
    _ ≤ ε / 4 := hk.le
  calc
  ‖p.partialSum n z - p.partialSum n y‖
  _ = ‖∑ i ∈ range n, p i (fun _ ↦ z) - ∑ i ∈ range n, p i (fun _ ↦ y)‖ := rfl
  _ = ‖(∑ i ∈ range k, p i (fun _ ↦ z) + ∑ i ∈ Ico k n, p i (fun _ ↦ z))
        - (∑ i ∈ range k, p i (fun _ ↦ y) + ∑ i ∈ Ico k n, p i (fun _ ↦ y))‖ := by
    simp [sum_range_add_sum_Ico _ hkn]
  _ = ‖(p.partialSum k z - p.partialSum k y) + (∑ i ∈ Ico k n, p i (fun _ ↦ z))
        + (- ∑ i ∈ Ico k n, p i (fun _ ↦ y))‖ := by
    congr 1
    simp only [FormalMultilinearSeries.partialSum]
    abel
  _ ≤ ‖p.partialSum k z - p.partialSum k y‖ + ‖∑ i ∈ Ico k n, p i (fun _ ↦ z)‖
      + ‖- ∑ i ∈ Ico k n, p i (fun _ ↦ y)‖ := norm_add₃_le
  _ ≤ ε / 4 + ε / 4 + ε / 4 := by
    gcongr
    · exact I _ h'z
    · simp only [norm_neg]; exact I _ yr'
  _ < ε := by linarith

/-- If a function admits a power series on a ball, then the partial sums
`p.partialSum n z` converges to `f (x + y)` as `n → ∞` and `z → y`. -/
theorem HasFPowerSeriesOnBall.tendsto_partialSum_prod {y : E}
    (hf : HasFPowerSeriesOnBall f p x r) (hy : y ∈ EMetric.ball (0 : E) r) :
    Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 z.2) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y))) :=
  (hf.hasFPowerSeriesWithinOnBall (s := univ)).tendsto_partialSum_prod hy (by simp)

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `‖y‖` and `n`. See also
`HasFPowerSeriesWithinOnBall.uniform_geometric_approx` for a weaker version. -/
theorem HasFPowerSeriesWithinOnBall.uniform_geometric_approx' {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n, x + y ∈ insert x s →
      ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n := by
  obtain ⟨a, ha, C, hC, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n, ‖p n‖ * (r' : ℝ) ^ n ≤ C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (h.trans_le hf.r_le)
  refine ⟨a, ha, C / (1 - a), div_pos hC (sub_pos.2 ha.2), fun y hy n ys => ?_⟩
  have yr' : ‖y‖ < r' := by
    rw [ball_zero_eq] at hy
    exact hy
  have hr'0 : 0 < (r' : ℝ) := (norm_nonneg _).trans_lt yr'
  have : y ∈ EMetric.ball (0 : E) r := by
    refine mem_emetric_ball_zero_iff.2 (lt_trans ?_ h)
    simpa [enorm] using yr'
  rw [norm_sub_rev, ← mul_div_right_comm]
  have ya : a * (‖y‖ / ↑r') ≤ a :=
    mul_le_of_le_one_right ha.1.le (div_le_one_of_le₀ yr'.le r'.coe_nonneg)
  suffices ‖p.partialSum n y - f (x + y)‖ ≤ C * (a * (‖y‖ / r')) ^ n / (1 - a * (‖y‖ / r')) by
    refine this.trans ?_
    have : 0 < a := ha.1
    gcongr
    apply_rules [sub_pos.2, ha.2]
  apply norm_sub_le_of_geometric_bound_of_hasSum (ya.trans_lt ha.2) _ (hf.hasSum ys this)
  intro n
  calc
    ‖(p n) fun _ : Fin n => y‖
    _ ≤ ‖p n‖ * ∏ _i : Fin n, ‖y‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖p n‖ * (r' : ℝ) ^ n * (‖y‖ / r') ^ n := by field_simp [mul_right_comm]
    _ ≤ C * a ^ n * (‖y‖ / r') ^ n := by gcongr ?_ * _; apply hp
    _ ≤ C * (a * (‖y‖ / r')) ^ n := by rw [mul_pow, mul_assoc]

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `‖y‖` and `n`. See also
`HasFPowerSeriesOnBall.uniform_geometric_approx` for a weaker version. -/
theorem HasFPowerSeriesOnBall.uniform_geometric_approx' {r' : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
      ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.uniform_geometric_approx' h

/-- If a function admits a power series expansion within a set in a ball, then it is exponentially
close to the partial sums of this power series on strict subdisks of the disk of convergence. -/
theorem HasFPowerSeriesWithinOnBall.uniform_geometric_approx {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n, x + y ∈ insert x s →
      ‖f (x + y) - p.partialSum n y‖ ≤ C * a ^ n := by
  obtain ⟨a, ha, C, hC, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
      x + y ∈ insert x s → ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n :=
    hf.uniform_geometric_approx' h
  refine ⟨a, ha, C, hC, fun y hy n ys => (hp y hy n ys).trans ?_⟩
  have yr' : ‖y‖ < r' := by rwa [ball_zero_eq] at hy
  have := ha.1.le -- needed to discharge a side goal on the next line
  gcongr
  exact mul_le_of_le_one_right ha.1.le (div_le_one_of_le₀ yr'.le r'.coe_nonneg)

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence. -/
theorem HasFPowerSeriesOnBall.uniform_geometric_approx {r' : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
      ‖f (x + y) - p.partialSum n y‖ ≤ C * a ^ n := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.uniform_geometric_approx h

/-- Taylor formula for an analytic function within a set, `IsBigO` version. -/
theorem HasFPowerSeriesWithinAt.isBigO_sub_partialSum_pow
    (hf : HasFPowerSeriesWithinAt f p s x) (n : ℕ) :
    (fun y : E => f (x + y) - p.partialSum n y)
      =O[𝓝[(x + ·)⁻¹' insert x s] 0] fun y => ‖y‖ ^ n := by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  obtain ⟨a, -, C, -, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
      x + y ∈ insert x s → ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n :=
    hf.uniform_geometric_approx' h
  refine isBigO_iff.2 ⟨C * (a / r') ^ n, ?_⟩
  replace r'0 : 0 < (r' : ℝ) := mod_cast r'0
  filter_upwards [inter_mem_nhdsWithin _ (Metric.ball_mem_nhds (0 : E) r'0)] with y hy
  simpa [mul_pow, mul_div_assoc, mul_assoc, div_mul_eq_mul_div, div_pow]
    using hp y hy.2 n (by simpa using hy.1)

/-- Taylor formula for an analytic function, `IsBigO` version. -/
theorem HasFPowerSeriesAt.isBigO_sub_partialSum_pow
    (hf : HasFPowerSeriesAt f p x) (n : ℕ) :
    (fun y : E => f (x + y) - p.partialSum n y) =O[𝓝 0] fun y => ‖y‖ ^ n := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_sub_partialSum_pow n

/-- If `f` has formal power series `∑ n, pₙ` in a set, within a ball of radius `r`, then
for `y, z` in any smaller ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is
bounded above by `C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. This lemma formulates this property
using `IsBigO` and `Filter.principal` on `E × E`. -/
theorem HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (hr : r' < r) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓟 (EMetric.ball (x, x) r' ∩ ((insert x s) ×ˢ (insert x s)))]
      fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  lift r' to ℝ≥0 using ne_top_of_lt hr
  rcases (zero_le r').eq_or_lt with (rfl | hr'0)
  · simp only [ENNReal.coe_zero, EMetric.ball_zero, empty_inter, principal_empty, isBigO_bot]
  obtain ⟨a, ha, C, hC : 0 < C, hp⟩ :
      ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n : ℕ, ‖p n‖ * (r' : ℝ) ^ n ≤ C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (hr.trans_le hf.r_le)
  simp only [← le_div_iff₀ (pow_pos (NNReal.coe_pos.2 hr'0) _)] at hp
  set L : E × E → ℝ := fun y =>
    C * (a / r') ^ 2 * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * (a / (1 - a) ^ 2 + 2 / (1 - a))
  have hL : ∀ y ∈ EMetric.ball (x, x) r' ∩ ((insert x s) ×ˢ (insert x s)),
      ‖f y.1 - f y.2 - p 1 fun _ => y.1 - y.2‖ ≤ L y := by
    intro y ⟨hy', ys⟩
    have hy : y ∈ EMetric.ball x r ×ˢ EMetric.ball x r := by
      rw [EMetric.ball_prod_same]
      exact EMetric.ball_subset_ball hr.le hy'
    set A : ℕ → F := fun n => (p n fun _ => y.1 - x) - p n fun _ => y.2 - x
    have hA : HasSum (fun n => A (n + 2)) (f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) := by
      convert (hasSum_nat_add_iff' 2).2
        ((hf.hasSum_sub ⟨ys.1, hy.1⟩).sub (hf.hasSum_sub ⟨ys.2, hy.2⟩)) using 1
      rw [Finset.sum_range_succ, Finset.sum_range_one, hf.coeff_zero, hf.coeff_zero, sub_self,
        zero_add, ← Subsingleton.pi_single_eq (0 : Fin 1) (y.1 - x), Pi.single,
        ← Subsingleton.pi_single_eq (0 : Fin 1) (y.2 - x), Pi.single, ← (p 1).map_update_sub,
        ← Pi.single, Subsingleton.pi_single_eq, sub_sub_sub_cancel_right]
    rw [EMetric.mem_ball, edist_eq_enorm_sub, enorm_lt_coe] at hy'
    set B : ℕ → ℝ := fun n => C * (a / r') ^ 2 * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * ((n + 2) * a ^ n)
    have hAB : ∀ n, ‖A (n + 2)‖ ≤ B n := fun n =>
      calc
        ‖A (n + 2)‖ ≤ ‖p (n + 2)‖ * ↑(n + 2) * ‖y - (x, x)‖ ^ (n + 1) * ‖y.1 - y.2‖ := by
          simpa only [Fintype.card_fin, pi_norm_const, Prod.norm_def, Pi.sub_def,
            Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right] using
            (p <| n + 2).norm_image_sub_le (fun _ => y.1 - x) fun _ => y.2 - x
        _ = ‖p (n + 2)‖ * ‖y - (x, x)‖ ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) := by
          rw [pow_succ ‖y - (x, x)‖]
          ring
        _ ≤ C * a ^ (n + 2) / r' ^ (n + 2)
            * r' ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) := by
          have : 0 < a := ha.1
          gcongr
          · apply hp
          · apply hy'.le
        _ = B n := by
          field_simp [B, pow_succ]
          simp only [mul_assoc, mul_comm, mul_left_comm]
    have hBL : HasSum B (L y) := by
      apply HasSum.mul_left
      simp only [add_mul]
      have : ‖a‖ < 1 := by simp only [Real.norm_eq_abs, abs_of_pos ha.1, ha.2]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact (hasSum_coe_mul_geometric_of_norm_lt_one this).add
          ((hasSum_geometric_of_norm_lt_one this).mul_left 2)
    exact hA.norm_le_of_bounded hBL hAB
  suffices L =O[𝓟 (EMetric.ball (x, x) r' ∩ ((insert x s) ×ˢ (insert x s)))]
      fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ from
    .trans (.of_norm_eventuallyLE (eventually_principal.2 hL)) this
  simp_rw [L, mul_right_comm _ (_ * _)]
  exact (isBigO_refl _ _).const_mul_left _

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is bounded above by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. This lemma formulates this property using `IsBigO` and
`Filter.principal` on `E × E`. -/
theorem HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal
    (hf : HasFPowerSeriesOnBall f p x r) (hr : r' < r) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓟 (EMetric.ball (x, x) r')] fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.isBigO_image_sub_image_sub_deriv_principal hr

/-- If `f` has formal power series `∑ n, pₙ` within a set, on a ball of radius `r`, then for `y, z`
in any smaller ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is bounded above
by `C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. -/
theorem HasFPowerSeriesWithinOnBall.image_sub_sub_deriv_le
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (hr : r' < r) :
    ∃ C, ∀ᵉ (y ∈ insert x s ∩ EMetric.ball x r') (z ∈ insert x s ∩ EMetric.ball x r'),
      ‖f y - f z - p 1 fun _ => y - z‖ ≤ C * max ‖y - x‖ ‖z - x‖ * ‖y - z‖ := by
  have := hf.isBigO_image_sub_image_sub_deriv_principal hr
  simp only [isBigO_principal, mem_inter_iff, EMetric.mem_ball, Prod.edist_eq, max_lt_iff, mem_prod,
    norm_mul, Real.norm_eq_abs, abs_norm, and_imp, Prod.forall, mul_assoc] at this ⊢
  rcases this with ⟨C, hC⟩
  exact ⟨C, fun y ys hy z zs hz ↦ hC y z hy hz ys zs⟩

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is bounded above by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. -/
theorem HasFPowerSeriesOnBall.image_sub_sub_deriv_le
    (hf : HasFPowerSeriesOnBall f p x r) (hr : r' < r) :
    ∃ C, ∀ᵉ (y ∈ EMetric.ball x r') (z ∈ EMetric.ball x r'),
      ‖f y - f z - p 1 fun _ => y - z‖ ≤ C * max ‖y - x‖ ‖z - x‖ * ‖y - z‖ := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa only [mem_univ, insert_eq_of_mem, univ_inter] using hf.image_sub_sub_deriv_le hr

/-- If `f` has formal power series `∑ n, pₙ` at `x` within a set `s`, then
`f y - f z - p 1 (fun _ ↦ y - z) = O(‖(y, z) - (x, x)‖ * ‖y - z‖)` as `(y, z) → (x, x)`
within `s × s`. -/
theorem HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub
    (hf : HasFPowerSeriesWithinAt f p s x) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓝[(insert x s) ×ˢ (insert x s)] (x, x)] fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  refine (hf.isBigO_image_sub_image_sub_deriv_principal h).mono ?_
  rw [inter_comm]
  exact le_principal_iff.2 (inter_mem_nhdsWithin _ (EMetric.ball_mem_nhds _ r'0))

/-- If `f` has formal power series `∑ n, pₙ` at `x`, then
`f y - f z - p 1 (fun _ ↦ y - z) = O(‖(y, z) - (x, x)‖ * ‖y - z‖)` as `(y, z) → (x, x)`.
In particular, `f` is strictly differentiable at `x`. -/
theorem HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub (hf : HasFPowerSeriesAt f p x) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) =O[𝓝 (x, x)] fun y =>
      ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_image_sub_norm_mul_norm_sub

/-- If a function admits a power series expansion within a set at `x`, then it is the uniform limit
of the partial sums of this power series on strict subdisks of the disk of convergence, i.e.,
`f (x + y)` is the uniform limit of `p.partialSum n y` there. -/
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      ((x + ·)⁻¹' (insert x s) ∩ Metric.ball (0 : E) r') := by
  obtain ⟨a, ha, C, -, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
    x + y ∈ insert x s → ‖f (x + y) - p.partialSum n y‖ ≤ C * a ^ n := hf.uniform_geometric_approx h
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have L : Tendsto (fun n => (C : ℝ) * a ^ n) atTop (𝓝 ((C : ℝ) * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one ha.1.le ha.2)
  rw [mul_zero] at L
  refine (L.eventually (gt_mem_nhds εpos)).mono fun n hn y hy => ?_
  rw [dist_eq_norm]
  exact (hp y hy.2 n hy.1).trans_lt hn

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f (x + y)`
is the uniform limit of `p.partialSum n y` there. -/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn {r' : ℝ≥0} (hf : HasFPowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      (Metric.ball (0 : E) r') := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn h

/-- If a function admits a power series expansion within a set at `x`, then it is the locally
uniform limit of the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partialSum n y` there. -/
theorem HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      ((x + ·)⁻¹' (insert x s) ∩ EMetric.ball (0 : E) r) := by
  intro u hu y hy
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hy.2 with ⟨r', yr', hr'⟩
  have : EMetric.ball (0 : E) r' ∈ 𝓝 y := IsOpen.mem_nhds EMetric.isOpen_ball yr'
  refine ⟨(x + ·)⁻¹' (insert x s) ∩ EMetric.ball (0 : E) r', ?_, ?_⟩
  · rw [nhdsWithin_inter_of_mem']
    · exact inter_mem_nhdsWithin _ this
    · apply mem_nhdsWithin_of_mem_nhds
      apply Filter.mem_of_superset this (EMetric.ball_subset_ball hr'.le)
  · simpa [Metric.emetric_ball_nnreal] using hf.tendstoUniformlyOn hr' u hu

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partialSum n y` there. -/
theorem HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn (hf : HasFPowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      (EMetric.ball (0 : E) r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn

/-- If a function admits a power series expansion within a set at `x`, then it is the uniform limit
of the partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partialSum n (y - x)` there. -/
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn' {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop
      (insert x s ∩ Metric.ball (x : E) r') := by
  convert (hf.tendstoUniformlyOn h).comp fun y => y - x using 1
  · simp [Function.comp_def]
  · ext z
    simp [dist_eq_norm]

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partialSum n (y - x)` there. -/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn' {r' : ℝ≥0} (hf : HasFPowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop (Metric.ball (x : E) r') := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn' h

/-- If a function admits a power series expansion within a set at `x`, then it is the locally
uniform limit of the partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partialSum n (y - x)` there. -/
theorem HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn'
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop
      (insert x s ∩ EMetric.ball (x : E) r) := by
  have A : ContinuousOn (fun y : E => y - x) (insert x s ∩ EMetric.ball (x : E) r) :=
    (continuous_id.sub continuous_const).continuousOn
  convert hf.tendstoLocallyUniformlyOn.comp (fun y : E => y - x) _ A using 1
  · ext z
    simp
  · intro z
    simp [edist_zero_eq_enorm, edist_eq_enorm_sub]

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partialSum n (y - x)` there. -/
theorem HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn' (hf : HasFPowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop
      (EMetric.ball (x : E) r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn'

/-- If a function admits a power series expansion within a set on a ball, then it is
continuous there. -/
protected theorem HasFPowerSeriesWithinOnBall.continuousOn
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    ContinuousOn f (insert x s ∩ EMetric.ball x r) :=
  hf.tendstoLocallyUniformlyOn'.continuousOn <|
    Eventually.of_forall fun n =>
      ((p.partialSum_continuous n).comp (continuous_id.sub continuous_const)).continuousOn

/-- If a function admits a power series expansion on a ball, then it is continuous there. -/
protected theorem HasFPowerSeriesOnBall.continuousOn (hf : HasFPowerSeriesOnBall f p x r) :
    ContinuousOn f (EMetric.ball x r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.continuousOn

protected theorem HasFPowerSeriesWithinOnBall.continuousWithinAt_insert
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    ContinuousWithinAt f (insert x s) x := by
  apply (hf.continuousOn.continuousWithinAt (x := x) (by simp [hf.r_pos])).mono_of_mem_nhdsWithin
  exact inter_mem_nhdsWithin _ (EMetric.ball_mem_nhds x hf.r_pos)

protected theorem HasFPowerSeriesWithinOnBall.continuousWithinAt
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    ContinuousWithinAt f s x :=
  hf.continuousWithinAt_insert.mono (subset_insert x s)

protected theorem HasFPowerSeriesWithinAt.continuousWithinAt_insert
    (hf : HasFPowerSeriesWithinAt f p s x) :
    ContinuousWithinAt f (insert x s) x := by
  rcases hf with ⟨r, hr⟩
  apply hr.continuousWithinAt_insert

protected theorem HasFPowerSeriesWithinAt.continuousWithinAt
    (hf : HasFPowerSeriesWithinAt f p s x) :
    ContinuousWithinAt f s x :=
  hf.continuousWithinAt_insert.mono (subset_insert x s)

protected theorem HasFPowerSeriesAt.continuousAt (hf : HasFPowerSeriesAt f p x) :
    ContinuousAt f x :=
  let ⟨_, hr⟩ := hf
  hr.continuousOn.continuousAt (EMetric.ball_mem_nhds x hr.r_pos)

protected theorem AnalyticWithinAt.continuousWithinAt_insert (hf : AnalyticWithinAt 𝕜 f s x) :
    ContinuousWithinAt f (insert x s) x :=
  let ⟨_, hp⟩ := hf
  hp.continuousWithinAt_insert

protected theorem AnalyticWithinAt.continuousWithinAt (hf : AnalyticWithinAt 𝕜 f s x) :
    ContinuousWithinAt f s x :=
  hf.continuousWithinAt_insert.mono (subset_insert x s)

@[fun_prop]
protected theorem AnalyticAt.continuousAt (hf : AnalyticAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨_, hp⟩ := hf
  hp.continuousAt

protected theorem AnalyticAt.eventually_continuousAt (hf : AnalyticAt 𝕜 f x) :
    ∀ᶠ y in 𝓝 x, ContinuousAt f y := by
  rcases hf with ⟨g, r, hg⟩
  have : EMetric.ball x r ∈ 𝓝 x := EMetric.ball_mem_nhds _ hg.r_pos
  filter_upwards [this] with y hy
  apply hg.continuousOn.continuousAt
  exact EMetric.isOpen_ball.mem_nhds hy

protected theorem AnalyticOnNhd.continuousOn {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) :
    ContinuousOn f s :=
  fun x hx => (hf x hx).continuousAt.continuousWithinAt

protected lemma AnalyticOn.continuousOn {f : E → F} {s : Set E} (h : AnalyticOn 𝕜 f s) :
    ContinuousOn f s :=
  fun x m ↦ (h x m).continuousWithinAt

/-- Analytic everywhere implies continuous -/
theorem AnalyticOnNhd.continuous {f : E → F} (fa : AnalyticOnNhd 𝕜 f univ) : Continuous f := by
  rw [continuous_iff_continuousOn_univ]; exact fa.continuousOn

/-- In a complete space, the sum of a converging power series `p` admits `p` as a power series.
This is not totally obvious as we need to check the convergence of the series. -/
protected theorem FormalMultilinearSeries.hasFPowerSeriesOnBall [CompleteSpace F]
    (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    HasFPowerSeriesOnBall p.sum p 0 p.radius :=
  { r_le := le_rfl
    r_pos := h
    hasSum := fun hy => by
      rw [zero_add]
      exact p.hasSum hy }

theorem HasFPowerSeriesWithinOnBall.sum (h : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
    (h'y : x + y ∈ insert x s) (hy : y ∈ EMetric.ball (0 : E) r) : f (x + y) = p.sum y :=
  (h.hasSum h'y hy).tsum_eq.symm

theorem HasFPowerSeriesOnBall.sum (h : HasFPowerSeriesOnBall f p x r) {y : E}
    (hy : y ∈ EMetric.ball (0 : E) r) : f (x + y) = p.sum y :=
  (h.hasSum hy).tsum_eq.symm

/-- The sum of a converging power series is continuous in its disk of convergence. -/
protected theorem FormalMultilinearSeries.continuousOn [CompleteSpace F] :
    ContinuousOn p.sum (EMetric.ball 0 p.radius) := by
  rcases (zero_le p.radius).eq_or_lt with h | h
  · simp [← h, continuousOn_empty]
  · exact (p.hasFPowerSeriesOnBall h).continuousOn

end

section

open FormalMultilinearSeries

variable {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E} {z₀ : 𝕜}

/-- A function `f : 𝕜 → E` has `p` as power series expansion at a point `z₀` iff it is the sum of
`p` in a neighborhood of `z₀`. This makes some proofs easier by hiding the fact that
`HasFPowerSeriesAt` depends on `p.radius`. -/
theorem hasFPowerSeriesAt_iff :
    HasFPowerSeriesAt f p z₀ ↔ ∀ᶠ z in 𝓝 0, HasSum (fun n => z ^ n • p.coeff n) (f (z₀ + z)) := by
  refine ⟨fun ⟨r, _, r_pos, h⟩ =>
    eventually_of_mem (EMetric.ball_mem_nhds 0 r_pos) fun _ => by simpa using h, ?_⟩
  simp only [Metric.eventually_nhds_iff]
  rintro ⟨r, r_pos, h⟩
  refine ⟨p.radius ⊓ r.toNNReal, by simp, ?_, ?_⟩
  · simp only [r_pos.lt, lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos, and_true]
    obtain ⟨z, z_pos, le_z⟩ := NormedField.exists_norm_lt 𝕜 r_pos.lt
    have : (‖z‖₊ : ENNReal) ≤ p.radius := by
      simp only [dist_zero_right] at h
      apply FormalMultilinearSeries.le_radius_of_tendsto
      convert tendsto_norm.comp (h le_z).summable.tendsto_atTop_zero
      simp [norm_smul, mul_comm]
    refine lt_of_lt_of_le ?_ this
    simp only [ENNReal.coe_pos]
    exact zero_lt_iff.mpr (nnnorm_ne_zero_iff.mpr (norm_pos_iff.mp z_pos))
  · simp only [EMetric.mem_ball, lt_inf_iff, edist_lt_coe, apply_eq_pow_smul_coeff, and_imp,
      dist_zero_right] at h ⊢
    refine fun {y} _ hyr => h ?_
    simpa [nndist_eq_nnnorm, Real.lt_toNNReal_iff_coe_lt] using hyr

theorem hasFPowerSeriesAt_iff' :
    HasFPowerSeriesAt f p z₀ ↔ ∀ᶠ z in 𝓝 z₀, HasSum (fun n => (z - z₀) ^ n • p.coeff n) (f z) := by
  rw [← map_add_left_nhds_zero, eventually_map, hasFPowerSeriesAt_iff]
  simp_rw [add_sub_cancel_left]

end
