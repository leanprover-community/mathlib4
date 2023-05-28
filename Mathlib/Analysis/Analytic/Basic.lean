/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.analytic.basic
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Equiv.Fin
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
* `p.le_radius_of_bound`, `p.le_radius_of_bound_nnreal`, `p.le_radius_of_is_O`: if `‖p n‖ * r ^ n`
  is bounded above, then `r ≤ p.radius`;
* `p.is_o_of_lt_radius`, `p.norm_mul_pow_le_mul_pow_of_lt_radius`, `p.is_o_one_of_lt_radius`,
  `p.norm_mul_pow_le_of_lt_radius`, `p.nnnorm_mul_pow_le_of_lt_radius`: if `r < p.radius`, then
  `‖p n‖ * r ^ n` tends to zero exponentially;
* `p.lt_radius_of_is_O`: if `r ≠ 0` and `‖p n‖ * r ^ n = O(a ^ n)` for some `-1 < a < 1`, then
  `r < p.radius`;
* `p.partial_sum n x`: the sum `∑_{i = 0}^{n-1} pᵢ xⁱ`.
* `p.sum x`: the sum `∑'_{i = 0}^{∞} pᵢ xⁱ`.

Additionally, let `f` be a function from `E` to `F`.

* `has_fpower_series_on_ball f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₙ yⁿ`.
* `has_fpower_series_at f p x`: on some ball of center `x` with positive radius, holds
  `has_fpower_series_on_ball f p x r`.
* `analytic_at 𝕜 f x`: there exists a power series `p` such that holds
  `has_fpower_series_at f p x`.
* `analytic_on 𝕜 f s`: the function `f` is analytic at every point of `s`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `has_fpower_series_on_ball.continuous_on` and `has_fpower_series_at.continuous_at` and
  `analytic_at.continuous_at`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `formal_multilinear_series.has_fpower_series_on_ball`.
* If a function admits a power series in a ball, then it is analytic at any point `y` of this ball,
  and the power series there can be expressed in terms of the initial power series `p` as
  `p.change_origin y`. See `has_fpower_series_on_ball.change_origin`. It follows in particular that
  the set of points at which a given function is analytic is open, see `is_open_analytic_at`.

## Implementation details

We only introduce the radius of convergence of a power series, as `p.radius`.
For a power series in finitely many dimensions, there is a finer (directional, coordinate-dependent)
notion, describing the polydisk of convergence. This notion is more specific, and not necessary to
build the general theory. We do not define it here.
-/


noncomputable section

variable {𝕜 E F G : Type _}

open Topology Classical BigOperators NNReal Filter ENNReal

open Set Filter Asymptotics

namespace FormalMultilinearSeries

variable [Ring 𝕜] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

variable [TopologicalSpace E] [TopologicalSpace F]

variable [TopologicalAddGroup E] [TopologicalAddGroup F]

variable [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F]

/-- Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A
priori, it only behaves well when `‖x‖ < p.radius`. -/
protected def sum (p : FormalMultilinearSeries 𝕜 E F) (x : E) : F :=
  ∑' n : ℕ, p n fun _ => x
#align formal_multilinear_series.sum FormalMultilinearSeries.sum

/-- Given a formal multilinear series `p` and a vector `x`, then `p.partial_sum n x` is the sum
`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/
def partialSum (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (x : E) : F :=
  ∑ k in Finset.range n, p k fun _ : Fin k => x
#align formal_multilinear_series.partial_sum FormalMultilinearSeries.partialSum

/-- The partial sums of a formal multilinear series are continuous. -/
theorem partialSum_continuous (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
    Continuous (p.partialSum n) := by
  unfold partialSum -- Porting note: added
  continuity
#align formal_multilinear_series.partial_sum_continuous FormalMultilinearSeries.partialSum_continuous

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
  ⨆ (r : ℝ≥0) (C : ℝ) (_hr : ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C), (r : ℝ≥0∞)
#align formal_multilinear_series.radius FormalMultilinearSeries.radius

/-- If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound (C : ℝ) {r : ℝ≥0} (h : ∀ n : ℕ, ‖p n‖ * (r : ℝ) ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ p.radius :=
  le_iSup_of_le r <| le_iSup_of_le C <| le_iSup (fun _ => (r : ℝ≥0∞)) h
#align formal_multilinear_series.le_radius_of_bound FormalMultilinearSeries.le_radius_of_bound

/-- If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound_nNReal (C : ℝ≥0) {r : ℝ≥0} (h : ∀ n : ℕ, ‖p n‖₊ * r ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ p.radius :=
  p.le_radius_of_bound C fun n => by exact_mod_cast h n
#align formal_multilinear_series.le_radius_of_bound_nnreal FormalMultilinearSeries.le_radius_of_bound_nNReal

/-- If `‖pₙ‖ rⁿ = O(1)`, as `n → ∞`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_isBigO (h : (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] fun _ => (1 : ℝ)) :
    ↑r ≤ p.radius :=
  Exists.elim (isBigO_one_nat_atTop_iff.1 h) fun C hC =>
    p.le_radius_of_bound C fun n => (le_abs_self _).trans (hC n)
set_option linter.uppercaseLean3 false in
#align formal_multilinear_series.le_radius_of_is_O FormalMultilinearSeries.le_radius_of_isBigO

theorem le_radius_of_eventually_le (C) (h : ∀ᶠ n in atTop, ‖p n‖ * (r : ℝ) ^ n ≤ C) : ↑r ≤ p.radius :=
  p.le_radius_of_isBigO <| IsBigO.of_bound C <| h.mono fun n hn => by simpa
#align formal_multilinear_series.le_radius_of_eventually_le FormalMultilinearSeries.le_radius_of_eventually_le

theorem le_radius_of_summable_nnnorm (h : Summable fun n => ‖p n‖₊ * r ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_bound_nNReal (∑' n, ‖p n‖₊ * r ^ n) fun _ => le_tsum' h _
#align formal_multilinear_series.le_radius_of_summable_nnnorm FormalMultilinearSeries.le_radius_of_summable_nnnorm

theorem le_radius_of_summable (h : Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_summable_nnnorm <| by
    simp only [← coe_nnnorm] at h
    exact_mod_cast h
#align formal_multilinear_series.le_radius_of_summable FormalMultilinearSeries.le_radius_of_summable

theorem radius_eq_top_of_forall_nnreal_isBigO
    (h : ∀ r : ℝ≥0, (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] fun _ => (1 : ℝ)) : p.radius = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_isBigO (h r)
set_option linter.uppercaseLean3 false in
#align formal_multilinear_series.radius_eq_top_of_forall_nnreal_is_O FormalMultilinearSeries.radius_eq_top_of_forall_nnreal_isBigO

theorem radius_eq_top_of_eventually_eq_zero (h : ∀ᶠ n in atTop, p n = 0) : p.radius = ∞ :=
  p.radius_eq_top_of_forall_nnreal_isBigO fun r =>
    (isBigO_zero _ _).congr' (h.mono fun n hn => by simp [hn]) EventuallyEq.rfl
#align formal_multilinear_series.radius_eq_top_of_eventually_eq_zero FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero

theorem radius_eq_top_of_forall_image_add_eq_zero (n : ℕ) (hn : ∀ m, p (m + n) = 0) :
    p.radius = ∞ :=
  p.radius_eq_top_of_eventually_eq_zero <|
    mem_atTop_sets.2 ⟨n, fun _ hk => tsub_add_cancel_of_le hk ▸ hn _⟩
#align formal_multilinear_series.radius_eq_top_of_forall_image_add_eq_zero FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero

@[simp]
theorem constFormalMultilinearSeries_radius {v : F} :
    (constFormalMultilinearSeries 𝕜 E v).radius = ⊤ :=
  (constFormalMultilinearSeries 𝕜 E v).radius_eq_top_of_forall_image_add_eq_zero 1
    (by simp [constFormalMultilinearSeries])
#align formal_multilinear_series.const_formal_multilinear_series_radius FormalMultilinearSeries.constFormalMultilinearSeries_radius

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
  refine' ⟨_, rt, C, Or.inr zero_lt_one, fun n => _⟩
  calc
    |‖p n‖ * (r : ℝ) ^ n| = ‖p n‖ * (t : ℝ) ^ n * (r / t : ℝ) ^ n := by
      field_simp [mul_right_comm, abs_mul, this.ne']
    _ ≤ C * (r / t : ℝ) ^ n := mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (div_nonneg r.2 t.2) _)

#align formal_multilinear_series.is_o_of_lt_radius FormalMultilinearSeries.isLittleO_of_lt_radius

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ = o(1)`. -/
theorem isLittleO_one_of_lt_radius (h : ↑r < p.radius) :
    (fun n => ‖p n‖ * (r : ℝ) ^ n) =o[atTop] (fun _ => 1 : ℕ → ℝ) :=
  let ⟨_, ha, hp⟩ := p.isLittleO_of_lt_radius h
  hp.trans <| (isLittleO_pow_pow_of_lt_left ha.1.le ha.2).congr (fun _ => rfl) one_pow
#align formal_multilinear_series.is_o_one_of_lt_radius FormalMultilinearSeries.isLittleO_one_of_lt_radius

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` tends to zero exponentially:
for some `0 < a < 1` and `C > 0`,  `‖p n‖ * r ^ n ≤ C * a ^ n`. -/
theorem norm_mul_pow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C * a ^ n := by
  -- Porting note: moved out of `rcases`
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 5).mp
    (p.isLittleO_of_lt_radius h)
  rcases this with ⟨a, ha, C, hC, H⟩
  exact ⟨a, ha, C, hC, fun n => (le_abs_self _).trans (H n)⟩
#align formal_multilinear_series.norm_mul_pow_le_mul_pow_of_lt_radius FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius

/-- If `r ≠ 0` and `‖pₙ‖ rⁿ = O(aⁿ)` for some `-1 < a < 1`, then `r < p.radius`. -/
theorem lt_radius_of_isBigO (h₀ : r ≠ 0) {a : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hp : (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] (a ^ ·)) : ↑r < p.radius := by
  -- Porting note: moved out of `rcases`
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 2 5)
  rcases this.mp ⟨a, ha, hp⟩ with ⟨a, ha, C, hC, hp⟩
  rw [← pos_iff_ne_zero, ← NNReal.coe_pos] at h₀
  lift a to ℝ≥0 using ha.1.le
  have : (r : ℝ) < r / a := by
    simpa only [div_one] using (div_lt_div_left h₀ zero_lt_one ha.1).2 ha.2
  norm_cast  at this
  rw [← ENNReal.coe_lt_coe] at this
  refine' this.trans_le (p.le_radius_of_bound C fun n => _)
  rw [NNReal.coe_div, div_pow, ← mul_div_assoc, div_le_iff (pow_pos ha.1 n)]
  exact (le_abs_self _).trans (hp n)
set_option linter.uppercaseLean3 false in
#align formal_multilinear_series.lt_radius_of_is_O FormalMultilinearSeries.lt_radius_of_isBigO

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
theorem norm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C :=
  let ⟨_, ha, C, hC, h⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  ⟨C, hC, fun n => (h n).trans <| mul_le_of_le_one_right hC.lt.le (pow_le_one _ ha.1.le ha.2.le)⟩
#align formal_multilinear_series.norm_mul_pow_le_of_lt_radius FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
theorem norm_le_div_pow_of_pos_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h0 : 0 < r) (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖ ≤ C / (r : ℝ) ^ n :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨C, hC, fun n => Iff.mpr (le_div_iff (pow_pos h0 _)) (hp n)⟩
#align formal_multilinear_series.norm_le_div_pow_of_pos_of_lt_radius FormalMultilinearSeries.norm_le_div_pow_of_pos_of_lt_radius

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
theorem nnnorm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖₊ * r ^ n ≤ C :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨⟨C, hC.lt.le⟩, hC, by exact_mod_cast hp⟩
#align formal_multilinear_series.nnnorm_mul_pow_le_of_lt_radius FormalMultilinearSeries.nnnorm_mul_pow_le_of_lt_radius

theorem le_radius_of_tendsto (p : FormalMultilinearSeries 𝕜 E F) {l : ℝ}
    (h : Tendsto (fun n => ‖p n‖ * (r : ℝ) ^ n) atTop (𝓝 l)) : ↑r ≤ p.radius :=
  p.le_radius_of_isBigO (h.isBigO_one _)
#align formal_multilinear_series.le_radius_of_tendsto FormalMultilinearSeries.le_radius_of_tendsto

theorem le_radius_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_tendsto hs.tendsto_atTop_zero
#align formal_multilinear_series.le_radius_of_summable_norm FormalMultilinearSeries.le_radius_of_summable_norm

theorem not_summable_norm_of_radius_lt_nnnorm (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (h : p.radius < ‖x‖₊) : ¬Summable fun n => ‖p n‖ * ‖x‖ ^ n := fun hs =>
  not_le_of_lt h (p.le_radius_of_summable_norm hs)
#align formal_multilinear_series.not_summable_norm_of_radius_lt_nnnorm FormalMultilinearSeries.not_summable_norm_of_radius_lt_nnnorm

theorem summable_norm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0} (h : ↑r < p.radius) :
    Summable fun n : ℕ => ‖p n‖ * (r : ℝ) ^ n := by
  obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  exact
    summable_of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg _)) hp
      ((summable_geometric_of_lt_1 ha.1.le ha.2).mul_left _)
#align formal_multilinear_series.summable_norm_mul_pow FormalMultilinearSeries.summable_norm_mul_pow

theorem summable_norm_apply (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ EMetric.ball (0 : E) p.radius) : Summable fun n : ℕ => ‖p n fun _ => x‖ := by
  rw [mem_emetric_ball_zero_iff] at hx
  refine'
    summable_of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ((p n).le_op_norm _).trans_eq _)
      (p.summable_norm_mul_pow hx)
  simp
#align formal_multilinear_series.summable_norm_apply FormalMultilinearSeries.summable_norm_apply

theorem summable_nnnorm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0} (h : ↑r < p.radius) :
    Summable fun n : ℕ => ‖p n‖₊ * r ^ n := by
  rw [← NNReal.summable_coe]
  push_cast
  exact p.summable_norm_mul_pow h
#align formal_multilinear_series.summable_nnnorm_mul_pow FormalMultilinearSeries.summable_nnnorm_mul_pow

protected theorem summable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ EMetric.ball (0 : E) p.radius) : Summable fun n : ℕ => p n fun _ => x :=
  summable_of_summable_norm (p.summable_norm_apply hx)
#align formal_multilinear_series.summable FormalMultilinearSeries.summable

theorem radius_eq_top_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : ∀ r : ℝ≥0, Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : p.radius = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_summable_norm (hs r)
#align formal_multilinear_series.radius_eq_top_of_summable_norm FormalMultilinearSeries.radius_eq_top_of_summable_norm

theorem radius_eq_top_iff_summable_norm (p : FormalMultilinearSeries 𝕜 E F) :
    p.radius = ∞ ↔ ∀ r : ℝ≥0, Summable fun n => ‖p n‖ * (r : ℝ) ^ n := by
  constructor
  · intro h r
    obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, - : 0 < C, hp⟩ :=
      p.norm_mul_pow_le_mul_pow_of_lt_radius
        (show (r : ℝ≥0∞) < p.radius from h.symm ▸ ENNReal.coe_lt_top)
    refine'
      summable_of_norm_bounded (fun n => (C : ℝ) * a ^ n)
        ((summable_geometric_of_lt_1 ha.1.le ha.2).mul_left _) fun n => _
    specialize hp n
    rwa [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg n))]
  · exact p.radius_eq_top_of_summable_norm
#align formal_multilinear_series.radius_eq_top_iff_summable_norm FormalMultilinearSeries.radius_eq_top_iff_summable_norm

/-- If the radius of `p` is positive, then `‖pₙ‖` grows at most geometrically. -/
theorem le_mul_pow_of_radius_pos (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    ∃ (C r : _)(hC : 0 < C)(hr : 0 < r), ∀ n, ‖p n‖ ≤ C * r ^ n := by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨r, r0, rlt⟩
  have rpos : 0 < (r : ℝ) := by simp [ENNReal.coe_pos.1 r0]
  rcases norm_le_div_pow_of_pos_of_lt_radius p rpos rlt with ⟨C, Cpos, hCp⟩
  refine' ⟨C, r⁻¹, Cpos, by simp only [inv_pos, rpos], fun n => _⟩
  -- Porting note: was `convert`
  rw [inv_pow, ← div_eq_mul_inv]
  exact hCp n
#align formal_multilinear_series.le_mul_pow_of_radius_pos FormalMultilinearSeries.le_mul_pow_of_radius_pos

/-- The radius of the sum of two formal series is at least the minimum of their two radii. -/
theorem min_radius_le_radius_add (p q : FormalMultilinearSeries 𝕜 E F) :
    min p.radius q.radius ≤ (p + q).radius := by
  refine' ENNReal.le_of_forall_nnreal_lt fun r hr => _
  rw [lt_min_iff] at hr
  have := ((p.isLittleO_one_of_lt_radius hr.1).add (q.isLittleO_one_of_lt_radius hr.2)).isBigO
  refine' (p + q).le_radius_of_isBigO ((isBigO_of_le _ fun n => _).trans this)
  rw [← add_mul, norm_mul, norm_mul, norm_norm]
  exact mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (le_abs_self _)) (norm_nonneg _)
#align formal_multilinear_series.min_radius_le_radius_add FormalMultilinearSeries.min_radius_le_radius_add

@[simp]
theorem radius_neg (p : FormalMultilinearSeries 𝕜 E F) : (-p).radius = p.radius := by
  simp only [radius, Pi.neg_apply, norm_neg]
  sorry
#align formal_multilinear_series.radius_neg FormalMultilinearSeries.radius_neg

protected theorem hasSum [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ EMetric.ball (0 : E) p.radius) : HasSum (fun n : ℕ => p n fun _ => x) (p.sum x) :=
  (p.summable hx).hasSum
#align formal_multilinear_series.has_sum FormalMultilinearSeries.hasSum

theorem radius_le_radius_continuousLinearMap_comp (p : FormalMultilinearSeries 𝕜 E F)
    (f : F →L[𝕜] G) : p.radius ≤ (f.compFormalMultilinearSeries p).radius := by
  refine' ENNReal.le_of_forall_nnreal_lt fun r hr => _
  apply le_radius_of_isBigO
  apply (IsBigO.trans_isLittleO _ (p.isLittleO_one_of_lt_radius hr)).isBigO
  refine' IsBigO.mul (@IsBigOWith.isBigO _ _ _ _ _ ‖f‖ _ _ _ _) (isBigO_refl _ _)
  refine IsBigOWith.of_bound (eventually_of_forall fun n => ?_)
  simpa only [norm_norm] using f.norm_compContinuousMultilinearMap_le (p n)
#align formal_multilinear_series.radius_le_radius_continuous_linear_map_comp FormalMultilinearSeries.radius_le_radius_continuousLinearMap_comp

end FormalMultilinearSeries

/-! ### Expanding a function as a power series -/


section

variable {f g : E → F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r r' : ℝ≥0∞}

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series on the ball of radius `r > 0` around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `‖y‖ < r`.
-/
structure HasFpowerSeriesOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (r : ℝ≥0∞) :
  Prop where
  r_le : r ≤ p.radius
  r_pos : 0 < r
  hasSum :
    ∀ {y}, y ∈ EMetric.ball (0 : E) r → HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y))
#align has_fpower_series_on_ball HasFpowerSeriesOnBall

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a neighborhood of `0`. -/
def HasFpowerSeriesAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) :=
  ∃ r, HasFpowerSeriesOnBall f p x r
#align has_fpower_series_at HasFpowerSeriesAt

variable (𝕜)

/-- Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a convergent power
series expansion around `x`. -/
def AnalyticAt (f : E → F) (x : E) :=
  ∃ p : FormalMultilinearSeries 𝕜 E F, HasFpowerSeriesAt f p x
#align analytic_at AnalyticAt

/-- Given a function `f : E → F`, we say that `f` is analytic on a set `s` if it is analytic around
every point of `s`. -/
def AnalyticOn (f : E → F) (s : Set E) :=
  ∀ x, x ∈ s → AnalyticAt 𝕜 f x
#align analytic_on AnalyticOn

variable {𝕜}

theorem HasFpowerSeriesOnBall.hasFpowerSeriesAt (hf : HasFpowerSeriesOnBall f p x r) :
    HasFpowerSeriesAt f p x :=
  ⟨r, hf⟩
#align has_fpower_series_on_ball.has_fpower_series_at HasFpowerSeriesOnBall.hasFpowerSeriesAt

theorem HasFpowerSeriesAt.analyticAt (hf : HasFpowerSeriesAt f p x) : AnalyticAt 𝕜 f x :=
  ⟨p, hf⟩
#align has_fpower_series_at.analytic_at HasFpowerSeriesAt.analyticAt

theorem HasFpowerSeriesOnBall.analyticAt (hf : HasFpowerSeriesOnBall f p x r) : AnalyticAt 𝕜 f x :=
  hf.hasFpowerSeriesAt.analyticAt
#align has_fpower_series_on_ball.analytic_at HasFpowerSeriesOnBall.analyticAt

theorem HasFpowerSeriesOnBall.congr (hf : HasFpowerSeriesOnBall f p x r)
    (hg : EqOn f g (EMetric.ball x r)) : HasFpowerSeriesOnBall g p x r :=
  { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {y} hy => by
      convert hf.hasSum hy
      stop
      apply hg.symm
      simpa [edist_eq_coe_nnnorm_sub] using hy }
#align has_fpower_series_on_ball.congr HasFpowerSeriesOnBall.congr

/-- If a function `f` has a power series `p` around `x`, then the function `z ↦ f (z - y)` has the
same power series around `x + y`. -/
theorem HasFpowerSeriesOnBall.compSub (hf : HasFpowerSeriesOnBall f p x r) (y : E) :
    HasFpowerSeriesOnBall (fun z => f (z - y)) p (x + y) r :=
  { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {z} hz => by
      convert hf.hasSum hz using 2
      abel }
#align has_fpower_series_on_ball.comp_sub HasFpowerSeriesOnBall.compSub

theorem HasFpowerSeriesOnBall.hasSum_sub (hf : HasFpowerSeriesOnBall f p x r) {y : E}
    (hy : y ∈ EMetric.ball x r) : HasSum (fun n : ℕ => p n fun _ => y - x) (f y) := by
  have : y - x ∈ EMetric.ball (0 : E) r := by simpa [edist_eq_coe_nnnorm_sub] using hy
  simpa only [add_sub_cancel'_right] using hf.hasSum this
#align has_fpower_series_on_ball.has_sum_sub HasFpowerSeriesOnBall.hasSum_sub

theorem HasFpowerSeriesOnBall.radius_pos (hf : HasFpowerSeriesOnBall f p x r) : 0 < p.radius :=
  lt_of_lt_of_le hf.r_pos hf.r_le
#align has_fpower_series_on_ball.radius_pos HasFpowerSeriesOnBall.radius_pos

theorem HasFpowerSeriesAt.radius_pos (hf : HasFpowerSeriesAt f p x) : 0 < p.radius :=
  let ⟨_, hr⟩ := hf
  hr.radius_pos
#align has_fpower_series_at.radius_pos HasFpowerSeriesAt.radius_pos

theorem HasFpowerSeriesOnBall.mono (hf : HasFpowerSeriesOnBall f p x r) (r'_pos : 0 < r')
    (hr : r' ≤ r) : HasFpowerSeriesOnBall f p x r' :=
  ⟨le_trans hr hf.1, r'_pos, fun hy => hf.hasSum (EMetric.ball_subset_ball hr hy)⟩
#align has_fpower_series_on_ball.mono HasFpowerSeriesOnBall.mono

theorem HasFpowerSeriesAt.congr (hf : HasFpowerSeriesAt f p x) (hg : f =ᶠ[𝓝 x] g) :
    HasFpowerSeriesAt g p x := by
  rcases hf with ⟨r₁, h₁⟩
  rcases EMetric.mem_nhds_iff.mp hg with ⟨r₂, h₂pos, h₂⟩
  exact
    ⟨min r₁ r₂,
      (h₁.mono (lt_min h₁.r_pos h₂pos) inf_le_left).congr fun y hy =>
        h₂ (EMetric.ball_subset_ball inf_le_right hy)⟩
#align has_fpower_series_at.congr HasFpowerSeriesAt.congr

protected theorem HasFpowerSeriesAt.eventually (hf : HasFpowerSeriesAt f p x) :
    ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, HasFpowerSeriesOnBall f p x r :=
  let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsWithin_Ioi (left_mem_Ico.2 hr.r_pos)) fun _ hr' =>
    hr.mono hr'.1 hr'.2.le
#align has_fpower_series_at.eventually HasFpowerSeriesAt.eventually

theorem HasFpowerSeriesOnBall.eventually_hasSum (hf : HasFpowerSeriesOnBall f p x r) :
    ∀ᶠ y in 𝓝 0, HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y)) := by
  filter_upwards [EMetric.ball_mem_nhds (0 : E) hf.r_pos]using fun _ => hf.hasSum
#align has_fpower_series_on_ball.eventually_has_sum HasFpowerSeriesOnBall.eventually_hasSum

theorem HasFpowerSeriesAt.eventually_hasSum (hf : HasFpowerSeriesAt f p x) :
    ∀ᶠ y in 𝓝 0, HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y)) :=
  let ⟨_, hr⟩ := hf
  hr.eventually_hasSum
#align has_fpower_series_at.eventually_has_sum HasFpowerSeriesAt.eventually_hasSum

theorem HasFpowerSeriesOnBall.eventually_hasSum_sub (hf : HasFpowerSeriesOnBall f p x r) :
    ∀ᶠ y in 𝓝 x, HasSum (fun n : ℕ => p n fun _ : Fin n => y - x) (f y) := by
  filter_upwards [EMetric.ball_mem_nhds x hf.r_pos]with y using hf.hasSum_sub
#align has_fpower_series_on_ball.eventually_has_sum_sub HasFpowerSeriesOnBall.eventually_hasSum_sub

theorem HasFpowerSeriesAt.eventually_hasSum_sub (hf : HasFpowerSeriesAt f p x) :
    ∀ᶠ y in 𝓝 x, HasSum (fun n : ℕ => p n fun _ : Fin n => y - x) (f y) :=
  let ⟨_, hr⟩ := hf
  hr.eventually_hasSum_sub
#align has_fpower_series_at.eventually_has_sum_sub HasFpowerSeriesAt.eventually_hasSum_sub

theorem HasFpowerSeriesOnBall.eventually_eq_zero
    (hf : HasFpowerSeriesOnBall f (0 : FormalMultilinearSeries 𝕜 E F) x r) : ∀ᶠ z in 𝓝 x, f z = 0 :=
  by filter_upwards [hf.eventually_hasSum_sub]with z hz using hz.unique hasSum_zero
#align has_fpower_series_on_ball.eventually_eq_zero HasFpowerSeriesOnBall.eventually_eq_zero

theorem HasFpowerSeriesAt.eventually_eq_zero
    (hf : HasFpowerSeriesAt f (0 : FormalMultilinearSeries 𝕜 E F) x) : ∀ᶠ z in 𝓝 x, f z = 0 :=
  let ⟨_, hr⟩ := hf
  hr.eventually_eq_zero
#align has_fpower_series_at.eventually_eq_zero HasFpowerSeriesAt.eventually_eq_zero

theorem hasFpowerSeriesOnBallConst {c : F} {e : E} :
    HasFpowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e ⊤ := by
  refine' ⟨by simp, WithTop.zero_lt_top, fun _ => hasSum_single 0 fun n hn => _⟩
  simp [constFormalMultilinearSeries_apply hn]
#align has_fpower_series_on_ball_const hasFpowerSeriesOnBallConst

theorem hasFpowerSeriesAtConst {c : F} {e : E} :
    HasFpowerSeriesAt (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e :=
  ⟨⊤, hasFpowerSeriesOnBallConst⟩
#align has_fpower_series_at_const hasFpowerSeriesAtConst

theorem analyticAt_const {v : F} : AnalyticAt 𝕜 (fun _ => v) x :=
  ⟨constFormalMultilinearSeries 𝕜 E v, hasFpowerSeriesAtConst⟩
#align analytic_at_const analyticAt_const

theorem analyticOn_const {v : F} {s : Set E} : AnalyticOn 𝕜 (fun _ => v) s := fun _ _ =>
  analyticAt_const
#align analytic_on_const analyticOn_const

theorem HasFpowerSeriesOnBall.add (hf : HasFpowerSeriesOnBall f pf x r)
    (hg : HasFpowerSeriesOnBall g pg x r) : HasFpowerSeriesOnBall (f + g) (pf + pg) x r :=
  { r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg)
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).add (hg.hasSum hy) }
#align has_fpower_series_on_ball.add HasFpowerSeriesOnBall.add

theorem HasFpowerSeriesAt.add (hf : HasFpowerSeriesAt f pf x) (hg : HasFpowerSeriesAt g pg x) :
    HasFpowerSeriesAt (f + g) (pf + pg) x := by
  rcases(hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩
#align has_fpower_series_at.add HasFpowerSeriesAt.add

theorem AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) : AnalyticAt 𝕜 (f + g) x :=
  let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.add hqf).analyticAt
#align analytic_at.add AnalyticAt.add

theorem HasFpowerSeriesOnBall.neg (hf : HasFpowerSeriesOnBall f pf x r) :
    HasFpowerSeriesOnBall (-f) (-pf) x r :=
  { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).neg }
#align has_fpower_series_on_ball.neg HasFpowerSeriesOnBall.neg

theorem HasFpowerSeriesAt.neg (hf : HasFpowerSeriesAt f pf x) : HasFpowerSeriesAt (-f) (-pf) x :=
  let ⟨_, hrf⟩ := hf
  hrf.neg.hasFpowerSeriesAt
#align has_fpower_series_at.neg HasFpowerSeriesAt.neg

theorem AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-f) x :=
  let ⟨_, hpf⟩ := hf
  hpf.neg.analyticAt
#align analytic_at.neg AnalyticAt.neg

theorem HasFpowerSeriesOnBall.sub (hf : HasFpowerSeriesOnBall f pf x r)
    (hg : HasFpowerSeriesOnBall g pg x r) : HasFpowerSeriesOnBall (f - g) (pf - pg) x r := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_fpower_series_on_ball.sub HasFpowerSeriesOnBall.sub

theorem HasFpowerSeriesAt.sub (hf : HasFpowerSeriesAt f pf x) (hg : HasFpowerSeriesAt g pg x) :
    HasFpowerSeriesAt (f - g) (pf - pg) x := by simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_fpower_series_at.sub HasFpowerSeriesAt.sub

theorem AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) : AnalyticAt 𝕜 (f - g) x :=
  by simpa only [sub_eq_add_neg] using hf.add hg.neg
#align analytic_at.sub AnalyticAt.sub

theorem AnalyticOn.mono {s t : Set E} (hf : AnalyticOn 𝕜 f t) (hst : s ⊆ t) : AnalyticOn 𝕜 f s :=
  fun z hz => hf z (hst hz)
#align analytic_on.mono AnalyticOn.mono

theorem AnalyticOn.add {s : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (f + g) s := fun z hz => (hf z hz).add (hg z hz)
#align analytic_on.add AnalyticOn.add

theorem AnalyticOn.sub {s : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (f - g) s := fun z hz => (hf z hz).sub (hg z hz)
#align analytic_on.sub AnalyticOn.sub

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i «expr ≠ » 0) -/
theorem HasFpowerSeriesOnBall.coeff_zero (hf : HasFpowerSeriesOnBall f pf x r) (v : Fin 0 → E) :
    pf 0 v = f x := by
  have v_eq : v = fun i => 0 := Subsingleton.elim _ _
  have zero_mem : (0 : E) ∈ EMetric.ball (0 : E) r := by simp [hf.r_pos]
  have : ∀ (i) (_ : i ≠ 0), (pf i fun j => 0) = 0 := by
    intro i hi
    have : 0 < i := pos_iff_ne_zero.2 hi
    exact ContinuousMultilinearMap.map_coord_zero _ (⟨0, this⟩ : Fin i) rfl
  have A := (hf.hasSum zero_mem).unique (hasSum_single _ this)
  simpa [v_eq] using A.symm
#align has_fpower_series_on_ball.coeff_zero HasFpowerSeriesOnBall.coeff_zero

theorem HasFpowerSeriesAt.coeff_zero (hf : HasFpowerSeriesAt f pf x) (v : Fin 0 → E) :
    pf 0 v = f x :=
  let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v
#align has_fpower_series_at.coeff_zero HasFpowerSeriesAt.coeff_zero

/-- If a function `f` has a power series `p` on a ball and `g` is linear, then `g ∘ f` has the
power series `g ∘ p` on the same ball. -/
theorem ContinuousLinearMap.compHasFpowerSeriesOnBall (g : F →L[𝕜] G)
    (h : HasFpowerSeriesOnBall f p x r) :
    HasFpowerSeriesOnBall (g ∘ f) (g.compFormalMultilinearSeries p) x r :=
  { r_le := h.r_le.trans (p.radius_le_radius_continuousLinearMap_comp _)
    r_pos := h.r_pos
    hasSum := fun hy => by
      simpa only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
        ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] using
        g.hasSum (h.hasSum hy) }
#align continuous_linear_map.comp_has_fpower_series_on_ball ContinuousLinearMap.compHasFpowerSeriesOnBall

/-- If a function `f` is analytic on a set `s` and `g` is linear, then `g ∘ f` is analytic
on `s`. -/
theorem ContinuousLinearMap.comp_analyticOn {s : Set E} (g : F →L[𝕜] G) (h : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.compHasFpowerSeriesOnBall hp⟩
#align continuous_linear_map.comp_analytic_on ContinuousLinearMap.comp_analyticOn

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `‖y‖` and `n`. See also
`has_fpower_series_on_ball.uniform_geometric_approx` for a weaker version. -/
theorem HasFpowerSeriesOnBall.uniform_geometric_approx' {r' : ℝ≥0}
    (hf : HasFpowerSeriesOnBall f p x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0,
        ∀ y ∈ Metric.ball (0 : E) r',
          ∀ n, ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n := by
  obtain ⟨a, ha, C, hC, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n, ‖p n‖ * (r' : ℝ) ^ n ≤ C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (h.trans_le hf.r_le)
  refine' ⟨a, ha, C / (1 - a), div_pos hC (sub_pos.2 ha.2), fun y hy n => _⟩
  have yr' : ‖y‖ < r' := by
    rw [ball_zero_eq] at hy
    exact hy
  have hr'0 : 0 < (r' : ℝ) := (norm_nonneg _).trans_lt yr'
  have : y ∈ EMetric.ball (0 : E) r := by
    refine' mem_emetric_ball_zero_iff.2 (lt_trans _ h)
    exact_mod_cast yr'
  rw [norm_sub_rev, ← mul_div_right_comm]
  have ya : a * (‖y‖ / ↑r') ≤ a :=
    mul_le_of_le_one_right ha.1.le (div_le_one_of_le yr'.le r'.coe_nonneg)
  suffices ‖p.partialSum n y - f (x + y)‖ ≤ C * (a * (‖y‖ / r')) ^ n / (1 - a * (‖y‖ / r')) by
    refine' this.trans _
    apply_rules [div_le_div_of_le_left, sub_pos.2, div_nonneg, mul_nonneg, pow_nonneg, hC.lt.le,
        ha.1.le, norm_nonneg, NNReal.coe_nonneg, ha.2, (sub_le_sub_iff_left _).2]
  apply norm_sub_le_of_geometric_bound_of_hasSum (ya.trans_lt ha.2) _ (hf.hasSum this)
  intro n
  calc
    ‖(p n) fun _ : Fin n => y‖
    _ ≤ ‖p n‖ * ∏ _i : Fin n, ‖y‖ := ContinuousMultilinearMap.le_op_norm _ _
    _ = ‖p n‖ * (r' : ℝ) ^ n * (‖y‖ / r') ^ n := by field_simp [hr'0.ne', mul_right_comm]
    _ ≤ C * a ^ n * (‖y‖ / r') ^ n :=
      (mul_le_mul_of_nonneg_right (hp n) (pow_nonneg (div_nonneg (norm_nonneg _) r'.coe_nonneg) _))
    _ ≤ C * (a * (‖y‖ / r')) ^ n := by rw [mul_pow, mul_assoc]

#align has_fpower_series_on_ball.uniform_geometric_approx' HasFpowerSeriesOnBall.uniform_geometric_approx'

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence. -/
theorem HasFpowerSeriesOnBall.uniform_geometric_approx {r' : ℝ≥0}
    (hf : HasFpowerSeriesOnBall f p x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n, ‖f (x + y) - p.partialSum n y‖ ≤ C * a ^ n := by
  obtain ⟨a, ha, C, hC, hp⟩ :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0,
        ∀ y ∈ Metric.ball (0 : E) r',
          ∀ n, ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n :=
    hf.uniform_geometric_approx' h
  refine' ⟨a, ha, C, hC, fun y hy n => (hp y hy n).trans _⟩
  have yr' : ‖y‖ < r' := by rwa [ball_zero_eq] at hy
  refine' mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left _ _ _) hC.lt.le
  exacts[mul_nonneg ha.1.le (div_nonneg (norm_nonneg y) r'.coe_nonneg),
    mul_le_of_le_one_right ha.1.le (div_le_one_of_le yr'.le r'.coe_nonneg)]
#align has_fpower_series_on_ball.uniform_geometric_approx HasFpowerSeriesOnBall.uniform_geometric_approx

/-- Taylor formula for an analytic function, `is_O` version. -/
theorem HasFpowerSeriesAt.isBigO_sub_partialSum_pow (hf : HasFpowerSeriesAt f p x) (n : ℕ) :
    (fun y : E => f (x + y) - p.partialSum n y) =O[𝓝 0] fun y => ‖y‖ ^ n := by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  obtain ⟨a, -, C, -, hp⟩ :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0,
        ∀ y ∈ Metric.ball (0 : E) r',
          ∀ n, ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n :=
    hf.uniform_geometric_approx' h
  refine' isBigO_iff.2 ⟨C * (a / r') ^ n, _⟩
  replace r'0 : 0 < (r' : ℝ); · exact_mod_cast r'0
  filter_upwards [Metric.ball_mem_nhds (0 : E) r'0]with y hy
  simpa [mul_pow, mul_div_assoc, mul_assoc, div_mul_eq_mul_div] using hp y hy n
set_option linter.uppercaseLean3 false in
#align has_fpower_series_at.is_O_sub_partial_sum_pow HasFpowerSeriesAt.isBigO_sub_partialSum_pow

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. This lemma formulates this property using `is_O` and
`filter.principal` on `E × E`. -/
theorem HasFpowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal
    (hf : HasFpowerSeriesOnBall f p x r) (hr : r' < r) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) =O[𝓟 (EMetric.ball (x, x) r')]
      fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  lift r' to ℝ≥0 using ne_top_of_lt hr
  rcases(zero_le r').eq_or_lt with (rfl | hr'0)
  · simp only [isBigO_bot, EMetric.ball_zero, principal_empty, ENNReal.coe_zero]
  obtain ⟨a, ha, C, hC : 0 < C, hp⟩ :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n : ℕ, ‖p n‖ * (r' : ℝ) ^ n ≤ C * a ^ n
  exact p.norm_mul_pow_le_mul_pow_of_lt_radius (hr.trans_le hf.r_le)
  simp only [← le_div_iff (pow_pos (NNReal.coe_pos.2 hr'0) _)] at hp
  set L : E × E → ℝ := fun y =>
    C * (a / r') ^ 2 * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * (a / (1 - a) ^ 2 + 2 / (1 - a))
  have hL : ∀ y ∈ EMetric.ball (x, x) r', ‖f y.1 - f y.2 - p 1 fun _ => y.1 - y.2‖ ≤ L y := by
    intro y hy'
    have hy : y ∈ EMetric.ball x r ×ˢ EMetric.ball x r := by
      rw [EMetric.ball_prod_same]
      exact EMetric.ball_subset_ball hr.le hy'
    set A : ℕ → F := fun n => (p n fun _ => y.1 - x) - p n fun _ => y.2 - x
    have hA : HasSum (fun n => A (n + 2)) (f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) := by
      convert(hasSum_nat_add_iff' 2).2 ((hf.hasSum_sub hy.1).sub (hf.hasSum_sub hy.2)) using 1
      rw [Finset.sum_range_succ, Finset.sum_range_one, hf.coeff_zero, hf.coeff_zero, sub_self,
        zero_add, ← Subsingleton.pi_single_eq (0 : Fin 1) (y.1 - x), Pi.single, ←
        Subsingleton.pi_single_eq (0 : Fin 1) (y.2 - x), Pi.single, ← (p 1).map_sub, ← Pi.single,
        Subsingleton.pi_single_eq, sub_sub_sub_cancel_right]
    rw [EMetric.mem_ball, edist_eq_coe_nnnorm_sub, ENNReal.coe_lt_coe] at hy'
    set B : ℕ → ℝ := fun n => C * (a / r') ^ 2 * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * ((n + 2) * a ^ n)
    have hAB : ∀ n, ‖A (n + 2)‖ ≤ B n := fun n =>
      calc
        ‖A (n + 2)‖ ≤ ‖p (n + 2)‖ * ↑(n + 2) * ‖y - (x, x)‖ ^ (n + 1) * ‖y.1 - y.2‖ := by
          -- porting note: `pi_norm_const` was `pi_norm_const (_ : E)`
          simpa only [Fintype.card_fin, pi_norm_const, Prod.norm_def, Pi.sub_def,
            Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right] using
            (p <| n + 2).norm_image_sub_le (fun _ => y.1 - x) fun _ => y.2 - x
        _ = ‖p (n + 2)‖ * ‖y - (x, x)‖ ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) := by
          rw [pow_succ ‖y - (x, x)‖]
          ring
        --  porting note: the two `↑` in `↑r'` are new, without them, Lean errors with `HDiv, HMul`
        _ ≤ C * a ^ (n + 2) / ↑r' ^ (n + 2) * ↑r' ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) := by
          apply_rules [mul_le_mul_of_nonneg_right, mul_le_mul, hp, pow_le_pow_of_le_left, hy'.le,
            norm_nonneg, pow_nonneg, div_nonneg, mul_nonneg, Nat.cast_nonneg, hC.le, r'.coe_nonneg,
            ha.1.le]
        _ = B n := by
          -- porting note: in the original, `B` was in the `field_simp`, but now Lean does not
          -- accept it.  The current proof works in Lean 4, but does not in Lean 3.
          field_simp [pow_succ, hr'0.ne']
          simp only [mul_assoc, mul_comm, mul_left_comm]

    have hBL : HasSum B (L y) := by
      apply HasSum.mul_left
      simp only [add_mul]
      have : ‖a‖ < 1 := by simp only [Real.norm_eq_abs, abs_of_pos ha.1, ha.2]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact (hasSum_coe_mul_geometric_of_norm_lt_1 this).add  -- porting note: was `convert`!
          ((hasSum_geometric_of_norm_lt_1 this).mul_left 2)
    exact hA.norm_le_of_bounded hBL hAB
  suffices L =O[𝓟 (EMetric.ball (x, x) r')] fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ by
    refine' (IsBigO.of_bound 1 (eventually_principal.2 fun y hy => _)).trans this
    rw [one_mul]
    exact (hL y hy).trans (le_abs_self _)
  simp_rw [mul_right_comm _ (_ * _)]  -- porting note: there was an `L` inside the `simp_rw`.
  exact (isBigO_refl _ _).const_mul_left _
set_option linter.uppercaseLean3 false in
#align has_fpower_series_on_ball.isBigO_image_sub_image_sub_deriv_principal HasFpowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y z «expr ∈ » emetric.ball[emetric.ball] x r') -/
/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. -/
theorem HasFpowerSeriesOnBall.image_sub_sub_deriv_le (hf : HasFpowerSeriesOnBall f p x r)
    (hr : r' < r) :
    ∃ C,
      ∀ (y) (_ : y ∈ EMetric.ball x r') (z) (_ : z ∈ EMetric.ball x r'),
        ‖f y - f z - p 1 fun _ => y - z‖ ≤ C * max ‖y - x‖ ‖z - x‖ * ‖y - z‖ := by
  simpa only [isBigO_principal, mul_assoc, norm_mul, norm_norm, Prod.forall, EMetric.mem_ball,
    Prod.edist_eq, max_lt_iff, and_imp, @forall_swap (_ < _) E] using
    hf.isBigO_image_sub_image_sub_deriv_principal hr
#align has_fpower_series_on_ball.image_sub_sub_deriv_le HasFpowerSeriesOnBall.image_sub_sub_deriv_le

/-- If `f` has formal power series `∑ n, pₙ` at `x`, then
`f y - f z - p 1 (λ _, y - z) = O(‖(y, z) - (x, x)‖ * ‖y - z‖)` as `(y, z) → (x, x)`.
In particular, `f` is strictly differentiable at `x`. -/
theorem HasFpowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub (hf : HasFpowerSeriesAt f p x) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) =O[𝓝 (x, x)] fun y =>
      ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  refine' (hf.isBigO_image_sub_image_sub_deriv_principal h).mono _
  exact le_principal_iff.2 (EMetric.ball_mem_nhds _ r'0)
set_option linter.uppercaseLean3 false in
#align has_fpower_series_at.is_O_image_sub_norm_mul_norm_sub HasFpowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f (x + y)`
is the uniform limit of `p.partial_sum n y` there. -/
theorem HasFpowerSeriesOnBall.tendstoUniformlyOn {r' : ℝ≥0} (hf : HasFpowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      (Metric.ball (0 : E) r') := by
  obtain ⟨a, ha, C, -, hp⟩ :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n, ‖f (x + y) - p.partialSum n y‖ ≤ C * a ^ n
  exact hf.uniform_geometric_approx h
  refine' Metric.tendstoUniformlyOn_iff.2 fun ε εpos => _
  have L : Tendsto (fun n => (C : ℝ) * a ^ n) atTop (𝓝 ((C : ℝ) * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_0_of_lt_1 ha.1.le ha.2)
  rw [MulZeroClass.mul_zero] at L
  refine' (L.eventually (gt_mem_nhds εpos)).mono fun n hn y hy => _
  rw [dist_eq_norm]
  exact (hp y hy n).trans_lt hn
#align has_fpower_series_on_ball.tendsto_uniformly_on HasFpowerSeriesOnBall.tendstoUniformlyOn

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partial_sum n y` there. -/
theorem HasFpowerSeriesOnBall.tendstoLocallyUniformlyOn (hf : HasFpowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      (EMetric.ball (0 : E) r) := by
  intro u hu x hx
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hx with ⟨r', xr', hr'⟩
  have : EMetric.ball (0 : E) r' ∈ 𝓝 x := IsOpen.mem_nhds EMetric.isOpen_ball xr'
  refine' ⟨EMetric.ball (0 : E) r', mem_nhdsWithin_of_mem_nhds this, _⟩
  simpa [Metric.emetric_ball_nnreal] using hf.tendstoUniformlyOn hr' u hu
#align has_fpower_series_on_ball.tendsto_locally_uniformly_on HasFpowerSeriesOnBall.tendstoLocallyUniformlyOn

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partial_sum n (y - x)` there. -/
theorem HasFpowerSeriesOnBall.tendstoUniformlyOn' {r' : ℝ≥0} (hf : HasFpowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop (Metric.ball (x : E) r') := by
  convert(hf.tendstoUniformlyOn h).comp fun y => y - x using 1
  · simp [(· ∘ ·)]
  · ext z
    simp [dist_eq_norm]
#align has_fpower_series_on_ball.tendsto_uniformly_on' HasFpowerSeriesOnBall.tendstoUniformlyOn'

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the  partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partial_sum n (y - x)` there. -/
theorem HasFpowerSeriesOnBall.tendstoLocallyUniformlyOn' (hf : HasFpowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop
      (EMetric.ball (x : E) r) := by
  have A : ContinuousOn (fun y : E => y - x) (EMetric.ball (x : E) r) :=
    (continuous_id.sub continuous_const).continuousOn
  convert hf.tendstoLocallyUniformlyOn.comp (fun y : E => y - x) _ A using 1
  · ext z
    simp
  · intro z
    simp [edist_eq_coe_nnnorm, edist_eq_coe_nnnorm_sub]
#align has_fpower_series_on_ball.tendsto_locally_uniformly_on' HasFpowerSeriesOnBall.tendstoLocallyUniformlyOn'

/-- If a function admits a power series expansion on a disk, then it is continuous there. -/
protected theorem HasFpowerSeriesOnBall.continuousOn (hf : HasFpowerSeriesOnBall f p x r) :
    ContinuousOn f (EMetric.ball x r) :=
  hf.tendstoLocallyUniformlyOn'.continuousOn <|
    eventually_of_forall fun n =>
      ((p.partialSum_continuous n).comp (continuous_id.sub continuous_const)).continuousOn
#align has_fpower_series_on_ball.continuous_on HasFpowerSeriesOnBall.continuousOn

protected theorem HasFpowerSeriesAt.continuousAt (hf : HasFpowerSeriesAt f p x) :
    ContinuousAt f x :=
  let ⟨_, hr⟩ := hf
  hr.continuousOn.continuousAt (EMetric.ball_mem_nhds x hr.r_pos)
#align has_fpower_series_at.continuous_at HasFpowerSeriesAt.continuousAt

protected theorem AnalyticAt.continuousAt (hf : AnalyticAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨_, hp⟩ := hf
  hp.continuousAt
#align analytic_at.continuous_at AnalyticAt.continuousAt

protected theorem AnalyticOn.continuousOn {s : Set E} (hf : AnalyticOn 𝕜 f s) : ContinuousOn f s :=
  fun x hx => (hf x hx).continuousAt.continuousWithinAt
#align analytic_on.continuous_on AnalyticOn.continuousOn

/-- In a complete space, the sum of a converging power series `p` admits `p` as a power series.
This is not totally obvious as we need to check the convergence of the series. -/
protected theorem FormalMultilinearSeries.hasFpowerSeriesOnBall [CompleteSpace F]
    (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    HasFpowerSeriesOnBall p.sum p 0 p.radius :=
  { r_le := le_rfl
    r_pos := h
    hasSum := fun hy => by
      rw [zero_add]
      exact p.hasSum hy }
#align formal_multilinear_series.has_fpower_series_on_ball FormalMultilinearSeries.hasFpowerSeriesOnBall

theorem HasFpowerSeriesOnBall.sum (h : HasFpowerSeriesOnBall f p x r) {y : E}
    (hy : y ∈ EMetric.ball (0 : E) r) : f (x + y) = p.sum y :=
  (h.hasSum hy).tsum_eq.symm
#align has_fpower_series_on_ball.sum HasFpowerSeriesOnBall.sum

/-- The sum of a converging power series is continuous in its disk of convergence. -/
protected theorem FormalMultilinearSeries.continuousOn [CompleteSpace F] :
    ContinuousOn p.sum (EMetric.ball 0 p.radius) := by
  cases' (zero_le p.radius).eq_or_lt with h h
  · simp [← h, continuousOn_empty]
  · exact (p.hasFpowerSeriesOnBall h).continuousOn
#align formal_multilinear_series.continuous_on FormalMultilinearSeries.continuousOn

end

/-!
### Uniqueness of power series
If a function `f : E → F` has two representations as power series at a point `x : E`, corresponding
to formal multilinear series `p₁` and `p₂`, then these representations agree term-by-term. That is,
for any `n : ℕ` and `y : E`,  `p₁ n (λ i, y) = p₂ n (λ i, y)`. In the one-dimensional case, when
`f : 𝕜 → E`, the continuous multilinear maps `p₁ n` and `p₂ n` are given by
`formal_multilinear_series.mk_pi_field`, and hence are determined completely by the value of
`p₁ n (λ i, 1)`, so `p₁ = p₂`. Consequently, the radius of convergence for one series can be
transferred to the other.
-/


section Uniqueness

open ContinuousMultilinearMap

theorem Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero {n : ℕ} {p : E[×n]→L[𝕜] F}
    (h : (fun y => p fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^ (n + 1)) (y : E) : (p fun _ => y) = 0 := by
  obtain ⟨c, c_pos, hc⟩ := h.exists_pos
  obtain ⟨t, ht, t_open, z_mem⟩ := eventually_nhds_iff.mp (isBigOWith_iff.mp hc)
  obtain ⟨δ, δ_pos, δε⟩ := (Metric.isOpen_iff.mp t_open) 0 z_mem
  clear h hc z_mem
  cases' n with n
  ·
    exact
      norm_eq_zero.mp
        (by -- porting note: the symmetric difference of the `simpa only` sets:
            -- added `Nat.zero_eq, zero_add, pow_one`
            -- removed `zero_pow', Ne.def, Nat.one_ne_zero, not_false_iff`
          simpa only [Nat.zero_eq, fin0_apply_norm, norm_eq_zero, norm_zero, zero_add, pow_one,
            mul_zero, norm_le_zero_iff] using ht 0 (δε (Metric.mem_ball_self δ_pos)))
  · refine' Or.elim (Classical.em (y = 0))
      (fun hy => by simpa only [hy] using p.map_zero) fun hy => _
    replace hy := norm_pos_iff.mpr hy
    refine' norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun ε ε_pos => _) (norm_nonneg _))
    have h₀ := _root_.mul_pos c_pos (pow_pos hy (n.succ + 1))
    obtain ⟨k, k_pos, k_norm⟩ :=
      NormedField.exists_norm_lt 𝕜
        (lt_min (mul_pos δ_pos (inv_pos.mpr hy)) (mul_pos ε_pos (inv_pos.mpr h₀)))
    have h₁ : ‖k • y‖ < δ := by
      rw [norm_smul]
      exact
        inv_mul_cancel_right₀ hy.ne.symm δ ▸
          mul_lt_mul_of_pos_right (lt_of_lt_of_le k_norm (min_le_left _ _)) hy
    have h₂ :=
      calc
        ‖p fun _ => k • y‖ ≤ c * ‖k • y‖ ^ (n.succ + 1) := by
          -- porting note: now Lean wants `_root_.`
          simpa only [norm_pow, _root_.norm_norm] using ht (k • y) (δε (mem_ball_zero_iff.mpr h₁))
          --simpa only [norm_pow, norm_norm] using ht (k • y) (δε (mem_ball_zero_iff.mpr h₁))
        _ = ‖k‖ ^ n.succ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1))) := by
          -- porting note: added `Nat.succ_eq_add_one` since otherwise `ring` does not conclude.
          simp only [norm_smul, mul_pow, Nat.succ_eq_add_one]
          --  porting note: removed `rw [pow_succ]`, since it now becomes superfluous.
          ring

    have h₃ : ‖k‖ * (c * ‖y‖ ^ (n.succ + 1)) < ε :=
      inv_mul_cancel_right₀ h₀.ne.symm ε ▸
        mul_lt_mul_of_pos_right (lt_of_lt_of_le k_norm (min_le_right _ _)) h₀
    calc
      ‖p fun _ => y‖ = ‖k⁻¹ ^ n.succ‖ * ‖p fun _ => k • y‖ := by
        simpa only [inv_smul_smul₀ (norm_pos_iff.mp k_pos), norm_smul, Finset.prod_const,
          Finset.card_fin] using
          congr_arg norm (p.map_smul_univ (fun _ : Fin n.succ => k⁻¹) fun _ : Fin n.succ => k • y)
      _ ≤ ‖k⁻¹ ^ n.succ‖ * (‖k‖ ^ n.succ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1)))) :=
        (mul_le_mul_of_nonneg_left h₂ (norm_nonneg _))
      _ = ‖(k⁻¹ * k) ^ n.succ‖ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1))) := by
        rw [← mul_assoc]
        simp [norm_mul, mul_pow]
      _ ≤ 0 + ε := by
        rw [inv_mul_cancel (norm_pos_iff.mp k_pos)]
        simpa using h₃.le
set_option linter.uppercaseLean3 false in
#align asymptotics.is_O.continuous_multilinear_map_apply_eq_zero Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero

/-- If a formal multilinear series `p` represents the zero function at `x : E`, then the
terms `p n (λ i, y)` appearing the in sum are zero for any `n : ℕ`, `y : E`. -/
theorem HasFpowerSeriesAt.apply_eq_zero {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (h : HasFpowerSeriesAt 0 p x) (n : ℕ) : ∀ y : E, (p n fun _ => y) = 0 := by
  refine' Nat.strong_induction_on n fun k hk => _
  have psum_eq : p.partialSum (k + 1) = fun y => p k fun _ => y := by
    funext z
    refine' Finset.sum_eq_single _ (fun b hb hnb => _) fun hn => _
    · have := Finset.mem_range_succ_iff.mp hb
      simp only [hk b (this.lt_of_ne hnb), Pi.zero_apply]
    · exact False.elim (hn (Finset.mem_range.mpr (lt_add_one k)))
  replace h := h.isBigO_sub_partialSum_pow k.succ
  simp only [psum_eq, zero_sub, Pi.zero_apply, Asymptotics.isBigO_neg_left] at h
  exact h.continuousMultilinearMap_apply_eq_zero
#align has_fpower_series_at.apply_eq_zero HasFpowerSeriesAt.apply_eq_zero

/-- A one-dimensional formal multilinear series representing the zero function is zero. -/
theorem HasFpowerSeriesAt.eq_zero {p : FormalMultilinearSeries 𝕜 𝕜 E} {x : 𝕜}
    (h : HasFpowerSeriesAt 0 p x) : p = 0 := by
  -- porting note: `funext ; ext` was `ext (n x)`
  funext n
  ext x
  rw [← mkPiField_apply_one_eq_self (p n)]
  -- porting note: nasty hack, was `simp [h.apply_eq_zero n 1]`
  have := Or.intro_right ?_ (h.apply_eq_zero n 1)
  simpa using this
#align has_fpower_series_at.eq_zero HasFpowerSeriesAt.eq_zero

/-- One-dimensional formal multilinear series representing the same function are equal. -/
theorem HasFpowerSeriesAt.eq_formalMultilinearSeries {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E}
    {f : 𝕜 → E} {x : 𝕜} (h₁ : HasFpowerSeriesAt f p₁ x) (h₂ : HasFpowerSeriesAt f p₂ x) : p₁ = p₂ :=
  sub_eq_zero.mp (HasFpowerSeriesAt.eq_zero (by simpa only [sub_self] using h₁.sub h₂))
#align has_fpower_series_at.eq_formal_multilinear_series HasFpowerSeriesAt.eq_formalMultilinearSeries

theorem HasFpowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {x : 𝕜} (hp : HasFpowerSeriesAt f p x)
    (hq : HasFpowerSeriesAt g q x) (heq : ∀ᶠ z in 𝓝 x, f z = g z) : p = q :=
  (hp.congr heq).eq_formalMultilinearSeries hq
#align has_fpower_series_at.eq_formal_multilinear_series_of_eventually HasFpowerSeriesAt.eq_formalMultilinearSeries_of_eventually

/-- A one-dimensional formal multilinear series representing a locally zero function is zero. -/
theorem HasFpowerSeriesAt.eq_zero_of_eventually {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E}
    {x : 𝕜} (hp : HasFpowerSeriesAt f p x) (hf : f =ᶠ[𝓝 x] 0) : p = 0 :=
  (hp.congr hf).eq_zero
#align has_fpower_series_at.eq_zero_of_eventually HasFpowerSeriesAt.eq_zero_of_eventually

/-- If a function `f : 𝕜 → E` has two power series representations at `x`, then the given radii in
which convergence is guaranteed may be interchanged. This can be useful when the formal multilinear
series in one representation has a particularly nice form, but the other has a larger radius. -/
theorem HasFpowerSeriesOnBall.exchangeRadius {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E}
    {r₁ r₂ : ℝ≥0∞} {x : 𝕜} (h₁ : HasFpowerSeriesOnBall f p₁ x r₁)
    (h₂ : HasFpowerSeriesOnBall f p₂ x r₂) : HasFpowerSeriesOnBall f p₁ x r₂ :=
  h₂.hasFpowerSeriesAt.eq_formalMultilinearSeries h₁.hasFpowerSeriesAt ▸ h₂
#align has_fpower_series_on_ball.exchange_radius HasFpowerSeriesOnBall.exchangeRadius

/-- If a function `f : 𝕜 → E` has power series representation `p` on a ball of some radius and for
each positive radius it has some power series representation, then `p` converges to `f` on the whole
`𝕜`. -/
theorem HasFpowerSeriesOnBall.rEqTopOfExists {f : 𝕜 → E} {r : ℝ≥0∞} {x : 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 E} (h : HasFpowerSeriesOnBall f p x r)
    (h' :
      ∀ (r' : ℝ≥0) (_ : 0 < r'),
        ∃ p' : FormalMultilinearSeries 𝕜 𝕜 E, HasFpowerSeriesOnBall f p' x r') :
    HasFpowerSeriesOnBall f p x ∞ :=
  { r_le :=
      ENNReal.le_of_forall_pos_nnreal_lt fun r hr _ =>
        let ⟨_, hp'⟩ := h' r hr
        (h.exchangeRadius hp').r_le
    r_pos := ENNReal.coe_lt_top
    hasSum := fun {y} _ =>
      let ⟨r', hr'⟩ := exists_gt ‖y‖₊
      let ⟨_, hp'⟩ := h' r' hr'.ne_bot.bot_lt
      (h.exchangeRadius hp').hasSum <| mem_emetric_ball_zero_iff.mpr (ENNReal.coe_lt_coe.2 hr') }
#align has_fpower_series_on_ball.r_eq_top_of_exists HasFpowerSeriesOnBall.rEqTopOfExists

end Uniqueness

/-!
### Changing origin in a power series

If a function is analytic in a disk `D(x, R)`, then it is analytic in any disk contained in that
one. Indeed, one can write
$$
f (x + y + z) = \sum_{n} p_n (y + z)^n = \sum_{n, k} \binom{n}{k} p_n y^{n-k} z^k
= \sum_{k} \Bigl(\sum_{n} \binom{n}{k} p_n y^{n-k}\Bigr) z^k.
$$
The corresponding power series has thus a `k`-th coefficient equal to
$\sum_{n} \binom{n}{k} p_n y^{n-k}$. In the general case where `pₙ` is a multilinear map, this has
to be interpreted suitably: instead of having a binomial coefficient, one should sum over all
possible subsets `s` of `fin n` of cardinal `k`, and attribute `z` to the indices in `s` and
`y` to the indices outside of `s`.

In this paragraph, we implement this. The new power series is called `p.change_origin y`. Then, we
check its convergence and the fact that its sum coincides with the original sum. The outcome of this
discussion is that the set of points where a function is analytic is open.
-/


namespace FormalMultilinearSeries

section

variable (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r R : ℝ≥0}

/-- A term of `formal_multilinear_series.change_origin_series`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.change_origin x` is a formal multilinear series such that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense. Each term of `p.change_origin x`
is itself an analytic function of `x` given by the series `p.change_origin_series`. Each term in
`change_origin_series` is the sum of `change_origin_series_term`'s over all `s` of cardinality `l`.
The definition is such that
`p.changeOriginSeriesTerm k l s hs (λ _, x) (λ _, y) = p (k + l) (s.piecewise (λ _, x) (λ _, y))`
-/
def changeOriginSeriesTerm (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    E[×l]→L[𝕜] E[×k]→L[𝕜] F :=
  by let k := p ; sorry <;> exact
  ContinuousMultilinearMap.curryFinFinset 𝕜 E F hs
  --  (by erw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right]) (p <| k + l)
#align formal_multilinear_series.change_origin_series_term FormalMultilinearSeries.changeOriginSeriesTerm

theorem changeOriginSeriesTerm_apply (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l)
    (x y : E) :
    (p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ => y) =
      p (k + l) (s.piecewise (fun _ => x) fun _ => y) :=
  sorry --ContinuousMultilinearMap.curryFinFinset_apply_const _ _ _ _ _
#align formal_multilinear_series.change_origin_series_term_apply FormalMultilinearSeries.changeOriginSeriesTerm_apply

@[simp]
theorem norm_changeOriginSeriesTerm (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    ‖p.changeOriginSeriesTerm k l s hs‖ = ‖p (k + l)‖ := by
  sorry -- simp only [changeOriginSeriesTerm, LinearIsometryEquiv.norm_map]
#align formal_multilinear_series.norm_change_origin_series_term FormalMultilinearSeries.norm_changeOriginSeriesTerm

@[simp]
theorem nnnorm_changeOriginSeriesTerm (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    ‖p.changeOriginSeriesTerm k l s hs‖₊ = ‖p (k + l)‖₊ := by
  sorry -- simp only [changeOriginSeriesTerm, LinearIsometryEquiv.nnnorm_map]
#align formal_multilinear_series.nnnorm_change_origin_series_term FormalMultilinearSeries.nnnorm_changeOriginSeriesTerm

theorem nnnorm_changeOriginSeriesTerm_apply_le (k l : ℕ) (s : Finset (Fin (k + l)))
    (hs : s.card = l) (x y : E) :
    ‖p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ => y‖₊ ≤
      ‖p (k + l)‖₊ * ‖x‖₊ ^ l * ‖y‖₊ ^ k := by
  rw [← p.nnnorm_changeOriginSeriesTerm k l s hs, ← Fin.prod_const, ← Fin.prod_const]
  apply ContinuousMultilinearMap.le_of_op_nnnorm_le
  apply ContinuousMultilinearMap.le_op_nnnorm
#align formal_multilinear_series.nnnorm_change_origin_series_term_apply_le FormalMultilinearSeries.nnnorm_changeOriginSeriesTerm_apply_le

/-- The power series for `f.change_origin k`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.change_origin x` is a formal multilinear series such that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense. Its `k`-th term is the sum of
the series `p.change_origin_series k`. -/
def changeOriginSeries (k : ℕ) : FormalMultilinearSeries 𝕜 E (E[×k]→L[𝕜] F) := fun l =>
  ∑ s : { s : Finset (Fin (k + l)) // Finset.card s = l }, p.changeOriginSeriesTerm k l s s.2
#align formal_multilinear_series.change_origin_series FormalMultilinearSeries.changeOriginSeries

theorem nnnorm_changeOriginSeries_le_tsum (k l : ℕ) :
    ‖p.changeOriginSeries k l‖₊ ≤ ∑' x : { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + l)‖₊ :=
  by sorry --(nnnorm_sum_le _ _).trans_eq <| by simp only [tsum_fintype, nnnorm_changeOriginSeriesTerm]
#align formal_multilinear_series.nnnorm_change_origin_series_le_tsum FormalMultilinearSeries.nnnorm_changeOriginSeries_le_tsum

theorem nnnorm_changeOriginSeries_apply_le_tsum (k l : ℕ) (x : E) :
    ‖p.changeOriginSeries k l fun _ => x‖₊ ≤
      ∑' _s : { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + l)‖₊ * ‖x‖₊ ^ l := by
  rw [NNReal.tsum_mul_right, ← Fin.prod_const]
  exact
    (p.changeOriginSeries k l).le_of_op_nnnorm_le _ (p.nnnorm_changeOriginSeries_le_tsum _ _)
#align formal_multilinear_series.nnnorm_change_origin_series_apply_le_tsum FormalMultilinearSeries.nnnorm_changeOriginSeries_apply_le_tsum

/-- Changing the origin of a formal multilinear series `p`, so that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense.
-/
def changeOrigin (x : E) : FormalMultilinearSeries 𝕜 E F := fun k => (p.changeOriginSeries k).sum x
#align formal_multilinear_series.change_origin FormalMultilinearSeries.changeOrigin

/-- An auxiliary equivalence useful in the proofs about
`formal_multilinear_series.change_origin_series`: the set of triples `(k, l, s)`, where `s` is a
`finset (fin (k + l))` of cardinality `l` is equivalent to the set of pairs `(n, s)`, where `s` is a
`finset (fin n)`.

The forward map sends `(k, l, s)` to `(k + l, s)` and the inverse map sends `(n, s)` to
`(n - finset.card s, finset.card s, s)`. The actual definition is less readable because of problems
with non-definitional equalities. -/
@[simps]
def changeOriginIndexEquiv :
    (Σk l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) ≃ Σn : ℕ, Finset (Fin n) where
  toFun s := ⟨s.1 + s.2.1, s.2.2⟩
  invFun s :=
    ⟨s.1 - s.2.card, s.2.card,
      ⟨s.2.map
          (Fin.cast <| (tsub_add_cancel_of_le <| card_finset_fin_le s.2).symm).toEquiv.toEmbedding,
        Finset.card_map _⟩⟩
  left_inv := by
    rintro ⟨k, l, ⟨s : Finset (Fin <| k + l), hs : s.card = l⟩⟩
    dsimp only [Subtype.coe_mk]
    -- Lean can't automatically generalize `k' = k + l - s.card`, `l' = s.card`, so we explicitly
    -- formulate the generalized goal
    suffices
      ∀ k' l',
        k' = k →
          l' = l →
            ∀ (hkl : k + l = k' + l') (hs'),
              (⟨k', l', ⟨Finset.map (Fin.cast hkl).toEquiv.toEmbedding s, hs'⟩⟩ :
                  Σk l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) =
                ⟨k, l, ⟨s, hs⟩⟩
      by apply this <;> simp only [hs, add_tsub_cancel_right]
    rintro _ _ rfl rfl hkl hs'
    simp only [Equiv.refl_toEmbedding, Fin.cast_refl, Finset.map_refl, eq_self_iff_true,
      OrderIso.refl_toEquiv, and_self_iff, heq_iff_eq]
  right_inv := by
    rintro ⟨n, s⟩
    simp [tsub_add_cancel_of_le (card_finset_fin_le s), Fin.cast_to_equiv]
#align formal_multilinear_series.change_origin_index_equiv FormalMultilinearSeries.changeOriginIndexEquiv

theorem changeOriginSeries_summable_aux₁ {r r' : ℝ≥0} (hr : (r + r' : ℝ≥0∞) < p.radius) :
    Summable fun s : Σk l : ℕ, { s : Finset (Fin (k + l)) // s.card = l } =>
      ‖p (s.1 + s.2.1)‖₊ * r ^ s.2.1 * r' ^ s.1 := by
  rw [← changeOriginIndexEquiv.symm.summable_iff]
  dsimp only [(· ∘ ·), changeOriginIndexEquiv_symm_apply_fst,
    changeOriginIndexEquiv_symm_apply_snd_fst]
  have :
    ∀ n : ℕ,
      HasSum (fun s : Finset (Fin n) => ‖p (n - s.card + s.card)‖₊ * r ^ s.card * r' ^ (n - s.card))
        (‖p n‖₊ * (r + r') ^ n) := by
    intro n
    -- TODO: why `simp only [tsub_add_cancel_of_le (card_finset_fin_le _)]` fails?
    convert_to HasSum (fun s : Finset (Fin n) => ‖p n‖₊ * (r ^ s.card * r' ^ (n - s.card))) _
    · ext1 s
      rw [tsub_add_cancel_of_le (card_finset_fin_le _), mul_assoc]
    rw [← Fin.sum_pow_mul_eq_add_pow]
    exact (hasSum_fintype _).mul_left _
  refine' NNReal.summable_sigma.2 ⟨fun n => (this n).summable, _⟩
  simp only [(this _).tsum_eq]
  exact p.summable_nnnorm_mul_pow hr
#align formal_multilinear_series.change_origin_series_summable_aux₁ FormalMultilinearSeries.changeOriginSeries_summable_aux₁

theorem changeOriginSeries_summable_aux₂ (hr : (r : ℝ≥0∞) < p.radius) (k : ℕ) :
    Summable fun s : Σl : ℕ, { s : Finset (Fin (k + l)) // s.card = l } =>
      ‖p (k + s.1)‖₊ * r ^ s.1 := by
  rcases ENNReal.lt_iff_exists_add_pos_lt.1 hr with ⟨r', h0, hr'⟩
  simpa only [mul_inv_cancel_right₀ (pow_pos h0 _).ne'] using
    ((NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr')).1 k).mul_right (r' ^ k)⁻¹
#align formal_multilinear_series.change_origin_series_summable_aux₂ FormalMultilinearSeries.changeOriginSeries_summable_aux₂

theorem changeOriginSeries_summable_aux₃ {r : ℝ≥0} (hr : ↑r < p.radius) (k : ℕ) :
    Summable fun l : ℕ => ‖p.changeOriginSeries k l‖₊ * r ^ l := by
  refine'
    NNReal.summable_of_le (fun n => _)
      (NNReal.summable_sigma.1 <| p.changeOriginSeries_summable_aux₂ hr k).2
  simp only [NNReal.tsum_mul_right]
  exact mul_le_mul' (p.nnnorm_changeOriginSeries_le_tsum _ _) le_rfl
#align formal_multilinear_series.change_origin_series_summable_aux₃ FormalMultilinearSeries.changeOriginSeries_summable_aux₃

theorem le_changeOriginSeries_radius (k : ℕ) : p.radius ≤ (p.changeOriginSeries k).radius :=
  ENNReal.le_of_forall_nnreal_lt fun _r hr =>
    le_radius_of_summable_nnnorm _ (p.changeOriginSeries_summable_aux₃ hr k)
#align formal_multilinear_series.le_change_origin_series_radius FormalMultilinearSeries.le_changeOriginSeries_radius

theorem nnnorm_changeOrigin_le (k : ℕ) (h : (‖x‖₊ : ℝ≥0∞) < p.radius) :
    ‖p.changeOrigin x k‖₊ ≤
      ∑' s : Σl : ℕ, { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1 := by
  refine' tsum_of_nnnorm_bounded _ fun l => p.nnnorm_changeOriginSeries_apply_le_tsum k l x
  have := p.changeOriginSeries_summable_aux₂ h k
  refine' HasSum.sigma this.hasSum fun l => _
  exact ((NNReal.summable_sigma.1 this).1 l).hasSum
#align formal_multilinear_series.nnnorm_change_origin_le FormalMultilinearSeries.nnnorm_changeOrigin_le

/-- The radius of convergence of `p.change_origin x` is at least `p.radius - ‖x‖`. In other words,
`p.change_origin x` is well defined on the largest ball contained in the original ball of
convergence.-/
theorem changeOrigin_radius : p.radius - ‖x‖₊ ≤ (p.changeOrigin x).radius := by
  refine' ENNReal.le_of_forall_pos_nnreal_lt fun r _h0 hr => _
  rw [lt_tsub_iff_right, add_comm] at hr
  have hr' : (‖x‖₊ : ℝ≥0∞) < p.radius := (le_add_right le_rfl).trans_lt hr
  apply le_radius_of_summable_nnnorm
  have :
    ∀ k : ℕ,
      ‖p.changeOrigin x k‖₊ * r ^ k ≤
        (∑' s : Σl : ℕ, { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1) *
          r ^ k :=
    fun k => mul_le_mul_right' (p.nnnorm_changeOrigin_le k hr') (r ^ k)
  refine' NNReal.summable_of_le this _
  simpa only [← NNReal.tsum_mul_right] using
    (NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr)).2
#align formal_multilinear_series.change_origin_radius FormalMultilinearSeries.changeOrigin_radius

end

-- From this point on, assume that the space is complete, to make sure that series that converge
-- in norm also converge in `F`.
variable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r R : ℝ≥0}

theorem hasFpowerSeriesOnBallChangeOrigin (k : ℕ) (hr : 0 < p.radius) :
    HasFpowerSeriesOnBall (fun x => p.changeOrigin x k) (p.changeOriginSeries k) 0 p.radius :=
  have := p.le_changeOriginSeries_radius k
  ((p.changeOriginSeries k).hasFpowerSeriesOnBall (hr.trans_le this)).mono hr this
#align formal_multilinear_series.has_fpower_series_on_ball_change_origin FormalMultilinearSeries.hasFpowerSeriesOnBallChangeOrigin

/-- Summing the series `p.change_origin x` at a point `y` gives back `p (x + y)`-/
theorem changeOrigin_eval (h : (‖x‖₊ + ‖y‖₊ : ℝ≥0∞) < p.radius) :
    (p.changeOrigin x).sum y = p.sum (x + y) := by
  have radius_pos : 0 < p.radius := lt_of_le_of_lt (zero_le _) h
  have x_mem_ball : x ∈ EMetric.ball (0 : E) p.radius :=
    mem_emetric_ball_zero_iff.2 ((le_add_right le_rfl).trans_lt h)
  have y_mem_ball : y ∈ EMetric.ball (0 : E) (p.changeOrigin x).radius := by
    refine' mem_emetric_ball_zero_iff.2 (lt_of_lt_of_le _ p.changeOrigin_radius)
    rwa [lt_tsub_iff_right, add_comm]
  have x_add_y_mem_ball : x + y ∈ EMetric.ball (0 : E) p.radius := by
    refine' mem_emetric_ball_zero_iff.2 (lt_of_le_of_lt _ h)
    exact_mod_cast nnnorm_add_le x y
  set f : (Σk l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) → F := fun s =>
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) fun _ => y
  have hsf : Summable f := by
    refine' summable_of_nnnorm_bounded _ (p.changeOriginSeries_summable_aux₁ h) _
    rintro ⟨k, l, s, hs⟩
    dsimp only [Subtype.coe_mk]
    exact p.nnnorm_changeOriginSeriesTerm_apply_le _ _ _ _ _ _
  have hf : HasSum f ((p.changeOrigin x).sum y) := by
    refine' HasSum.sigma_of_hasSum ((p.changeOrigin x).summable y_mem_ball).hasSum (fun k => _) hsf
    · dsimp only --[f]
      refine' ContinuousMultilinearMap.hasSum_eval _ _
      have := (p.hasFpowerSeriesOnBallChangeOrigin k radius_pos).hasSum x_mem_ball
      rw [zero_add] at this
      refine' HasSum.sigma_of_hasSum this (fun l => _) _
      · simp only [changeOriginSeries, ContinuousMultilinearMap.sum_apply]
        apply hasSum_fintype
      · refine'
          summable_of_nnnorm_bounded _
            (p.changeOriginSeries_summable_aux₂ (mem_emetric_ball_zero_iff.1 x_mem_ball) k)
            fun s => _
        refine' (ContinuousMultilinearMap.le_op_nnnorm _ _).trans_eq _
        simp
  refine' hf.unique (changeOriginIndexEquiv.symm.hasSum_iff.1 _)
  refine'
    HasSum.sigma_of_hasSum (p.hasSum x_add_y_mem_ball) (fun n => _)
      (changeOriginIndexEquiv.symm.summable_iff.2 hsf)
  erw [(p n).map_add_univ (fun _ => x) fun _ => y]
  -- porting note: added explicit function
  convert hasSum_fintype (fun c : Finset (Fin n) => f (changeOriginIndexEquiv.symm ⟨n, c⟩))
  --ext1 s
  dsimp only [changeOriginSeriesTerm, (· ∘ ·), changeOriginIndexEquiv_symm_apply_fst,
    changeOriginIndexEquiv_symm_apply_snd_fst, changeOriginIndexEquiv_symm_apply_snd_snd_coe]
  dsimp
  rw [ContinuousMultilinearMap.curryFinFinset_apply_const]
  have :
    ∀ (m) (hm : n = m),
      p n (s.piecewise (fun _ => x) fun _ => y) =
        p m ((s.map (Fin.cast hm).toEquiv.toEmbedding).piecewise (fun _ => x) fun _ => y) := by
    rintro m rfl
    simp
  apply this
#align formal_multilinear_series.change_origin_eval FormalMultilinearSeries.changeOrigin_eval

end FormalMultilinearSeries

section

variable [CompleteSpace F] {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x y : E} {r : ℝ≥0∞}

/-- If a function admits a power series expansion `p` on a ball `B (x, r)`, then it also admits a
power series on any subball of this ball (even with a different center), given by `p.change_origin`.
-/
theorem HasFpowerSeriesOnBall.changeOrigin (hf : HasFpowerSeriesOnBall f p x r)
    (h : (‖y‖₊ : ℝ≥0∞) < r) : HasFpowerSeriesOnBall f (p.changeOrigin y) (x + y) (r - ‖y‖₊) :=
  { r_le := by
      apply le_trans _ p.changeOrigin_radius
      exact tsub_le_tsub hf.r_le le_rfl
    r_pos := by simp [h]
    hasSum := fun z hz => by
      convert(p.changeOrigin y).hasSum _
      · rw [mem_emetric_ball_zero_iff, lt_tsub_iff_right, add_comm] at hz
        rw [p.change_origin_eval (hz.trans_le hf.r_le), add_assoc, hf.sum]
        refine' mem_emetric_ball_zero_iff.2 (lt_of_le_of_lt _ hz)
        exact_mod_cast nnnorm_add_le y z
      · refine' EMetric.ball_subset_ball (le_trans _ p.changeOrigin_radius) hz
        exact tsub_le_tsub hf.r_le le_rfl }
#align has_fpower_series_on_ball.change_origin HasFpowerSeriesOnBall.changeOrigin

/-- If a function admits a power series expansion `p` on an open ball `B (x, r)`, then
it is analytic at every point of this ball. -/
theorem HasFpowerSeriesOnBall.analyticAt_of_mem (hf : HasFpowerSeriesOnBall f p x r)
    (h : y ∈ EMetric.ball x r) : AnalyticAt 𝕜 f y := by
  have : (‖y - x‖₊ : ℝ≥0∞) < r := by simpa [edist_eq_coe_nnnorm_sub] using h
  have := hf.changeOrigin this
  rw [add_sub_cancel'_right] at this
  exact this.analyticAt
#align has_fpower_series_on_ball.analytic_at_of_mem HasFpowerSeriesOnBall.analyticAt_of_mem

theorem HasFpowerSeriesOnBall.analyticOn (hf : HasFpowerSeriesOnBall f p x r) :
    AnalyticOn 𝕜 f (EMetric.ball x r) := fun _y hy => hf.analyticAt_of_mem hy
#align has_fpower_series_on_ball.analytic_on HasFpowerSeriesOnBall.analyticOn

variable (𝕜 f)

/-- For any function `f` from a normed vector space to a Banach space, the set of points `x` such
that `f` is analytic at `x` is open. -/
theorem isOpen_analyticAt : IsOpen { x | AnalyticAt 𝕜 f x } := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, r, hr⟩
  exact mem_of_superset (EMetric.ball_mem_nhds _ hr.r_pos) fun y hy => hr.analyticAt_of_mem hy
#align is_open_analytic_at isOpen_analyticAt

end

section

open FormalMultilinearSeries

variable {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E} {z₀ : 𝕜}

/-- A function `f : 𝕜 → E` has `p` as power series expansion at a point `z₀` iff it is the sum of
`p` in a neighborhood of `z₀`. This makes some proofs easier by hiding the fact that
`has_fpower_series_at` depends on `p.radius`. -/
theorem hasFpowerSeriesAt_iff :
    HasFpowerSeriesAt f p z₀ ↔ ∀ᶠ z in 𝓝 0, HasSum (fun n => z ^ n • p.coeff n) (f (z₀ + z)) := by
  refine'
    ⟨fun ⟨r, r_le, r_pos, h⟩ =>
      eventually_of_mem (EMetric.ball_mem_nhds 0 r_pos) fun _ => by simpa using h, _⟩
  simp only [Metric.eventually_nhds_iff]
  rintro ⟨r, r_pos, h⟩
  refine' ⟨p.radius ⊓ r.toNNReal, by simp, _, _⟩
  · simp only [r_pos.lt, lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos, and_true_iff]
    obtain ⟨z, z_pos, le_z⟩ := NormedField.exists_norm_lt 𝕜 r_pos.lt
    have : (‖z‖₊ : ENNReal) ≤ p.radius := by
      simp only [dist_zero_right] at h
      apply FormalMultilinearSeries.le_radius_of_tendsto
      convert tendsto_norm.comp (h le_z).summable.tendsto_atTop_zero
      funext <;> simp [norm_smul, mul_comm]
    refine' lt_of_lt_of_le _ this
    simp only [ENNReal.coe_pos]
    exact zero_lt_iff.mpr (nnnorm_ne_zero_iff.mpr (norm_pos_iff.mp z_pos))
  · simp only [EMetric.mem_ball, lt_inf_iff, edist_lt_coe, apply_eq_pow_smul_coeff, and_imp,
      dist_zero_right] at h⊢
    refine' fun y hyp hyr => h _
    simpa [nndist_eq_nnnorm, Real.lt_toNNReal_iff_coe_lt] using hyr
#align has_fpower_series_at_iff hasFpowerSeriesAt_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr∀ᶠ in , »((z), (nhds() 0 : filter 𝕜), has_sum (λ n, _) (f «expr + »(z₀, z)))]] -/
theorem hasFpowerSeriesAt_iff' :
    HasFpowerSeriesAt f p z₀ ↔ ∀ᶠ z in 𝓝 z₀, HasSum (fun n => (z - z₀) ^ n • p.coeff n) (f z) := by
  rw [← map_add_left_nhds_zero, eventually_map, hasFpowerSeriesAt_iff]
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr∀ᶠ in , »((z), (nhds() 0 : filter 𝕜), has_sum (λ n, _) (f «expr + »(z₀, z)))]]"
  rw [add_sub_cancel']
#align has_fpower_series_at_iff' hasFpowerSeriesAt_iff'

end
