/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Pringsheim's theorem

A power series `∑ aₙ zⁿ` with nonnegative real coefficients and finite positive radius of
convergence `R` cannot be continued analytically to a neighbourhood of the point `z = R`
(Vivanti–Pringsheim).

## Main results

* `Pringsheim.exists_gt_summable_mul_pow_of_analyticAt`: the theorem in contrapositive form. If
  `aₙ ≥ 0`, `∑ aₙ rⁿ` converges for `0 ≤ r < R`, and the sum on `‖z‖ < R` agrees with a function
  analytic at `R`, then `∑ aₙ rⁿ` converges for some `r > R`.

## Implementation notes

Analyticity at `R` gives a disc `B(R, ε)`. With `e = min ε R` and `t = R − e/4`, the closed disc
`closedBall t (e/2)` lies in `B(R, ε)`, so the Cauchy power series of the continuation at `t`
has radius at least `e/2`. Near `t` the function is also the re-expanded series `∑ₖ cₖ wᵏ` with
`cₖ = ∑ₙ (n choose k) aₙ t^(n−k) ≥ 0` (`hasSum_reexpand`). Uniqueness of power series
identifies the two coefficient sequences, so `∑ cₖ (3e/8)ᵏ < ∞`. The rearrangement in `ℝ≥0∞`
(`reexpand_ennreal`, which needs no convergence hypotheses) turns this into
`∑ aₙ (t + 3e/8)ⁿ < ∞`, where `t + 3e/8 = R + e/8 > R`.
-/

@[expose] public section

open scoped ENNReal NNReal
open Filter Topology

namespace Pringsheim

variable (a : ℕ → ℝ)

/-- The power series sum. -/
private noncomputable def sum (z : ℂ) : ℂ := ∑' n, (a n : ℂ) * z ^ n

/-- Re-expanded coefficients at `t`. -/
private noncomputable def reexpandCoeff (t : ℝ) (k : ℕ) : ℝ :=
    ∑' n, (n.choose k : ℝ) * a n * t ^ (n - k)

/-- Complex re-expansion: for `t ≥ 0`, `t + ‖w‖ < R` with summability below `R`, the series
`∑ₖ cₖ wᵏ` sums to `h (t + w)`. -/
private theorem hasSum_reexpand (ha : ∀ n, 0 ≤ a n) {t : ℝ} (ht : 0 ≤ t) (w : ℂ)
    (hsum : Summable (fun n => a n * (t + ‖w‖) ^ n)) :
    HasSum (fun k => (reexpandCoeff a t k : ℂ) * w ^ k) (sum a (t + w)) := by
  set F : ℕ × ℕ → ℂ := fun p => ((p.1.choose p.2 : ℝ) * a p.1 * t ^ (p.1 - p.2) : ℝ) * w ^ p.2
  have hFn : ∀ p : ℕ × ℕ, ‖F p‖ = (p.1.choose p.2 : ℝ) * a p.1 * t ^ (p.1 - p.2) * ‖w‖ ^ p.2 := by
    intro p
    simp only [F, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (ha p.1), abs_of_nonneg ht, Nat.abs_cast]
  have hrow : ∀ n, HasSum (fun k => F (n, k)) ((a n : ℂ) * (t + w) ^ n) := by
    intro n
    have : (a n : ℂ) * (t + w) ^ n = ∑ k ∈ Finset.range (n + 1), F (n, k) := by
      rw [add_comm (t : ℂ) w, add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [F]; push_cast; ring
    rw [this]
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have : n < k := by simpa using hk
    simp [F, Nat.choose_eq_zero_of_lt this]
  have hrowN : ∀ n, HasSum (fun k => ‖F (n, k)‖) (a n * (t + ‖w‖) ^ n) := by
    intro n
    have : a n * (t + ‖w‖) ^ n = ∑ k ∈ Finset.range (n + 1), ‖F (n, k)‖ := by
      rw [add_comm t, add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [hFn]; ring
    rw [this]
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have : n < k := by simpa using hk
    rw [hFn]; simp [Nat.choose_eq_zero_of_lt this]
  have hFsum : Summable (fun p => ‖F p‖) := by
    rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
    exact ⟨fun n => (hrowN n).summable, by
      simpa [fun n => (hrowN n).tsum_eq] using hsum⟩
  have hF : Summable F := hFsum.of_norm
  have hrowsum : HasSum (fun n => (a n : ℂ) * (t + w) ^ n) (∑' p, F p) := by
    have := hF.hasSum.prod_fiberwise (fun n => (hrow n).summable.hasSum)
    simpa [fun n => (hrow n).tsum_eq] using this
  have htot : ∑' p, F p = sum a (t + w) := by unfold sum; exact hrowsum.tsum_eq.symm
  have hswap : Summable (fun p : ℕ × ℕ => F p.swap) := hF.comp_injective Prod.swap_injective
  have hcol : HasSum (fun k => ∑' n, F (n, k)) (∑' p, F p) := by
    have h1 := hswap.hasSum.prod_fiberwise (fun k => (hswap.prod_factor k).hasSum)
    have e : ∑' p : ℕ × ℕ, F p.swap = ∑' p, F p := (Equiv.prodComm ℕ ℕ).tsum_eq F
    simpa [e] using h1
  rw [htot] at hcol
  refine hcol.congr_fun (fun k => ?_)
  simp only [F, reexpandCoeff]
  rw [Complex.ofReal_tsum, tsum_mul_right]

/-- Inner summability of the re-expanded coefficients below the radius. -/
private theorem summable_inner (ha : ∀ n, 0 ≤ a n) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s)
    (hsum : Summable (fun n => a n * (t + s) ^ n)) (k : ℕ) :
    Summable (fun n => (n.choose k : ℝ) * a n * t ^ (n - k)) := by
  refine Summable.of_nonneg_of_le (fun n => by have := ha n; positivity) (fun n => ?_)
    (hsum.mul_right ((s ^ k)⁻¹))
  by_cases hk : k ≤ n
  · have hterm : (n.choose k : ℝ) * t ^ (n - k) * s ^ k ≤ (t + s) ^ n := by
      rw [add_pow]
      have := Finset.single_le_sum (f := fun m => t ^ m * s ^ (n - m) * (n.choose m : ℝ))
        (fun m _ => by positivity) (Finset.mem_range.mpr (show n - k < n + 1 by omega))
      rw [Nat.choose_symm_of_eq_add (by omega : n = (n - k) + k),
        show n - (n - k) = k by omega] at this
      linarith
    have hsk : 0 < s ^ k := by positivity
    rw [show a n * (t + s) ^ n * (s ^ k)⁻¹ = a n * ((t + s) ^ n / s ^ k) by ring]
    rw [show (n.choose k : ℝ) * a n * t ^ (n - k) = a n * ((n.choose k : ℝ) * t ^ (n - k)) by ring]
    exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hsk).mpr hterm) (ha n)
  · have : n < k := by omega
    rw [Nat.choose_eq_zero_of_lt this, Nat.cast_zero, zero_mul, zero_mul]
    have := ha n; positivity


/-- Re-expansion in `ℝ≥0∞`, no convergence hypotheses. -/
private theorem reexpand_ennreal (A : ℕ → ℝ≥0∞) (T P : ℝ≥0∞) :
    ∑' n, A n * (T + P) ^ n
      = ∑' k, (∑' n, (n.choose k : ℝ≥0∞) * A n * T ^ (n - k)) * P ^ k := by
  have hpow : ∀ n, (T + P) ^ n = ∑' k, (n.choose k : ℝ≥0∞) * T ^ (n - k) * P ^ k := by
    intro n
    rw [add_comm, add_pow]
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl (fun k hk => ?_)
      ring
    · intro k hk
      have : n < k := by simpa using hk
      simp [Nat.choose_eq_zero_of_lt this]
  have e1 : ∀ n, A n * (T + P) ^ n = ∑' k, A n * ((n.choose k : ℝ≥0∞) * T ^ (n - k) * P ^ k) := by
    intro n; rw [hpow, ENNReal.tsum_mul_left]
  simp_rw [e1]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun k => ?_)
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr (fun n => ?_)
  ring

/-- For nonnegative real `f`, finiteness of `∑ ofReal (f n)` gives summability. -/
private theorem summable_of_ofReal_ne_top {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∑' n, ENNReal.ofReal (f n) ≠ ⊤) : Summable f := by
  have h' : ∑' n, ((Real.toNNReal (f n) : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := by simpa [ENNReal.ofReal] using h
  have hs := ENNReal.tsum_coe_ne_top_iff_summable.mp h'
  have := NNReal.summable_coe.mpr hs
  refine this.congr (fun n => ?_)
  simp [Real.coe_toNNReal _ (hf n)]

/-- **Pringsheim's theorem (Vivanti–Pringsheim), contrapositive form.** If `∑ aₙ zⁿ` has nonnegative
coefficients and converges for `0 ≤ r < R`, and the function it defines on `‖z‖ < R` extends
analytically to a neighbourhood of the positive real point `R`, then the series converges at some
`r > R`. Equivalently: a nonnegative power series is singular at the positive point of its circle of
convergence. -/
theorem exists_gt_summable_mul_pow_of_analyticAt (ha : ∀ n, 0 ≤ a n) {R : ℝ} (hR : 0 < R)
    (hconv : ∀ r, 0 ≤ r → r < R → Summable (fun n => a n * r ^ n))
    {g : ℂ → ℂ} (hgR : AnalyticAt ℂ g (R : ℂ))
    (hgh : ∀ z : ℂ, ‖z‖ < R → g z = ∑' n, (a n : ℂ) * z ^ n) :
    ∃ r, R < r ∧ Summable (fun n => a n * r ^ n) := by
  obtain ⟨ε, hε, hg⟩ := hgR.exists_ball_analyticOnNhd
  set e : ℝ := min ε R with he
  have he0 : 0 < e := lt_min hε hR
  have heε : e ≤ ε := min_le_left _ _
  have heR : e ≤ R := min_le_right _ _
  set t : ℝ := R - e / 4 with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; linarith
  set ρ : ℝ≥0 := ⟨e / 2, by positivity⟩ with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; exact_mod_cast (show (0:ℝ) < e / 2 by positivity)
  have hsub : Metric.closedBall (t : ℂ) ρ ⊆ Metric.ball (R : ℂ) ε := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    calc dist z (R : ℂ) ≤ dist z (t : ℂ) + dist (t : ℂ) (R : ℂ) := dist_triangle _ _ _
      _ ≤ e / 2 + e / 4 := by
          refine add_le_add (le_of_le_of_eq hz rfl) ?_
          rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, htdef,
            show R - e / 4 - R = -(e / 4) by ring, abs_neg, abs_of_pos (by positivity)]
      _ < ε := by linarith
  have hdiff : DifferentiableOn ℂ g (Metric.closedBall (t : ℂ) ρ) :=
    fun z hz => (hg z (hsub hz)).differentiableAt.differentiableWithinAt
  have hB := hdiff.hasFPowerSeriesOnBall hρ0
  -- the re-expanded series at `t`
  set q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun k => (reexpandCoeff a t k : ℂ))
  have hc0 : ∀ k, 0 ≤ reexpandCoeff a t k :=
    fun k => tsum_nonneg (fun n => by have := ha n; positivity)
  have hqnorm : ∀ k, ‖q k‖ = reexpandCoeff a t k := by
    intro k
    rw [FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hc0 k)]
  -- convergence of ∑ c_k r^k for 0 ≤ r with t + r < R
  have hcsum : ∀ r : ℝ, 0 ≤ r → t + r < R → Summable (fun k => reexpandCoeff a t k * r ^ k) := by
    intro r hr htr
    have hs := hconv (t + r) (by positivity) htr
    have := hasSum_reexpand a ha ht0 (r : ℂ)
      (by simpa [Complex.norm_real, abs_of_nonneg hr] using hs)
    have h2 : Summable (fun k => ((reexpandCoeff a t k * r ^ k : ℝ) : ℂ)) := by
      refine this.summable.congr (fun k => ?_); push_cast; ring
    exact Complex.summable_ofReal.mp h2
  set r0 : ℝ≥0 := ⟨e / 8, by positivity⟩ with hr0
  have hq : HasFPowerSeriesAt g q (t : ℂ) := by
    refine ⟨(r0 : ℝ≥0∞), ?_⟩
    refine
      { r_le := ?_
        r_pos := by
          have h8 : (0 : ℝ) < e / 8 := by positivity
          exact ENNReal.coe_pos.mpr (by rw [hr0]; exact h8)
        hasSum := ?_ }
    · refine q.le_radius_of_summable_norm ?_
      have := hcsum (e / 8) (by positivity) (by rw [htdef]; linarith)
      refine this.congr (fun k => ?_)
      rw [hqnorm]; rfl
    · intro y hy
      have h1 : ‖y‖ < (r0 : ℝ) := by
        simpa [Metric.mem_eball, edist_zero_right, enorm, ENNReal.coe_lt_coe] using hy
      have hy' : ‖y‖ < e / 8 := lt_of_lt_of_eq h1 rfl
      rw [FormalMultilinearSeries.ofScalars_apply_eq']
      have hs := hconv (t + ‖y‖) (by positivity) (by rw [htdef]; linarith)
      have hre := hasSum_reexpand a ha ht0 y hs
      have hgy : g ((t : ℂ) + y) = sum a ((t : ℂ) + y) := by
        apply hgh
        calc ‖(t : ℂ) + y‖ ≤ ‖(t : ℂ)‖ + ‖y‖ := norm_add_le _ _
          _ = t + ‖y‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
          _ < R := by rw [htdef]; linarith
      rw [hgy]
      simpa [smul_eq_mul] using hre
  have heq : cauchyPowerSeries g (t : ℂ) ρ = q := hB.hasFPowerSeriesAt.eq_formalMultilinearSeries hq
  have hrad : (ρ : ℝ≥0∞) ≤ q.radius := heq ▸ hB.r_le
  set r1 : ℝ≥0 := ⟨3 * e / 8, by positivity⟩ with hr1
  have hr1lt : (r1 : ℝ≥0∞) < q.radius := by
    refine lt_of_lt_of_le ?_ hrad
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hr1, hρ]
    change 3 * e / 8 < e / 2
    linarith
  have hsum1 : Summable (fun k => reexpandCoeff a t k * (3 * e / 8) ^ k) := by
    have := q.summable_norm_mul_pow hr1lt
    refine this.congr (fun k => ?_)
    rw [hqnorm]; rfl
  -- back to the original series at t + 3e/8 > R
  refine ⟨t + 3 * e / 8, by rw [htdef]; linarith, ?_⟩
  have hinner : ∀ k, ∑' n, (n.choose k : ℝ≥0∞) * ENNReal.ofReal (a n) * ENNReal.ofReal t ^ (n - k)
      = ENNReal.ofReal (reexpandCoeff a t k) := by
    intro k
    have hs := summable_inner a ha ht0 (s := e / 8) (by positivity)
      (hconv (t + e / 8) (by positivity) (by rw [htdef]; linarith)) k
    rw [reexpandCoeff, ENNReal.ofReal_tsum_of_nonneg (fun n => by have := ha n; positivity) hs]
    refine tsum_congr (fun n => ?_)
    rw [ENNReal.ofReal_mul (by have := ha n; positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow ht0, ENNReal.ofReal_natCast]
  have hkey := reexpand_ennreal (fun n => ENNReal.ofReal (a n)) (ENNReal.ofReal t)
    (ENNReal.ofReal (3 * e / 8))
  simp_rw [hinner] at hkey
  have hR' : ∑' k, ENNReal.ofReal (reexpandCoeff a t k) * ENNReal.ofReal (3 * e / 8) ^ k ≠ ⊤ := by
    have : ∑' k, ENNReal.ofReal (reexpandCoeff a t k) * ENNReal.ofReal (3 * e / 8) ^ k
        = ENNReal.ofReal (∑' k, reexpandCoeff a t k * (3 * e / 8) ^ k) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by have := hc0 k; positivity) hsum1]
      refine tsum_congr (fun k => ?_)
      rw [ENNReal.ofReal_mul (hc0 k), ENNReal.ofReal_pow (by positivity)]
    rw [this]; exact ENNReal.ofReal_ne_top
  rw [← hkey] at hR'
  refine summable_of_ofReal_ne_top (fun n => by have := ha n; positivity) ?_
  refine ne_of_eq_of_ne (tsum_congr (fun n => ?_)) hR'
  rw [ENNReal.ofReal_mul (ha n), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add ht0 (by positivity)]

end Pringsheim
