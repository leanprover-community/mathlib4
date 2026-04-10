/-
Copyright (c) 2025 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Absolutely Monotone Functions

A function `f : ℝ → ℝ` is absolutely monotone on a set `s` if it is smooth
on `s` and all its iterated derivatives within `s` are nonneg on `s`.

## Main definitions

* `AbsolutelyMonotoneOn` — smooth on `s` with nonneg iterated derivatives within `s`

## Main results

* Closure under `add`, `smul`, `mul`
* `absolutelyMonotoneOn_exp`, `absolutelyMonotoneOn_cosh`, `absolutelyMonotoneOn_pow`
* `absolutelyMonotoneOn_of_nonneg_coeffs` — Bernstein backward direction:
  a convergent power series with nonneg coefficients is absolutely monotone
* `analyticWithinAt_zero_of_nonneg_iteratedDerivWithin` — Bernstein forward direction:
  a smooth function with nonneg iterated derivatives on a convex set containing 0 is
  real-analytic at 0 (within the set)

## References

* Widder, D.V. (1941). *The Laplace Transform*.
-/

public section

open Set Filter
open scoped ENNReal NNReal Topology ContDiff

/-- A function `f : ℝ → ℝ` is absolutely monotone on a set `s` if it is
smooth on `s` and all iterated derivatives within `s` are nonneg. -/
structure AbsolutelyMonotoneOn (f : ℝ → ℝ) (s : Set ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ ∞ f s
  nonneg : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDerivWithin n f s x

namespace AbsolutelyMonotoneOn

/-- Constructor from global `ContDiff` and global `iteratedDeriv`.
Works for any `UniqueDiffOn` set (includes open sets, `Ici a`,
convex sets with nonempty interior, etc.). -/
theorem of_contDiff {f : ℝ → ℝ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s)
    (hf : ContDiff ℝ ∞ f)
    (h : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDeriv n f x) :
    AbsolutelyMonotoneOn f s where
  contDiffOn := hf.contDiffOn
  nonneg n x hx := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs
      (hf.contDiffAt.of_le (by exact_mod_cast le_top)) hx]
    exact h n x hx

/-- Nonneg Taylor coefficients at any point in `s`. -/
theorem nonneg_taylor_coeffs {f : ℝ → ℝ} {s : Set ℝ}
    (hf : AbsolutelyMonotoneOn f s) {x : ℝ} (hx : x ∈ s)
    (n : ℕ) :
    0 ≤ iteratedDerivWithin n f s x / (n.factorial : ℝ) :=
  div_nonneg (hf.nonneg n x hx) (Nat.cast_nonneg _)

/-! ### Basic closure properties -/

theorem add {f g : ℝ → ℝ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hf : AbsolutelyMonotoneOn f s) (hg : AbsolutelyMonotoneOn g s) :
    AbsolutelyMonotoneOn (f + g) s where
  contDiffOn := hf.contDiffOn.add hg.contDiffOn
  nonneg n x hx := by
    rw [iteratedDerivWithin_add hx hs
      ((hf.contDiffOn x hx).of_le (by exact_mod_cast le_top))
      ((hg.contDiffOn x hx).of_le (by exact_mod_cast le_top))]
    exact add_nonneg (hf.nonneg n x hx) (hg.nonneg n x hx)

theorem smul {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ}
    (hf : AbsolutelyMonotoneOn f s) (hc : 0 ≤ c) :
    AbsolutelyMonotoneOn (c • f) s where
  contDiffOn := hf.contDiffOn.const_smul c
  nonneg n x hx := by
    rw [iteratedDerivWithin_const_smul_field c f]
    exact smul_nonneg hc (hf.nonneg n x hx)

theorem mul {f g : ℝ → ℝ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hf : AbsolutelyMonotoneOn f s) (hg : AbsolutelyMonotoneOn g s) :
    AbsolutelyMonotoneOn (f * g) s where
  contDiffOn := hf.contDiffOn.mul hg.contDiffOn
  nonneg n x hx := by
    rw [iteratedDerivWithin_mul hx hs
      ((hf.contDiffOn x hx).of_le (by exact_mod_cast le_top))
      ((hg.contDiffOn x hx).of_le (by exact_mod_cast le_top))]
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (hf.nonneg i x hx)
    · exact hg.nonneg (n - i) x hx

end AbsolutelyMonotoneOn

/-! ### Examples -/

theorem absolutelyMonotoneOn_exp (s : Set ℝ) (hs : UniqueDiffOn ℝ s) :
    AbsolutelyMonotoneOn Real.exp s :=
  .of_contDiff hs Real.contDiff_exp fun n x _hx => by
    have : iteratedDeriv n Real.exp x = Real.exp x := by
      have h := iteratedDeriv_exp_const_mul n (1 : ℝ)
      simp only [one_pow, one_mul] at h
      exact congr_fun h x
    rw [this]; exact (Real.exp_pos x).le

theorem absolutelyMonotoneOn_cosh :
    AbsolutelyMonotoneOn Real.cosh (Ici 0) :=
  .of_contDiff (uniqueDiffOn_Ici 0) Real.contDiff_cosh
    fun n x hx => by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [hk, show k + k = 2 * k from by ring,
          Real.iteratedDeriv_even_cosh]
        exact (Real.cosh_pos x).le
      · rw [hk, Real.iteratedDeriv_odd_cosh]
        exact Real.sinh_nonneg_iff.mpr (mem_Ici.mp hx)

theorem absolutelyMonotoneOn_const {c : ℝ} (hc : 0 ≤ c)
    (s : Set ℝ) (hs : UniqueDiffOn ℝ s) :
    AbsolutelyMonotoneOn (fun _ => c) s :=
  .of_contDiff hs contDiff_const fun n x _hx => by
    simp only [iteratedDeriv_const]
    split
    · exact hc
    · exact le_refl 0

theorem absolutelyMonotoneOn_pow (n : ℕ) :
    AbsolutelyMonotoneOn (fun x => x ^ n) (Ici 0) :=
  .of_contDiff (uniqueDiffOn_Ici 0) (contDiff_id.pow n)
    fun k x hx => by
      simp only [iteratedDeriv_pow]
      exact mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (mem_Ici.mp hx) _)

/-! ### Bernstein characterization -/

private lemma summable_of_nonneg_coeffs_abs
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ x : ℝ, 0 ≤ x → Summable (fun n => a n * x ^ n))
    (t : ℝ) : Summable (fun n => a n * t ^ n) := by
  apply Summable.of_norm_bounded
    (g := fun n => a n * |t| ^ n) (hs |t| (abs_nonneg t))
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha n), abs_pow]

private lemma summable_descFactorial_mul
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ x : ℝ, 0 ≤ x → Summable (fun n => a n * x ^ n))
    (j : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun n => a n * (n.descFactorial j : ℝ) * R ^ n) := by
  have hR1 : (0 : ℝ) < R + 1 := by linarith
  have hratio_abs : |R / (R + 1)| < 1 := by
    rw [abs_of_nonneg (div_nonneg hR hR1.le), div_lt_one hR1]
    linarith
  have hsmall : ∀ᶠ (n : ℕ) in Filter.atTop,
      (n : ℝ) ^ j * (R / (R + 1)) ^ n ≤ 1 := by
    have htend :=
      tendsto_pow_const_mul_const_pow_of_abs_lt_one j hratio_abs
    exact (htend.eventually (Iio_mem_nhds one_pos)).mono
      fun n (hn : _ < 1) => le_of_lt hn
  apply (hs (R + 1) hR1.le).of_norm_bounded_eventually_nat
  filter_upwards [hsmall] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (ha n) (Nat.cast_nonneg _))
      (pow_nonneg hR n))]
  calc a n * (n.descFactorial j : ℝ) * R ^ n
      ≤ a n * ((n : ℝ) ^ j) * R ^ n := by
        gcongr
        · exact ha n
        · exact_mod_cast Nat.descFactorial_le_pow n j
    _ = a n * (R + 1) ^ n *
        ((n : ℝ) ^ j * (R / (R + 1)) ^ n) := by
        rw [div_pow]; field_simp
    _ ≤ a n * (R + 1) ^ n * 1 := by
        apply mul_le_mul_of_nonneg_left hn
        exact mul_nonneg (ha n) (pow_nonneg hR1.le n)
    _ = a n * (R + 1) ^ n := by ring

private lemma iteratedDeriv_monomial_nonneg
    {a_coeff : ℝ} (ha : 0 ≤ a_coeff) (n k : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ iteratedDeriv k (fun z => a_coeff * z ^ n) x := by
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  exact mul_nonneg ha
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _))

/-- Globally smooth version of `fun x => ∑' n, a n * x ^ n` from nonneg coefficients.
    Used as the `ContDiff` input for `of_contDiff`. -/
private lemma contDiff_nonneg_power_series
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ x : ℝ, 0 ≤ x → Summable (fun n => a n * x ^ n)) :
    ContDiff ℝ ⊤ (fun x => ∑' n, a n * x ^ n) := by
  set p := FormalMultilinearSeries.ofScalars ℝ a with hp_def
  have hradius : p.radius = ⊤ := by
    apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
    intro r
    have hsumm := hs (r : ℝ) r.coe_nonneg
    refine hsumm.congr (fun n => ?_)
    rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_of_nonneg (ha n)]
  have hfps : HasFPowerSeriesOnBall p.sum p 0 ⊤ := by
    rw [← hradius]
    exact p.hasFPowerSeriesOnBall (hradius ▸ ENNReal.zero_lt_top)
  have hanalytic : AnalyticOnNhd ℝ p.sum Set.univ := by
    rw [← Metric.eball_top (0 : ℝ)]
    exact hfps.analyticOnNhd
  have hsmooth : ContDiff ℝ ⊤ p.sum := hanalytic.contDiff
  suffices heq : p.sum = fun x => ∑' n, a n * x ^ n by rwa [← heq]
  have : p.sum = FormalMultilinearSeries.ofScalarsSum a := rfl
  rw [this, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  ext x; simp [smul_eq_mul]

/-- Nonneg global iterated derivatives for the power series sum with nonneg coefficients. -/
private lemma nonneg_iteratedDeriv_power_series
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ x : ℝ, 0 ≤ x → Summable (fun n => a n * x ^ n))
    (k : ℕ) (x : ℝ) (hx : x ∈ Ici (0 : ℝ)) :
    0 ≤ iteratedDeriv k (fun z => ∑' n, a n * z ^ n) x := by
  have hkey : iteratedDerivWithin k
      (fun z => ∑' n, a n * z ^ n) Set.univ x =
      ∑' n, iteratedDerivWithin k
        (fun z => a n * z ^ n) Set.univ x := by
    apply iteratedDerivWithin_tsum k isOpen_univ
      (Set.mem_univ x)
    · exact fun t _ =>
        summable_of_nonneg_coeffs_abs a ha hs t
    · intro j hj1 hjk
      apply SummableLocallyUniformlyOn_of_locally_bounded
        isOpen_univ
      intro K _ hKc
      obtain ⟨R, hRpos, hKR⟩ :=
        hKc.isBounded.subset_ball_lt 0 0
      set R' := max R 1 with hR'def
      have hR'pos : 0 < R' := lt_max_of_lt_right one_pos
      have hR'ge1 : 1 ≤ R' := le_max_right R 1
      have hRleR' : R ≤ R' := le_max_left R 1
      refine ⟨fun n =>
        a n * (n.descFactorial j : ℝ) * R' ^ n,
        summable_descFactorial_mul a ha hs j R'
          hR'pos.le,
        fun n z hz => ?_⟩
      have hzR : |z| < R := by
        have := hKR hz
        rwa [Metric.mem_ball, Real.dist_eq, sub_zero]
          at this
      have hzR' : |z| ≤ R' :=
        (le_of_lt hzR).trans hRleR'
      rw [iteratedDerivWithin_univ]
      simp only [iteratedDeriv_const_mul_field,
        iteratedDeriv_pow]
      rw [Real.norm_eq_abs, abs_mul (a n),
        abs_of_nonneg (ha n)]
      calc a n * |↑(n.descFactorial j) *
            z ^ (n - j)|
          = a n * ((n.descFactorial j : ℝ) *
              |z| ^ (n - j)) := by
            rw [abs_mul,
              abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
        _ ≤ a n * (n.descFactorial j : ℝ) *
            R' ^ n := by
            have habs : |z| ^ (n - j) ≤ R' ^ n :=
              calc |z| ^ (n - j)
                  ≤ R' ^ (n - j) :=
                    pow_le_pow_left₀ (abs_nonneg z)
                      hzR' (n - j)
                _ ≤ R' ^ n :=
                    pow_le_pow_right₀ hR'ge1
                      (Nat.sub_le n j)
            have h1 :
                (n.descFactorial j : ℝ) *
                  |z| ^ (n - j) ≤
                (n.descFactorial j : ℝ) * R' ^ n := by
              nlinarith [pow_nonneg (abs_nonneg z)
                (n - j), pow_nonneg hR'pos.le n]
            nlinarith [ha n]
    · intro n j' r _ _
      rw [iteratedDerivWithin_univ]
      have : iteratedDeriv j' (fun z => a n * z ^ n) =
          fun z => a n * (n.descFactorial j' : ℝ) *
            z ^ (n - j') := by
        ext z
        simp [iteratedDeriv_const_mul_field,
          iteratedDeriv_pow, mul_assoc]
      rw [this]
      exact (differentiableAt_pow _).const_mul _
  rw [← iteratedDerivWithin_univ]
  rw [hkey]
  apply tsum_nonneg
  intro n
  rw [iteratedDerivWithin_univ]
  exact iteratedDeriv_monomial_nonneg (ha n) n k
    (Set.mem_Ici.mp hx)

/-- **Bernstein characterization (backward direction)**: a convergent
power series with nonneg coefficients defines an absolutely monotone
function on `[0, ∞)`. -/
theorem absolutelyMonotoneOn_of_nonneg_coeffs
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ x : ℝ, 0 ≤ x →
      Summable (fun n => a n * x ^ n)) :
    AbsolutelyMonotoneOn (fun x => ∑' n, a n * x ^ n) (Ici 0) :=
  .of_contDiff (uniqueDiffOn_Ici 0)
    ((contDiff_nonneg_power_series a ha hs).of_le (by exact_mod_cast le_top))
    (nonneg_iteratedDeriv_power_series a ha hs)

/-!
### Bernstein's theorem

The deep content of Bernstein's theorem is that a C^∞ function on a convex set
with all iterated derivatives nonneg is actually analytic. The proof uses Taylor's
theorem with the integral remainder plus a Widder-style estimate showing the
remainder tends to zero.
-/

/-- The Taylor coefficients at 0 for a function with nonneg derivatives within `s`. -/
private noncomputable def taylorCoeffs (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) : ℝ :=
  iteratedDerivWithin n f s 0 / (n.factorial : ℝ)

/-- Taylor coefficients are nonneg when iterated derivatives are nonneg. -/
private lemma taylorCoeffs_nonneg {f : ℝ → ℝ} {s : Set ℝ}
    (h0 : (0 : ℝ) ∈ s)
    (hf_nonneg : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDerivWithin n f s x) (n : ℕ) :
    0 ≤ taylorCoeffs f s n :=
  div_nonneg (hf_nonneg n 0 h0) (Nat.cast_nonneg _)

/-- **Widder's bound**: Under the hypotheses of the deep Bernstein theorem, the Taylor
partial sums at `0` are bounded by `f(y)` for `y ∈ s` with `y ≥ 0`. This is the key
step in the proof: it follows from Taylor's theorem with integral remainder,
using that the remainder is nonneg when all iterated derivatives are nonneg. -/
private lemma taylor_partial_sum_le_of_nonneg_iteratedDerivWithin
    {f : ℝ → ℝ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hconv : Convex ℝ s) (h0 : (0 : ℝ) ∈ s)
    (hf_smooth : ContDiffOn ℝ ∞ f s)
    (hf_nonneg : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDerivWithin n f s x)
    {y : ℝ} (hy : y ∈ s) (hy_pos : 0 ≤ y) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (iteratedDerivWithin k f s 0 / (k.factorial : ℝ)) * y ^ k ≤ f y := by
  -- Handle the trivial case y = 0 first.
  rcases eq_or_lt_of_le hy_pos with hy0 | hy_pos'
  · -- `hy0 : 0 = y`, so y = 0. Only the k = 0 term is nonzero.
    subst hy0
    rw [show (fun k : ℕ =>
        (iteratedDerivWithin k f s 0 / (k.factorial : ℝ)) * (0 : ℝ) ^ k) =
        fun k : ℕ => if k = 0 then f 0 else 0 from ?_]
    · rw [Finset.sum_ite_eq' (Finset.range (n + 1)) 0 (fun _ => f 0)]
      simp
    · funext k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp [iteratedDerivWithin_zero]
      · rw [zero_pow hk.ne', mul_zero, if_neg hk.ne']
  -- Now 0 < y. The interval [0, y] is contained in `s` by convexity.
  have hsub : Set.Icc (0 : ℝ) y ⊆ s := by
    have hoc : s.OrdConnected := hconv.ordConnected
    exact hoc.out h0 hy
  have huIcc : Set.uIcc (0 : ℝ) y = Set.Icc (0 : ℝ) y := Set.uIcc_of_le hy_pos
  have huIcc_sub : Set.uIcc (0 : ℝ) y ⊆ s := by rw [huIcc]; exact hsub
  have hs_uIcc : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) y) := by
    rw [huIcc]; exact uniqueDiffOn_Icc hy_pos'
  -- `f` is (n+1)-times continuously differentiable on `uIcc 0 y` (via restriction from `s`).
  have hf_uIcc : ContDiffOn ℝ (n + 1) f (Set.uIcc (0 : ℝ) y) :=
    (hf_smooth.of_le (by exact_mod_cast le_top)).mono huIcc_sub
  -- Taylor's integral remainder formula.
  have htaylor := taylor_integral_remainder (f := f) (x₀ := (0 : ℝ)) (x := y)
    (n := n) hf_uIcc
  -- Key lemma: iteratedDerivWithin on `uIcc 0 y` agrees with on `s` for points in `uIcc 0 y`.
  have hiter_eq : ∀ k ≤ n + 1, ∀ t ∈ Set.uIcc (0 : ℝ) y,
      iteratedDerivWithin k f (Set.uIcc (0 : ℝ) y) t = iteratedDerivWithin k f s t := by
    intro k _ t ht
    simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
    congr 1
    exact iteratedFDerivWithin_subset huIcc_sub hs_uIcc hs
      (hf_smooth.of_le (by exact_mod_cast le_top)) ht
  -- Nonnegativity of the integrand.
  have hpow_nn : ∀ t ∈ Set.Icc (0 : ℝ) y, 0 ≤ (y - t) ^ n := fun t ht =>
    pow_nonneg (sub_nonneg.mpr ht.2) n
  have hfact_pos : (0 : ℝ) < (n.factorial : ℝ) :=
    Nat.cast_pos.mpr n.factorial_pos
  have hderiv_nn : ∀ t ∈ Set.Icc (0 : ℝ) y,
      0 ≤ iteratedDerivWithin (n + 1) f (Set.uIcc (0 : ℝ) y) t := by
    intro t ht
    rw [hiter_eq (n + 1) le_rfl t (by rw [huIcc]; exact ht)]
    exact hf_nonneg (n + 1) t (hsub ht)
  -- The remainder integral is nonneg.
  have hrem_nn : 0 ≤ ∫ t in (0 : ℝ)..y,
      ((y - t) ^ n / (n.factorial : ℝ)) •
        iteratedDerivWithin (n + 1) f (Set.uIcc (0 : ℝ) y) t := by
    apply intervalIntegral.integral_nonneg hy_pos
    intro t ht
    rw [smul_eq_mul]
    apply mul_nonneg
    · exact div_nonneg (hpow_nn t ht) hfact_pos.le
    · exact hderiv_nn t ht
  -- Rearrange: f y - partial sum = nonneg remainder, so partial sum ≤ f y.
  have hkey : f y - taylorWithinEval f n (Set.uIcc (0 : ℝ) y) 0 y =
      ∫ t in (0 : ℝ)..y, ((y - t) ^ n / (n.factorial : ℝ)) •
        iteratedDerivWithin (n + 1) f (Set.uIcc (0 : ℝ) y) t := htaylor
  have hsum_le : taylorWithinEval f n (Set.uIcc (0 : ℝ) y) 0 y ≤ f y := by
    linarith [hrem_nn, hkey]
  -- Rewrite the Taylor polynomial as the stated partial sum.
  rw [taylor_within_apply] at hsum_le
  -- Now convert `iteratedDerivWithin k f (uIcc 0 y) 0` to `iteratedDerivWithin k f s 0`
  -- and simplify the scalar multiplication.
  have h0_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) y := by
    rw [huIcc]; exact Set.left_mem_Icc.mpr hy_pos
  have hrw : ∑ k ∈ Finset.range (n + 1),
      (((k.factorial : ℝ)⁻¹ * (y - 0) ^ k) •
        iteratedDerivWithin k f (Set.uIcc (0 : ℝ) y) 0) =
      ∑ k ∈ Finset.range (n + 1),
        (iteratedDerivWithin k f s 0 / (k.factorial : ℝ)) * y ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hiter_eq k (by simp at hk; omega) 0 h0_uIcc]
    rw [smul_eq_mul, sub_zero]
    ring
  rw [hrw] at hsum_le
  exact hsum_le

/-- **Bernstein's theorem at 0** (substantive version): a C^∞ function with nonneg iterated
derivatives on a convex set containing 0, with a strictly positive element, is real-analytic
(within `s`) at `0`.

This is the deep content of the Bernstein characterization: the C^∞ hypothesis (via
`∀ n : ℕ, ContDiffOn ℝ n f s`, equivalent to `ContDiffOn ℝ ∞ f s`) suffices when combined
with nonnegativity of all derivatives, to conclude real-analyticity within `s` at `0`.
The `AnalyticWithinAt` formulation is necessary because we only control `f` on `s`,
not on a two-sided neighbourhood of `0` in general.

**Proof strategy.**
1. Let `y₀ ∈ s` with `y₀ > 0`.
2. Define Taylor coefficients `a n := iteratedDerivWithin n f s 0 / n!`. All `a n ≥ 0`.
3. By the Widder bound (`taylor_partial_sum_le_of_nonneg_iteratedDerivWithin`),
   `∑_{k=0}^n a_k * y₀^k ≤ f y₀` for every `n`; in particular each single term
   `a_k * y₀^k ≤ f y₀`.
4. Hence `a_k ≤ f(y₀) / y₀^k`, so the series `∑ a_k * R^k` for `R = y₀/2` is dominated
   by the geometric series `f(y₀) * (1/2)^k`. This gives `p.radius ≥ y₀/2`.
5. The power series `p` therefore defines an analytic function `p.sum` on `ball 0 (y₀/2)`.
6. For `x ∈ s ∩ ball 0 (y₀/2)`, a Taylor remainder estimate (using the substitution
   `t = xu, u ∈ [0,1]`, together with monotonicity of `f^{(n+1)}` on `s`) gives
   `|R_n(x)| ≤ (|x|/y₀)^{n+1} · f y₀ → 0`, so `f x = p.sum x`.
7. Combining with `HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall` and
   `HasFPowerSeriesWithinOnBall.congr'`, we conclude `AnalyticWithinAt ℝ f s 0`.
-/
theorem analyticWithinAt_zero_of_nonneg_iteratedDerivWithin {f : ℝ → ℝ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hconv : Convex ℝ s) (h0 : (0 : ℝ) ∈ s)
    (hf_smooth : ContDiffOn ℝ ∞ f s)
    (hf_nonneg : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDerivWithin n f s x)
    (hpos : ∃ y ∈ s, 0 < y) :
    AnalyticWithinAt ℝ f s 0 := by
  -- Unpack a strictly positive witness `y₀ ∈ s`.
  obtain ⟨y₀, hy₀s, hy₀pos⟩ := hpos
  -- Taylor coefficients at `0`.
  set a : ℕ → ℝ := fun n => iteratedDerivWithin n f s 0 / (n.factorial : ℝ) with ha_def
  -- Each coefficient is nonneg.
  have ha_nn : ∀ n, 0 ≤ a n := fun n =>
    div_nonneg (hf_nonneg n 0 h0) (Nat.cast_nonneg _)
  -- Single-term Widder bound: `a k * y₀^k ≤ f y₀` for all `k`.
  have hterm : ∀ k, a k * y₀ ^ k ≤ f y₀ := by
    intro k
    -- Use the partial sum bound with `n = k`, then drop the other nonneg terms.
    have hsum := taylor_partial_sum_le_of_nonneg_iteratedDerivWithin
      hs hconv h0 hf_smooth hf_nonneg hy₀s hy₀pos.le k
    -- The `k`-th term of the sum equals `a k * y₀ ^ k`.
    have hkmem : k ∈ Finset.range (k + 1) := Finset.self_mem_range_succ k
    -- All summands are nonneg, so a single term is ≤ the full sum.
    have hnn : ∀ j ∈ Finset.range (k + 1), 0 ≤ a j * y₀ ^ j := fun j _ =>
      mul_nonneg (ha_nn j) (pow_nonneg hy₀pos.le _)
    have hterm_le :
        a k * y₀ ^ k ≤
          ∑ j ∈ Finset.range (k + 1),
            (iteratedDerivWithin j f s 0 / (j.factorial : ℝ)) * y₀ ^ j := by
      simpa [ha_def] using
        Finset.single_le_sum (f := fun j => a j * y₀ ^ j) (s := Finset.range (k + 1))
          (fun j hj => hnn j hj) hkmem
    exact hterm_le.trans hsum
  -- `f y₀ ≥ 0` follows from the 0-th coefficient being nonneg (it equals `f 0`)
  -- combined with the `k = 0` bound, but we don't actually need this; still, it's
  -- convenient to have.
  have hf_y₀_nn : 0 ≤ f y₀ := by
    have h := hterm 0
    have ha0 : 0 ≤ a 0 := ha_nn 0
    have : a 0 * y₀ ^ 0 = a 0 := by simp
    linarith [this ▸ h]
  -- The formal power series.
  set p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ a with hp_def
  -- Choose half of `y₀` as the radius for our ball.
  set R : ℝ := y₀ / 2 with hR_def
  have hRpos : 0 < R := by positivity
  have hRlt : R < y₀ := by
    rw [hR_def]
    linarith
  -- Promote `R` to an `NNReal`.
  have hRnn : (0 : ℝ) ≤ R := hRpos.le
  let R' : NNReal := ⟨R, hRnn⟩
  have hR'pos : (0 : ℝ≥0∞) < (R' : ℝ≥0∞) := by
    rw [ENNReal.coe_pos]
    exact hRpos
  -- Step 1: `p.radius ≥ R' = y₀/2` by the geometric bound.
  -- Bound: `‖p n‖ * R^n = a n * R^n ≤ f y₀ * (R / y₀)^n = f y₀ * (1/2)^n ≤ f y₀`.
  have hp_radius : (R' : ℝ≥0∞) ≤ p.radius := by
    refine p.le_radius_of_bound (f y₀) (fun n => ?_)
    -- `‖p n‖ = ‖a n‖ = a n` by nonnegativity.
    have hnorm : ‖p n‖ = a n := by
      rw [hp_def, FormalMultilinearSeries.ofScalars_norm,
          Real.norm_of_nonneg (ha_nn n)]
    rw [hnorm]
    -- Show: `a n * R^n ≤ f y₀`.
    -- We use `a n * y₀^n ≤ f y₀` and `R^n ≤ y₀^n`.
    have h1 : a n * y₀ ^ n ≤ f y₀ := hterm n
    have hRy : R ≤ y₀ := hRlt.le
    have hRnny : (R : ℝ) ^ n ≤ y₀ ^ n :=
      pow_le_pow_left₀ hRnn hRy n
    have : a n * (R : ℝ) ^ n ≤ a n * y₀ ^ n :=
      mul_le_mul_of_nonneg_left hRnny (ha_nn n)
    -- Combine.
    have hRcoe : ((R' : ℝ≥0) : ℝ) = R := rfl
    calc a n * ((R' : ℝ≥0) : ℝ) ^ n
        = a n * (R : ℝ) ^ n := by rw [hRcoe]
      _ ≤ a n * y₀ ^ n := this
      _ ≤ f y₀ := h1
  -- Step 2: `p.sum` has `p` as a power series on the ball of radius `p.radius`,
  -- which we then restrict to the smaller ball of radius `R'`.
  have hp_radius_pos : (0 : ℝ≥0∞) < p.radius :=
    lt_of_lt_of_le hR'pos hp_radius
  have hfps_sum_full : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall hp_radius_pos
  have hfps_sum : HasFPowerSeriesOnBall p.sum p 0 (R' : ℝ≥0∞) :=
    hfps_sum_full.mono hR'pos hp_radius
  -- Lift `hfps_sum` to a `HasFPowerSeriesWithinOnBall` on `s`.
  have hfps_sum_within : HasFPowerSeriesWithinOnBall p.sum p s 0 (R' : ℝ≥0∞) :=
    hfps_sum.hasFPowerSeriesWithinOnBall
  -- Step 3: `f = p.sum` on `insert 0 s ∩ ball 0 R'`.
  -- The proof uses a Taylor remainder bound: `|f x - S_n(x)| ≤ (|x|/y₀)^{n+1} * f y₀`,
  -- which follows from the formula `R_n(x) = x^{n+1}/n! * K_n(x)` where
  -- `K_n(x) = ∫_0^1 (1-u)^n f^{(n+1)}(xu) du`, combined with monotonicity
  -- of `f^{(n+1)}` on `s` (which gives `K_n(x) ≤ K_n(y₀)`).
  -- Step 3a: monotonicity of `iteratedDerivWithin k f s` on `s` for any `k`.
  have hf_mono : ∀ k : ℕ, MonotoneOn (iteratedDerivWithin k f s) s := by
    intro k
    -- The derivative of `iteratedDerivWithin k f s` on `s` is `iteratedDerivWithin (k+1) f s`,
    -- which is nonneg. So it is monotone.
    have hk_le : ((k : ℕ) : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_succ k
    have hk_lt : ((k : ℕ) : WithTop ℕ∞) < ((k + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.lt_succ_self k
    have hcont : ContinuousOn (iteratedDerivWithin k f s) s := by
      have hkplus : ContDiffOn ℝ (k + 1) f s :=
        hf_smooth.of_le (by exact_mod_cast le_top)
      exact hkplus.continuousOn_iteratedDerivWithin hk_le hs
    apply monotoneOn_of_deriv_nonneg hconv hcont
    · -- DifferentiableOn on interior s.
      intro x hx_int
      have hx : x ∈ s := interior_subset hx_int
      have hdiff : DifferentiableWithinAt ℝ (iteratedDerivWithin k f s) s x := by
        have hkplus : ContDiffOn ℝ (k + 1) f s :=
        hf_smooth.of_le (by exact_mod_cast le_top)
        exact (hkplus.differentiableOn_iteratedDerivWithin hk_lt hs) x hx
      -- At an interior point, `s ∈ 𝓝 x`, so `DifferentiableWithinAt ℝ g s x`
      -- implies `DifferentiableAt`, which restricts to `interior s`.
      have hs_nhds : s ∈ nhds x :=
        Filter.mem_of_superset (isOpen_interior.mem_nhds hx_int) interior_subset
      exact (hdiff.differentiableAt hs_nhds).differentiableWithinAt
    · intro x hx_int
      have hx : x ∈ s := interior_subset hx_int
      have hs_nhds : s ∈ nhds x :=
        Filter.mem_of_superset (isOpen_interior.mem_nhds hx_int) interior_subset
      have hderiv_eq : derivWithin (iteratedDerivWithin k f s) s x =
          iteratedDerivWithin (k + 1) f s x := by
        rw [iteratedDerivWithin_succ]
      have hderiv_eq2 : deriv (iteratedDerivWithin k f s) x =
          derivWithin (iteratedDerivWithin k f s) s x :=
        (derivWithin_of_mem_nhds hs_nhds).symm
      rw [hderiv_eq2, hderiv_eq]
      exact hf_nonneg (k + 1) x hx
  -- Step 3b: prove EqOn of f and p.sum on `insert 0 s ∩ ball 0 R'`.
  -- Key fact: `p.partialSum (n+1) x = ∑_{k=0}^n a_k x^k = taylorWithinEval f n s 0 x`.
  have hpsum_eq_taylor : ∀ (x : ℝ) (n : ℕ),
      p.partialSum (n + 1) x = taylorWithinEval f n s 0 x := by
    intro x n
    rw [FormalMultilinearSeries.partialSum, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hpk : p k (fun _ => x) = a k * x ^ k := by
      rw [hp_def, FormalMultilinearSeries.ofScalars_apply_eq]
      simp [smul_eq_mul]
    rw [hpk, smul_eq_mul, sub_zero, ha_def]
    have hfact : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    field_simp
  have hfeq : EqOn f p.sum (insert (0 : ℝ) s ∩ Metric.eball (0 : ℝ) (R' : ℝ≥0∞)) := by
    intro x hx
    obtain ⟨hxs_or, hxball⟩ := hx
    -- Unpack `|x| < R` from the eball membership.
    have hxabs : |x| < R := by
      have hedist : edist x (0 : ℝ) < (R' : ℝ≥0∞) := hxball
      have h1 : (‖x - 0‖₊ : ℝ≥0∞) < (R' : ℝ≥0∞) := by
        simpa [edist_eq_enorm_sub] using hedist
      have h2 : (‖x‖₊ : ℝ≥0∞) < (R' : ℝ≥0∞) := by simpa using h1
      have h3 : (‖x‖₊ : ℝ) < (R' : ℝ) := by
        exact_mod_cast (ENNReal.coe_lt_coe.mp h2)
      simpa [Real.norm_eq_abs] using h3
    -- p.partialSum tends to p.sum x.
    have htend_psum : Tendsto (fun n => p.partialSum n x) atTop (𝓝 (p.sum x)) := by
      have h := hfps_sum.tendsto_partialSum (y := x) hxball
      simpa [zero_add] using h
    -- Case split on whether x = 0 or x ∈ s.
    rcases eq_or_ne x 0 with hx0 | hx_ne
    · -- Case x = 0: directly `f 0 = p.sum 0 = a 0 = f 0`.
      subst hx0
      have : p.sum 0 = a 0 := by
        change FormalMultilinearSeries.ofScalarsSum a 0 = a 0
        rw [FormalMultilinearSeries.ofScalarsSum_zero]
        simp
      rw [this, ha_def]
      simp [iteratedDerivWithin_zero]
    · -- Case x ≠ 0: need x ∈ s.
      have hxs : x ∈ s := hxs_or.resolve_left hx_ne
      -- The interval `uIcc 0 x` is contained in `s` by convexity.
      have hsub_x : Set.uIcc (0 : ℝ) x ⊆ s := by
        have hoc : s.OrdConnected := hconv.ordConnected
        rcases le_or_gt 0 x with hxnn | hxneg
        · rw [Set.uIcc_of_le hxnn]
          exact hoc.out h0 hxs
        · rw [Set.uIcc_of_ge hxneg.le]
          exact hoc.out hxs h0
      -- Set `b := max x y₀` so `Icc 0 b ⊆ s` when x ≥ 0, and similarly for negative.
      -- We'll use `Icc 0 y₀ ⊆ s` for the positive case.
      have hsub_Icc_y₀ : Set.Icc (0 : ℝ) y₀ ⊆ s := by
        have hoc : s.OrdConnected := hconv.ordConnected
        exact hoc.out h0 hy₀s
      have hs_Icc_y₀ : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) y₀) := uniqueDiffOn_Icc hy₀pos
      -- `iteratedDerivWithin` on subsets agrees with on `s`.
      have hiter_eq_y₀ : ∀ k ≤ 0 + 1 + 1, ∀ t ∈ Set.Icc (0 : ℝ) y₀,
          iteratedDerivWithin k f (Set.Icc (0 : ℝ) y₀) t =
            iteratedDerivWithin k f s t := by
        intro k _ t ht
        simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
        congr 1
        exact iteratedFDerivWithin_subset hsub_Icc_y₀ hs_Icc_y₀ hs (hf_smooth.of_le (by exact_mod_cast le_top)) ht
      -- Intermediate point `y₁ := y₀/2 ∈ s` by convexity.
      have hy₁s : y₀ / 2 ∈ s := by
        have := hconv.segment_subset h0 hy₀s
        apply this
        refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
        simp; ring
      have hy₁pos : (0 : ℝ) < y₀ / 2 := by positivity
      have hxy₁ : |x| < y₀ / 2 := hxabs.trans_eq rfl
      -- Show that `(fun n => taylorWithinEval f n s 0 x) → f x`, i.e., `R_n(x) → 0`.
      -- The ratio `r := 2|x|/y₀` is strictly less than `1`.
      set r : ℝ := 2 * |x| / y₀ with hr_def
      have hr_nn : 0 ≤ r := by
        rw [hr_def]; positivity
      have hr_lt : r < 1 := by
        rw [hr_def, div_lt_one hy₀pos]
        linarith [hxy₁]
      have hRn_tendsto : Tendsto (fun n => f x - taylorWithinEval f n s 0 x)
          atTop (𝓝 0) := by
        -- The bounding sequence: `(n+1) * f y₀ * r^(n+1) → 0`.
        have hbound_tendsto :
            Tendsto (fun n : ℕ => ((n : ℝ) + 1) * f y₀ * r ^ (n + 1))
              atTop (𝓝 0) := by
          have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * r ^ (n + 1))
              atTop (𝓝 0) := by
            have hbase : Tendsto (fun n : ℕ => (n : ℝ) * r ^ n) atTop (𝓝 0) := by
              have := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1
                (show |r| < 1 by rwa [abs_of_nonneg hr_nn])
              simpa [pow_one] using this
            have hshift := hbase.comp (tendsto_add_atTop_nat 1)
            have hfun : (fun n : ℕ => ((n : ℝ) + 1) * r ^ (n + 1)) =
                (fun n : ℕ => ((n : ℝ) * r ^ n)) ∘ (fun a => a + 1) := by
              funext n
              simp only [Function.comp_apply]
              push_cast
              ring
            rw [hfun]; exact hshift
          have := h1.const_mul (f y₀)
          simpa [mul_comm, mul_assoc, mul_left_comm] using this
        -- Prove `|R_n(x)| ≤ (n+1) * f y₀ * r^(n+1)` for all n.
        refine squeeze_zero_norm' ?_ hbound_tendsto
        filter_upwards with n
        -- The core Taylor-remainder bound.
        -- Step A: iteratedDerivWithin on subsets agrees with on `s` for points in the subset.
        have hs_uIcc_x : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) x) :=
          uniqueDiffOn_Icc (inf_lt_sup.mpr (Ne.symm hx_ne))
        have hiter_eq_x : ∀ k ≤ n + 1, ∀ t ∈ Set.uIcc (0 : ℝ) x,
            iteratedDerivWithin k f (Set.uIcc (0 : ℝ) x) t =
              iteratedDerivWithin k f s t := by
          intro k _ t ht
          simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
          congr 1
          exact iteratedFDerivWithin_subset hsub_x hs_uIcc_x hs (hf_smooth.of_le (by exact_mod_cast le_top)) ht
        -- Step B: apply Taylor integral remainder on uIcc 0 x.
        have hf_uIcc_x : ContDiffOn ℝ (n + 1) f (Set.uIcc (0 : ℝ) x) :=
          (hf_smooth.of_le (by exact_mod_cast le_top)).mono hsub_x
        have htaylor_x := taylor_integral_remainder (f := f) (x₀ := (0 : ℝ)) (x := x)
          (n := n) hf_uIcc_x
        -- Step C: convert the Taylor polynomial to use `s`.
        have h0_uIcc_x : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) x := Set.left_mem_uIcc
        have htaylor_eq :
            taylorWithinEval f n (Set.uIcc (0 : ℝ) x) 0 x =
              taylorWithinEval f n s 0 x := by
          rw [taylor_within_apply, taylor_within_apply]
          apply Finset.sum_congr rfl
          intro k hk
          rw [hiter_eq_x k (by simp at hk; omega) 0 h0_uIcc_x]
        -- Step D: bound the integrand using monotonicity.
        -- First, bound `iteratedDerivWithin (n+1) f s (y₀/2)`.
        -- Apply Taylor on `Icc (y₀/2) y₀` expanded at `y₀/2`, evaluated at `y₀`.
        have hy₁sub : Set.Icc (y₀ / 2) y₀ ⊆ s :=
          hconv.ordConnected.out hy₁s hy₀s
        have hs_Icc_y₁ : UniqueDiffOn ℝ (Set.Icc (y₀ / 2) y₀) :=
          uniqueDiffOn_Icc (by linarith [hy₀pos])
        have hiter_eq_y₁ : ∀ k ≤ n + 2, ∀ t ∈ Set.Icc (y₀ / 2) y₀,
            iteratedDerivWithin k f (Set.Icc (y₀ / 2) y₀) t =
              iteratedDerivWithin k f s t := by
          intro k _ t ht
          simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
          congr 1
          exact iteratedFDerivWithin_subset hy₁sub hs_Icc_y₁ hs (hf_smooth.of_le (by exact_mod_cast le_top)) ht
        have hf_Icc_y₁ : ContDiffOn ℝ (n + 2 : ℕ) f (Set.Icc (y₀ / 2) y₀) :=
          (hf_smooth.of_le
            (WithTop.coe_le_coe.mpr (le_top : ((n + 2 : ℕ) : ℕ∞) ≤ ⊤))).mono hy₁sub
        -- `uIcc (y₀/2) y₀ = Icc (y₀/2) y₀` since `y₀/2 ≤ y₀`.
        have huIcc_eq : Set.uIcc (y₀ / 2) y₀ = Set.Icc (y₀ / 2) y₀ :=
          Set.uIcc_of_le (by linarith [hy₀pos])
        have hf_uIcc_y₁ : ContDiffOn ℝ ((n + 1) + 1 : ℕ) f (Set.uIcc (y₀/2) y₀) := by
          rw [huIcc_eq]; exact_mod_cast hf_Icc_y₁
        have htaylor_y₁ := taylor_integral_remainder (f := f) (x₀ := y₀/2) (x := y₀)
          (n := n + 1) hf_uIcc_y₁
        -- The remainder integral is nonneg.
        have hrem_y₁_nn : 0 ≤ ∫ t in (y₀/2)..y₀,
            ((y₀ - t) ^ (n + 1) / (((n+1).factorial : ℕ) : ℝ)) •
              iteratedDerivWithin ((n + 1) + 1) f (Set.uIcc (y₀/2) y₀) t := by
          apply intervalIntegral.integral_nonneg (by linarith [hy₀pos])
          intro t ht
          rw [huIcc_eq] at *
          rw [smul_eq_mul]
          apply mul_nonneg
          · apply div_nonneg
            · exact pow_nonneg (by linarith [ht.2]) _
            · exact Nat.cast_nonneg _
          · rw [hiter_eq_y₁ ((n + 1) + 1) le_rfl t ht]
            exact hf_nonneg ((n + 1) + 1) t (hy₁sub ht)
        -- So `taylorWithinEval f (n+1) (uIcc (y₀/2) y₀) (y₀/2) y₀ ≤ f y₀`.
        have hSn_le_f :
            taylorWithinEval f (n + 1) (Set.uIcc (y₀/2) y₀) (y₀/2) y₀ ≤ f y₀ := by
          linarith [htaylor_y₁, hrem_y₁_nn]
        -- Extract the k = n+1 term.
        rw [taylor_within_apply] at hSn_le_f
        -- The sum is a sum of nonneg terms; the last term is specifically
        -- `((n+1)!⁻¹ * (y₀ - y₀/2)^(n+1)) •
        --    iteratedDerivWithin (n+1) f (uIcc ..) (y₀/2)`.
        -- We use that this single term ≤ the whole sum.
        have hterms_nn : ∀ j ∈ Finset.range (n + 1 + 1),
            0 ≤ ((j.factorial : ℝ)⁻¹ * (y₀ - y₀/2) ^ j) •
                iteratedDerivWithin j f (Set.uIcc (y₀/2) y₀) (y₀/2) := by
          intro j hj
          have hj_le : j ≤ n + 2 := by
            simp at hj; omega
          have h_y₁_mem : y₀ / 2 ∈ Set.Icc (y₀/2) y₀ :=
            Set.left_mem_Icc.mpr (by linarith)
          have h_eq_j : iteratedDerivWithin j f (Set.uIcc (y₀/2) y₀) (y₀/2) =
              iteratedDerivWithin j f s (y₀/2) := by
            rw [huIcc_eq]
            exact hiter_eq_y₁ j hj_le (y₀/2) h_y₁_mem
          rw [h_eq_j, smul_eq_mul]
          apply mul_nonneg
          · apply mul_nonneg
            · exact inv_nonneg.mpr (Nat.cast_nonneg _)
            · exact pow_nonneg (by linarith [hy₀pos]) _
          · exact hf_nonneg j (y₀/2) hy₁s
        have hsingle_le :
            (((n + 1).factorial : ℝ)⁻¹ * (y₀ - y₀/2) ^ (n + 1)) •
                iteratedDerivWithin (n + 1) f (Set.uIcc (y₀/2) y₀) (y₀/2) ≤
            ∑ j ∈ Finset.range (n + 1 + 1),
              ((j.factorial : ℝ)⁻¹ * (y₀ - y₀/2) ^ j) •
                iteratedDerivWithin j f (Set.uIcc (y₀/2) y₀) (y₀/2) := by
          exact Finset.single_le_sum (f := fun j =>
            ((j.factorial : ℝ)⁻¹ * (y₀ - y₀/2) ^ j) •
              iteratedDerivWithin j f (Set.uIcc (y₀/2) y₀) (y₀/2))
            (fun j hj => hterms_nn j hj) (Finset.self_mem_range_succ (n + 1))
        -- Combine: single term ≤ sum ≤ f y₀.
        have h_y₁_mem_Icc : y₀ / 2 ∈ Set.Icc (y₀/2) y₀ :=
          Set.left_mem_Icc.mpr (by linarith)
        have h_deriv_y₁_bound :
            iteratedDerivWithin (n + 1) f s (y₀/2) ≤
              ((n + 1).factorial : ℝ) * f y₀ / (y₀/2) ^ (n + 1) := by
          have hcombined :
              ((((n + 1).factorial : ℝ)⁻¹ * (y₀ - y₀/2) ^ (n + 1)) •
                iteratedDerivWithin (n + 1) f (Set.uIcc (y₀/2) y₀) (y₀/2)) ≤ f y₀ :=
            le_trans hsingle_le hSn_le_f
          have h_iter_eq : iteratedDerivWithin (n + 1) f (Set.uIcc (y₀/2) y₀) (y₀/2) =
              iteratedDerivWithin (n + 1) f s (y₀/2) := by
            rw [huIcc_eq]
            exact hiter_eq_y₁ (n + 1) (by omega) (y₀/2) h_y₁_mem_Icc
          rw [h_iter_eq, smul_eq_mul] at hcombined
          have hy₀_sub : y₀ - y₀/2 = y₀/2 := by ring
          rw [hy₀_sub] at hcombined
          have hfact_pos : (0 : ℝ) < ((n + 1).factorial : ℝ) :=
            Nat.cast_pos.mpr (n + 1).factorial_pos
          have hy₁_pow_pos : (0 : ℝ) < (y₀/2) ^ (n + 1) :=
            pow_pos hy₁pos _
          -- From `(1/(n+1)!) * (y₀/2)^(n+1) * iter ≤ f y₀` derive
          -- `iter ≤ (n+1)! * f y₀ / (y₀/2)^(n+1)`.
          rw [show (((n + 1).factorial : ℝ)⁻¹ * (y₀/2) ^ (n + 1)) *
              iteratedDerivWithin (n + 1) f s (y₀/2) =
              iteratedDerivWithin (n + 1) f s (y₀/2) *
                ((y₀/2)^(n+1) / ((n+1).factorial : ℝ)) from by ring] at hcombined
          have hpos : (0 : ℝ) < (y₀/2)^(n+1) / ((n+1).factorial : ℝ) :=
            div_pos hy₁_pow_pos hfact_pos
          rw [← le_div_iff₀ hpos] at hcombined
          -- hcombined: iteratedDerivWithin (n+1) f s (y₀/2)
          --   ≤ f y₀ / ((y₀/2)^(n+1) / (n+1)!)
          -- Goal: iteratedDerivWithin (n + 1) f s (y₀/2) ≤ (n+1)! * f y₀ / (y₀/2)^(n+1)
          convert hcombined using 1
          field_simp
        -- Step E: bound the integrand in the Taylor remainder.
        -- `|R_n(x)| = |∫_0^x ((x-t)^n/n!) • iteratedDerivWithin (n+1) f (uIcc 0 x) t dt|`
        -- We bound by `|x|^(n+1)/n! * (n+1)! * f y₀ / (y₀/2)^(n+1)`.
        have hrewrite :
            f x - taylorWithinEval f n s 0 x =
              ∫ t in (0 : ℝ)..x, ((x - t) ^ n / (n.factorial : ℝ)) •
                iteratedDerivWithin (n + 1) f (Set.uIcc (0 : ℝ) x) t := by
          rw [← htaylor_eq]
          exact htaylor_x
        rw [hrewrite]
        -- Bound the integral.
        have habs_integral_bound :
            ‖∫ t in (0 : ℝ)..x, ((x - t) ^ n / (n.factorial : ℝ)) •
                iteratedDerivWithin (n + 1) f (Set.uIcc (0 : ℝ) x) t‖ ≤
              (((n + 1).factorial : ℝ) * f y₀ / (y₀/2) ^ (n + 1)) *
                |x|^(n+1) / (n.factorial : ℝ) := by
          -- Apply `intervalIntegral.norm_integral_le_of_norm_le_const` with bound
          -- `C := (n+1)! * f y₀ / (y₀/2)^(n+1) * |x|^n / n!`.
          set C : ℝ := (((n+1).factorial : ℝ) * f y₀ / (y₀/2)^(n+1))
            * |x|^n / (n.factorial : ℝ)
          have hC_bound : ∀ t ∈ Set.uIcc (0 : ℝ) x,
              ‖((x - t) ^ n / (n.factorial : ℝ)) •
                iteratedDerivWithin (n + 1) f (Set.uIcc (0 : ℝ) x) t‖ ≤ C := by
            intro t ht
            rw [hiter_eq_x (n + 1) le_rfl t ht]
            have h_iter_nn : 0 ≤ iteratedDerivWithin (n + 1) f s t :=
              hf_nonneg (n + 1) t (hsub_x ht)
            -- Bound `iteratedDerivWithin (n+1) f s t` by the value at `y₀/2`
            -- by monotonicity, since `|t| ≤ |x| < y₀/2`.
            -- If `x ≥ 0`, `0 ≤ t ≤ x < y₀/2`;
            -- if `x ≤ 0`, `x ≤ t ≤ 0 ≤ y₀/2`.
            -- We need `t ≤ y₀/2`; from `uIcc 0 x ⊆ [-(y₀/2), y₀/2]` via `|x| < y₀/2`.
            have ht_le : t ≤ y₀/2 := by
              rcases le_or_gt 0 x with hxnn | hxneg
              · have : t ≤ x := (Set.uIcc_of_le hxnn ▸ ht).2
                linarith [abs_of_nonneg hxnn, hxy₁]
              · have : t ≤ 0 := (Set.uIcc_of_ge hxneg.le ▸ ht).2
                linarith [hy₁pos]
            have ht_in_s : t ∈ s := hsub_x ht
            have h_mono := hf_mono (n + 1) ht_in_s hy₁s ht_le
            have h_iter_bound : iteratedDerivWithin (n + 1) f s t ≤
                ((n + 1).factorial : ℝ) * f y₀ / (y₀/2) ^ (n + 1) :=
              h_mono.trans h_deriv_y₁_bound
            -- Now bound the norm.
            rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h_iter_nn, abs_div, abs_pow]
            have hfact_abs : |((n.factorial : ℕ) : ℝ)| = (n.factorial : ℝ) := by
              rw [abs_of_nonneg (Nat.cast_nonneg _)]
            rw [hfact_abs]
            have hfact_pos : (0 : ℝ) < (n.factorial : ℝ) :=
              Nat.cast_pos.mpr n.factorial_pos
            -- `|x - t|^n ≤ |x|^n` on uIcc 0 x.
            have h_xt_le : |x - t| ≤ |x| := by
              rcases le_or_gt 0 x with hxnn | hxneg
              · have htmem := Set.uIcc_of_le hxnn ▸ ht
                rcases htmem with ⟨ht0, htx⟩
                rw [abs_of_nonneg (by linarith : 0 ≤ x - t), abs_of_nonneg hxnn]
                linarith
              · have htmem := Set.uIcc_of_ge hxneg.le ▸ ht
                rcases htmem with ⟨htx, ht0⟩
                rw [abs_of_nonpos (by linarith : x - t ≤ 0), abs_of_neg hxneg]
                linarith
            have h_xt_pow : |x - t| ^ n ≤ |x|^n :=
              pow_le_pow_left₀ (abs_nonneg _) h_xt_le n
            have h_iter_bound_pos :
                0 ≤ ((n + 1).factorial : ℝ) * f y₀ / (y₀/2) ^ (n + 1) := by
              apply div_nonneg
              · exact mul_nonneg (Nat.cast_nonneg _) hf_y₀_nn
              · exact le_of_lt (pow_pos hy₁pos _)
            calc |x - t| ^ n / (n.factorial : ℝ) * iteratedDerivWithin (n + 1) f s t
                ≤ |x| ^ n / (n.factorial : ℝ) *
                    (((n + 1).factorial : ℝ) * f y₀ / (y₀/2) ^ (n + 1)) := by
                  apply mul_le_mul _ h_iter_bound h_iter_nn _
                  · exact div_le_div_of_nonneg_right h_xt_pow hfact_pos.le
                  · positivity
              _ = C := by
                  simp only [C]
                  ring
          have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := x)
            (f := fun t => ((x - t) ^ n / (n.factorial : ℝ)) •
              iteratedDerivWithin (n + 1) f (Set.uIcc (0 : ℝ) x) t)
            (C := C) (fun t ht => hC_bound t (by
              -- ht : t ∈ Ι 0 x (uIoc), need t ∈ Set.uIcc 0 x.
              have hmem : t ∈ Set.uIcc (0 : ℝ) x := by
                rcases le_total (0 : ℝ) x with hxnn | hxnp
                · rw [Set.uIoc_of_le hxnn] at ht
                  rw [Set.uIcc_of_le hxnn]
                  exact ⟨ht.1.le, ht.2⟩
                · rw [Set.uIoc_of_ge hxnp] at ht
                  rw [Set.uIcc_of_ge hxnp]
                  exact ⟨ht.1.le, ht.2⟩
              exact hmem))
          have hCalc :
              C * |x - 0| =
                ((((n+1).factorial : ℝ) * f y₀ / (y₀/2)^(n+1))) *
                  |x|^(n+1) / (n.factorial : ℝ) := by
            simp only [C]
            rw [sub_zero, pow_succ]
            ring
          linarith [this, hCalc.le]
        -- Finish: the norm bound is what we need.
        have h_final :
            (((n + 1).factorial : ℝ) * f y₀ / (y₀/2) ^ (n + 1)) *
              |x|^(n+1) / (n.factorial : ℝ) =
            ((n : ℝ) + 1) * f y₀ * r ^ (n + 1) := by
          have hfact : ((n + 1).factorial : ℝ) = (n + 1) * (n.factorial : ℝ) := by
            rw [Nat.factorial_succ]; push_cast; ring
          have hfact_ne : (n.factorial : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr n.factorial_ne_zero
          have hy₀_ne : y₀ ≠ 0 := hy₀pos.ne'
          have hy₁_pow_ne : ((y₀/2 : ℝ)) ^ (n + 1) ≠ 0 := (pow_pos hy₁pos _).ne'
          have h_r_pow : r^(n+1) = (2 * |x|)^(n+1) / y₀^(n+1) := by
            rw [hr_def, div_pow]
          rw [hfact, h_r_pow]
          have h2x_pow : (2 * |x|)^(n+1) = 2^(n+1) * |x|^(n+1) := by
            rw [mul_pow]
          rw [h2x_pow]
          have hpow_half : ((y₀/2 : ℝ))^(n+1) = y₀^(n+1) / 2^(n+1) := by rw [div_pow]
          rw [hpow_half]
          have h2_ne : (2 : ℝ)^(n+1) ≠ 0 := pow_ne_zero _ (by norm_num)
          have hy₀_pow_ne : (y₀ : ℝ)^(n+1) ≠ 0 := pow_ne_zero _ hy₀_ne
          field_simp
        calc ‖∫ t in (0 : ℝ)..x, ((x - t) ^ n / (n.factorial : ℝ)) •
                iteratedDerivWithin (n + 1) f (Set.uIcc (0 : ℝ) x) t‖
            ≤ (((n + 1).factorial : ℝ) * f y₀ / (y₀/2) ^ (n + 1)) *
                |x|^(n+1) / (n.factorial : ℝ) := habs_integral_bound
          _ = ((n : ℝ) + 1) * f y₀ * r ^ (n + 1) := h_final
      -- Derive `S_n(x) → f x`.
      have htend_sn : Tendsto (fun n => taylorWithinEval f n s 0 x) atTop (𝓝 (f x)) := by
        have hconst : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)) := tendsto_const_nhds
        have h := hconst.sub hRn_tendsto
        simpa using h
      -- Using `hpsum_eq_taylor`, `p.partialSum (n+1) x → f x`.
      have htend_pn1 : Tendsto (fun n => p.partialSum (n + 1) x) atTop (𝓝 (f x)) := by
        have : (fun n => p.partialSum (n + 1) x) = fun n => taylorWithinEval f n s 0 x := by
          funext n
          exact hpsum_eq_taylor x n
        rw [this]; exact htend_sn
      -- But also `p.partialSum (n+1) x → p.sum x`.
      have htend_pn1' : Tendsto (fun n => p.partialSum (n + 1) x) atTop (𝓝 (p.sum x)) :=
        htend_psum.comp (tendsto_add_atTop_nat 1)
      exact tendsto_nhds_unique htend_pn1 htend_pn1'
  -- Step 4: transport the power series from `p.sum` to `f` along the equality.
  have hfps_f : HasFPowerSeriesWithinOnBall f p s 0 (R' : ℝ≥0∞) :=
    hfps_sum_within.congr' hfeq
  exact hfps_f.analyticWithinAt

/-- **Bernstein's theorem** for absolutely monotone functions: if `f` is absolutely
monotone on a convex set `s` containing 0 (with some positive element), then `f` is
analytic within `s` at 0. -/
theorem AbsolutelyMonotoneOn.analyticWithinAt_zero {f : ℝ → ℝ} {s : Set ℝ}
    (hf : AbsolutelyMonotoneOn f s) (hs : UniqueDiffOn ℝ s)
    (hconv : Convex ℝ s) (h0 : (0 : ℝ) ∈ s) (hpos : ∃ y ∈ s, 0 < y) :
    AnalyticWithinAt ℝ f s 0 :=
  analyticWithinAt_zero_of_nonneg_iteratedDerivWithin hs hconv h0
    hf.contDiffOn hf.nonneg hpos
