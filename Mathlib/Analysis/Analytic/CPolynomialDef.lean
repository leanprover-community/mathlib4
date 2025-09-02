/-
Copyright (c) 2023 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Analysis.Analytic.ChangeOrigin

/-! We specialize the theory of analytic functions to the case of functions that admit a
development given by a *finite* formal multilinear series. We call them "continuously polynomial",
which is abbreviated to `CPolynomial`. One reason to do that is that we no longer need a
completeness assumption on the target space `F` to make the series converge, so some of the results
are more general. The class of continuously polynomial functions includes functions defined by
polynomials on a normed `𝕜`-algebra and continuous multilinear maps.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`, and let `f` be a function from `E` to `F`.

* `HasFiniteFPowerSeriesOnBall f p x n r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₘ yᵐ`, and moreover `pₘ = 0` if `n ≤ m`.
* `HasFiniteFPowerSeriesAt f p x n`: on some ball of center `x` with positive radius, holds
  `HasFiniteFPowerSeriesOnBall f p x n r`.
* `CPolynomialAt 𝕜 f x`: there exists a power series `p` and a natural number `n` such that
  holds `HasFPowerSeriesAt f p x n`.
* `CPolynomialOn 𝕜 f s`: the function `f` is analytic at every point of `s`.

In this file, we develop the basic properties of these notions, notably:
* If a function is continuously polynomial, then it is analytic, see
  `HasFiniteFPowerSeriesOnBall.hasFPowerSeriesOnBall`, `HasFiniteFPowerSeriesAt.hasFPowerSeriesAt`,
  `CPolynomialAt.analyticAt` and `CPolynomialOn.analyticOnNhd`.
* The sum of a finite formal power series with positive radius is well defined on the whole space,
  see `FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite`.
* If a function admits a finite power series in a ball, then it is continuously polynomial at
  any point `y` of this ball, and the power series there can be expressed in terms of the initial
  power series `p` as `p.changeOrigin y`, which is finite (with the same bound as `p`) by
  `changeOrigin_finite_of_finite`. See `HasFiniteFPowerSeriesOnBall.changeOrigin`. It follows in
  particular that the set of points at which a given function is continuously polynomial is open,
  see `isOpen_cpolynomialAt`.

More API is available in the file `Mathlib/Analysis/Analytic/CPolynomial.lean`, with heavier
imports.
-/

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology
open Set Filter Asymptotics NNReal ENNReal

variable {f g : E → F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r r' : ℝ≥0∞} {n m : ℕ}

section FiniteFPowerSeries

/-- Given a function `f : E → F`, a formal multilinear series `p` and `n : ℕ`, we say that
`f` has `p` as a finite power series on the ball of radius `r > 0` around `x` if
`f (x + y) = ∑' pₘ yᵐ` for all `‖y‖ < r` and `pₙ = 0` for `n ≤ m`. -/
structure HasFiniteFPowerSeriesOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
    (n : ℕ) (r : ℝ≥0∞) : Prop extends HasFPowerSeriesOnBall f p x r where
  finite : ∀ (m : ℕ), n ≤ m → p m = 0

theorem HasFiniteFPowerSeriesOnBall.mk' {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    {n : ℕ} {r : ℝ≥0∞} (finite : ∀ (m : ℕ), n ≤ m → p m = 0) (pos : 0 < r)
    (sum_eq : ∀ y ∈ EMetric.ball 0 r, (∑ i ∈ Finset.range n, p i fun _ ↦ y) = f (x + y)) :
    HasFiniteFPowerSeriesOnBall f p x n r where
  r_le := p.radius_eq_top_of_eventually_eq_zero (Filter.eventually_atTop.mpr ⟨n, finite⟩) ▸ le_top
  r_pos := pos
  hasSum hy := sum_eq _ hy ▸ hasSum_sum_of_ne_finset_zero fun m hm ↦ by
    rw [Finset.mem_range, not_lt] at hm; rw [finite m hm]; rfl
  finite := finite

/-- Given a function `f : E → F`, a formal multilinear series `p` and `n : ℕ`, we say that
`f` has `p` as a finite power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a
neighborhood of `0`and `pₙ = 0` for `n ≤ m`. -/
def HasFiniteFPowerSeriesAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (n : ℕ) :=
  ∃ r, HasFiniteFPowerSeriesOnBall f p x n r

theorem HasFiniteFPowerSeriesAt.hasFPowerSeriesAt
    (hf : HasFiniteFPowerSeriesAt f p x n) : HasFPowerSeriesAt f p x :=
  let ⟨r, hf⟩ := hf
  ⟨r, hf.toHasFPowerSeriesOnBall⟩

theorem HasFiniteFPowerSeriesAt.finite (hf : HasFiniteFPowerSeriesAt f p x n) :
    ∀ m : ℕ, n ≤ m → p m = 0 := let ⟨_, hf⟩ := hf; hf.finite

variable (𝕜)

/-- Given a function `f : E → F`, we say that `f` is continuously polynomial (cpolynomial)
at `x` if it admits a finite power series expansion around `x`. -/
def CPolynomialAt (f : E → F) (x : E) :=
  ∃ (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ), HasFiniteFPowerSeriesAt f p x n

/-- Given a function `f : E → F`, we say that `f` is continuously polynomial on a set `s`
if it is continuously polynomial around every point of `s`. -/
def CPolynomialOn (f : E → F) (s : Set E) :=
  ∀ x, x ∈ s → CPolynomialAt 𝕜 f x

variable {𝕜}

theorem HasFiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesAt f p x n :=
  ⟨r, hf⟩

theorem HasFiniteFPowerSeriesAt.cpolynomialAt (hf : HasFiniteFPowerSeriesAt f p x n) :
    CPolynomialAt 𝕜 f x :=
  ⟨p, n, hf⟩

theorem HasFiniteFPowerSeriesOnBall.cpolynomialAt (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    CPolynomialAt 𝕜 f x :=
  hf.hasFiniteFPowerSeriesAt.cpolynomialAt

theorem CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜 f x) : AnalyticAt 𝕜 f x :=
  let ⟨p, _, hp⟩ := hf
  ⟨p, hp.hasFPowerSeriesAt⟩

theorem CPolynomialAt.analyticWithinAt {s : Set E} (hf : CPolynomialAt 𝕜 f x) :
    AnalyticWithinAt 𝕜 f s x :=
  hf.analyticAt.analyticWithinAt

theorem CPolynomialOn.analyticOnNhd {s : Set E} (hf : CPolynomialOn 𝕜 f s) : AnalyticOnNhd 𝕜 f s :=
  fun x hx ↦ (hf x hx).analyticAt

theorem CPolynomialOn.analyticOn {s : Set E} (hf : CPolynomialOn 𝕜 f s) : AnalyticOn 𝕜 f s :=
  hf.analyticOnNhd.analyticOn

theorem HasFiniteFPowerSeriesOnBall.congr (hf : HasFiniteFPowerSeriesOnBall f p x n r)
    (hg : EqOn f g (EMetric.ball x r)) : HasFiniteFPowerSeriesOnBall g p x n r :=
  ⟨hf.1.congr hg, hf.finite⟩

theorem HasFiniteFPowerSeriesOnBall.of_le {m n : ℕ}
    (h : HasFiniteFPowerSeriesOnBall f p x n r) (hmn : n ≤ m) :
    HasFiniteFPowerSeriesOnBall f p x m r :=
  ⟨h.toHasFPowerSeriesOnBall, fun i hi ↦ h.finite i (hmn.trans hi)⟩

theorem HasFiniteFPowerSeriesAt.of_le {m n : ℕ}
    (h : HasFiniteFPowerSeriesAt f p x n) (hmn : n ≤ m) :
    HasFiniteFPowerSeriesAt f p x m := by
  rcases h with ⟨r, hr⟩
  exact ⟨r, hr.of_le hmn⟩

/-- If a function `f` has a finite power series `p` around `x`, then the function
`z ↦ f (z - y)` has the same finite power series around `x + y`. -/
theorem HasFiniteFPowerSeriesOnBall.comp_sub (hf : HasFiniteFPowerSeriesOnBall f p x n r) (y : E) :
    HasFiniteFPowerSeriesOnBall (fun z => f (z - y)) p (x + y) n r :=
  ⟨hf.1.comp_sub y, hf.finite⟩

theorem HasFiniteFPowerSeriesOnBall.mono (hf : HasFiniteFPowerSeriesOnBall f p x n r)
    (r'_pos : 0 < r') (hr : r' ≤ r) : HasFiniteFPowerSeriesOnBall f p x n r' :=
  ⟨hf.1.mono r'_pos hr, hf.finite⟩

theorem HasFiniteFPowerSeriesAt.congr (hf : HasFiniteFPowerSeriesAt f p x n) (hg : f =ᶠ[𝓝 x] g) :
    HasFiniteFPowerSeriesAt g p x n :=
  Exists.imp (fun _ hg ↦ ⟨hg, hf.finite⟩) (hf.hasFPowerSeriesAt.congr hg)

protected theorem HasFiniteFPowerSeriesAt.eventually (hf : HasFiniteFPowerSeriesAt f p x n) :
    ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, HasFiniteFPowerSeriesOnBall f p x n r :=
  hf.hasFPowerSeriesAt.eventually.mono fun _ h ↦ ⟨h, hf.finite⟩

theorem CPolynomialAt.congr (hf : CPolynomialAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g) : CPolynomialAt 𝕜 g x :=
  let ⟨_, _, hpf⟩ := hf
  (hpf.congr hg).cpolynomialAt

theorem CPolynomialAt_congr (h : f =ᶠ[𝓝 x] g) : CPolynomialAt 𝕜 f x ↔ CPolynomialAt 𝕜 g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

theorem CPolynomialOn.mono {s t : Set E} (hf : CPolynomialOn 𝕜 f t) (hst : s ⊆ t) :
    CPolynomialOn 𝕜 f s :=
  fun z hz => hf z (hst hz)

theorem CPolynomialOn.congr' {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g) :
    CPolynomialOn 𝕜 g s :=
  fun z hz => (hf z hz).congr (mem_nhdsSet_iff_forall.mp hg z hz)

theorem CPolynomialOn_congr' {s : Set E} (h : f =ᶠ[𝓝ˢ s] g) :
    CPolynomialOn 𝕜 f s ↔ CPolynomialOn 𝕜 g s :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr' h.symm⟩

theorem CPolynomialOn.congr {s : Set E} (hs : IsOpen s) (hf : CPolynomialOn 𝕜 f s)
    (hg : s.EqOn f g) : CPolynomialOn 𝕜 g s :=
  hf.congr' <| mem_nhdsSet_iff_forall.mpr
    (fun _ hz => eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hz, hg⟩)

theorem CPolynomialOn_congr {s : Set E} (hs : IsOpen s) (h : s.EqOn f g) :
    CPolynomialOn 𝕜 f s ↔ CPolynomialOn 𝕜 g s :=
  ⟨fun hf => hf.congr hs h, fun hg => hg.congr hs h.symm⟩

/-- If a function `f` has a finite power series `p` on a ball and `g` is a continuous linear map,
then `g ∘ f` has the finite power series `g ∘ p` on the same ball. -/
theorem ContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall (g : F →L[𝕜] G)
    (h : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesOnBall (g ∘ f) (g.compFormalMultilinearSeries p) x n r :=
  ⟨g.comp_hasFPowerSeriesOnBall h.1, fun m hm ↦ by
    rw [compFormalMultilinearSeries_apply, h.finite m hm]
    ext; exact map_zero g⟩

/-- If a function `f` is continuously polynomial on a set `s` and `g` is a continuous linear map,
then `g ∘ f` is continuously polynomial on `s`. -/
theorem ContinuousLinearMap.comp_cpolynomialOn {s : Set E} (g : F →L[𝕜] G)
    (h : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, n, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, n, r, g.comp_hasFiniteFPowerSeriesOnBall hp⟩

/-- If a function admits a finite power series expansion bounded by `n`, then it is equal to
the `m`th partial sums of this power series at every point of the disk for `n ≤ m`. -/
theorem HasFiniteFPowerSeriesOnBall.eq_partialSum
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    ∀ y ∈ EMetric.ball (0 : E) r, ∀ m, n ≤ m →
    f (x + y) = p.partialSum m y :=
  fun y hy m hm ↦ (hf.hasSum hy).unique (hasSum_sum_of_ne_finset_zero
    (f := fun m => p m (fun _ => y)) (s := Finset.range m)
    (fun N hN => by simp only; simp only [Finset.mem_range, not_lt] at hN
                    rw [hf.finite _ (le_trans hm hN), ContinuousMultilinearMap.zero_apply]))

/-- Variant of the previous result with the variable expressed as `y` instead of `x + y`. -/
theorem HasFiniteFPowerSeriesOnBall.eq_partialSum'
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    ∀ y ∈ EMetric.ball x r, ∀ m, n ≤ m →
    f y = p.partialSum m (y - x) := by
  intro y hy m hm
  rw [EMetric.mem_ball, edist_eq_enorm_sub, ← mem_emetric_ball_zero_iff] at hy
  rw [← (HasFiniteFPowerSeriesOnBall.eq_partialSum hf _ hy m hm), add_sub_cancel]

/-! The particular cases where `f` has a finite power series bounded by `0` or `1`. -/

/-- If `f` has a formal power series on a ball bounded by `0`, then `f` is equal to `0` on
the ball. -/
theorem HasFiniteFPowerSeriesOnBall.eq_zero_of_bound_zero
    (hf : HasFiniteFPowerSeriesOnBall f pf x 0 r) : ∀ y ∈ EMetric.ball x r, f y = 0 := by
  intro y hy
  rw [hf.eq_partialSum' y hy 0 le_rfl, FormalMultilinearSeries.partialSum]
  simp only [Finset.range_zero, Finset.sum_empty]

theorem HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero (hf : ∀ y ∈ EMetric.ball x r, f y = 0)
    (r_pos : 0 < r) (hp : ∀ n, p n = 0) : HasFiniteFPowerSeriesOnBall f p x 0 r := by
  refine ⟨⟨?_, r_pos, ?_⟩, fun n _ ↦ hp n⟩
  · rw [p.radius_eq_top_of_forall_image_add_eq_zero 0 (fun n ↦ by rw [add_zero]; exact hp n)]
    exact le_top
  · intro y hy
    rw [hf (x + y)]
    · convert hasSum_zero
      rw [hp, ContinuousMultilinearMap.zero_apply]
    · rwa [EMetric.mem_ball, edist_eq_enorm_sub, add_comm, add_sub_cancel_right,
        ← edist_zero_eq_enorm, ← EMetric.mem_ball]

/-- If `f` has a formal power series at `x` bounded by `0`, then `f` is equal to `0` in a
neighborhood of `x`. -/
theorem HasFiniteFPowerSeriesAt.eventually_zero_of_bound_zero
    (hf : HasFiniteFPowerSeriesAt f pf x 0) : f =ᶠ[𝓝 x] 0 :=
  Filter.eventuallyEq_iff_exists_mem.mpr (let ⟨r, hf⟩ := hf; ⟨EMetric.ball x r,
    EMetric.ball_mem_nhds x hf.r_pos, fun y hy ↦ hf.eq_zero_of_bound_zero y hy⟩)

/-- If `f` has a formal power series on a ball bounded by `1`, then `f` is constant equal
to `f x` on the ball. -/
theorem HasFiniteFPowerSeriesOnBall.eq_const_of_bound_one
    (hf : HasFiniteFPowerSeriesOnBall f pf x 1 r) : ∀ y ∈ EMetric.ball x r, f y = f x := by
  intro y hy
  rw [hf.eq_partialSum' y hy 1 le_rfl, hf.eq_partialSum' x
    (by rw [EMetric.mem_ball, edist_self]; exact hf.r_pos) 1 le_rfl]
  simp only [FormalMultilinearSeries.partialSum, Finset.range_one, Finset.sum_singleton]
  congr
  apply funext
  simp only [IsEmpty.forall_iff]

/-- If `f` has a formal power series at x bounded by `1`, then `f` is constant equal
to `f x` in a neighborhood of `x`. -/
theorem HasFiniteFPowerSeriesAt.eventually_const_of_bound_one
    (hf : HasFiniteFPowerSeriesAt f pf x 1) : f =ᶠ[𝓝 x] (fun _ => f x) :=
  Filter.eventuallyEq_iff_exists_mem.mpr (let ⟨r, hf⟩ := hf; ⟨EMetric.ball x r,
    EMetric.ball_mem_nhds x hf.r_pos, fun y hy ↦ hf.eq_const_of_bound_one y hy⟩)

/-- If a function admits a finite power series expansion on a disk, then it is continuous there. -/
protected theorem HasFiniteFPowerSeriesOnBall.continuousOn
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    ContinuousOn f (EMetric.ball x r) := hf.1.continuousOn

protected theorem HasFiniteFPowerSeriesAt.continuousAt (hf : HasFiniteFPowerSeriesAt f p x n) :
    ContinuousAt f x := hf.hasFPowerSeriesAt.continuousAt

protected theorem CPolynomialAt.continuousAt (hf : CPolynomialAt 𝕜 f x) : ContinuousAt f x :=
  hf.analyticAt.continuousAt

protected theorem CPolynomialOn.continuousOn {s : Set E} (hf : CPolynomialOn 𝕜 f s) :
    ContinuousOn f s :=
  hf.analyticOnNhd.continuousOn

/-- Continuously polynomial everywhere implies continuous -/
theorem CPolynomialOn.continuous {f : E → F} (fa : CPolynomialOn 𝕜 f univ) : Continuous f := by
  rw [← continuousOn_univ]; exact fa.continuousOn

protected theorem FormalMultilinearSeries.sum_of_finite (p : FormalMultilinearSeries 𝕜 E F)
    {n : ℕ} (hn : ∀ m, n ≤ m → p m = 0) (x : E) :
    p.sum x = p.partialSum n x :=
  tsum_eq_sum fun m hm ↦ by rw [Finset.mem_range, not_lt] at hm; rw [hn m hm]; rfl

/-- A finite formal multilinear series sums to its sum at every point. -/
protected theorem FormalMultilinearSeries.hasSum_of_finite (p : FormalMultilinearSeries 𝕜 E F)
    {n : ℕ} (hn : ∀ m, n ≤ m → p m = 0) (x : E) :
    HasSum (fun n : ℕ => p n fun _ => x) (p.sum x) :=
  summable_of_ne_finset_zero (s := .range n)
    (fun m hm ↦ by rw [Finset.mem_range, not_lt] at hm; rw [hn m hm]; rfl)
    |>.hasSum

/-- The sum of a finite power series `p` admits `p` as a power series. -/
protected theorem FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite
    (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (hn : ∀ m, n ≤ m → p m = 0) :
    HasFiniteFPowerSeriesOnBall p.sum p 0 n ⊤ where
  r_le := by rw [radius_eq_top_of_forall_image_add_eq_zero p n fun _ => hn _ (Nat.le_add_left _ _)]
  r_pos := zero_lt_top
  finite := hn
  hasSum {y} _ := by rw [zero_add]; exact p.hasSum_of_finite hn y

theorem HasFiniteFPowerSeriesOnBall.sum (h : HasFiniteFPowerSeriesOnBall f p x n r) {y : E}
    (hy : y ∈ EMetric.ball (0 : E) r) : f (x + y) = p.sum y :=
  (h.hasSum hy).tsum_eq.symm

/-- The sum of a finite power series is continuous. -/
protected theorem FormalMultilinearSeries.continuousOn_of_finite
    (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (hn : ∀ m, n ≤ m → p m = 0) :
    Continuous p.sum := by
  rw [← continuousOn_univ, ← Metric.emetric_ball_top]
  exact (p.hasFiniteFPowerSeriesOnBall_of_finite hn).continuousOn

end FiniteFPowerSeries

namespace FormalMultilinearSeries

section

/-! We study what happens when we change the origin of a finite formal multilinear series `p`. The
main point is that the new series `p.changeOrigin x` is still finite, with the same bound. -/

/-- If `p` is a formal multilinear series such that `p m = 0` for `n ≤ m`, then
`p.changeOriginSeriesTerm k l = 0` for `n ≤ k + l`. -/
lemma changeOriginSeriesTerm_bound (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (hn : ∀ (m : ℕ), n ≤ m → p m = 0) (k l : ℕ) {s : Finset (Fin (k + l))}
    (hs : s.card = l) (hkl : n ≤ k + l) :
    p.changeOriginSeriesTerm k l s hs = 0 := by
  rw [changeOriginSeriesTerm, hn _ hkl, map_zero]

/-- If `p` is a finite formal multilinear series, then so is `p.changeOriginSeries k` for every
`k` in `ℕ`. More precisely, if `p m = 0` for `n ≤ m`, then `p.changeOriginSeries k m = 0` for
`n ≤ k + m`. -/
lemma changeOriginSeries_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (hn : ∀ (m : ℕ), n ≤ m → p m = 0) (k : ℕ) : ∀ {m : ℕ}, n ≤ k + m →
    p.changeOriginSeries k m = 0 := by
  intro m hm
  rw [changeOriginSeries]
  exact Finset.sum_eq_zero (fun _ _ => p.changeOriginSeriesTerm_bound hn _ _ _ hm)

lemma changeOriginSeries_sum_eq_partialSum_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (hn : ∀ (m : ℕ), n ≤ m → p m = 0) (k : ℕ) :
    (p.changeOriginSeries k).sum = (p.changeOriginSeries k).partialSum (n - k) := by
  ext x
  rw [partialSum, FormalMultilinearSeries.sum,
    tsum_eq_sum (f := fun m => p.changeOriginSeries k m (fun _ => x)) (s := Finset.range (n - k))]
  intro m hm
  rw [Finset.mem_range, not_lt] at hm
  rw [p.changeOriginSeries_finite_of_finite hn k (by rw [add_comm]; exact Nat.le_add_of_sub_le hm),
    ContinuousMultilinearMap.zero_apply]

/-- If `p` is a formal multilinear series such that `p m = 0` for `n ≤ m`, then
`p.changeOrigin x k = 0` for `n ≤ k`. -/
lemma changeOrigin_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (hn : ∀ (m : ℕ), n ≤ m → p m = 0) {k : ℕ} (hk : n ≤ k) :
    p.changeOrigin x k = 0 := by
  rw [changeOrigin, p.changeOriginSeries_sum_eq_partialSum_of_finite hn]
  apply Finset.sum_eq_zero
  intro m hm
  rw [Finset.mem_range] at hm
  rw [p.changeOriginSeries_finite_of_finite hn k (le_add_of_le_left hk),
    ContinuousMultilinearMap.zero_apply]

theorem hasFiniteFPowerSeriesOnBall_changeOrigin (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (k : ℕ) (hn : ∀ (m : ℕ), n + k ≤ m → p m = 0) :
    HasFiniteFPowerSeriesOnBall (p.changeOrigin · k) (p.changeOriginSeries k) 0 n ⊤ :=
  (p.changeOriginSeries k).hasFiniteFPowerSeriesOnBall_of_finite
    (fun _ hm => p.changeOriginSeries_finite_of_finite hn k
    (by rw [add_comm n k]; apply add_le_add_left hm))

theorem changeOrigin_eval_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ}
    (hn : ∀ (m : ℕ), n ≤ m → p m = 0) (x y : E) :
    (p.changeOrigin x).sum y = p.sum (x + y) := by
  let f (s : Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) : F :=
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ ↦ x) fun _ ↦ y
  have finsupp : f.support.Finite := by
    apply Set.Finite.subset (s := changeOriginIndexEquiv ⁻¹' (Sigma.fst ⁻¹' {m | m < n}))
    · apply Set.Finite.preimage (Equiv.injective _).injOn
      simp_rw [← {m | m < n}.iUnion_of_singleton_coe, preimage_iUnion, ← range_sigmaMk]
      exact finite_iUnion fun _ ↦ finite_range _
    · refine fun s ↦ Not.imp_symm fun hs ↦ ?_
      simp only [preimage_setOf_eq, changeOriginIndexEquiv_apply_fst, mem_setOf, not_lt] at hs
      dsimp only [f]
      rw [changeOriginSeriesTerm_bound p hn _ _ _ hs, ContinuousMultilinearMap.zero_apply,
        ContinuousMultilinearMap.zero_apply]
  have hfkl k l : HasSum (f ⟨k, l, ·⟩) (changeOriginSeries p k l (fun _ ↦ x) fun _ ↦ y) := by
    simp_rw [changeOriginSeries, ContinuousMultilinearMap.sum_apply]; apply hasSum_fintype
  have hfk k : HasSum (f ⟨k, ·⟩) (changeOrigin p x k fun _ ↦ y) := by
    have (m) (hm : m ∉ Finset.range n) : changeOriginSeries p k m (fun _ ↦ x) = 0 := by
      rw [Finset.mem_range, not_lt] at hm
      rw [changeOriginSeries_finite_of_finite _ hn _ (le_add_of_le_right hm),
        ContinuousMultilinearMap.zero_apply]
    rw [changeOrigin, FormalMultilinearSeries.sum,
      ContinuousMultilinearMap.tsum_eval (summable_of_ne_finset_zero this)]
    refine (summable_of_ne_finset_zero (s := Finset.range n) fun m hm ↦ ?_).hasSum.sigma_of_hasSum
      (hfkl k) (summable_of_finite_support <| finsupp.preimage sigma_mk_injective.injOn)
    rw [this m hm, ContinuousMultilinearMap.zero_apply]
  have hf : HasSum f ((p.changeOrigin x).sum y) :=
    ((p.changeOrigin x).hasSum_of_finite (fun _ ↦ changeOrigin_finite_of_finite p hn) _)
      |>.sigma_of_hasSum hfk (summable_of_finite_support finsupp)
  refine hf.unique (changeOriginIndexEquiv.symm.hasSum_iff.1 ?_)
  refine (p.hasSum_of_finite hn (x + y)).sigma_of_hasSum (fun n ↦ ?_)
    (changeOriginIndexEquiv.symm.summable_iff.2 hf.summable)
  rw [← Pi.add_def, (p n).map_add_univ (fun _ ↦ x) fun _ ↦ y]
  simp_rw [← changeOriginSeriesTerm_changeOriginIndexEquiv_symm]
  exact hasSum_fintype fun c ↦ f (changeOriginIndexEquiv.symm ⟨n, c⟩)

/-- The terms of the formal multilinear series `p.changeOrigin` are continuously polynomial
as we vary the origin -/
theorem cpolynomialAt_changeOrigin_of_finite (p : FormalMultilinearSeries 𝕜 E F)
    {n : ℕ} (hn : ∀ (m : ℕ), n ≤ m → p m = 0) (k : ℕ) :
    CPolynomialAt 𝕜 (p.changeOrigin · k) 0 :=
  (p.hasFiniteFPowerSeriesOnBall_changeOrigin k fun _ h ↦ hn _ (le_self_add.trans h)).cpolynomialAt

end

end FormalMultilinearSeries

section

variable {x y : E}

theorem HasFiniteFPowerSeriesOnBall.changeOrigin (hf : HasFiniteFPowerSeriesOnBall f p x n r)
    (h : (‖y‖₊ : ℝ≥0∞) < r) :
    HasFiniteFPowerSeriesOnBall f (p.changeOrigin y) (x + y) n (r - ‖y‖₊) where
  r_le := (tsub_le_tsub_right hf.r_le _).trans p.changeOrigin_radius
  r_pos := by simp [h]
  finite _ hm := p.changeOrigin_finite_of_finite hf.finite hm
  hasSum {z} hz := by
    have : f (x + y + z) =
        FormalMultilinearSeries.sum (FormalMultilinearSeries.changeOrigin p y) z := by
      rw [mem_emetric_ball_zero_iff, lt_tsub_iff_right, add_comm] at hz
      rw [p.changeOrigin_eval_of_finite hf.finite, add_assoc, hf.sum]
      exact mem_emetric_ball_zero_iff.2 ((enorm_add_le _ _).trans_lt hz)
    rw [this]
    apply (p.changeOrigin y).hasSum_of_finite fun _ => p.changeOrigin_finite_of_finite hf.finite

/-- If a function admits a finite power series expansion `p` on an open ball `B (x, r)`, then
it is continuously polynomial at every point of this ball. -/
theorem HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) (h : y ∈ EMetric.ball x r) :
    CPolynomialAt 𝕜 f y := by
  have : (‖y - x‖₊ : ℝ≥0∞) < r := by simpa [edist_eq_enorm_sub] using h
  have := hf.changeOrigin this
  rw [add_sub_cancel] at this
  exact this.cpolynomialAt

theorem HasFiniteFPowerSeriesOnBall.cpolynomialOn (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    CPolynomialOn 𝕜 f (EMetric.ball x r) :=
  fun _y hy => hf.cpolynomialAt_of_mem hy

variable (𝕜 f)

/-- For any function `f` from a normed vector space to a normed vector space, the set of points
`x` such that `f` is continuously polynomial at `x` is open. -/
theorem isOpen_cpolynomialAt : IsOpen { x | CPolynomialAt 𝕜 f x } := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, n, r, hr⟩
  exact mem_of_superset (EMetric.ball_mem_nhds _ hr.r_pos) fun y hy => hr.cpolynomialAt_of_mem hy

variable {𝕜}

theorem CPolynomialAt.eventually_cpolynomialAt {f : E → F} {x : E} (h : CPolynomialAt 𝕜 f x) :
    ∀ᶠ y in 𝓝 x, CPolynomialAt 𝕜 f y :=
  (isOpen_cpolynomialAt 𝕜 f).mem_nhds h

theorem CPolynomialAt.exists_mem_nhds_cpolynomialOn {f : E → F} {x : E} (h : CPolynomialAt 𝕜 f x) :
    ∃ s ∈ 𝓝 x, CPolynomialOn 𝕜 f s :=
  h.eventually_cpolynomialAt.exists_mem

/-- If `f` is continuously polynomial at a point, then it is continuously polynomial in a
nonempty ball around that point. -/
theorem CPolynomialAt.exists_ball_cpolynomialOn {f : E → F} {x : E} (h : CPolynomialAt 𝕜 f x) :
    ∃ r : ℝ, 0 < r ∧ CPolynomialOn 𝕜 f (Metric.ball x r) :=
  Metric.isOpen_iff.mp (isOpen_cpolynomialAt _ _) _ h

end
