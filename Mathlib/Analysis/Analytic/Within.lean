/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Analysis.Analytic.Constructions
-- import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Properties of analyticity restricted to a set

From `Mathlib.Analysis.Analytic.Basic`, we have the definitions

1. `AnalyticWithinAt 𝕜 f s x` means a power series at `x` converges to `f` on `𝓝[insert x s] x`.
2. `AnalyticWithinOn 𝕜 f s t` means `∀ x ∈ t, AnalyticWithinAt 𝕜 f s x`.

This means there exists an extension of `f` which is analytic and agrees with `f` on `s ∪ {x}`, but
`f` is allowed to be arbitrary elsewhere.

Here we prove basic properties of these definitions. Where convenient we assume completeness of the
ambient space, which allows us to relate `AnalyticWithinAt` to analyticity of a local extension.
-/

noncomputable section

open Topology Filter ENNReal

open Set Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

/-!
### Basic properties
-/

lemma HasFPowerSeriesWithinOnBall.congr {f g : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {s : Set E} {x : E} {r : ℝ≥0∞} (h : HasFPowerSeriesWithinOnBall f p s x r)
    (h' : EqOn g f (s ∩ EMetric.ball x r)) (h'' : g x = f x) :
    HasFPowerSeriesWithinOnBall g p s x r := by
  refine ⟨h.r_le, h.r_pos, ?_⟩
  · intro y hy h'y
    convert h.hasSum hy h'y using 1
    simp only [mem_insert_iff, add_right_eq_self] at hy
    rcases hy with rfl | hy
    · simpa using h''
    · apply h'
      refine ⟨hy, ?_⟩
      simpa [edist_eq_coe_nnnorm_sub] using h'y

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

/-- `AnalyticWithinAt` is trivial if `{x} ∈ 𝓝[s] x` -/
lemma analyticWithinAt_of_singleton_mem {f : E → F} {s : Set E} {x : E} (h : {x} ∈ 𝓝[s] x) :
    AnalyticWithinAt 𝕜 f s x := by
  rcases mem_nhdsWithin.mp h with ⟨t, ot, xt, st⟩
  rcases Metric.mem_nhds_iff.mp (ot.mem_nhds xt) with ⟨r, r0, rt⟩
  exact ⟨constFormalMultilinearSeries 𝕜 E (f x), .ofReal r,
  { r_le := by simp only [FormalMultilinearSeries.constFormalMultilinearSeries_radius, le_top]
    r_pos := by positivity
    hasSum := by
      intro y ys yr
      simp only [subset_singleton_iff, mem_inter_iff, and_imp] at st
      simp only [mem_insert_iff, add_right_eq_self] at ys
      have : x + y = x := by
        rcases ys with rfl | ys
        · simp
        · exact st (x + y) (rt (by simpa using yr)) ys
      simp only [this]
      apply (hasFPowerSeriesOnBall_const (e := 0)).hasSum
      simp only [Metric.emetric_ball_top, mem_univ] }⟩

lemma AnalyticWithinOn.continuousOn {f : E → F} {s : Set E} (h : AnalyticWithinOn 𝕜 f s) :
    ContinuousOn f s :=
  fun x m ↦ (h x m).continuousWithinAt.mono (by simp)

/-- If `f` is `AnalyticWithinOn` near each point in a set, it is `AnalyticWithinOn` the set -/
lemma analyticWithinOn_of_locally_analyticWithinOn {f : E → F} {s : Set E}
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ AnalyticWithinOn 𝕜 f (s ∩ u)) :
    AnalyticWithinOn 𝕜 f s := by
  intro x m
  rcases h x m with ⟨u, ou, xu, fu⟩
  rcases Metric.mem_nhds_iff.mp (ou.mem_nhds xu) with ⟨r, r0, ru⟩
  rcases fu x ⟨m, xu⟩ with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
    { r_pos := lt_min (by positivity) fp.r_pos
      r_le := min_le_of_right_le fp.r_le
      hasSum := by
        intro y ys yr
        simp only [EMetric.mem_ball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at yr
        apply fp.hasSum
        · simp only [mem_insert_iff, add_right_eq_self] at ys
          rcases ys with rfl | ys
          · simp
          · simp only [mem_insert_iff, add_right_eq_self, mem_inter_iff, ys, true_and]
            apply Or.inr (ru ?_)
            simp only [Metric.mem_ball, dist_self_add_left, yr]
        · simp only [EMetric.mem_ball, yr] }⟩

/-- On open sets, `AnalyticOn` and `AnalyticWithinOn` coincide -/
@[simp] lemma IsOpen.analyticWithinOn_iff_analyticOn {f : E → F} {s : Set E} (hs : IsOpen s) :
    AnalyticWithinOn 𝕜 f s ↔ AnalyticOn 𝕜 f s := by
  refine ⟨?_, AnalyticOn.analyticWithinOn⟩
  intro hf x m
  rcases Metric.mem_nhds_iff.mp (hs.mem_nhds m) with ⟨r, r0, rs⟩
  rcases hf x m with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
  { r_pos := lt_min (by positivity) fp.r_pos
    r_le := min_le_of_right_le fp.r_le
    hasSum := by
      intro y ym
      simp only [EMetric.mem_ball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at ym
      refine fp.hasSum ?_ ym.2
      apply mem_insert_of_mem
      apply rs
      simp only [Metric.mem_ball, dist_self_add_left, ym.1] }⟩


/-!
### Congruence
-/

lemma AnalyticWithinAt.congr_of_eventuallyEq {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : g =ᶠ[𝓝[s] x] f) (hx : g x = f x) :
    AnalyticWithinAt 𝕜 g s x := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p, hp.congr hs hx⟩

lemma AnalyticWithinAt.congr {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : EqOn g f s) (hx : g x = f x) :
    AnalyticWithinAt 𝕜 g s x :=
  hf.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx

lemma AnalyticWithinOn.congr {f g : E → F} {s : Set E}
    (hf : AnalyticWithinOn 𝕜 f s) (hs : EqOn g f s) :
    AnalyticWithinOn 𝕜 g s :=
  fun x m ↦ (hf x m).congr hs (hs m)

/-!
### Equivalence to analyticity of a local extension

We show that `HasFPowerSeriesWithinOnBall`, `HasFPowerSeriesWithinAt`, and `AnalyticWithinAt` are
equivalent to the existence of a local extension with full analyticity.  We do not yet show a
result for `AnalyticWithinOn`, as this requires a bit more work to show that local extensions can
be stitched together.
-/

/-- `f` has power series `p` at `x` iff some local extension of `f` has that series -/
lemma hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞} :
    HasFPowerSeriesWithinOnBall f p s x r ↔
      ∃ g, EqOn f g (insert x s ∩ EMetric.ball x r) ∧
        HasFPowerSeriesOnBall g p x r := by
  constructor
  · intro h
    refine ⟨fun y ↦ p.sum (y - x), ?_, ?_⟩
    · intro y ⟨ys,yb⟩
      simp only [EMetric.mem_ball, edist_eq_coe_nnnorm_sub] at yb
      have e0 := p.hasSum (x := y - x) ?_
      have e1 := (h.hasSum (y := y - x) ?_ ?_)
      · simp only [add_sub_cancel] at e1
        exact e1.unique e0
      · simpa only [add_sub_cancel]
      · simpa only [EMetric.mem_ball, edist_eq_coe_nnnorm]
      · simp only [EMetric.mem_ball, edist_eq_coe_nnnorm]
        exact lt_of_lt_of_le yb h.r_le
    · refine ⟨h.r_le, h.r_pos, ?_⟩
      intro y lt
      simp only [add_sub_cancel_left]
      apply p.hasSum
      simp only [EMetric.mem_ball] at lt ⊢
      exact lt_of_lt_of_le lt h.r_le
  · intro ⟨g, hfg, hg⟩
    refine ⟨hg.r_le, hg.r_pos, ?_⟩
    intro y ys lt
    rw [hfg]
    · exact hg.hasSum lt
    · refine ⟨ys, ?_⟩
      simpa only [EMetric.mem_ball, edist_eq_coe_nnnorm_sub, add_sub_cancel_left, sub_zero] using lt

/-- `f` has power series `p` at `x` iff some local extension of `f` has that series -/
lemma hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} :
    HasFPowerSeriesWithinAt f p s x ↔
      ∃ g, f =ᶠ[𝓝[insert x s] x] g ∧ HasFPowerSeriesAt g p x := by
  constructor
  · intro ⟨r, h⟩
    rcases hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mp h with ⟨g, e, h⟩
    refine ⟨g, ?_, ⟨r, h⟩⟩
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, ?_, e⟩
    exact inter_mem_nhdsWithin _ (EMetric.ball_mem_nhds _ h.r_pos)
  · intro ⟨g, hfg, ⟨r, hg⟩⟩
    simp only [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff] at hfg
    rcases hfg with ⟨e, e0, hfg⟩
    refine ⟨min r (.ofReal e), ?_⟩
    refine hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mpr ⟨g, ?_, ?_⟩
    · intro y ⟨ys, xy⟩
      refine hfg ?_ ys
      simp only [EMetric.mem_ball, lt_min_iff, edist_lt_ofReal] at xy
      exact xy.2
    · exact hg.mono (lt_min hg.r_pos (by positivity)) (min_le_left _ _)

/-- `f` is analytic within `s` at `x` iff some local extension of `f` is analytic at `x` -/
lemma analyticWithinAt_iff_exists_analyticAt [CompleteSpace F] {f : E → F} {s : Set E} {x : E} :
    AnalyticWithinAt 𝕜 f s x ↔
      ∃ g, f =ᶠ[𝓝[insert x s] x] g ∧ AnalyticAt 𝕜 g x := by
  simp only [AnalyticWithinAt, AnalyticAt, hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt]
  tauto

/-- `f` is analytic within `s` at `x` iff some local extension of `f` is analytic at `x`. In this
version, we make sure that the extension coincides with `f` on all of `insert x s`. -/
lemma analyticWithinAt_iff_exists_analyticAt' [CompleteSpace F] {f : E → F} {s : Set E} {x : E} :
    AnalyticWithinAt 𝕜 f s x ↔
      ∃ g, f x = g x ∧ EqOn f g (insert x s) ∧ AnalyticAt 𝕜 g x := by
  classical
  simp only [analyticWithinAt_iff_exists_analyticAt]
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hf, hg⟩
    rcases mem_nhdsWithin.1 hf with ⟨u, u_open, xu, hu⟩
    let g' := Set.piecewise u g f
    refine ⟨g', ?_, ?_, ?_⟩
    · have : x ∈ u ∩ insert x s := ⟨xu, by simp⟩
      simpa [g', xu, this] using hu this
    · intro y hy
      by_cases h'y : y ∈ u
      · have : y ∈ u ∩ insert x s := ⟨h'y, hy⟩
        simpa [g', h'y, this] using hu this
      · simp [g', h'y]
    · apply hg.congr
      filter_upwards [u_open.mem_nhds xu] with y hy using by simp [g', hy]
  · rintro ⟨g, -, hf, hg⟩
    exact ⟨g, by filter_upwards [self_mem_nhdsWithin] using hf, hg⟩

alias ⟨AnalyticWithinAt.exists_analyticAt, _⟩ := analyticWithinAt_iff_exists_analyticAt'

lemma AnalyticWithinAt.exists_mem_nhdsWithin_analyticWithinOn
    [CompleteSpace F] {f : E → F} {s : Set E} {x : E} (h : AnalyticWithinAt 𝕜 f s x) :
    ∃ u ∈ 𝓝[insert x s] x, AnalyticWithinOn 𝕜 f u := by
  obtain ⟨g, -, h'g, hg⟩ : ∃ g, f x = g x ∧ EqOn f g (insert x s) ∧ AnalyticAt 𝕜 g x :=
    h.exists_analyticAt
  let u := insert x s ∩ {y | AnalyticAt 𝕜 g y}
  refine ⟨u, ?_, ?_⟩
  · exact inter_mem_nhdsWithin _ ((isOpen_analyticAt 𝕜 g).mem_nhds hg)
  · intro y hy
    have : AnalyticWithinAt 𝕜 g u y := hy.2.analyticWithinAt
    exact this.congr (h'g.mono (inter_subset_left)) (h'g (inter_subset_left hy))

/-!
### Monotonicity w.r.t. the set we're analytic within
-/

theorem AnalyticWithinAt.mono_of_mem {f : E → F} {s t : Set E} {x : E}
    (h : AnalyticWithinAt 𝕜 f s x) (hst : s ∈ 𝓝[t] x) : AnalyticWithinAt 𝕜 f t x := by
  rcases h with ⟨p, r, hr⟩
  rcases EMetric.mem_nhdsWithin_iff.1 hst with ⟨r', r'_pos, hr'⟩
  refine ⟨p, min r r', ?_⟩
  have Z := hr.of_le (by simp [r'_pos, hr.r_pos]) (min_le_left r r')
  refine ⟨Z.r_le, Z.r_pos, fun {y} hy h'y ↦ ?_⟩
  apply Z.hasSum ?_ h'y
  simp only [mem_insert_iff, add_right_eq_self] at hy
  rcases hy with rfl | hy
  · simp
  apply mem_insert_of_mem _ (hr' ?_)
  simp only [EMetric.mem_ball, edist_eq_coe_nnnorm_sub, sub_zero, lt_min_iff, mem_inter_iff,
    add_sub_cancel_left, hy, and_true] at h'y ⊢
  exact h'y.2

lemma AnalyticWithinOn.mono {f : E → F} {s t : Set E} (h : AnalyticWithinOn 𝕜 f t)
    (hs : s ⊆ t) : AnalyticWithinOn 𝕜 f s :=
  fun _ m ↦ (h _ (hs m)).mono hs

@[simp] lemma hasFPowerSeriesWithinOnBall_insert_self {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞} :
    HasFPowerSeriesWithinOnBall f p (insert x s) x r ↔ HasFPowerSeriesWithinOnBall f p s x r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩  <;>
  exact ⟨h.r_le, h.r_pos, fun {y} ↦ by simpa only [insert_idem] using h.hasSum (y := y)⟩

@[simp] theorem hasFPowerSeriesAt_insert_self {f : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {s : Set E} {x : E} :
    HasFPowerSeriesWithinAt f p (insert x s) x ↔ HasFPowerSeriesWithinAt f p s x := by
  simp [HasFPowerSeriesWithinAt]

@[simp] theorem analyticWithinAt_insert_self {f : E → F} {s : Set E} {x : E} :
    AnalyticWithinAt 𝕜 f (insert x s) x ↔ AnalyticWithinAt 𝕜 f s x := by
  simp [AnalyticWithinAt]


/-!
### Analyticity within respects composition

-/

lemma AnalyticWithinOn.comp {f : F → G} {g : E → F} {s : Set F}
    {t : Set E} (hf : AnalyticWithinOn 𝕜 f s) (hg : AnalyticWithinOn 𝕜 g t) (h : MapsTo g t s) :
    AnalyticWithinOn 𝕜 (f ∘ g) t :=
  fun x m ↦ (hf _ (h m)).comp (hg x m) h

lemma AnalyticOn.comp_analyticWithinOn {f : F → G} {g : E → F} {s : Set F}
    {t : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticWithinOn 𝕜 g t) (h : MapsTo g t s) :
    AnalyticWithinOn 𝕜 (f ∘ g) t :=
  fun x m ↦ (hf _ (h m)).comp_analyticWithinAt (hg x m)

/-!
### Analyticity within implies smoothness
-/

/-
lemma AnalyticWithinAt.contDiffWithinAt [CompleteSpace F] {f : E → F} {s : Set E} {x : E}
    (h : AnalyticWithinAt 𝕜 f s x) {n : ℕ∞} : ContDiffWithinAt 𝕜 n f s x := by
  rcases h.exists_analyticAt with ⟨g, fx, fg, hg⟩
  exact hg.contDiffAt.contDiffWithinAt.congr_of_eventuallyEq fg fx

lemma AnalyticWithinOn.contDiffOn [CompleteSpace F] {f : E → F} {s : Set E}
    (h : AnalyticWithinOn 𝕜 f s) {n : ℕ∞} : ContDiffOn 𝕜 n f s :=
  fun x m ↦ (h x m).contDiffWithinAt
-/


/-!
### Analyticity within respects products
-/

lemma HasFPowerSeriesWithinOnBall.prod {e : E} {f : E → F} {g : E → G} {s : Set E} {r t : ℝ≥0∞}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinOnBall f p s e r) (hg : HasFPowerSeriesWithinOnBall g q s e t) :
    HasFPowerSeriesWithinOnBall (fun x ↦ (f x, g x)) (p.prod q) s e (min r t) where
  r_le := by
    rw [p.radius_prod_eq_min]
    exact min_le_min hf.r_le hg.r_le
  r_pos := lt_min hf.r_pos hg.r_pos
  hasSum := by
    intro y m hy
    simp_rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.prod_apply]
    refine (hf.hasSum m ?_).prod_mk (hg.hasSum m ?_)
    · exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left _ _))
    · exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_right _ _))

lemma HasFPowerSeriesWithinAt.prod {e : E} {f : E → F} {g : E → G} {s : Set E}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinAt f p s e) (hg : HasFPowerSeriesWithinAt g q s e) :
    HasFPowerSeriesWithinAt (fun x ↦ (f x, g x)) (p.prod q) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

lemma AnalyticWithinAt.prod {e : E} {f : E → F} {g : E → G} {s : Set E}
    (hf : AnalyticWithinAt 𝕜 f s e) (hg : AnalyticWithinAt 𝕜 g s e) :
    AnalyticWithinAt 𝕜 (fun x ↦ (f x, g x)) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

lemma AnalyticWithinOn.prod {f : E → F} {g : E → G} {s : Set E}
    (hf : AnalyticWithinOn 𝕜 f s) (hg : AnalyticWithinOn 𝕜 g s) :
    AnalyticWithinOn 𝕜 (fun x ↦ (f x, g x)) s :=
  fun x hx ↦ (hf x hx).prod (hg x hx)

/-!
### Analyticity in Pi spaces
-/

variable {ι : Type*} [Fintype ι] {e : E} {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    {f : Π i, E → F i} {s : Set E} {r : ℝ≥0∞}
    {p : Π i, FormalMultilinearSeries 𝕜 E (F i)}

lemma FormalMultilinearSeries.le_pi_radius (h : ∀ i, r ≤ (p i).radius) :
    r ≤ (FormalMultilinearSeries.pi p).radius := by
  apply le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  have I i : ∃ C > 0, ∀ n, ‖p i n‖ * (r' : ℝ) ^ n ≤ C :=
    norm_mul_pow_le_of_lt_radius _ (hr'.trans_le (h i))
  choose C C_pos hC using I
  obtain ⟨D, D_nonneg, hD⟩ : ∃ D ≥ 0, ∀ i, C i ≤ D := by
    refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ ↦ (C_pos i).le),
      fun i ↦ Finset.single_le_sum (fun j _ ↦ (C_pos j).le) (Finset.mem_univ _)⟩
  apply le_radius_of_bound _ D (fun n ↦ ?_)
  rcases le_or_lt ((r' : ℝ)^n) 0 with hr' | hr'
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hr') D_nonneg
  · simp only [pi]
    rw [← le_div_iff₀ hr', ContinuousMultilinearMap.opNorm_pi,
      pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    exact (le_div_iff₀ hr').2 ((hC i n).trans (hD i))

lemma HasFPowerSeriesWithinOnBall.pi
    (hf : ∀ i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r) (hr : 0 < r) :
    HasFPowerSeriesWithinOnBall (fun x ↦ (fun i ↦ f i x)) (FormalMultilinearSeries.pi p) s e r where
  r_le := by
    apply FormalMultilinearSeries.le_pi_radius (fun i ↦ ?_)
    exact (hf i).r_le
  r_pos := hr
  hasSum := by
    intro y m hy
    simp_rw [FormalMultilinearSeries.pi]
    apply Pi.hasSum.2 (fun i ↦ (hf i).hasSum m hy)

lemma HasFPowerSeriesOnBall.pi
    (hf : ∀ i, HasFPowerSeriesOnBall (f i) (p i) e r) (hr : 0 < r) :
    HasFPowerSeriesOnBall (fun x ↦ (fun i ↦ f i x)) (FormalMultilinearSeries.pi p) e r := by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact HasFPowerSeriesWithinOnBall.pi hf hr

lemma HasFPowerSeriesWithinAt.pi
    (hf : ∀ i, HasFPowerSeriesWithinAt (f i) (p i) s e) :
    HasFPowerSeriesWithinAt (fun x ↦ (fun i ↦ f i x)) (FormalMultilinearSeries.pi p) s e := by
  have : ∀ᶠ r in 𝓝[>] 0, ∀ i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r :=
    eventually_all.mpr (fun i ↦ (hf i).eventually)
  obtain ⟨r, hr, r_pos⟩ := (this.and self_mem_nhdsWithin).exists
  exact ⟨r, HasFPowerSeriesWithinOnBall.pi hr r_pos⟩

lemma HasFPowerSeriesAt.pi
    (hf : ∀ i, HasFPowerSeriesAt (f i) (p i) e) :
    HasFPowerSeriesAt (fun x ↦ (fun i ↦ f i x)) (FormalMultilinearSeries.pi p) e := by
  simp_rw [← hasFPowerSeriesWithinAt_univ] at hf ⊢
  exact HasFPowerSeriesWithinAt.pi hf

lemma AnalyticWithinAt.pi (hf : ∀ i, AnalyticWithinAt 𝕜 (f i) s e) :
    AnalyticWithinAt 𝕜 (fun x ↦ (fun i ↦ f i x)) s e := by
  choose p hp using hf
  exact ⟨FormalMultilinearSeries.pi p, HasFPowerSeriesWithinAt.pi hp⟩

lemma AnalyticAt.pi (hf : ∀ i, AnalyticAt 𝕜 (f i) e) :
    AnalyticAt 𝕜 (fun x ↦ (fun i ↦ f i x)) e := by
  simp_rw [← analyticWithinAt_univ] at hf ⊢
  exact AnalyticWithinAt.pi hf

lemma AnalyticWithinOn.pi (hf : ∀ i, AnalyticWithinOn 𝕜 (f i) s) :
    AnalyticWithinOn 𝕜 (fun x ↦ (fun i ↦ f i x)) s :=
  fun x hx ↦ AnalyticWithinAt.pi (fun i ↦ hf i x hx)

lemma AnalyticOn.pi (hf : ∀ i, AnalyticOn 𝕜 (f i) s) :
    AnalyticOn 𝕜 (fun x ↦ (fun i ↦ f i x)) s :=
  fun x hx ↦ AnalyticAt.pi (fun i ↦ hf i x hx)
