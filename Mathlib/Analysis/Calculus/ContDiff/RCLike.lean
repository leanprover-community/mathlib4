/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Higher differentiability over `ℝ` or `ℂ`
-/

@[expose] public section

noncomputable section

open Set Fin Filter Function

open scoped NNReal Topology

section Real

/-!
### Results over `ℝ` or `ℂ`
  The results in this section rely on the Mean Value Theorem, and therefore hold only over `ℝ` (and
  its extension fields such as `ℂ`).
-/

variable {n : WithTop ℕ∞} {𝕂 : Type*} [RCLike 𝕂] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕂 E'] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕂 F']

/-- If a function has a Taylor series at order at least 1, then at points in the interior of the
domain of definition, the term of order 1 of this series is a strict derivative of `f`. -/
theorem HasFTaylorSeriesUpToOn.hasStrictFDerivAt {n : WithTop ℕ∞}
    {s : Set E'} {f : E' → F'} {x : E'}
    {p : E' → FormalMultilinearSeries 𝕂 E' F'} (hf : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hs : s ∈ 𝓝 x) : HasStrictFDerivAt f ((continuousMultilinearCurryFin1 𝕂 E' F') (p x 1)) x :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hf.eventually_hasFDerivAt hn hs) <|
    (continuousMultilinearCurryFin1 𝕂 E' F').continuousAt.comp <| (hf.cont 1 hn).continuousAt hs

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem ContDiffAt.hasStrictFDerivAt' {f : E' → F'} {f' : E' →L[𝕂] F'} {x : E'}
    (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f f' x) (hn : 1 ≤ n) :
    HasStrictFDerivAt f f' x := by
  rcases hf.of_le hn 1 le_rfl with ⟨u, H, p, hp⟩
  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem] at H
  have := hp.hasStrictFDerivAt le_rfl H
  rwa [hf'.unique this.hasFDerivAt]

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem ContDiffAt.hasStrictDerivAt' {f : 𝕂 → F'} {f' : F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x)
    (hf' : HasDerivAt f f' x) (hn : 1 ≤ n) : HasStrictDerivAt f f' x :=
  hf.hasStrictFDerivAt' hf' hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
theorem ContDiffAt.hasStrictFDerivAt {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) :
    HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.hasStrictFDerivAt' (hf.differentiableAt hn).hasFDerivAt hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
theorem ContDiffAt.hasStrictDerivAt {f : 𝕂 → F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) :
    HasStrictDerivAt f (deriv f x) x :=
  (hf.hasStrictFDerivAt hn).hasStrictDerivAt

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
theorem ContDiff.hasStrictFDerivAt {f : E' → F'} {x : E'} (hf : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.contDiffAt.hasStrictFDerivAt hn

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
theorem ContDiff.hasStrictDerivAt {f : 𝕂 → F'} {x : 𝕂} (hf : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    HasStrictDerivAt f (deriv f x) x :=
  hf.contDiffAt.hasStrictDerivAt hn

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {p : E → FormalMultilinearSeries ℝ E F} {s : Set E} {x : E}

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
and `‖p x 1‖₊ < K`, then `f` is `K`-Lipschitz in a neighborhood of `x` within `s`. -/
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt
    (hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex ℝ s) (K : ℝ≥0)
    (hK : ‖p x 1‖₊ < K) : ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  set f' := fun y => continuousMultilinearCurryFin1 ℝ E F (p y 1)
  have hder : ∀ y ∈ s, HasFDerivWithinAt f (f' y) s y := fun y hy =>
    (hf.hasFDerivWithinAt le_rfl (subset_insert x s hy)).mono (subset_insert x s)
  have hcont : ContinuousWithinAt f' s x :=
    (continuousMultilinearCurryFin1 ℝ E F).continuousAt.comp_continuousWithinAt
      ((hf.cont _ le_rfl _ (mem_insert _ _)).mono (subset_insert x s))
  replace hK : ‖f' x‖₊ < K := by simpa only [f', LinearIsometryEquiv.nnnorm_map]
  exact
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
      (eventually_nhdsWithin_iff.2 <| Eventually.of_forall hder) hcont K hK

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
then `f` is Lipschitz in a neighborhood of `x` within `s`. -/
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith
    (hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex ℝ s) :
    ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t :=
  (exists_gt _).imp <| hf.exists_lipschitzOnWith_of_nnnorm_lt hs

/-- If `f` is `C^1` within a convex set `s` at `x`, then it is Lipschitz on a neighborhood of `x`
within `s`. -/
theorem ContDiffWithinAt.exists_lipschitzOnWith
    (hf : ContDiffWithinAt ℝ 1 f s x) (hs : Convex ℝ s) :
    ∃ K : ℝ≥0, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  rcases hf 1 le_rfl with ⟨t, hst, p, hp⟩
  rcases Metric.mem_nhdsWithin_iff.mp hst with ⟨ε, ε0, hε⟩
  replace hp : HasFTaylorSeriesUpToOn 1 f p (Metric.ball x ε ∩ insert x s) := hp.mono hε
  clear hst hε t
  rw [← insert_eq_of_mem (Metric.mem_ball_self ε0), ← insert_inter_distrib] at hp
  rcases hp.exists_lipschitzOnWith ((convex_ball _ _).inter hs) with ⟨K, t, hst, hft⟩
  rw [inter_comm, ← nhdsWithin_restrict' _ (Metric.ball_mem_nhds _ ε0)] at hst
  exact ⟨K, t, hst, hft⟩

/-- If `f` is `C^1` at `x` and `K > ‖fderiv 𝕂 f x‖`, then `f` is `K`-Lipschitz in a neighborhood of
`x`. -/
theorem ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt {f : E' → F'} {x : E'}
    (hf : ContDiffAt 𝕂 1 f x) (K : ℝ≥0) (hK : ‖fderiv 𝕂 f x‖₊ < K) :
    ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt le_rfl).exists_lipschitzOnWith_of_nnnorm_lt K hK

/-- If `f` is `C^1` at `x`, then `f` is Lipschitz in a neighborhood of `x`. -/
theorem ContDiffAt.exists_lipschitzOnWith {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x) :
    ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt le_rfl).exists_lipschitzOnWith

/-- If `f` is `C¹` on a convex set `s`, it is locally Lipschitz on `s`. -/
lemma ContDiffOn.locallyLipschitzOn {f : E → F} {s : Set E} (hs : Convex ℝ s)
    (hf : ContDiffOn ℝ 1 f s) : LocallyLipschitzOn s f := by
  intro x hx
  obtain ⟨K, t, ht, hf⟩ := ContDiffWithinAt.exists_lipschitzOnWith (hf x hx) hs
  use K, t

/-- If `f` is `C¹`, it is locally Lipschitz. -/
lemma ContDiff.locallyLipschitz {f : E' → F'} (hf : ContDiff 𝕂 1 f) : LocallyLipschitz f := by
  intro x
  rcases hf.contDiffAt.exists_lipschitzOnWith with ⟨K, t, ht, hf⟩
  use K, t

-- TODO: find home
protected lemma LipschitzOnWith.closure {α β : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] {f : α → β} {s : Set α} {K : ℝ≥0}
    (hcont : ContinuousOn f (closure s)) (hf : LipschitzOnWith K f s) :
    LipschitzOnWith K f (closure s) := by
  have := ENNReal.continuous_const_mul (ENNReal.coe_ne_top (r := K))
  refine fun x hx ↦ le_on_closure (fun y hy ↦ le_on_closure (fun x hx ↦ hf hx hy) ?_ ?_ hx) ?_ ?_
  all_goals fun_prop

-- TODO: find home
open Metric in
/-- If `f` is locally Lipschitz on a compact set `s`, it is Lipschitz on `s`. -/
lemma LocallyLipschitzOn.exists_lipschitzOnWith_of_compact {α β : Type*} [PseudoMetricSpace α]
    [PseudoMetricSpace β] {f : α → β} {s : Set α} (hs : IsCompact s)
    (hf : LocallyLipschitzOn s f) : ∃ K, LipschitzOnWith K f s := by
  have hf' := hf.continuousOn
  replace hf : ∀ x ∈ s, ∃ ε > 0, ∃ K, LipschitzOnWith K f (ball x ε ∩ s) := fun x hx ↦ by
    let ⟨K, t, ht, hf⟩ := hf hx
    let ⟨ε, hε, hε'⟩ := Metric.mem_nhdsWithin_iff.1 ht
    exact ⟨ε, hε, K, hf.mono hε'⟩
  choose ε hε K hf using hf
  have : ∀ x (hx : x ∈ s), ∃ K' : ℝ≥0, ∀ y ∈ s.diff (ball x (ε x hx)),
      edist (f x) (f y) ≤ K' * edist x y := fun x hx ↦ by
    let ⟨K', hK'⟩ := (hs.diff isOpen_ball).bddAbove_image
      (f := fun y ↦ dist (f x) (f y) / dist x y) <| .div (.mono (by fun_prop) s.diff_subset)
        (by fun_prop) fun y hy ↦ ((hε x hx).trans_le <| not_lt.1 <| dist_comm x y ▸ hy.2).ne.symm
    refine ⟨⟨K' ⊔ 0, le_sup_right⟩, fun y hy ↦ ?_⟩
    rw [edist_nndist, edist_nndist, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    refine (div_le_iff₀ ?_).1 ?_
    · exact NNReal.coe_pos.1 <| coe_nndist x y ▸
        ((hε x hx).trans_le <| not_lt.1 <| dist_comm x y ▸ hy.2)
    · simp [← NNReal.coe_le_coe, (mem_upperBounds.1 hK') _ <| Set.mem_image_of_mem _ hy]
  choose K' hK' using this
  obtain ⟨t, ht⟩ := hs.elim_nhdsWithin_subcover' (fun x hx ↦ s ∩ ball x (ε x hx / 2))
    (fun x hx ↦ inter_mem_nhdsWithin s <| ball_mem_nhds x <| half_pos <| hε x hx)
  use t.sup fun i ↦ K _ i.2 + 2 * K' _ i.2
  intro x hx y hy
  let ⟨z, hz, hx'⟩ := mem_iUnion₂.1 <| ht hx
  by_cases hy' : y ∈ ball z.1 (ε _ z.2)
  · refine (hf _ z.2 ⟨hx'.2.trans <| half_lt_self <| hε _ z.2, hx⟩ ⟨hy', hy⟩).trans <|
      mul_le_mul_of_nonneg_right ?_ <| zero_le _
    exact ENNReal.coe_le_coe.2 <| t.le_sup_of_le hz <| le_self_add
  · refine (edist_triangle_left _ _ (f z)).trans ?_
    refine .trans ?_ <| mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.2 <| t.le_sup hz) (zero_le _)
    refine (add_le_add (hf _ z.2 ⟨mem_ball_self <| hε _ z.2, z.2⟩ ⟨hx'.2.trans <| half_lt_self <|
      hε _ z.2, hx⟩) <| hK' _ z.2 _ ⟨hy, hy'⟩).trans ?_
    refine (add_le_add_left (mul_le_mul_of_nonneg_left (edist_triangle_left z.1 y x)
      (zero_le _)) _).trans ?_
    simp_rw [edist_dist, ENNReal.coe_nnreal_eq]
    rw [← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add, ← ENNReal.ofReal_mul,
      ← ENNReal.ofReal_add, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat,
      mul_add, ← add_assoc, dist_comm, ← add_mul]
    · have h : dist x z ≤ dist x y := by
        linarith [mem_ball.1 hx'.2, (not_lt (α := ℝ)).1 hy', dist_triangle_left y z x]
      apply ENNReal.ofReal_le_ofReal
      refine (add_le_add_right (mul_le_mul_of_nonneg_left h (by positivity)) _).trans ?_
      linarith
    all_goals positivity

/-- If `f` is `C¹` on a convex compact set `s`, it is Lipschitz on `s`. -/
theorem ContDiffOn.exists_lipschitzOnWith {s : Set E} {f : E → F} {n} (hf : ContDiffOn ℝ n f s)
    (hn : 1 ≤ n) (hs : Convex ℝ s) (hs' : IsCompact s) :
    ∃ K, LipschitzOnWith K f s := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs'
  apply (hf.of_le hn).locallyLipschitzOn hs

/-- A `C^n` function with compact support is Lipschitz. -/
theorem ContDiff.lipschitzWith_of_hasCompactSupport {f : E' → F'}
    (hf : HasCompactSupport f) (h'f : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    ∃ C, LipschitzWith C f := by
  obtain ⟨C, hC⟩ := (hf.fderiv 𝕂).exists_bound_of_continuous (h'f.continuous_fderiv hn)
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (h'f.differentiable hn) (fun x ↦ ?_)
  simp [← NNReal.coe_le_coe, hC x]

end Real
