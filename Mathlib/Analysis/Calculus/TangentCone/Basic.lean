/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Basic properties of tangent cones and sets with unique differentiability property

In this file we prove basic lemmas about `tangentConeAt`, `UniqueDiffWithinAt`,
and `UniqueDiffOn`.
-/

public section

open Filter Set Metric
open scoped Topology Pointwise

variable {𝕜 E : Type*}

section SMul

variable [AddCommGroup E] [SMul 𝕜 E] [TopologicalSpace E] {s t : Set E} {x : E}

@[gcongr]
theorem tangentConeAt_mono (h : s ⊆ t) : tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x := by
  simp only [tangentConeAt_def, setOf_subset_setOf]
  refine fun y hy ↦ hy.mono ?_
  gcongr

/--
Given `x ∈ s` and a semiring extension `𝕜 ⊆ 𝕜'`, the tangent cone of `s` at `x` with
respect to `𝕜` is contained in the tangent cone of `s` at `x` with respect to `𝕜'`.
-/
theorem tangentConeAt_mono_field
    {𝕜' : Type*} [Monoid 𝕜'] [SMul 𝕜 𝕜'] [MulAction 𝕜' E] [IsScalarTower 𝕜 𝕜' E] :
    tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜' s x := by
  simp only [tangentConeAt_def, setOf_subset_setOf]
  refine fun y hy ↦ hy.mono ?_
  rw [← smul_one_smul (Filter 𝕜')]
  grw' [le_top (a := ⊤ • 1)]

theorem Filter.HasBasis.tangentConeAt_eq_biInter_closure {ι} {p : ι → Prop} {U : ι → Set E}
    (h : (𝓝 0).HasBasis p U) :
    tangentConeAt 𝕜 s x = ⋂ (i) (_ : p i), closure ((univ : Set 𝕜) • (U i ∩ (x + ·) ⁻¹' s)) := by
  ext y
  simp only [tangentConeAt_def, mem_setOf_eq, mem_iInter₂, ← map₂_smul, ← map_prod_eq_map₂,
    ((nhdsWithin_hasBasis h _).top_prod.map _).clusterPt_iff_forall_mem_closure, image_prod,
    image2_smul]

theorem tangentConeAt_eq_biInter_closure :
    tangentConeAt 𝕜 s x = ⋂ U ∈ 𝓝 0, closure ((univ : Set 𝕜) • (U ∩ (x + ·) ⁻¹' s)) :=
  (basis_sets _).tangentConeAt_eq_biInter_closure

variable [ContinuousAdd E]

theorem tangentConeAt_mono_nhds (h : 𝓝[s] x ≤ 𝓝[t] x) :
    tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x := by
  simp only [tangentConeAt_def, setOf_subset_setOf]
  refine fun y hy ↦ hy.mono ?_
  gcongr _ • ?_
  rw [nhdsWithin_le_iff]
  suffices Tendsto (x + ·) (𝓝[(x + ·) ⁻¹' s] 0) (𝓝[s] x) from
    this.mono_right h |> tendsto_nhdsWithin_iff.mp |>.2
  refine .inf ?_ (mapsTo_preimage _ _).tendsto
  exact (continuous_const_add x).tendsto' 0 x (add_zero _)

/-- Tangent cone of `s` at `x` depends only on `𝓝[s] x`. -/
theorem tangentConeAt_congr (h : 𝓝[s] x = 𝓝[t] x) : tangentConeAt 𝕜 s x = tangentConeAt 𝕜 t x :=
  Subset.antisymm (tangentConeAt_mono_nhds h.le) (tangentConeAt_mono_nhds h.ge)

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
theorem tangentConeAt_inter_nhds (ht : t ∈ 𝓝 x) : tangentConeAt 𝕜 (s ∩ t) x = tangentConeAt 𝕜 s x :=
  tangentConeAt_congr (nhdsWithin_restrict' _ ht).symm

theorem mem_closure_of_nonempty_tangentConeAt (h : (tangentConeAt 𝕜 s x).Nonempty) :
    x ∈ closure s := by
  rcases h with ⟨y, hy⟩
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, -, d, hd, hds, -⟩
  refine mem_closure_of_tendsto ?_ hds
  simpa using tendsto_const_nhds.add hd

variable [ContinuousConstSMul 𝕜 E]

@[simp]
theorem tangentConeAt_closure : tangentConeAt 𝕜 (closure s) x = tangentConeAt 𝕜 s x := by
  refine Subset.antisymm ?_ (tangentConeAt_mono subset_closure)
  simp only [(nhds_basis_opens _).tangentConeAt_eq_biInter_closure]
  refine iInter₂_mono fun U hU ↦ closure_minimal ?_ isClosed_closure
  grw [(isOpenMap_add_left x).preimage_closure_subset_closure_preimage, hU.2.inter_closure,
    set_smul_closure_subset]

end SMul

section Module

variable [AddCommGroup E] [Semiring 𝕜] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E]
  {s t : Set E} {x : E}

omit [ContinuousAdd E] in
theorem UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ t) :
    UniqueDiffWithinAt 𝕜 t x := by
  rw [uniqueDiffWithinAt_iff] at *
  grw [← st]
  exact h

omit [ContinuousAdd E] in
protected theorem UniqueDiffWithinAt.closure (h : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜 (closure s) x :=
  h.mono subset_closure

theorem UniqueDiffWithinAt.mono_nhds (h : UniqueDiffWithinAt 𝕜 s x) (st : 𝓝[s] x ≤ 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 t x := by
  simp only [uniqueDiffWithinAt_iff] at *
  rw [mem_closure_iff_nhdsWithin_neBot] at h ⊢
  exact ⟨h.1.mono <| Submodule.span_mono <| tangentConeAt_mono_nhds st, h.2.mono st⟩

theorem uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 s x ↔ UniqueDiffWithinAt 𝕜 t x :=
  ⟨fun h => h.mono_nhds <| le_of_eq st, fun h => h.mono_nhds <| le_of_eq st.symm⟩

theorem uniqueDiffWithinAt_inter (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict' _ ht).symm

theorem UniqueDiffWithinAt.inter (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter ht).2 hs

theorem UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsOpen t) : UniqueDiffOn 𝕜 (s ∩ t) :=
  fun x hx => (hs x hx.1).inter (IsOpen.mem_nhds ht hx.2)

theorem uniqueDiffWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict'' _ ht).symm

theorem UniqueDiffWithinAt.inter' (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter' ht).2 hs

/-- The tangent cone at a non-isolated point contains `0`. -/
theorem zero_mem_tangentConeAt (hx : x ∈ closure s) :
    0 ∈ tangentConeAt 𝕜 s x := by
  rw [mem_closure_iff_frequently] at hx
  apply mem_tangentConeAt_of_frequently (𝓝 x) 1 (· + (-x))
  · exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  · simpa
  · simp only [Pi.one_apply, one_smul]
    exact Continuous.tendsto' (by fun_prop) _ _ (by simp)

@[deprecated (since := "2026-01-21")]
alias zero_mem_tangentCone := zero_mem_tangentConeAt

@[simp]
theorem zero_mem_tangentConeAt_iff : 0 ∈ tangentConeAt 𝕜 s x ↔ x ∈ closure s :=
  ⟨fun h ↦ mem_closure_of_nonempty_tangentConeAt ⟨_, h⟩, zero_mem_tangentConeAt⟩

/-- If `x` is not an accumulation point of `s`, then the tangent cone of `s` at `x`
is a subset of `{0}`. -/
theorem tangentConeAt_subset_zero [T2Space E] (hx : ¬AccPt x (𝓟 s)) : tangentConeAt 𝕜 s x ⊆ 0 := by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  have H₁ : Tendsto (x + d ·) l (𝓝 x) := by
    simpa using tendsto_const_nhds.add hd₀
  have H₂ : ∀ᶠ n in l, d n = 0 := by
    simp only [accPt_iff_frequently, not_frequently, not_and', ne_eq, not_not] at hx
    simpa using hds.mp (H₁.eventually hx)
  have H₃ : ∀ᶠ n in l, c n • d n = 0 := H₂.mono fun n hn ↦ by simp [hn]
  simpa using tendsto_nhds_unique_of_eventuallyEq hcd tendsto_const_nhds H₃

theorem AccPt.of_mem_tangentConeAt_ne_zero [T2Space E] {y : E} (hy : y ∈ tangentConeAt 𝕜 s x)
    (hy₀ : y ≠ 0) : AccPt x (𝓟 s) := by
  contrapose hy₀
  exact tangentConeAt_subset_zero hy₀ hy

theorem UniqueDiffWithinAt.accPt [T2Space E] [Nontrivial E] (h : UniqueDiffWithinAt 𝕜 s x) :
    AccPt x (𝓟 s) := by
  by_contra! h'
  have : Dense (Submodule.span 𝕜 (0 : Set E) : Set E) :=
    h.1.mono <| by gcongr; exact tangentConeAt_subset_zero h'
  simp [dense_iff_closure_eq] at this

end Module

section TVS

variable [DivisionSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace 𝕜]
  [TopologicalSpace E] [ContinuousSMul 𝕜 E] {s : Set E} {x y : E}

theorem mem_tangentConeAt_of_add_smul_mem {α : Type*} {l : Filter α} [l.NeBot] {c : α → 𝕜}
    (hc₀ : Tendsto c l (𝓝[≠] 0)) (hmem : ∀ᶠ n in l, x + c n • y ∈ s) :
    y ∈ tangentConeAt 𝕜 s x := by
  rw [tendsto_nhdsWithin_iff] at hc₀
  refine mem_tangentConeAt_of_seq l c⁻¹ (c · • y) ?_ hmem ?_
  · simpa using hc₀.1.smul (tendsto_const_nhds (x := y))
  · refine tendsto_nhds_of_eventually_eq <| hc₀.2.mono fun n hn ↦ ?_
    simp_all

variable [(𝓝[≠] (0 : 𝕜)).NeBot]

@[simp]
theorem tangentConeAt_univ : tangentConeAt 𝕜 univ x = univ := by
  simp [tangentConeAt]

theorem tangentConeAt_of_mem_nhds [ContinuousAdd E] (h : s ∈ 𝓝 x) : tangentConeAt 𝕜 s x = univ := by
  rw [← s.univ_inter, tangentConeAt_inter_nhds h, tangentConeAt_univ]

end TVS

section UniqueDiff

/-!
### Properties of `UniqueDiffWithinAt` and `UniqueDiffOn`

This section is devoted to properties of the predicates `UniqueDiffWithinAt` and `UniqueDiffOn`. -/

section Semiring
variable [Semiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}

theorem uniqueDiffOn_empty : UniqueDiffOn 𝕜 (∅ : Set E) :=
  fun _ hx => hx.elim

theorem UniqueDiffWithinAt.congr_pt (h : UniqueDiffWithinAt 𝕜 s x) (hy : x = y) :
    UniqueDiffWithinAt 𝕜 s y := hy ▸ h

variable {𝕜' : Type*} [Semiring 𝕜'] [SMul 𝕜 𝕜'] [Module 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

/--
Assume that `E` is a normed vector space over semirings `𝕜 ⊆ 𝕜'` and that `x ∈ s` is a point
of unique differentiability with respect to the set `s` and the smaller semiring `𝕜`,
then `x` is also a point of unique differentiability with respect to the set `s`
and the larger semiring `𝕜'`.
-/
theorem UniqueDiffWithinAt.mono_field (hs : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜' s x := by
  simp_all only [uniqueDiffWithinAt_iff, and_true]
  apply Dense.mono _ hs.1
  trans ↑(Submodule.span 𝕜 (tangentConeAt 𝕜' s x)) <;>
    simp [Submodule.span_mono tangentConeAt_mono_field]

/--
Assume that `E` is a normed vector space over semirings `𝕜 ⊆ 𝕜'`
and all points of `s` are points of unique differentiability
with respect to the smaller semiring `𝕜`,
then they are also points of unique differentiability with respect to the larger semiring `𝕜`.
-/
theorem UniqueDiffOn.mono_field (hs : UniqueDiffOn 𝕜 s) : UniqueDiffOn 𝕜' s :=
  fun x hx ↦ (hs x hx).mono_field

variable [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]

@[simp]
theorem uniqueDiffWithinAt_closure :
    UniqueDiffWithinAt 𝕜 (closure s) x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp [uniqueDiffWithinAt_iff]

protected alias ⟨UniqueDiffWithinAt.of_closure, _⟩ := uniqueDiffWithinAt_closure

theorem UniqueDiffWithinAt.mono_closure (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ closure t) :
    UniqueDiffWithinAt 𝕜 t x :=
  (h.mono st).of_closure

end Semiring

section DivisionSemiring

variable [DivisionSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [TopologicalSpace 𝕜] [(𝓝[≠] (0 : 𝕜)).NeBot] [ContinuousSMul 𝕜 E]
  {x y : E} {s t : Set E}

@[simp]
theorem uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 univ x := by
  rw [uniqueDiffWithinAt_iff, tangentConeAt_univ]
  simp

@[simp]
theorem uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E) :=
  fun _ _ => uniqueDiffWithinAt_univ

variable [ContinuousAdd E]

theorem uniqueDiffWithinAt_of_mem_nhds (h : s ∈ 𝓝 x) : UniqueDiffWithinAt 𝕜 s x := by
  simpa only [univ_inter] using uniqueDiffWithinAt_univ.inter h

theorem IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs : x ∈ s) : UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_of_mem_nhds (IsOpen.mem_nhds hs xs)

theorem IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 𝕜 s :=
  fun _ hx => IsOpen.uniqueDiffWithinAt hs hx

end DivisionSemiring

end UniqueDiff
