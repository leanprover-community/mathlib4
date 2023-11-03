/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Tactic.RewriteSearch

/-!
# Charts are local diffeomorphisms

TODO: prove what I want to, then add a real docstring
-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

variable
  -- Let `M` be a manifold over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  --[SmoothManifoldWithCorners I M] {n : ℕ∞}

-- On any topological manifold (charted space on a normed space),
-- each chart is a structomorphism (from its source to its target).
variable {e e' : LocalHomeomorph M H} {G : StructureGroupoid H} [HasGroupoid M G]

/-- If `s` is a non-empty open subset of `M`, every chart of `s` is the restriction
 of some chart on `M`. -/
lemma chartOn_open_eq (s : Opens M) [Nonempty s] {e' : LocalHomeomorph s H} (he' : e' ∈ atlas H s) :
    ∃ x : s, e' = (chartAt H (x : M)).subtypeRestr s := by
  rcases he' with ⟨xset, ⟨x, hx⟩, he'⟩
  have : {LocalHomeomorph.subtypeRestr (chartAt H ↑x) s} = xset := hx
  exact ⟨x, mem_singleton_iff.mp (this ▸ he')⟩

-- XXX: can I unify this with `chartOn_open_eq`?
lemma chartOn_open_eq' (t : Opens H) [Nonempty t] {e' : LocalHomeomorph t H} (he' : e' ∈ atlas H t) :
    ∃ x : t, e' = (chartAt H ↑x).subtypeRestr t := by
  rcases he' with ⟨xset, ⟨x, hx⟩, he'⟩
  have : {LocalHomeomorph.subtypeRestr (chartAt H ↑x) t} = xset := hx
  exact ⟨x, mem_singleton_iff.mp (this ▸ he')⟩

open LocalHomeomorph in
/-- The maximal atlas of a structure groupoid is stable under equivalence. -/
lemma StructureGroupoid.mem_maximalAtlas_of_eqOnSource (h : e' ≈ e)
    (he : e ∈ G.maximalAtlas M) : e' ∈ G.maximalAtlas M := by
  intro e'' he''
  obtain ⟨l, r⟩ := mem_maximalAtlas_iff.mp he e'' he''
  exact ⟨G.eq_on_source l (EqOnSource.trans' (EqOnSource.symm' h) (e''.eqOnSource_refl)),
         G.eq_on_source r (EqOnSource.trans' (e''.symm).eqOnSource_refl h)⟩

/-- If `G` is closed under restriction, the transition function between
  the restriction of two charts `e` and `e'` lies in `G`. -/
theorem StructureGroupoid.trans_restricted (he : e ∈ atlas H M) (he' : e' ∈ atlas H M)
    [ClosedUnderRestriction G] (s : Opens M) [Nonempty s] :
    (e.subtypeRestr s).symm ≫ₕ e'.subtypeRestr s ∈ G := by
  have : (e.symm ≫ₕ e').restr (e.target ∩ e.symm ⁻¹' s) ∈ G := by
    let hopen := e.preimage_open_of_open_symm s.2
    refine G.locality fun x' hx' ↦ ⟨e.target ∩ e.symm ⁻¹' s, hopen, ?_, ?_ ⟩
    · exact interior_subset (mem_of_mem_inter_right hx')
    · exact closedUnderRestriction' (closedUnderRestriction' (G.compatible he he') hopen) hopen
  exact G.eq_on_source this (e.subtypeRestr_symm_trans_subtypeRestr s e')

/-- Restricting a chart of `M` to an open subset `s` yields a chart in the maximal atlas of `s`. -/
-- this is different from `closedUnderRestriction'` as we want membership in the maximal atlas
-- XXX: find a better name!
lemma StructureGroupoid.stable_under_restriction (he : e ∈ atlas H M) [ClosedUnderRestriction G]
    (s : Opens M) [Nonempty s] : e.subtypeRestr s ∈ G.maximalAtlas s := by
  intro e' he'
  -- `e'` is the restriction of some chart of `M` at `x`,
  obtain ⟨x, this⟩ := chartOn_open_eq s he'
  rw [this]
  -- The transition functions between the unrestricted charts are in the groupoid,
  -- the transition functions of the restriction are the restriction of the transition function.
  exact ⟨G.trans_restricted he (chart_mem_atlas H (x : M)) s,
         G.trans_restricted (chart_mem_atlas H (x : M)) he s⟩

-- real proof that local homeos induce a chart
-- xxx: find a better name and description!
theorem StructureGroupoid.restriction_chart (he : e ∈ atlas H M) [ClosedUnderRestriction G]
    (hs : Nonempty e.source) :
    let s := { carrier := e.source, is_open' := e.open_source : Opens M };
    let t := { carrier := e.target, is_open' := e.open_target  : Opens H };
    ∀ c' ∈ atlas H t, (e.toHomeomorphSourceTarget).toLocalHomeomorph ≫ₕ c' ∈ G.maximalAtlas s := by
  intro s t c' hc'
  have : Nonempty t := sorry -- -- easy, `e` is a bijection from `s` to `t`
  set e' := e.toHomeomorphSourceTarget.toLocalHomeomorph with eq -- source s, target t
  -- Choose `x ∈ t` so c' is the restriction of `chartAt H x`.
  obtain ⟨x, hc'⟩ := chartOn_open_eq' t hc'
  -- As H has only one chart, this chart is the identity: i.e., c' is the inclusion.
  rw [hc', (chartAt_self_eq)]
  -- Simplify slightly.
  rw [LocalHomeomorph.subtypeRestr_def, LocalHomeomorph.trans_refl]
  -- Argue that our expression equals this chart above, at least on its source.
  set goal := (e' ≫ₕ Opens.localHomeomorphSubtypeCoe t)
  have : goal ≈ e.subtypeRestr s :=
    (goal.eqOnSource_iff (e.subtypeRestr s)).mpr ⟨by simp, by intro x'' hx''; rfl⟩
  exact G.mem_maximalAtlas_of_eqOnSource (M := s) this (G.stable_under_restriction he s)

/-- Charts are structomorphisms. -/
-- xxx: do I need [ClosedUnderRestriction G]? in practice, is not an issue
lemma LocalHomeomorphism.toStructomorph (he : e ∈ atlas H M) [ClosedUnderRestriction G] : Structomorph G M H := by
  let s : Opens M := { carrier := e.source, is_open' := e.open_source }
  let t : Opens H := { carrier := e.target, is_open' := e.open_target }
  by_cases s = (∅ : Set M)
  · sorry -- trivial, TODO fill in!
  have hs : Nonempty s := nonempty_iff_ne_empty'.mpr h
  have : Structomorph G s t := {
    e.toHomeomorphSourceTarget with
    mem_groupoid := by
      intro c c' hc hc'
      show (c.symm).trans (e.toHomeomorphSourceTarget.toLocalHomeomorph.trans c') ∈ G
      -- The atlas on H on itself has only one chart (by `chartedSpaceSelf_atlas H`),
      -- hence c' (as a restriction of that) is the inclusion.
      -- This *almost* gives our claim: except that `e` is a chart on M and c is one on s:
      -- `real_helper` argues the restricted chart belongs to the maximal atlas, making this rigorous.
      -- so they don't fit together nicely. (Composing with the inclusion makes that nice...)
      apply G.compatible_of_mem_maximalAtlas (G.subset_maximalAtlas hc) (G.restriction_chart he hs c' hc')
  }
  sorry

-- /-- Each chart inverse is a structomorphism. -/
-- -- essentially re-use the proof above!
-- lemma LocalHomeomorphism.symm_toStructomorph {e : LocalHomeomorph M H} (he : e ∈ atlas H M)
--     {G : StructureGroupoid H} : Structomorph G M H := sorry

-- TODO: Generalise this to all extended charts, if `I` is boundaryless.
