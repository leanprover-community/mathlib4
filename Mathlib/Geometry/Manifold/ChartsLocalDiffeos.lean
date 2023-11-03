/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Tactic.RewriteSearch

/-!
# Charts are structomorphisms

We prove that charts of a charted space are `Structomorph`s.
For a `C^n` manifold in particular, this implies charts are `C^n` diffeomorphisms.
-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

-- Let `M` be a charted space modelled on `H`, with structure groupoid `G`.
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {G : StructureGroupoid H} [HasGroupoid M G]
  {e e' : LocalHomeomorph M H}

/-- If `G` is closed under restriction, the transition function between
  the restriction of two charts `e` and `e'` lies in `G`. -/
theorem StructureGroupoid.trans_restricted (he : e ∈ atlas H M) (he' : e' ∈ atlas H M)
    [ClosedUnderRestriction G] (s : Opens M) [Nonempty s] :
    (e.subtypeRestr s).symm ≫ₕ e'.subtypeRestr s ∈ G := by
  apply G.eq_on_source ?_ (e.subtypeRestr_symm_trans_subtypeRestr s e')
  let hopen := e.preimage_open_of_open_symm s.2
  refine G.locality fun x' hx' ↦ ⟨e.target ∩ e.symm ⁻¹' s, hopen, ?_, ?_ ⟩
  · exact interior_subset (mem_of_mem_inter_right hx')
  · exact closedUnderRestriction' (closedUnderRestriction' (G.compatible he he') hopen) hopen

/-- Restricting a chart of `M` to an open subset `s` yields a chart in the maximal atlas of `s`.

NB. We cannot deduce membership in `atlas H s` in general: by definition, this atlas contains
precisely the restriction of each preferred chart at `x ∈ s` --- whereas `atlas H M`
can contain more charts than these. -/
lemma StructureGroupoid.restriction_in_maximalAtlas (he : e ∈ atlas H M) [ClosedUnderRestriction G]
    {s : Opens M} [Nonempty s] : e.subtypeRestr s ∈ G.maximalAtlas s := by
  intro e' he'
  -- `e'` is the restriction of some chart of `M` at `x`,
  obtain ⟨x, this⟩ := Opens.chart_eq he'
  rw [this]
  -- The transition functions between the unrestricted charts are in the groupoid,
  -- the transition functions of the restriction are the restriction of the transition function.
  exact ⟨G.trans_restricted he (chart_mem_atlas H (x : M)) s,
         G.trans_restricted (chart_mem_atlas H (x : M)) he s⟩

-- missing lemma, it seems: or ask on zulip
-- xxx: move to Mathlib.Data.Set.Function
variable {X Y : Type*} {s : Set X} {t : Set Y} (f : X → Y)
theorem MapsTo.map_nonempty (h : MapsTo f s t) (hs : s.Nonempty) : t.Nonempty :=
  (hs.image f).mono (mapsTo'.mp h)

/-- Restricting a chart to its source `s ⊆ M` yields a chart in the maximal atlas of `s`. -/
-- xxx: better name? how does this differ from `restriction_in_maximalAtlas`?
theorem StructureGroupoid.restriction_chart (he : e ∈ atlas H M) [ClosedUnderRestriction G]
    (hs : Set.Nonempty e.source) :
    let s := { carrier := e.source, is_open' := e.open_source : Opens M };
    let t := { carrier := e.target, is_open' := e.open_target  : Opens H };
    ∀ c' ∈ atlas H t, (e.toHomeomorphSourceTarget).toLocalHomeomorph ≫ₕ c' ∈ G.maximalAtlas s := by
  intro s t c' hc'
  have : Nonempty s := nonempty_coe_sort.mpr hs
  have : Nonempty t := nonempty_coe_sort.mpr (MapsTo.map_nonempty e e.mapsTo hs)
  -- Choose `x ∈ t` so `c'` is the restriction of `chartAt H x`.
  obtain ⟨x, hc'⟩ := Opens.chart_eq' hc'
  -- As H has only one chart, `chartAt H x` is the identity: i.e., `c'` is the inclusion.
  rw [hc', (chartAt_self_eq)]
  -- Argue that our expression equals this chart above, at least on its source.
  rw [LocalHomeomorph.subtypeRestr_def, LocalHomeomorph.trans_refl]
  set goal := (e.toHomeomorphSourceTarget.toLocalHomeomorph ≫ₕ t.localHomeomorphSubtypeCoe)
  have : goal ≈ e.subtypeRestr s :=
    (goal.eqOnSource_iff (e.subtypeRestr s)).mpr ⟨by simp, by intro _ _; rfl⟩
  exact G.mem_maximalAtlas_of_eqOnSource (M := s) this (G.restriction_in_maximalAtlas he)

/-- Each chart of a charted space is a structomorphism between its source and target. -/
lemma LocalHomeomorphism.toStructomorph (he : e ∈ atlas H M) [ClosedUnderRestriction G] :
    let s : Opens M := { carrier := e.source, is_open' := e.open_source }
    let t : Opens H := { carrier := e.target, is_open' := e.open_target }
    Structomorph G s t := by
  intro s t
  by_cases s = (∅ : Set M)
  · sorry -- statement is mathematicially trivial; TODO fill in!
  · exact {
      e.toHomeomorphSourceTarget with
      mem_groupoid := by
        intro c c' hc hc'
        show (c.symm).trans (e.toHomeomorphSourceTarget.toLocalHomeomorph.trans c') ∈ G
        -- The atlas of H on itself has only one chart, hence c' is the inclusion.
        -- Then, compatibility of `G` *almost* yields our claim --- except that `e` is a chart
        -- on `M` and `c` is one on `s`: we need to show that restricting `e` to `s` and composing
        -- with `c'` yields a chart in the maximal atlas of `s`.
        apply G.compatible_of_mem_maximalAtlas (G.subset_maximalAtlas hc)
          (G.restriction_chart he (nmem_singleton_empty.mp h) c' hc')
  }

-- TODO: Generalise this to all extended charts, if `I` is boundaryless.
