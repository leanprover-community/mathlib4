/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

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
  --[SmoothManifoldWithCorners I M]
  -- Let `N` be a smooth manifold over the pair `(F, G)`.
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  --[SmoothManifoldWithCorners J N] {n : ℕ∞}

-- On any topological manifold (charted space on a normed space),
-- each chart is a structomorphism (from its source to its target).
variable {e : LocalHomeomorph M H} (he : e ∈ atlas H M)

-- TODO: prove this! it's the main load-bearing part of the lemma below!
lemma obvious (s : Opens M) [Nonempty s] : e.subtypeRestr s ∈ atlas H s := by
  -- can we argue that e = chartAt H x for some x,
  -- hence e.subtypeRestr s is the chart in s at x?
  -- then, would use  simp only [mem_iUnion, mem_singleton_iff]; rfl
  sorry

/-- Charts are structomorphisms. -/
-- xxx: do I need [ClosedUnderRestriction G]? in practice, is not an issue
lemma LocalHomeomorphism.toStructomorph {G : StructureGroupoid H} [ClosedUnderRestriction G]
    (h: HasGroupoid M G) : Structomorph G M H := by
  let s : Opens M := { carrier := e.source, is_open' := e.open_source }
  let t : Opens H := { carrier := e.target, is_open' := e.open_target }

  have : Nonempty s := sorry -- otherwise, trivial
  have : Nonempty t := sorry -- otherwise, trivial
  -- helper lemma: cannot pull out easily, but is conceptually independent
  have helper : ∀ c' : LocalHomeomorph t H, c' ∈ atlas H t →
      e.toHomeomorphSourceTarget.toLocalHomeomorph.trans c' ∈ atlas H s := by
    set e' := e.toHomeomorphSourceTarget.toLocalHomeomorph with eq -- source s, target t
    intro c'
    -- Choose `x ∈ t` so c' is the restriction of `chartAt H x`.
    intro ⟨xset, ⟨x, hx⟩, hc'⟩
    have : xset = {LocalHomeomorph.subtypeRestr (chartAt H ↑x) t} := hx.symm
    have : c' = LocalHomeomorph.subtypeRestr (chartAt H ↑x) t := mem_singleton_iff.mp (this ▸ hc')
    rw [this]
    -- As H has only one chart, this chart is the identity: i.e., c' is the inclusion.
    rw [(chartAt_self_eq)]
    -- simplify: perhaps not needed, but definitely ok
    rw [LocalHomeomorph.subtypeRestr_def, LocalHomeomorph.trans_refl]


    -- now: argue that our expression equals this chart above
    let r := LocalHomeomorph.subtypeRestr e s
    set goal := (e' ≫ₕ Opens.localHomeomorphSubtypeCoe t)
    -- TODO: this should be reasonably obvious... means some missing simp lemma somewhere
    have congr_inv : ∀ y, goal.symm y = r.symm y := by
      intro y
      rw [LocalHomeomorph.coe_trans_symm]
      have aux : ∀ y' : t, e'.symm y' = e.symm ↑y' := by intro; rfl
      let aux := aux (t.localHomeomorphSubtypeCoe.symm y)
      -- also fails: rw [aux]
      calc (e'.symm ∘ t.localHomeomorphSubtypeCoe.symm) y
        _ = e'.symm (t.localHomeomorphSubtypeCoe.symm y) := rfl
        -- doesn't work, for some reason! _ = (e.symm) ↑(t.localHomeomorphSubtypeCoe.symm y) := by rw [aux] -- rfl
        _ = (e.toHomeomorphSourceTarget.toLocalHomeomorph).symm (t.localHomeomorphSubtypeCoe.symm y) := rfl
        _ = (e.toHomeomorphSourceTarget.symm.toLocalHomeomorph) (t.localHomeomorphSubtypeCoe.symm y) := by rw [← Homeomorph.symm_toLocalHomeomorph]
        _ = (e.symm.toHomeomorphSourceTarget.toLocalHomeomorph) (t.localHomeomorphSubtypeCoe.symm y) := rfl

        _ = (e.symm.toHomeomorphSourceTarget.toLocalHomeomorph) (t.localHomeomorphSubtypeCoe.symm y) := sorry--rfl
        --_ = (e'.trans (t.localHomeomorphSubtypeCoe)).symm y := rfl
        --_ = (e.toHomeomorphSourceTarget.toLocalHomeomorph.trans (t.localHomeomorphSubtypeCoe)).symm y := rfl

        _ = (e.symm.trans s.localHomeomorphSubtypeCoe.symm) y := sorry
        _ = (s.localHomeomorphSubtypeCoe.trans e).symm y := rfl
        _ = r.symm y := rfl
    have congr_to : ∀ y, goal y = r ↑y := by intro; rfl
    have h2 : goal = r := LocalHomeomorph.ext goal r congr_to congr_inv (by simp)
    exact mem_of_eq_of_mem h2 (obvious s)
  -- singleton_hasGroupoid should also show this, by the way
  -- have : HasGroupoid t G := t.instHasGroupoid G -- as G is closed under restrictions
  let ehom := e.toHomeomorphSourceTarget -- temporarily given a name, to make the goal readable
  have : Structomorph G s t := {
    ehom with
    mem_groupoid := by
      intro c c' hc hc'
      show (c.symm).trans (ehom.toLocalHomeomorph.trans c') ∈ G -- just our pretty-printed goal

      -- Setting: have s ⊆ M and t ⊆ H, e maps s to t.
      -- c : s → H is a chart of M; c': t → M is essentially the inclusion.

      -- The atlas on H on itself has only one chart (by `chartedSpaceSelf_atlas H`),
      -- hence c' (as a restriction of that) is the inclusion.
      have : ∀ x, c' x = x := sorry -- unsure how to formally prove this...
      -- This *almost* gives our claim: except that `e` is a chart on M and c is one on s,
      -- so they don't fit together nicely. (Composing with the inclusion makes that nice...)
      -- let r := G.compatible hc he
      -- This version is rigorous... except the sorry (i.e. helper above) might be too optimistic.
      -- let e' : LocalHomeomorph s H := (ehom.toLocalHomeomorph.trans c')
      exact G.compatible hc (helper c' hc')
  }
  sorry

-- /-- Each chart inverse is a structomorphism. -/
-- -- essentially re-use the proof above!
-- lemma LocalHomeomorphism.symm_toStructomorph {e : LocalHomeomorph M H} (he : e ∈ atlas H M)
--     {G : StructureGroupoid H} : Structomorph G M H := sorry

-- TODO: Generalise this to all extended charts, if `I` is boundaryless.
