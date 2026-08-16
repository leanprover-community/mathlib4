/-
Copyright (c) 2026 Ryan Shin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Shin
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Pulling back charted-space and groupoid structures along a homeomorphism

Given a charted space `M` modelled on `H` and a homeomorphism `e : N ≃ₜ M`, we
endow `N` with the pulled-back charted-space structure, whose atlas is
`{e.transOpenPartialHomeomorph c | c ∈ atlas H M}`.

The coordinate changes of the transported atlas are *equal* to the coordinate
changes of the original atlas (`Homeomorph.pullback_symm_trans`): for a global
homeomorphism, nothing of the transport survives in the overlaps. Consequently
the transport preserves every satisfied structure groupoid
(`Homeomorph.pullback_hasGroupoid`), and `e` itself is a structomorphism from
the transported structure to the original one
(`Homeomorph.pullbackStructomorph`).

This complements `Homeomorph.chartedSpace`, which transports a charted-space
structure through the `IsLocalHomeomorph` machinery, chart-by-chart through
local inverses. The construction here instead composes the *global*
homeomorphism with each chart of the entire supplied atlas, so coordinate
changes are unchanged on the nose and every structure groupoid transports
with no `ClosedUnderRestriction G` assumption.

This construction transports structure along a specified homeomorphism; it
does not compare the transported structure with any pre-existing structure
on `N`.

## Main definitions

* `Homeomorph.pullbackChartedSpace e` : the charted-space structure on `N`
  pulled back along `e : N ≃ₜ M`.
* `Homeomorph.pullback_hasGroupoid e G` : the pulled-back structure satisfies
  every structure groupoid that `M` satisfies.
* `Homeomorph.pullbackStructomorph e G` : `e` as a `Structomorph G N M` for
  the pulled-back structure.
-/

@[expose] public section

open Set ChartedSpace

open scoped Manifold Topology

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {N : Type*} [TopologicalSpace N]

namespace Homeomorph

/-- Pull back a charted-space structure along a homeomorphism `e : N ≃ₜ M`:
the atlas on `N` is `{e.transOpenPartialHomeomorph c | c ∈ atlas H M}`. -/
@[instance_reducible]
def pullbackChartedSpace (e : N ≃ₜ M) : ChartedSpace H N where
  atlas := (e.transOpenPartialHomeomorph ·) '' atlas H M
  chartAt x := e.transOpenPartialHomeomorph (chartAt H (e x))
  mem_chart_source x := mem_chart_source H (e x)
  chart_mem_atlas x := ⟨_, chart_mem_atlas _ (e x), rfl⟩

@[simp, mfld_simps]
theorem pullbackChartedSpace_chartAt (e : N ≃ₜ M) (x : N) :
    @chartAt H _ N _ e.pullbackChartedSpace x =
      e.transOpenPartialHomeomorph (chartAt H (e x)) :=
  rfl

@[simp, mfld_simps]
theorem pullbackChartedSpace_atlas (e : N ≃ₜ M) :
    @atlas H _ N _ e.pullbackChartedSpace =
      (e.transOpenPartialHomeomorph ·) '' atlas H M :=
  rfl

theorem transOpenPartialHomeomorph_mem_pullbackChartedSpace_atlas (e : N ≃ₜ M)
    {c : OpenPartialHomeomorph M H} (hc : c ∈ atlas H M) :
    e.transOpenPartialHomeomorph c ∈ @atlas H _ N _ e.pullbackChartedSpace :=
  ⟨c, hc, rfl⟩

omit [ChartedSpace H M] in
/-- The open partial homeomorphism of a homeomorphism, composed with its
inverse, is the identity chart. -/
private theorem symm_trans_toOpenPartialHomeomorph (e : N ≃ₜ M) :
    e.toOpenPartialHomeomorph.symm ≫ₕ e.toOpenPartialHomeomorph =
      OpenPartialHomeomorph.refl M := by
  rw [← symm_toOpenPartialHomeomorph, ← trans_toOpenPartialHomeomorph,
    symm_trans_self, refl_toOpenPartialHomeomorph]

omit [ChartedSpace H M] in
/-- Coordinate changes of the pulled-back atlas are equal to coordinate
changes of the original atlas. -/
theorem pullback_symm_trans (e : N ≃ₜ M) (c c' : OpenPartialHomeomorph M H) :
    (e.transOpenPartialHomeomorph c).symm ≫ₕ e.transOpenPartialHomeomorph c' =
      c.symm ≫ₕ c' := by
  simp only [transOpenPartialHomeomorph_eq_trans]
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc e.toOpenPartialHomeomorph.symm,
    symm_trans_toOpenPartialHomeomorph, OpenPartialHomeomorph.refl_trans]

/-- The pulled-back charted-space structure satisfies every structure groupoid
that the original structure satisfies. -/
theorem pullback_hasGroupoid (e : N ≃ₜ M) (G : StructureGroupoid H)
    [HasGroupoid M G] :
    letI : ChartedSpace H N := e.pullbackChartedSpace
    HasGroupoid N G := by
  let _ : ChartedSpace H N := e.pullbackChartedSpace
  refine ⟨?_⟩
  rintro f g ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  rw [pullback_symm_trans]
  exact StructureGroupoid.compatible _ hc hc'

/-- A homeomorphism onto a `G`-manifold is a `G`-structomorphism for the
pulled-back structure. -/
def pullbackStructomorph (e : N ≃ₜ M) (G : StructureGroupoid H)
    [HasGroupoid M G] :
    letI : ChartedSpace H N := e.pullbackChartedSpace
    Structomorph G N M := by
  let _ : ChartedSpace H N := e.pullbackChartedSpace
  refine { e with mem_groupoid := ?_ }
  rintro c c' ⟨c₀, hc₀, rfl⟩ hc'
  rw [← transOpenPartialHomeomorph_eq_trans, pullback_symm_trans]
  exact StructureGroupoid.compatible _ hc₀ hc'

end Homeomorph
