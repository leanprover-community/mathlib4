/-
Copyright (c) 2026 Andrey Lukin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrey Lukin
-/
module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Facet incidence data

This file defines finite codimension-one incidence data whose ridges have one or two cofacets.
It is intended as the combinatorial input for a future formalization of Sperner's lemma: a ridge
with one cofacet is a boundary ridge, while a ridge with two cofacets is an interior ridge.
-/

@[expose] public section

namespace Combinatorics
namespace Sperner

/-- Finite facet-ridge incidence data in which every ridge has either one or two cofacets.

For a simplicial complex, the facets are its top-dimensional faces and the ridges are their
codimension-one faces. The one-or-two cofacet condition is the pseudomanifold-with-boundary
property needed by the usual incidence proof of Sperner's lemma. -/
structure FacetIncidence (Facet Ridge : Type*) [DecidableEq Facet] [DecidableEq Ridge] where
  /-- The top-dimensional faces. -/
  facets : Finset Facet
  /-- The codimension-one faces. -/
  ridges : Finset Ridge
  /-- Facet-ridge incidence. -/
  incident : Facet → Ridge → Prop
  /-- A decision procedure for facet-ridge incidence. -/
  incidentDecidable : DecidableRel incident
  /-- Every ridge is incident to at least one facet. -/
  ridgeNonempty : ∀ ridge ∈ ridges, (facets.bipartiteBelow incident ridge).Nonempty
  /-- Every ridge is incident to at most two facets. -/
  ridgeCardLeTwo : ∀ ridge ∈ ridges, (facets.bipartiteBelow incident ridge).card ≤ 2

namespace FacetIncidence

variable {Facet Ridge : Type*} [DecidableEq Facet] [DecidableEq Ridge]
  (I : FacetIncidence Facet Ridge)

instance : DecidableRel I.incident := I.incidentDecidable

/-- The facets incident to a ridge. -/
def cofacets (I : FacetIncidence Facet Ridge) (ridge : Ridge) : Finset Facet :=
  I.facets.bipartiteBelow I.incident ridge

@[simp]
theorem mem_cofacets {facet : Facet} {ridge : Ridge} :
    facet ∈ I.cofacets ridge ↔ facet ∈ I.facets ∧ I.incident facet ridge := by
  simpa only [cofacets] using
    (Finset.mem_bipartiteBelow (r := I.incident) (s := I.facets) (b := ridge) (a := facet))

/-- A ridge with exactly one cofacet. -/
def IsBoundaryRidge (I : FacetIncidence Facet Ridge) (ridge : Ridge) : Prop :=
  (I.cofacets ridge).card = 1

/-- A ridge with exactly two cofacets. -/
def IsInteriorRidge (I : FacetIncidence Facet Ridge) (ridge : Ridge) : Prop :=
  (I.cofacets ridge).card = 2

/-- Every ridge is either a boundary ridge or an interior ridge. -/
theorem isBoundaryRidge_or_isInteriorRidge {ridge : Ridge} (hridge : ridge ∈ I.ridges) :
    I.IsBoundaryRidge ridge ∨ I.IsInteriorRidge ridge := by
  have hpos : 0 < (I.cofacets ridge).card := Finset.card_pos.mpr (I.ridgeNonempty ridge hridge)
  have hle : (I.cofacets ridge).card ≤ 2 := I.ridgeCardLeTwo ridge hridge
  simp only [IsBoundaryRidge, IsInteriorRidge]
  omega

/-- The boundary ridges. -/
def boundaryRidges (I : FacetIncidence Facet Ridge) : Finset Ridge :=
  I.ridges.filter fun ridge ↦ (I.cofacets ridge).card = 1

@[simp]
theorem mem_boundaryRidges {ridge : Ridge} :
    ridge ∈ I.boundaryRidges ↔ ridge ∈ I.ridges ∧ I.IsBoundaryRidge ridge :=
  Finset.mem_filter

/-- The interior ridges. -/
def interiorRidges (I : FacetIncidence Facet Ridge) : Finset Ridge :=
  I.ridges.filter fun ridge ↦ (I.cofacets ridge).card = 2

@[simp]
theorem mem_interiorRidges {ridge : Ridge} :
    ridge ∈ I.interiorRidges ↔ ridge ∈ I.ridges ∧ I.IsInteriorRidge ridge :=
  Finset.mem_filter

/-- Boundary and interior ridges partition the ridges. -/
theorem boundaryRidges_union_interiorRidges : I.boundaryRidges ∪ I.interiorRidges = I.ridges := by
  ext ridge
  simp only [Finset.mem_union, mem_boundaryRidges, mem_interiorRidges]
  constructor
  · rintro (⟨hridge, -⟩ | ⟨hridge, -⟩)
    · exact hridge
    · exact hridge
  · intro hridge
    rcases I.isBoundaryRidge_or_isInteriorRidge hridge with hboundary | hinterior
    · exact Or.inl ⟨hridge, hboundary⟩
    · exact Or.inr ⟨hridge, hinterior⟩

/-- No ridge is both boundary and interior. -/
theorem disjoint_boundaryRidges_interiorRidges : Disjoint I.boundaryRidges I.interiorRidges := by
  refine Finset.disjoint_left.mpr fun ridge hboundary hinterior => ?_
  have hboundary' := (I.mem_boundaryRidges.mp hboundary).2
  have hinterior' := (I.mem_interiorRidges.mp hinterior).2
  simp only [IsBoundaryRidge, IsInteriorRidge] at hboundary' hinterior'
  omega

end FacetIncidence
end Sperner
end Combinatorics
