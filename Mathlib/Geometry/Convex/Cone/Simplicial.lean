/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Simplicial cones

A **simplicial cone** is the conic span of a finset of vectors that are
linearly independent over the ring R.

## Main definitions

* `PointedCone.IsSimplicial`: A pointed cone is simplicial if it equals the conic span of
  a finite linearly independent set.
* `PointedCone.IsGenerating`: Abbreviation - generating if it spans the whole module.
* `PointedCone.Simplicial.toBasis`: A simplicial generating cone determines a basis.

## Implementation notes

This is a minimal API containing only what is needed for
`Mathlib.Analysis.Convex.Cone.TensorProduct`. Additional lemmas (finite generation properties,
behavior under maps, simplicial cones in specific cases) may be added in future PRs.
-/

@[expose] public section

variable {R M : Type*}
variable [Ring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

local notation3 "R≥0" => {c : R // 0 ≤ c}

namespace PointedCone

/-- A pointed cone is simplicial if it equals the conic span of a finite set that is
linearly independent over `R`. Note: `span R s` here refers to `PointedCone.span`,
the span over nonnegative scalars `R≥0`. -/
def IsSimplicial (C : PointedCone R M) : Prop :=
  ∃ s : Finset M, LinearIndependent R ((↑) : s → M) ∧ span R (s : Set M) = C

/-- The generator finset of a simplicial cone, extracted from the existential. -/
noncomputable def IsSimplicial.generators {C : PointedCone R M} (h : C.IsSimplicial) : Finset M :=
  h.choose

/-- The generators of a simplicial cone are linearly independent. -/
lemma IsSimplicial.linearIndependent_generators {C : PointedCone R M} (h : C.IsSimplicial) :
    LinearIndependent R ((↑) : h.generators → M) :=
  h.choose_spec.1

/-- A simplicial cone equals the conic span of its generators. -/
lemma IsSimplicial.span_generators {C : PointedCone R M} (h : C.IsSimplicial) :
    span R (h.generators : Set M) = C :=
  h.choose_spec.2

/-- Abbreviation: A pointed cone is generating iff its underlying convex cone is generating. -/
abbrev IsGenerating (C : PointedCone R M) : Prop := (C : ConvexCone R M).IsGenerating

/-- If a simplicial cone is generating, its generators linearly span the whole space. -/
lemma IsSimplicial.span_generators_eq_top {C : PointedCone R M}
    (h_simp : C.IsSimplicial) (h_gen : C.IsGenerating) :
    Submodule.span R (h_simp.generators : Set M) = ⊤ := by
  rw [← Submodule.span_span_of_tower {c : R // 0 ≤ c} R (h_simp.generators : Set M)]
  simp only [h_simp.span_generators]
  exact h_gen

/-- The generators of a simplicial generating cone also form a basis for the module. -/
noncomputable def IsSimplicial.toBasis {C : PointedCone R M}
    (h_simp : C.IsSimplicial) (h_gen : C.IsGenerating) :
    Module.Basis h_simp.generators R M :=
  Module.Basis.mk h_simp.linearIndependent_generators (by
    rw [Subtype.range_coe_subtype, Finset.setOf_mem]
    exact le_of_eq (h_simp.span_generators_eq_top h_gen).symm)

/-- The basis `toBasis` acts as the natural inclusion: evaluating it at each generator
index yields the generator itself. -/
lemma IsSimplicial.toBasis_range {C : PointedCone R M}
    (h_simp : C.IsSimplicial) (h_gen : C.IsGenerating) :
    Set.range (h_simp.toBasis h_gen) = h_simp.generators := by
  ext x
  simp only [Set.mem_range, IsSimplicial.toBasis]
  constructor
  · rintro ⟨i, rfl⟩
    rw [Module.Basis.mk_apply]
    exact i.property
  · intro hx
    exact ⟨⟨x, hx⟩, Module.Basis.mk_apply _ _ _⟩

/-- The generators of a simplicial generating cone `C` form a basis, and each basis vector
lies inside the cone `C`. -/
lemma IsSimplicial.toBasis_mem {C : PointedCone R M}
    (h_simp : C.IsSimplicial) (h_gen : C.IsGenerating)
    (i : h_simp.generators) : (h_simp.toBasis h_gen) i ∈ C := by
  have h_range : (h_simp.toBasis h_gen) i ∈ Set.range (h_simp.toBasis h_gen) :=
    Set.mem_range_self i
  rw [h_simp.toBasis_range h_gen] at h_range
  have h_span : (h_simp.generators : Set M) ⊆ (span R (h_simp.generators : Set M) : Set M) :=
    subset_span
  rw [h_simp.span_generators] at h_span
  exact h_span h_range

end PointedCone
