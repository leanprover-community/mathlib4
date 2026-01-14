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

A **simplicial cone** (also called a **simplex cone**) is a pointed convex cone that equals the
conic span of a finite linearly independent set of vectors. We do not require that the
generators span the ambient module. However, in the case of a generating simplicial cone
the (simplicial) generators linearly span the module.

## Main definitions

* `PointedCone.IsSimplicial`: A pointed cone is simplicial if it equals the conic span of
  a finite linearly independent set.

## Results

* `PointedCone.IsSimplicial.span`: The conic span of a linearly independent finite set is
  simplicial.
* `PointedCone.IsSimplicial.toBasis`: A simplicial generating cone determines a basis.

## Implementation notes

This is a minimal API containing only what is needed to prove basic properties of
cone tensor products involving simplicial and generating cones.

Finset + classical choice (non-computable) seems a reasonable choice for this predicate. Other
possibilities are a finite set or using a structure (which brings along a proof of finiteness).

## References

* [de Bruyn *Tensor products of convex cones*][https://arxiv.org/abs/2009.11843v2]

-/

@[expose] public section

variable {R M : Type*}
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]

local notation3 "R≥0" => {c : R // 0 ≤ c}

namespace PointedCone

variable (C : PointedCone R M)

/-- A pointed cone is simplicial if it equals the conic span of a finite set that is
linearly independent over `R`. -/
def IsSimplicial : Prop :=
  ∃ s : Finset M, LinearIndependent R ((↑) : s → M) ∧ span R (s : Set M) = C

namespace IsSimplicial

/-- The conic span of a finite linearly independent set is simplicial. -/
protected theorem span (s : Finset M) (hli : LinearIndependent R ((↑) : s → M)) :
    (PointedCone.span R (s : Set M)).IsSimplicial :=
  ⟨s, hli, rfl⟩

variable {C}

/-- The generators of a simplicial cone. -/
noncomputable def generators (h : C.IsSimplicial) : Finset M := h.choose

/-- The generators of a simplicial cone are linearly independent. -/
lemma linearIndependent_generators (h : C.IsSimplicial) :
    LinearIndependent R ((↑) : h.generators → M) :=
  h.choose_spec.1

/-- A simplicial cone equals the conic span of its generators. -/
lemma span_generators (h : C.IsSimplicial) : span R (h.generators : Set M) = C :=
  h.choose_spec.2

/-- Each generator of a simplicial cone is a member of the cone. -/
lemma generator_mem (h : C.IsSimplicial) (i : h.generators) : (i : M) ∈ C :=
  (h.span_generators ▸ subset_span) i.prop

/-- The generators of a simplicial generating cone linearly span the module. -/
lemma span_generators_eq_top (h_simp : C.IsSimplicial) (h_gen : C.IsGenerating) :
    Submodule.span R (h_simp.generators : Set M) = ⊤ := by
  simpa only [eq_top_iff, ← Submodule.span_span_of_tower R≥0 R (h_simp.generators : Set M),
    h_simp.span_generators] using h_gen.symm.le

/-- The generators of a simplicial generating cone is a basis for the module. -/
noncomputable def toBasis (h_simp : C.IsSimplicial) (h_gen : C.IsGenerating) :
    Module.Basis h_simp.generators R M :=
  Module.Basis.mk h_simp.linearIndependent_generators <| by
    simpa using (h_simp.span_generators_eq_top h_gen).ge

/-- `toBasis` maps each generator to itself. -/
@[simp]
lemma toBasis_apply (h_simp : C.IsSimplicial) (h_gen : C.IsGenerating)
    (i : h_simp.generators) : h_simp.toBasis h_gen i = i := by simp [toBasis]

end IsSimplicial

end PointedCone
