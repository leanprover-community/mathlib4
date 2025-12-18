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
* `PointedCone.IsGenerating`: Abbreviation - generating if it spans the whole module.

## Results

* `PointedCone.span_isSimplicial`: The conic span of a linearly independent finite set is
  simplicial.
* `PointedCone.IsSimplicial.toBasis`: A simplicial generating cone determines a basis.

## Implementation notes

This is a minimal API containing only what is needed to prove basic properties of
cone tensor products involving simplicial and generating cones. Additional lemmas
(finite generation properties,behavior under maps, simplicial cones in specific cases)
may be added in future PRs.

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

/-- The conic span of a finite linearly independent set is simplicial. -/
theorem span_isSimplicial (s : Finset M) (hli : LinearIndependent R ((↑) : s → M)) :
    (span R (s : Set M)).IsSimplicial :=
  ⟨s, hli, rfl⟩

/-- Abbreviation: A pointed cone is generating iff its underlying convex cone is generating. -/
abbrev IsGenerating : Prop := (C : ConvexCone R M).IsGenerating

variable {C}

/-- The generator finset of a simplicial cone, extracted from the existential. -/
noncomputable def IsSimplicial.generators (h : C.IsSimplicial) : Finset M := h.choose

/-- The generators of a simplicial cone are linearly independent. -/
lemma IsSimplicial.linearIndependent_generators (h : C.IsSimplicial) :
    LinearIndependent R ((↑) : h.generators → M) :=
  h.choose_spec.1

/-- A simplicial cone equals the conic span of its generators. -/
lemma IsSimplicial.span_generators (h : C.IsSimplicial) : span R (h.generators : Set M) = C :=
  h.choose_spec.2

/-- If a simplicial cone is generating, every element lies in the linear span of its generators. -/
lemma IsSimplicial.top_le_span_generators (h_simp : C.IsSimplicial) (h_gen : C.IsGenerating) :
    ⊤ ≤ Submodule.span R (h_simp.generators : Set M) := by
  simp only [← Submodule.span_span_of_tower R≥0 R (h_simp.generators : Set M),
    h_simp.span_generators]
  exact h_gen.symm.le

/-- The generators of a simplicial generating cone also form a basis for the module. -/
noncomputable def IsSimplicial.toBasis (h_simp : C.IsSimplicial) (h_gen : C.IsGenerating) :
    Module.Basis h_simp.generators R M :=
  Module.Basis.mk h_simp.linearIndependent_generators (by
    rw [Subtype.range_coe_subtype, Finset.setOf_mem]
    exact h_simp.top_le_span_generators h_gen)

/-- The basis `toBasis` acts as the natural inclusion map: evaluating it at each generator
index yields the generator itself. -/
lemma IsSimplicial.toBasis_range (h_simp : C.IsSimplicial) (h_gen : C.IsGenerating) :
    Set.range (h_simp.toBasis h_gen) = h_simp.generators := by
  simp only [toBasis, Module.Basis.coe_mk, Subtype.range_coe_subtype, Finset.setOf_mem]

/-- The generators of a simplicial generating cone `C` form a module basis, and each basis vector
lies inside the cone `C`. -/
lemma IsSimplicial.toBasis_mem (h_simp : C.IsSimplicial) (h_gen : C.IsGenerating)
    (i : h_simp.generators) : (h_simp.toBasis h_gen) i ∈ C := by
  have h_range : (h_simp.toBasis h_gen) i ∈ Set.range (h_simp.toBasis h_gen) :=
    Set.mem_range_self i
  have h_span : (h_simp.generators : Set M) ⊆ (span R (h_simp.generators : Set M) : Set M) :=
    subset_span
  rw [h_simp.toBasis_range h_gen, h_simp.span_generators] at *
  exact h_span h_range

end PointedCone
