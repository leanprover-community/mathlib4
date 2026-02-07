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
* `PointedCone.IsSimplicial.toBasis_mem`: The elements of `toBasis` are in the cone.

## Implementation notes

This is a minimal API containing only what is needed to prove basic properties of
cone tensor products involving simplicial and generating cones.

The definition uses `Set.Finite` and `LinearIndepOn` since it is in reference to a subset.

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]

-/

@[expose] public section

variable {R M : Type*}
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]

local notation3 "R≥0" => {c : R // 0 ≤ c}

namespace PointedCone

variable (C : PointedCone R M)

/-- A pointed cone is simplicial if it equals the conic span of a finite set
that is linearly independent over `R`. -/
def IsSimplicial : Prop :=
  ∃ s : Set M, s.Finite ∧ LinearIndepOn R id s ∧ span R s = C

namespace IsSimplicial

/-- The conic span of a finite linearly independent set is simplicial. -/
protected theorem span {s : Set M} (hs : s.Finite) (hli : LinearIndepOn R id s) :
    (PointedCone.span R s).IsSimplicial := ⟨s, hs, hli, rfl⟩

variable {C}

/-- The generators of a simplicial generating cone form a basis of the module. -/
noncomputable def toBasis (h : C.IsSimplicial) (hgen : (C : ConvexCone R M).IsGenerating) :
    Module.Basis h.choose R M :=
  Module.Basis.mk h.choose_spec.2.1 <| by
    simpa using (by simpa only [eq_top_iff, ← Submodule.span_span_of_tower R≥0 R h.choose,
      h.choose_spec.2.2] using hgen.symm.le : Submodule.span R h.choose = ⊤).ge

/-- Each element of `toBasis` lies in the cone. -/
lemma toBasis_mem (h : C.IsSimplicial) (hgen : (C : ConvexCone R M).IsGenerating)
    (i : h.choose) : h.toBasis hgen i ∈ C := by
  simp only [toBasis, id_eq, Module.Basis.coe_mk]
  exact (h.choose_spec.2.2 ▸ subset_span) i.prop

end IsSimplicial

end PointedCone
