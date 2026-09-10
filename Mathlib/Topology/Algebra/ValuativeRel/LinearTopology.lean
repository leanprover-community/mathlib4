/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
TODO-/

@[expose] public section

open ValuativeRel

variable {O R : Type*} [Ring O] [Ring R] [Module O R]
  [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

namespace IsLinearTopology

section SMul

/-- If a ring `O` acts on a ring `R` carrying a valuative topology without increasing the
valuation, then the topology on `R` is `O`-linear.

The open balls `(valuation R).ltSubmoduleOfSMulLe h γ` form a basis of neighborhoods of zero made of
`O`-submodules. -/
theorem of_valuation_smul_le
    (h : ∀ (o : O) (x : R), valuation R (o • x) ≤ valuation R x) : IsLinearTopology O R :=
  IsLinearTopology.mk_of_hasBasis O (p := fun _ : (ValueGroupWithZero R)ˣ ↦ True)
    (s := (valuation R).ltSubmoduleOfSMulLe h) (IsValuativeTopology.hasBasis_nhds_zero R)

/-- If a ring `O` acts on a ring `R` carrying a valuative topology without increasing the
valuation, and if `O` carries the topology induced by an `O`-linear map `f : O →ₗ[O] R`, then the
topology on `O` is `O`-linear.

The preimages under `f` of the open balls of `R` form a basis of
neighborhoods of zero made of left ideals. -/
theorem of_valuation_smul_le_of_isInducing [TopologicalSpace O]
    (h : ∀ (o : O) (x : R), valuation R (o • x) ≤ valuation R x)
    (f : O →ₗ[O] R) (hf : Topology.IsInducing f) : IsLinearTopology O O := by
  refine IsLinearTopology.mk_of_hasBasis O (p := fun _ : (ValueGroupWithZero R)ˣ ↦ True)
    (s := fun γ ↦ ((valuation R).ltSubmoduleOfSMulLe h γ).comap f) ?_
  rw [hf.nhds_eq_comap, map_zero]
  exact (IsValuativeTopology.hasBasis_nhds_zero R).comap _

end SMul

end IsLinearTopology

section IsIntegerSMul

/-- The ring of integers of `R` acts on `R` by integers. -/
instance : IsIntegerSMul (valuation R).integer R where
  smul_vle o x :=
    (Valuation.vle_iff_le (valuation R)).mpr ((valuation R).valuation_integer_smul_le o x)

instance _root_.IsLinearTopology.of_isIntegerSMul [IsIntegerSMul O R] : IsLinearTopology O R :=
  .of_valuation_smul_le fun o x ↦ valuation_smul_le o x

/-- If `O` acts by integers on a ring `R` carrying a valuative topology, and if `O` carries the
topology induced by an `O`-linear map `f : O →ₗ[O] R`, then the topology on `O` is `O`-linear:
the preimages under `f` of the open balls of `R` form a basis of neighborhoods of zero made of
left ideals. -/
theorem _root_.IsLinearTopology.of_isIntegerSMul_of_isInducing [IsIntegerSMul O R]
    [TopologicalSpace O] (f : O →ₗ[O] R) (hf : Topology.IsInducing f) : IsLinearTopology O O :=
  .of_valuation_smul_le_of_isInducing (fun o x ↦ valuation_smul_le o x) f hf

end IsIntegerSMul

section Integers

variable {A : Type*} [CommRing A] [ValuativeRel A] {O : Type*} [CommRing O] [Algebra O A]

variable [TopologicalSpace A] [IsValuativeTopology A]

/-- If `O` is a ring of integers for the valuative relation on `A`, in the sense of
`Valuation.Integers`, then the topology on `A` is `O`-linear. -/
theorem _root_.Valuation.Integers.isLinearTopology (hO : (valuation A).Integers O) :
    IsLinearTopology O A :=
  have := hO.isIntegerSMul
  .of_isIntegerSMul

/-- If `O` is a ring of integers for the valuative relation on `A`, in the sense of
`Valuation.Integers`, and carries the topology induced by `algebraMap O A`, then the topology
on `O` is `O`-linear. -/
theorem _root_.Valuation.Integers.isLinearTopology_self [TopologicalSpace O]
    (hO : (valuation A).Integers O) (hf : Topology.IsInducing (algebraMap O A)) :
    IsLinearTopology O O :=
  have := hO.isIntegerSMul
  .of_isIntegerSMul_of_isInducing (Algebra.linearMap O A) hf

end Integers
