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

-- variable {O R : Type*} [Ring O] [Ring R] [Module O R]
--   [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

/-- If a ring `O` acts on a ring `R` carrying a valuative topology without increasing the
valuation, then the topology on `R` is `O`-linear: the open balls
`Valuation.ltSubmoduleOfSMulLe (valuation R) h γ` form a basis of neighborhoods of zero made of
`O`-submodules.
This is stated for an arbitrary such `O`, rather than for `(valuation R).integer`, so that it
applies to rings that are only propositionally, and not definitionally, the ring of integers. -/
theorem _root_.IsLinearTopology.of_valuation_smul_le
    (h : ∀ (o : O) (x : R), valuation R (o • x) ≤ valuation R x) : IsLinearTopology O R :=
  IsLinearTopology.mk_of_hasBasis O (p := fun _ : (ValueGroupWithZero R)ˣ ↦ True)
    (s := (valuation R).ltSubmoduleOfSMulLe h) (IsValuativeTopology.hasBasis_nhds_zero R)

/-- If a ring `O` acts on a ring `R` carrying a valuative topology without increasing the
valuation, and if `O` carries the topology induced by an `O`-linear map `f : O →ₗ[O] R`, then the
topology on `O` is `O`-linear: the preimages under `f` of the open balls of `R` form a basis of
neighborhoods of zero made of left ideals. -/
theorem _root_.IsLinearTopology.of_valuation_smul_le_of_isInducing [TopologicalSpace O]
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
