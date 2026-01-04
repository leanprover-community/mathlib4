/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# `Module.End R M` is a central algebra

This file shows that the algebra of endomorphisms on a free module is central.
-/

open Module

variable {R S M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Free R M]
  [CommSemiring S] [Module S M] [SMulCommClass R S M] [Algebra S R] [IsScalarTower S R M]

public theorem Module.End.mem_subsemiringCenter_iff {f : End R M} :
    f ∈ Subsemiring.center (End R M) ↔
      ∃ (α : R) (hα : α ∈ Subsemiring.center R), f = smulLeft α hα :=
  mem_center_iff

public theorem Module.End.mem_subalgebraCenter_iff {f : End R M} :
    f ∈ Subalgebra.center S (End R M) ↔
      ∃ (α : R) (hα : α ∈ Subalgebra.center S R), f = smulLeft α hα :=
  mem_center_iff

namespace Algebra.IsCentral

/-- The center of endomorphisms on a free module is trivial,
in other words, it is a central algebra. -/
public instance [IsCentral S R] : IsCentral S (End R M) where out T hT :=
  have ⟨_, h, _⟩ := T.mem_subalgebraCenter_iff.mp hT
  have ⟨y, _⟩ := center_eq_bot S R ▸ h
  ⟨y, by aesop⟩

end Algebra.IsCentral

open LinearMap in
public theorem LinearEquiv.conjAlgEquiv_ext_iff {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]
    [Module S M₂] [SMulCommClass R S M₂] [IsScalarTower S R M₂] [Algebra.IsCentral S R]
    (f g : M ≃ₗ[R] M₂) : f.conjAlgEquiv S = g.conjAlgEquiv S ↔ ∃ α : S, ⇑f = α • g := by
  conv_lhs => rw [eq_comm]
  simp_rw [AlgEquiv.ext_iff, conjAlgEquiv_apply, ← eq_toLinearMap_symm_comp, ← comp_assoc,
    eq_comp_toLinearMap_symm, comp_assoc, ← comp_assoc _ _ g.symm.toLinearMap, comp_coe,
    ← End.mul_eq_comp, ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot,
    ← comp_coe, Algebra.mem_bot, Set.mem_range, Algebra.algebraMap_eq_smul_one,
    eq_toLinearMap_symm_comp, eq_comm, LinearMap.ext_iff, funext_iff, comp_apply, coe_coe,
    LinearMap.smul_apply, End.one_apply]
  constructor
  all_goals
    refine fun ⟨y, hy⟩ ↦ ⟨y, fun _ ↦ ?_⟩
    simp_all only [EmbeddingLike.apply_eq_iff_eq, eq_comm (a := y • _), Pi.smul_apply]
    exact LinearMapClass.map_smul_of_tower _ _ _
