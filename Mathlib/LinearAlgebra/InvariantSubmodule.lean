/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.Algebra.Group.Commute.Units

/-!
# Invariant submodules

In this file, we prove some basic results on invariant submodules.

## Notation

This file uses the local notation `pᵤ` for the linear projection to `U` along its complement `V`
and `pᵥ` for the linear projection to `V` along its complement `U`.

## Tags

invariant
-/

namespace Module.End

open Submodule

variable {E R : Type*} [Ring R] [AddCommGroup E] [Module R E]
  {U V : Submodule R E} (hUV : IsCompl U V) (T : E →ₗ[R] E)

local notation "pᵤ" => linearProjOfIsCompl U V hUV
local notation "pᵥ" => linearProjOfIsCompl V U hUV.symm

lemma mem_invtSubmodule_linear_proj_comp_self_eq (h : U ∈ invtSubmodule T) (x : U) :
    (pᵤ (T x) : E) = T x := (linearProjOfIsCompl_eq_self_iff _ _).mpr <| h (coe_mem _)

lemma mem_invtSubmodule_of_linear_proj_comp_self_eq (h : ∀ x : U, (pᵤ (T x) : E) = T x) :
    U ∈ Module.End.invtSubmodule T := fun u hu => by
  rw [mem_comap, ← linearProjOfIsCompl_eq_self_iff hUV _,
    ← (linearProjOfIsCompl_eq_self_iff hUV u).mpr hu, h]

/-- `U` is invariant under `T` if and only if `pᵤ ∘ₗ T = T`,
where `pᵤ` denotes the linear projection to `U` along `V`. -/
lemma mem_invtSubmodule_iff_linear_proj_comp_self_eq :
    U ∈ Module.End.invtSubmodule T ↔ (∀ x : U, (pᵤ (T x) : E) = T x) :=
  ⟨mem_invtSubmodule_linear_proj_comp_self_eq hUV T,
    mem_invtSubmodule_of_linear_proj_comp_self_eq hUV T⟩

/-- `V` is invariant under `T` if and only if `pᵤ ∘ₗ (T ∘ₗ pᵤ) = pᵤ ∘ₗ T`,
where `pᵤ` denotes the linear projection to `U` along `V`. -/
lemma mem_invtSubmodule'_iff_linear_proj_comp_self_comp_linear_proj_eq :
    V ∈ Module.End.invtSubmodule T ↔ (∀ x : E, (pᵤ (T (pᵤ x)) : E) = pᵤ (T x)) := by
  simp_rw [mem_invtSubmodule_iff_linear_proj_comp_self_eq hUV.symm,
    (LinearMap.range_eq_top.1 (linearProjOfIsCompl_range hUV.symm)).forall,
    linearProjOfIsCompl_eq_self_sub_linear_proj hUV, map_sub,
    sub_eq_self, Submodule.coe_sub, sub_eq_zero, eq_comm]

/-- Both `U` and `V` are invariant under `T` if and only if `T` commutes with `pᵤ`,
where `pᵤ` denotes the linear projection to `U` along `V`. -/
lemma isCompl_mem_invtSubmodule_iff_linear_proj_and_self_commute :
    (U ∈ Module.End.invtSubmodule T ∧ V ∈ Module.End.invtSubmodule T)
      ↔ Commute (U.subtype ∘ₗ pᵤ) T := by
  simp_rw [Commute, SemiconjBy, LinearMap.ext_iff, Module.End.mul_apply,
    LinearMap.comp_apply, U.subtype_apply]
  constructor
  · rintro ⟨h1, h2⟩ x
    rw [← (mem_invtSubmodule'_iff_linear_proj_comp_self_comp_linear_proj_eq _ _).mp h2 x]
    exact (linearProjOfIsCompl_eq_self_iff hUV _).mpr (h1 (coe_mem (pᵤ x)))
  · intro h
    simp_rw [mem_invtSubmodule_iff_linear_proj_comp_self_eq hUV,
      (LinearMap.range_eq_top.1 (linearProjOfIsCompl_range hUV)).forall,
      mem_invtSubmodule'_iff_linear_proj_comp_self_comp_linear_proj_eq hUV, h,
      linearProjOfIsCompl_idempotent hUV, ← forall_and, and_self_iff,
      forall_const]

/-- `U` is `⅟T` invariant if and only if `U ⊆ T(U)`. -/
lemma mem_invtSubmodule_invOf_iff_le_map [Invertible T] :
    U ∈ Module.End.invtSubmodule (⅟T) ↔ U ≤ U.map T :=
  mem_invtSubmodule_symm_iff_le_map (LinearEquiv.ofInvertible T)

/-- `⅟T ∘ₗ pᵤ ∘ₗ T = pᵤ` if and only if `T(U) = U` and `T(V) = V`,
where `pᵤ` denotes the linear projection to `U` along `V`. -/
theorem _root_.Submodule.invOf_comp_linear_proj_comp_self_eq_linear_proj_iff_map_eq [Invertible T] :
    ⅟T ∘ₗ (U.subtype ∘ₗ pᵤ) ∘ₗ T = U.subtype ∘ₗ pᵤ ↔ U.map T = U ∧ V.map T = V := by
  have : ∀ f, Commute f T ↔ ⅟T ∘ₗ f ∘ₗ T = f :=
    fun f => Commute.symm_iff.trans ((unitOfInvertible T).commute_iff_inv_mul_cancel f)
  simp_rw [← this, ← isCompl_mem_invtSubmodule_iff_linear_proj_and_self_commute, le_antisymm_iff,
    ← Module.End.mem_invtSubmodule_iff_map, and_and_and_comm
      (c := (V ∈ Module.End.invtSubmodule T)), iff_self_and,
    ← mem_invtSubmodule_invOf_iff_le_map,
    isCompl_mem_invtSubmodule_iff_linear_proj_and_self_commute hUV]
  exact @Commute.units_inv_right _ _ _ (unitOfInvertible T)

end Module.End
