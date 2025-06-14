/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.Algebra.Group.Commute.Units

/-!
# Invariant submodules

In this file, we define and prove some basic results on invariant submodules.

## Definition

* `U.InvariantUnder T`: a submodule `U` is invariant under `T` if `U ≤ U.comap T`,
  in other words, it is invariant under `T` if for any `u ∈ U` we also have `T u ∈ U`

Equivalently, one can use `Submodule.map`, `Set.MapsTo`, and `set.image` to describe this using:

* `U.invariantUnder_iff_map T`: `U.InvariantUnder T` iff `U.map T ≤ U`
* `U.InvariantUnder_iff_mapsTo T`: `U.InvariantUnder T` iff `Set.MapsTo T U U`

## Notation

This file uses the local notation `pᵤ` for the linear projection to `U` along its complement `V`
and `pᵥ` for the linear projection to `V` along its complement `U`.

## Tags

invariant
-/

namespace Submodule

variable {E R : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- `U` is `T` invariant : `U ≤ U.comap` -/
def InvariantUnder (U : Submodule R E) (T : E →ₗ[R] E) : Prop := U ≤ U.comap T

/-- `U` is `T` invariant if and only if `U.map T ≤ U` -/
lemma invariantUnder_iff_map (U : Submodule R E) (T : E →ₗ[R] E) :
  U.InvariantUnder T ↔ U.map T ≤ U := map_le_iff_le_comap.symm

/-- `U` is `T` invariant if and only if `Set.MapsTo T U U` -/
lemma invariantUnder_iff_mapsTo (U : Submodule R E) (T : E →ₗ[R] E) :
  U.InvariantUnder T ↔ Set.MapsTo T U U := by rfl

variable (U V : Submodule R E) (hUV : IsCompl U V) (T : E →ₗ[R] E)

local notation "pᵤ" => linearProjOfIsCompl U V hUV
local notation "pᵥ" => linearProjOfIsCompl V U hUV.symm

lemma InvariantUnder.linear_proj_comp_self_eq (h : U.InvariantUnder T) (x : U) :
  (pᵤ (T x) : E) = T x :=
(linearProjOfIsCompl_eq_self_iff _ _).mpr <| h (coe_mem _)

lemma invariantUnder_of_linear_proj_comp_self_eq (h : ∀ x : U, (pᵤ (T x) : E) = T x) :
  U.InvariantUnder T := fun u hu =>
by rw [mem_comap, ← linearProjOfIsCompl_eq_self_iff hUV _,
  ← (linearProjOfIsCompl_eq_self_iff hUV u).mpr hu, h]

/-- `U` is invariant under `T` if and only if `pᵤ ∘ₗ T = T`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
lemma invariantUnder_iff_linear_proj_comp_self_eq :
  U.InvariantUnder T ↔ (∀ x : U, (pᵤ (T x) : E) = T x) :=
⟨InvariantUnder.linear_proj_comp_self_eq U V hUV T,
  invariantUnder_of_linear_proj_comp_self_eq U V hUV T⟩

/-- `V` is invariant under `T` if and only if `pᵤ ∘ₗ (T ∘ₗ pᵤ) = pᵤ ∘ₗ T`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
lemma invariantUnder'_iff_linear_proj_comp_self_comp_linear_proj_eq :
  V.InvariantUnder T ↔ (∀ x : E, (pᵤ (T (pᵤ x)) : E) = pᵤ (T x)) :=
by simp_rw [invariantUnder_iff_linear_proj_comp_self_eq _ _ hUV.symm,
  (LinearMap.range_eq_top.1 (linearProjOfIsCompl_range hUV.symm)).forall,
  linearProjOfIsCompl_eq_self_sub_linear_proj hUV, map_sub,
  sub_eq_self, Submodule.coe_sub, sub_eq_zero, eq_comm]

/-- both `U` and `V` are invariant under `T` if and only if `T` commutes with `pᵤ`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
lemma isCompl_invariantUnder_iff_linear_proj_and_self_commute :
  (U.InvariantUnder T ∧ V.InvariantUnder T) ↔ Commute (U.subtype ∘ₗ pᵤ) T :=
by
  simp_rw [Commute, SemiconjBy, LinearMap.ext_iff, Module.End.mul_apply,
    LinearMap.comp_apply, U.subtype_apply]
  constructor
  · rintro ⟨h1, h2⟩ x
    rw [← (U.invariantUnder'_iff_linear_proj_comp_self_comp_linear_proj_eq V _ _).mp h2 x]
    exact (linearProjOfIsCompl_eq_self_iff hUV _).mpr (h1 (coe_mem (pᵤ x)))
  · intro h
    simp_rw [U.invariantUnder_iff_linear_proj_comp_self_eq _ hUV,
      (LinearMap.range_eq_top.1 (linearProjOfIsCompl_range hUV)).forall,
      U.invariantUnder'_iff_linear_proj_comp_self_comp_linear_proj_eq _ hUV, h,
      linearProjOfIsCompl_idempotent hUV, ← forall_and, and_self_iff,
      forall_const]

/-- `U` is invariant under `T.symm` if and only if `U ⊆ T(U)` -/
lemma invariantUnder_symm_iff_le_map (T : E ≃ₗ[R] E) :
  U.InvariantUnder T.symm ↔ U ≤ U.map T :=
(U.invariantUnder_iff_map T.symm).trans (T.toEquiv.symm.subset_symm_image _ _).symm

/-- `U` is invariant under `⅟T` if and only if `U ⊆ T(U)` -/
lemma invariantUnder_invOf_iff_le_map [Invertible T] :
  U.InvariantUnder (⅟T) ↔ U ≤ U.map T :=
invariantUnder_symm_iff_le_map _ (LinearEquiv.ofInvertible T)

/-- `⅟T ∘ₗ pᵤ ∘ₗ T = pᵤ` if and only if `T(U) = U` and `T(V) = V`,
where `pᵤ` denotes the linear projection to `U` along `V` -/
theorem invOf_comp_linear_proj_comp_self_eq_linear_proj_iff_map_eq [Invertible T] :
  ⅟T ∘ₗ (U.subtype ∘ₗ pᵤ) ∘ₗ T = U.subtype ∘ₗ pᵤ ↔ U.map T = U ∧ V.map T = V :=
by
  have : ∀ f, Commute f T ↔ ⅟T ∘ₗ f ∘ₗ T = f :=
    fun f => Commute.symm_iff.trans ((unitOfInvertible T).commute_iff_inv_mul_cancel f)
  simp_rw [← this, ← isCompl_invariantUnder_iff_linear_proj_and_self_commute, le_antisymm_iff,
    ← invariantUnder_iff_map, and_and_and_comm, iff_self_and,
    ← invariantUnder_invOf_iff_le_map,
    isCompl_invariantUnder_iff_linear_proj_and_self_commute U V hUV]
  exact @Commute.units_inv_right _ _ _ (unitOfInvertible T)

end Submodule
