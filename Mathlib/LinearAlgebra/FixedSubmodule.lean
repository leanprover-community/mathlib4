/-
Copyright (c) 2026 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# The fixed submodule of a linear map

- `LinearMap.fixedSubmodule`: the submodule of a linear map consisting of its fixed points.

-/

@[expose] public section

namespace LinearMap

open Pointwise Submodule MulAction

variable {R : Type*} [Semiring R]
  {U V : Type*} [AddCommMonoid U] [AddCommMonoid V]
  [Module R U] [Module R V] (e : V ≃ₗ[R] V)


/-- The fixed submodule of a linear map. -/
def fixedSubmodule (f : V →ₗ[R] V) : Submodule R V where
  carrier := { x | f x = x }
  add_mem' {x y} hx hy := by aesop
  zero_mem' := by simp
  smul_mem' r x hx := by aesop

@[simp]
theorem mem_fixedSubmodule_iff {f : V →ₗ[R] V} {v : V} :
    v ∈ f.fixedSubmodule ↔ f v = v := by
  simp [fixedSubmodule]

theorem fixedSubmodule_eq_ker {R : Type*} [Ring R]
    {V : Type*} [AddCommGroup V] [Module R V] (f : V →ₗ[R] V) :
    f.fixedSubmodule = LinearMap.ker (f - id (R := R)) := by
  ext; simp [sub_eq_zero]

theorem fixedSubmodule_eq_top_iff {f : V →ₗ[R] V} :
    f.fixedSubmodule = ⊤ ↔ f = id (R := R) := by
  simp [LinearMap.ext_iff, Submodule.ext_iff]

theorem inf_fixedSubmodule_le_fixedSubmodule_mul (e f : V →ₗ[R] V) :
    e.fixedSubmodule ⊓ f.fixedSubmodule ≤ (e * f).fixedSubmodule := by
  intro; simp_all

theorem fixedSubmodule_mul_inf_fixedSubmodule_le_fixedSubmodule (e f : V →ₗ[R] V) :
    (e ∘ₗ f).fixedSubmodule ⊓ f.fixedSubmodule ≤ e.fixedSubmodule := by
  intro; aesop

theorem fixedSubmodule_mul_inf_fixedSubmodule_le_fixedSubmodule' (e f : V →ₗ[R] V) :
    (f ∘ₗ e).fixedSubmodule ⊓ e.fixedSubmodule ≤ f.fixedSubmodule := by
  intro x
  simp only [mem_inf, mem_fixedSubmodule_iff, coe_comp, Function.comp_apply, and_imp]
  grind

end LinearMap

namespace LinearEquiv

open Pointwise LinearMap Submodule MulAction

variable {R : Type*} [Semiring R]
  {U V : Type*} [AddCommMonoid U] [AddCommMonoid V]
  [Module R U] [Module R V] (e : V ≃ₗ[R] V)

theorem smul_submodule_def (W : Submodule R V) :
    e • W = map e.toLinearMap W := rfl

theorem mem_stabilizer_submodule_iff_map_eq (W : Submodule R V) :
    e ∈ stabilizer (V ≃ₗ[R] V) W ↔ map e.toLinearMap W = W := by
  simp [mem_stabilizer_iff, smul_submodule_def]

variable {P : Submodule R U} {Q : Submodule R V}

theorem fixedSubmodule_eq_top_iff {f : V ≃ₗ[R] V} :
    f.fixedSubmodule = ⊤ ↔ f = 1 := by
  simp [LinearEquiv.ext_iff, Submodule.ext_iff]

theorem mem_stabilizer_submodule_of_le_fixedSubmodule
    {e : V ≃ₗ[R] V} {W : Submodule R V} (hW : W ≤ LinearMap.fixedSubmodule e) :
    e ∈ stabilizer (V ≃ₗ[R] V) W := by
  rw [mem_stabilizer_submodule_iff_map_eq]
  apply le_antisymm
  · rintro _ ⟨x, hx : x ∈ W, rfl⟩
    suffices e x = x by simpa only [this, coe_coe]
    rw [← coe_toLinearMap, ← mem_fixedSubmodule_iff]
    exact hW hx
  · intro x hx
    refine ⟨x, hx, ?_⟩
    rw [coe_coe, ← coe_toLinearMap, ← mem_fixedSubmodule_iff]
    exact hW hx

theorem mem_stabilizer_fixedSubmodule (e : V ≃ₗ[R] V) :
    e ∈ stabilizer _ e.fixedSubmodule :=
  mem_stabilizer_submodule_of_le_fixedSubmodule (le_refl _)

theorem map_eq_of_mem_fixingSubgroup (W : Submodule R V)
    (he : e ∈ fixingSubgroup _ W.carrier) :
    map e.toLinearMap W = W := by
  ext v
  simp only [mem_fixingSubgroup_iff, carrier_eq_coe, SetLike.mem_coe, LinearEquiv.smul_def] at he
  refine ⟨fun ⟨w, hv, hv'⟩ ↦ ?_, fun hv ↦ ?_⟩
  · simp only [SetLike.mem_coe, coe_coe] at hv hv'
    rwa [← hv', he w hv]
  · refine ⟨v, hv, he v hv⟩

end LinearEquiv

end

