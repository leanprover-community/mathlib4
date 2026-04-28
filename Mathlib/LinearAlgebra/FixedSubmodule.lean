/-
Copyright (c) 2026 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.NormNum

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

theorem fixedSubmodule_inf_fixedSubmodule_le_comp (f g : V →ₗ[R] V) :
    f.fixedSubmodule ⊓ g.fixedSubmodule ≤ (f ∘ₗ g).fixedSubmodule := by
  intro; simp_all

theorem fixedSubmodule_comp_inf_fixedSubmodule_le (f g : V →ₗ[R] V) :
    (f ∘ₗ g).fixedSubmodule ⊓ g.fixedSubmodule ≤ f.fixedSubmodule := by intro; aesop

end LinearMap

namespace LinearEquiv

open Pointwise LinearMap Submodule MulAction

variable {R : Type*} [Semiring R]
  {U V : Type*} [AddCommMonoid U] [AddCommMonoid V]
  [Module R U] [Module R V] (e : V ≃ₗ[R] V)

variable {P : Submodule R U} {Q : Submodule R V}

theorem fixedSubmodule_eq_top_iff {f : V ≃ₗ[R] V} :
    f.fixedSubmodule = ⊤ ↔ f = .refl R V := by
  simp [LinearEquiv.ext_iff, Submodule.ext_iff]

theorem mem_stabilizer_submodule_of_le_fixedSubmodule
    {e : V ≃ₗ[R] V} {W : Submodule R V} (hW : W ≤ LinearMap.fixedSubmodule e) :
    e ∈ stabilizer (V ≃ₗ[R] V) W := by
  rw [mem_stabilizer_submodule_iff_map_eq]
  apply le_antisymm
  · rintro _ ⟨x, hx : x ∈ W, rfl⟩
    suffices e x = x by simpa [this, coe_coe]
    rw [← coe_toLinearMap, ← mem_fixedSubmodule_iff]
    exact hW hx
  · intro x hx
    refine ⟨x, hx, ?_⟩
    simp only [DistribSMul.toLinearMap_apply, LinearEquiv.smul_def]
    rw [← coe_toLinearMap, ← mem_fixedSubmodule_iff]
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

open Pointwise MulAction

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- When `u : V ≃ₗ[R] V` maps a submodule `W` into itself,
this is the induced linear equivalence of `V ⧸ W`, as a group homomorphism. -/
def reduce (W : Submodule R V) : stabilizer (V ≃ₗ[R] V) W →* (V ⧸ W) ≃ₗ[R] (V ⧸ W) where
  toFun u := Quotient.equiv W W u.val u.prop
  map_mul' u v := by
    ext x
    obtain ⟨y, rfl⟩ := W.mkQ_surjective x
    simp
  map_one' := by aesop

@[simp]
theorem reduce_mk (W : Submodule R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V) :
    reduce W u (Submodule.Quotient.mk x) = Submodule.Quotient.mk (u.val x) :=
  rfl

theorem reduce_mkQ (W : Submodule R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V) :
    reduce W u (W.mkQ x) = W.mkQ (u.val x) :=
  rfl

/-- The linear equivalence deduced from `e : V ≃ₗ[R] V`
by passing to the quotient by `e.fixedSubmodule`. -/
def fixedReduce (e : V ≃ₗ[R] V) :
    (V ⧸ e.fixedSubmodule) ≃ₗ[R] V ⧸ e.fixedSubmodule :=
  reduce e.fixedSubmodule ⟨e, e.mem_stabilizer_fixedSubmodule⟩

@[simp]
theorem fixedReduce_mk (e : V ≃ₗ[R] V) (x : V) :
    fixedReduce e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) :=
  rfl

@[simp]
theorem fixedReduce_mkQ (e : V ≃ₗ[R] V) (x : V) :
    fixedReduce e (e.fixedSubmodule.mkQ x) = e.fixedSubmodule.mkQ (e x) :=
  rfl

theorem fixedReduce_eq_smul_iff (e : V ≃ₗ[R] V) (a : R) :
    (∀ x, e.fixedReduce x = a • x) ↔
      ∀ v, e v - a • v ∈ e.fixedSubmodule := by
  simp only [← e.fixedSubmodule.ker_mkQ, mem_ker, map_sub, ← fixedReduce_mkQ, sub_eq_zero]
  constructor
  · intro H x; simp [H]
  · intro H x
    have ⟨y, hy⟩ := e.fixedSubmodule.mkQ_surjective x
    rw [← hy]
    apply H

theorem fixedReduce_eq_one (e : V ≃ₗ[R] V) :
    e.fixedReduce = LinearEquiv.refl R _ ↔ ∀ v, e v - v ∈ e.fixedSubmodule := by
  simpa [LinearEquiv.ext_iff] using fixedReduce_eq_smul_iff e 1

end LinearEquiv

end
