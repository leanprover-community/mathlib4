/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Continuous linear equivalences

## Notation
Continuous semilinear / linear / star-linear equivalences between topological modules are denoted
by `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.

## Main Definitions
* `ofEq`: `LinearEquiv.ofEq` as a continuous linear equivalence.
* `submoduleMap`: `LinearEquiv.submoduleMap` as a continuous linear equivalence.
* `ofSubmodules`: `LinearEquiv.ofSubmodules` as a continuous linear equivalence.
* `ofSubmodule'`: `ofSubmodule` but with `comap` on the left instead of `map` on the right.
* `Submodule.topContEquiv`: `Submodule.topEquiv` as a continuous linear equivalence.

## Main Results
-/

@[expose] public section

namespace ContinuousLinearEquiv

variable {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂] [AddCommMonoid M] [TopologicalSpace M]
  [AddCommMonoid M₂] [TopologicalSpace M₂]
  {module_M : Module R M} {module_M₂ : Module R₂ M₂} {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
  {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

/-- Continuous linear equivalence between two equal submodules:
this is `LinearEquiv.ofEq` as a continuous linear equivalence -/
def ofEq (p q : Submodule R M) (h : p = q) : p ≃L[R] q where
  toLinearEquiv := LinearEquiv.ofEq _ _ h
  continuous_toFun := by
    have h' : (fun x ↦ x ∈ p) = (fun x ↦ x ∈ q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').continuous
  continuous_invFun := by
    have h' : (fun x ↦ x ∈ p) = (fun x ↦ x ∈ q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').symm.continuous

/--
A continuous linear equivalence of two modules restricts to a continuous linear equivalence
from any submodule `p` of the domain onto the image of that submodule.

This is the continuous linear version of `LinearEquiv.submoduleMap`.
This is `ContinuousLinearEquiv.ofSubmodule'` but with map on the right instead of comap on the left.
-/
def submoduleMap (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) :
    p ≃SL[σ₁₂] Submodule.map (e : M →ₛₗ[σ₁₂] M₂) p where
  __ := LinearEquiv.submoduleMap e.toLinearEquiv p
  continuous_toFun := map_continuous ((e.toContinuousLinearMap.comp p.subtypeL).codRestrict _ _)
  continuous_invFun := (map_continuous e.symm).restrict fun x hx ↦
    ((LinearEquiv.submoduleMap e.toLinearEquiv p).symm ⟨x, hx⟩).2

@[simp]
lemma submoduleMap_apply (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) (x : p) :
    e.submoduleMap p x = e x := by
  rfl

@[simp]
lemma submoduleMap_symm_apply (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M)
    (x : p.map (e : M →ₛₗ[σ₁₂] M₂)) :
    (e.submoduleMap p).symm x = e.symm x := by
  rfl

/-- A continuous linear equivalence which maps a submodule of one module onto another,
restricts to a continuous linear equivalence of the two submodules.
This is `LinearEquiv.ofSubmodules` as a continuous linear equivalence. -/
def ofSubmodules (e : M ≃SL[σ₁₂] M₂)
    (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) : p ≃SL[σ₁₂] q :=
  (e.submoduleMap p).trans (.ofEq _ _ h)

@[simp]
theorem ofSubmodules_apply (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) (x : p) :
    e.ofSubmodules p q h x = e x :=
  rfl

@[simp]
theorem ofSubmodules_symm_apply (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) (x : q) : (e.ofSubmodules p q h).symm x = e.symm x :=
  rfl

/-- A continuous linear equivalence of two modules restricts to a continuous linear equivalence
from the preimage of any submodule to that submodule.
This is `ContinuousLinearEquiv.ofSubmodule` but with `comap` on the left
instead of `map` on the right. -/
def ofSubmodule' (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    U.comap (f : M →ₛₗ[σ₁₂] M₂) ≃SL[σ₁₂] U :=
  f.symm.ofSubmodules _ _ (U.map_equiv_eq_comap_symm f.toLinearEquiv.symm) |>.symm

theorem ofSubmodule'_toContinuousLinearMap (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    (f.ofSubmodule' U).toContinuousLinearMap =
      (f.toContinuousLinearMap.comp ((U.comap f.toLinearMap).subtypeL)).codRestrict U
        ((fun ⟨x, hx⟩ ↦ by simpa [Submodule.mem_comap])) := by
  rfl

@[simp]
theorem ofSubmodule'_apply (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂)
    (x : U.comap (f : M →ₛₗ[σ₁₂] M₂)) :
    (f.ofSubmodule' U x : M₂) = f (x : M) :=
  rfl

@[simp]
theorem ofSubmodule'_symm_apply (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) (x : U) :
    ((f.ofSubmodule' U).symm x : M) = f.symm (x : M₂) := rfl

end ContinuousLinearEquiv

/-- The top submodule is continuous linearly equivalent to the module.
This is the continuous version of `Submodule.topEquiv`. -/
abbrev _root_.Submodule.topContEquiv {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] : (⊤ : Submodule R M) ≃L[R] M where
  __ := Submodule.topEquiv
