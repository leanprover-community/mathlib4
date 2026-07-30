/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

@[expose] public section

assert_not_exists Algebra

universe u v
variable {R α β : Type*}

namespace Equiv
variable (R) [Zero R]

/-- Transfer `NoZeroSMulDivisors` across an `Equiv` -/
protected lemma noZeroSMulDivisors [Zero α] [Zero β] [SMul R β] [NoZeroSMulDivisors R β]
    (e : α ≃ β) (map_zero : e 0 = 0) :
    let := e.smul R
    NoZeroSMulDivisors R α := by
  extract_lets
  refine ⟨fun {r} m ↦ ?_⟩
  simp_rw [e.eq_symm_apply.2 map_zero, eq_symm_apply, smul_def, apply_symm_apply]
  exact eq_zero_or_eq_zero_of_smul_eq_zero

end Equiv

variable [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [Module R β]

namespace AddEquiv

variable (R) (e : α ≃+ β)

/-- Transfer `Module` across an `Equiv` -/
protected abbrev module : Module R α where
  __ := e.distribMulAction R
  zero_smul := by simp [e.smul_def, zero_smul]
  add_smul := by simp [e.smul_def, add_smul]

/-- When `α` is equipped with the `A`-module structure transferred via `e : α ≃+ β`,
this isomorphism is `A`-linear. -/
def linearEquiv :
    letI := e.module R
    α ≃ₗ[R] β :=
  letI := e.module R
  { e with
    map_smul' := fun r x => by
      apply e.symm.injective
      simp only [RingHom.id_apply, EmbeddingLike.apply_eq_iff_eq]
      exact Iff.mpr e.apply_eq_iff_eq_symm_apply rfl }

/-- Transfer `Module.IsTorsionFree` across an `Equiv` -/
protected lemma moduleIsTorsionFree [Module.IsTorsionFree R β] :
    letI := e.module R
    Module.IsTorsionFree R α :=
  letI := e.module R
  (e.linearEquiv R).injective.moduleIsTorsionFree _ (by simp)

end AddEquiv

variable [Module R α] (A : Type*) [Semiring A] [Module R A] [Module A β]

/-- The module instance from `AddEquiv.module` is compatible with the `R`-module structures,
if the `AddEquiv` is induced by an `R`-module isomorphism. -/
lemma LinearEquiv.isScalarTower [IsScalarTower R A β] (e : α ≃ₗ[R] β) :
    letI := e.toAddEquiv.module A
    IsScalarTower R A α := by
  letI := e.toAddEquiv.module A
  constructor
  intro x y z
  simp only [Equiv.smul_def, smul_assoc]
  apply e.symm.map_smul
