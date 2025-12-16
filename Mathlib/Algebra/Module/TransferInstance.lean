/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

@[expose] public section

assert_not_exists Algebra

universe u v
variable {R α β : Type*} [Semiring R]

namespace Equiv
variable (e : α ≃ β)

variable (R : Type*) [Zero R] in
/-- Transfer `NoZeroSMulDivisors` across an `Equiv` -/
protected lemma noZeroSMulDivisors [Zero β] [SMul R β] [NoZeroSMulDivisors R β] :
    let := e.zero
    let := e.smul R
    NoZeroSMulDivisors R α := by
  extract_lets
  refine ⟨fun {r} m ↦ ?_⟩
  simpa [smul_def, zero_def, Equiv.eq_symm_apply] using eq_zero_or_eq_zero_of_smul_eq_zero

variable (R) in
/-- Transfer `Module` across an `Equiv` -/
protected abbrev module (e : α ≃ β) [AddCommMonoid β] [Module R β] :
    letI := Equiv.addCommMonoid e
    Module R α :=
  letI := Equiv.addCommMonoid e
  { Equiv.distribMulAction R e with
      zero_smul := by simp [smul_def, zero_smul, zero_def]
      add_smul := by simp [add_def, smul_def, add_smul] }

variable (R) in
/-- An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def linearEquiv (e : α ≃ β) [AddCommMonoid β] [Module R β] :
    letI := Equiv.addCommMonoid e
    letI := Equiv.module R e
    α ≃ₗ[R] β :=
  letI := Equiv.addCommMonoid e
  letI module := Equiv.module R e
  { Equiv.addEquiv e with
    map_smul' := fun r x => by
      apply e.symm.injective
      simp only [toFun_as_coe, RingHom.id_apply, EmbeddingLike.apply_eq_iff_eq]
      exact Iff.mpr (apply_eq_iff_eq_symm_apply _) rfl }

end Equiv

variable (A) [Semiring A] [Module R A] [AddCommMonoid α] [AddCommMonoid β] [Module A β]

/-- Transport a module instance via an isomorphism of the underlying abelian groups.
This has better definitional properties than `Equiv.module` since here
the abelian group structure remains unmodified. -/
abbrev AddEquiv.module (e : α ≃+ β) : Module A α where
  toSMul := e.toEquiv.smul A
  one_smul := by simp [Equiv.smul_def]
  mul_smul := by simp [Equiv.smul_def, mul_smul]
  smul_zero := by simp [Equiv.smul_def]
  smul_add := by simp [Equiv.smul_def]
  add_smul := by simp [Equiv.smul_def, add_smul]
  zero_smul := by simp [Equiv.smul_def]

/-- The module instance from `AddEquiv.module` is compatible with the `R`-module structures,
if the `AddEquiv` is induced by an `R`-module isomorphism. -/
lemma LinearEquiv.isScalarTower [Module R α] [Module R β] [IsScalarTower R A β]
    (e : α ≃ₗ[R] β) :
    letI := e.toAddEquiv.module A
    IsScalarTower R A α := by
  letI := e.toAddEquiv.module A
  constructor
  intro x y z
  simp only [Equiv.smul_def, smul_assoc]
  apply e.symm.map_smul
