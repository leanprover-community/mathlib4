/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Ring.FunLike
public import Mathlib.Algebra.Algebra.Pi

/-! # Algebra map `FunLike` class
In this file we define the type class `IsAlgebraApply` that states that the `algebraMap` on a
`FunLike` type class is inherited from the `algebraMap` of the function type.

We also define the coercion and evaluation as algebra homomorphisms.
-/

public section

variable {R F α β : Type*}

section Def

/-- `IsAlgebraApply R F` states for all `r : R` and `x : α`, the algebra map `algebraMap R F r x`
coincides with `algebraMap R β r`. -/
class IsAlgebraApply (R F : Type*) {α β : Type*} [FunLike F α β] [CommSemiring R] [Semiring F]
    [Semiring β] [Algebra R F] [Algebra R β] where
  algebraMap_apply (r : R) (x : α) : algebraMap R F r x = algebraMap R β r := by intros; rfl

@[simp, grind =]
alias algebraMap_apply := IsAlgebraApply.algebraMap_apply

end Def

namespace FunLike

variable [FunLike F α β] [CommSemiring R] [Semiring F] [Semiring β] [Algebra R F] [Algebra R β]

@[simp, norm_cast]
theorem coe_algebraMap [IsAlgebraApply R F] (r : R) :
    algebraMap R F r = algebraMap R (α → β) r := by ext; simp

section AlgHom

variable [IsZeroApply F] [IsOneApply F] [IsAddApply F] [IsMulApply F] [IsAlgebraApply R F]

variable (R F) in
/-- Coercion as an algebra homomorphism. -/
@[expose]
def coeAlgHom : F →ₐ[R] α → β where
  toFun f := f
  map_zero' := by simp
  map_one' := by simp
  map_add' := by simp
  map_mul' := by simp
  commutes' := by simp

@[simp]
theorem coeAlgHom_apply (f : F) : coeAlgHom R F f = f := rfl

@[norm_cast]
theorem coe_coeAlgHom : (coeAlgHom R F : F → α → β) = DFunLike.coe := rfl

theorem coeAlgHom_injective : Function.Injective (coeAlgHom R F) := by
  rw [coe_coeAlgHom]
  exact DFunLike.coe_injective

variable (R F) in
/-- Evaluation as an algebra homomorphism. -/
@[expose]
def evalAlgHom (x : α) : F →ₐ[R] β where
  toFun f := f x
  map_zero' := by simp
  map_one' := by simp
  map_add' := by simp
  map_mul' := by simp
  commutes' := by simp

@[simp]
theorem evalAlgHom_apply (x : α) (f : F) : evalAlgHom R F x f = f x := rfl

end AlgHom

end FunLike
