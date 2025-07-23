/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.InjSurj

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

assert_not_exists Ring

universe u v

variable {α : Type u} {β : Type v}

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `SemigroupWithZero` across an `Equiv` -/
protected abbrev semigroupWithZero [SemigroupWithZero β] : SemigroupWithZero α := by
  let mul := e.mul
  let zero := e.zero
  apply e.injective.semigroupWithZero _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `MulZeroClass` across an `Equiv` -/
protected abbrev mulZeroClass [MulZeroClass β] : MulZeroClass α := by
  let zero := e.zero
  let mul := e.mul
  apply e.injective.mulZeroClass _ <;> intros <;> exact e.apply_symm_apply _


/-- Transfer `MulZeroOneClass` across an `Equiv` -/
protected abbrev mulZeroOneClass [MulZeroOneClass β] : MulZeroOneClass α := by
  let zero := e.zero
  let one := e.one
  let mul := e.mul
  apply e.injective.mulZeroOneClass _ <;> intros <;> exact e.apply_symm_apply _

variable (M : Type*) [Monoid M]

/-- Transfer `DistribMulAction` across an `Equiv` -/
protected abbrev distribMulAction (e : α ≃ β) [AddCommMonoid β] :
    letI := Equiv.addCommMonoid e
    ∀ [DistribMulAction M β], DistribMulAction M α := by
  intros
  letI := Equiv.addCommMonoid e
  exact
    ({ Equiv.mulAction M e with
        smul_zero := by simp [zero_def, smul_def]
        smul_add := by simp [add_def, smul_def, smul_add] } :
      DistribMulAction M α)

end Equiv
