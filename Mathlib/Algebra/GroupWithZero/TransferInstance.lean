/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.GroupWithZero.InjSurj

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

assert_not_exists MulAction Ring

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

/-- Transfer `MonoidWithZero` across an `Equiv` -/
protected abbrev monoidWithZero [MonoidWithZero β] : MonoidWithZero α := by
  let _ := e.mulZeroOneClass
  let _ := e.pow ℕ
  apply e.injective.monoidWithZero _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommMonoidWithZero` across an `Equiv` -/
protected abbrev commMonoidWithZero [CommMonoidWithZero β] : CommMonoidWithZero α := by
  let _ := e.monoidWithZero
  apply e.injective.commMonoidWithZero _ <;> intros <;> exact e.apply_symm_apply _

end Equiv
