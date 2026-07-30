/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

public section

assert_not_exists Ring

variable (M M₀ : Type*) {A B : Type*}

namespace Equiv

/-- Transfer `SMulZeroClass` across an `Equiv` -/
protected abbrev smulZeroClass [Zero A] [Zero B] [SMulZeroClass M B] (e : A ≃ B)
    (map_zero : e 0 = 0) : SMulZeroClass M A where
  __ := e.smul M
  smul_zero := by simp [smul_def, symm_apply_eq, map_zero]

/-- Transfer `SMulWithZero` across an `Equiv` -/
protected abbrev smulWithZero [Zero M₀] [Zero A] [Zero B] [SMulWithZero M₀ B] (e : A ≃ B)
    (map_zero : e 0 = 0) : SMulWithZero M₀ A where
  __ := e.smulZeroClass M₀ map_zero
  zero_smul := by simp [smul_def, symm_apply_eq, map_zero]

/-- Transfer `MulActionWithZero` across an `Equiv` -/
protected abbrev mulActionWithZero [MonoidWithZero M₀] [Zero A] [Zero B] (e : A ≃ B)
    [MulActionWithZero M₀ B] (map_zero : e 0 = 0) : MulActionWithZero M₀ A where
  __ := e.smulWithZero M₀ map_zero
  __ := e.mulAction M₀

end Equiv

namespace AddEquiv

/-- Transfer `DistribSMul` across an `Equiv` -/
protected abbrev distribSMul [AddZeroClass A] [AddZeroClass B] [DistribSMul M B] (e : A ≃+ B) :
    DistribSMul M A where
  __ := e.smulZeroClass M e.map_zero
  smul_add := by simp [e.smul_def, smul_add]

/-- Transfer `DistribMulAction` across an `Equiv` -/
protected abbrev distribMulAction [Monoid M] [AddMonoid A] [AddMonoid B]
    [DistribMulAction M B] (e : A ≃+ B) :
    DistribMulAction M A where
  __ := e.distribSMul M
  __ := e.mulAction M

end AddEquiv
