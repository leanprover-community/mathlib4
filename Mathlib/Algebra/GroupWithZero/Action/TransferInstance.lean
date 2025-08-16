/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.TransferInstance
import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

assert_not_exists Ring

variable {M M₀ A B : Type*}

namespace Equiv

variable (M) in
/-- Transfer `SMulZeroClass` across an `Equiv` -/
protected abbrev smulZeroClass (e : A ≃ B) [Zero B] [SMulZeroClass M B] :
    letI := e.zero
    SMulZeroClass M A := by
  letI := e.zero
  exact {
    e.smul M with
    smul_zero := by simp [smul_def, zero_def]
  }

variable (M₀) in
/-- Transfer `SMulWithZero` across an `Equiv` -/
protected abbrev smulWithZero (e : A ≃ B) [Zero M₀] [Zero B] [SMulWithZero M₀ B] :
    letI := e.zero
    SMulWithZero M₀ A := by
  letI := e.zero
  exact {
    e.smulZeroClass M₀ with
    zero_smul := by simp [smul_def, zero_def]
  }

variable (M₀) in
/-- Transfer `MulActionWithZero` across an `Equiv` -/
protected abbrev mulActionWithZero (e : A ≃ B) [MonoidWithZero M₀] [Zero B]
    [MulActionWithZero M₀ B] :
    letI := e.zero
    MulActionWithZero M₀ A := by
  letI := e.zero
  exact { e.smulWithZero M₀, e.mulAction M₀ with }

variable (M) in
/-- Transfer `DistribSMul` across an `Equiv` -/
protected abbrev distribSMul (e : A ≃ B) [AddZeroClass B] [DistribSMul M B] :
    letI := e.addZeroClass
    DistribSMul M A := by
  letI := e.addZeroClass
  exact {
    e.smulZeroClass M with
    smul_add := by simp [add_def, smul_def, smul_add]
  }

variable (M) in
/-- Transfer `DistribMulAction` across an `Equiv` -/
protected abbrev distribMulAction (e : A ≃ B) [Monoid M] [AddMonoid B] [DistribMulAction M B] :
    letI := e.addMonoid
    DistribMulAction M A := by
  letI := e.addMonoid
  exact { e.distribSMul M, e.mulAction M with }

end Equiv
