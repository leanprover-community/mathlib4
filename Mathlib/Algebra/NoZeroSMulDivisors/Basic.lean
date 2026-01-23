/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yury Kudryashov, Joseph Myers, Heather Macbeth, Kim Morrison, Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs

/-!
# `NoZeroSMulDivisors`

This file proves more lemmas about the `NoZeroSMulDivisors` class, which is deprecated in favor of
`Module.IsTorsionFree`.
-/

@[expose] public section

assert_not_exists Multiset Set.indicator Pi.single_smul₀ Field

variable {R M : Type*}

section GroupWithZero

variable [GroupWithZero R] [AddMonoid M] [DistribMulAction R M]

-- see note [lower instance priority]
/-- This instance applies to `DivisionSemiring`s, in particular `NNReal` and `NNRat`. -/
instance (priority := 100) GroupWithZero.toNoZeroSMulDivisors : NoZeroSMulDivisors R M :=
  ⟨fun {a _} h ↦ or_iff_not_imp_left.2 fun ha ↦ (smul_eq_zero_iff_eq <| Units.mk0 a ha).1 h⟩

end GroupWithZero
