/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module -- shake: keep-all

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Tactic.Linter.DeprecatedModule

/-!
# Faithful actions involving groups with zero
-/
deprecated_module (since := "2026-02-03")

@[expose] public section

assert_not_exists Equiv.Perm.equivUnitsEnd Prod.fst_mul Ring

open Function

variable {α : Type*}

/-- `Monoid.toMulAction` is faithful on nontrivial cancellative monoids with zero. -/
@[nolint unusedArguments, deprecated "subsumed by `instFaithfulSMul`" (since := "2026-02-03")]
lemma IsRightCancelMulZero.faithfulSMul [MonoidWithZero α] [IsRightCancelMulZero α] :
    FaithfulSMul α α := inferInstance
