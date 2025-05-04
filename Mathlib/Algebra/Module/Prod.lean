/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathlib.Algebra.GroupWithZero.Action.Prod
import Mathlib.Algebra.Module.Defs

/-!
# Prod instances for module and multiplicative actions

This file defines instances for binary product of modules
-/


variable {R : Type*} {M : Type*} {N : Type*}

namespace Prod

instance smulWithZero [Zero R] [Zero M] [Zero N] [SMulWithZero R M] [SMulWithZero R N] :
    SMulWithZero R (M × N) where
  smul_zero _ := by ext <;> exact smul_zero ..
  zero_smul _ := by ext <;> exact zero_smul ..

instance mulActionWithZero [MonoidWithZero R] [Zero M] [Zero N] [MulActionWithZero R M]
    [MulActionWithZero R N] : MulActionWithZero R (M × N) :=
  { Prod.mulAction, Prod.smulWithZero with }

instance instModule [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] :
    Module R (M × N) where
  add_smul _ _ _ := by ext <;> exact add_smul ..
  zero_smul _ := by ext <;> exact zero_smul ..

end Prod
