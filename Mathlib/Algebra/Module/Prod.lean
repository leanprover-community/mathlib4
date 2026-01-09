/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Prod
public import Mathlib.Algebra.Module.Defs

/-!
# Prod instances for module and multiplicative actions

This file defines instances for binary product of modules
-/

@[expose] public section


variable {R : Type*} {M : Type*} {N : Type*}

namespace Prod

instance instModule [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] :
    Module R (M × N) where
  add_smul _ _ _ := by ext <;> exact add_smul ..
  zero_smul _ := by ext <;> exact zero_smul ..

end Prod
