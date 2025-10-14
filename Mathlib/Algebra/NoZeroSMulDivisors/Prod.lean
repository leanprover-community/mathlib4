/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Module.Prod

/-!
# Prod instances for Module.IsTorsionFree

This file defines a Module.IsTorsionFree instance for the binary product of actions.
-/

@[expose] public section

variable {R M N : Type*}

namespace Prod

instance noZeroSMulDivisors [Semiring R] [IsDomain R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N] :
    NoZeroSMulDivisors R (M × N) where
  eq_zero_or_eq_zero_of_smul_eq_zero {c xy} h := by simpa [Prod.ext_iff, or_and_left] using h

end Prod
