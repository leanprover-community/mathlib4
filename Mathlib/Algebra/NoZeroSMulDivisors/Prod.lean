/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Group.Action.Prod

/-!
# Prod instances for NoZeroSMulDivisors

This file defines a NoZeroSMulDivisors instance for the binary product of actions.
-/

variable {R M N : Type*}

namespace Prod

instance noZeroSMulDivisors [Zero R] [Zero M] [Zero N]
    [SMulWithZero R M] [SMulWithZero R N] [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N] :
    NoZeroSMulDivisors R (M × N) :=
  { eq_zero_or_eq_zero_of_smul_eq_zero := by -- Porting note: in mathlib3 there is no need for `by`/
      -- `intro`/`exact`, i.e. the following works:
      -- ⟨fun c ⟨x, y⟩ h =>
      --   or_iff_not_imp_left.mpr fun hc =>
      intro c ⟨x, y⟩ h
      exact or_iff_not_imp_left.mpr fun hc =>
        mk.inj_iff.mpr
          ⟨(smul_eq_zero.mp (congr_arg fst h)).resolve_left hc,
            (smul_eq_zero.mp (congr_arg snd h)).resolve_left hc⟩ }

end Prod
