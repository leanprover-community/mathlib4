/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.GroupTheory.GroupAction.Prod

#align_import algebra.module.prod from "leanprover-community/mathlib"@"a437a2499163d85d670479f69f625f461cc5fef9"

/-!
# Prod instances for module and multiplicative actions

This file defines instances for binary product of modules
-/


variable {R : Type*} {S : Type*} {M : Type*} {N : Type*}

namespace Prod

instance smulWithZero [Zero R] [Zero M] [Zero N] [SMulWithZero R M] [SMulWithZero R N] :
    SMulWithZero R (M × N) :=
  { Prod.smul with
    smul_zero := fun _ => Prod.ext (smul_zero _) (smul_zero _)
    zero_smul := fun _ => Prod.ext (zero_smul _ _) (zero_smul _ _) }
#align prod.smul_with_zero Prod.smulWithZero

instance mulActionWithZero [MonoidWithZero R] [Zero M] [Zero N] [MulActionWithZero R M]
    [MulActionWithZero R N] : MulActionWithZero R (M × N) :=
  { Prod.mulAction with
    smul_zero := fun _ => Prod.ext (smul_zero _) (smul_zero _)
    zero_smul := fun _ => Prod.ext (zero_smul _ _) (zero_smul _ _) }
#align prod.mul_action_with_zero Prod.mulActionWithZero

instance instModule [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] :
    Module R (M × N) :=
  { Prod.distribMulAction with
    add_smul := fun _ _ _ => mk.inj_iff.mpr ⟨add_smul _ _ _, add_smul _ _ _⟩
    zero_smul := fun _ => mk.inj_iff.mpr ⟨zero_smul _ _, zero_smul _ _⟩ }
#align prod.module Prod.instModule

instance noZeroSMulDivisors {r : Semiring R} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [NoZeroSMulDivisors R M] [NoZeroSMulDivisors R N] :
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
#align prod.no_zero_smul_divisors Prod.noZeroSMulDivisors

end Prod
