/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Mathlib.Mathport.Rename

namespace Mathlib.Prelude

-- Note: we do not currently auto-align constants.
#align quot Quot
#align quot.mk Quot.mk
#align quot.lift Quot.lift
#align quot.ind Quot.ind

-- Otherwise would be`OutParam` and `OptParam`!
-- Note: we want `auto_param` to *not* align.
#align out_param               outParam
#align opt_param               optParam

#align heq                     HEq

#align psigma                  PSigma
#align punit                   PUnit
#align pprod                   PProd
#align psum                    PSum
#align ulift                   ULift

#align has_coe Coe
#align has_coe.coe Coe.coe

#align has_coe_t CoeT
#align has_coe_t.coe CoeT.coe

#align has_coe_to_fun CoeFun
#align has_coe_to_fun.coe CoeFun.coe

#align has_coe_to_sort CoeSort
#align has_coe_to_sort.coe CoeSort.coe

#align has_le                  LE
#align has_le.le               LE.le
#align has_lt                  LT
#align has_lt.lt               LT.lt

#align has_beq                 BEq
#align has_sizeof              SizeOf

-- This otherwise causes filenames to clash
#align category_theory.Kleisli CategoryTheory.KleisliCat

-- TODO: backport?
#align int.neg_succ_of_nat     Int.negSucc

-- Generic 'has'-stripping
-- Note: we don't currently strip automatically for various reasons.
#align has_zero      Zero
#align has_one       One
#align has_inv       Inv
#align has_add       Add
#align has_sub       Sub
#align has_mul       Mul
#align has_div       Div
#align has_neg       Neg
#align has_mod       Mod
#align has_pow       Pow
#align has_append    Append
#align has_pure      Pure
#align has_bind      Bind
#align has_seq       Seq
#align has_seq_left  SeqLeft
#align has_seq_right SeqRight
#align has_dvd       Dvd

-- Implementation detail
#align _sorry_placeholder_     _sorry_placeholder_



end Mathlib.Prelude
