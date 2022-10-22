/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Mathlib.Mathport.Rename

namespace Mathlib.Prelude

#align classical.some          Classical.choose
#align classical.some_spec     Classical.choose_spec

#align Exists.some             Exists.choose
#align Exists.some_spec        Exists.choose_spec

#align has_coe Coe
#align has_coe.coe Coe.coe

#align has_coe_t CoeT
#align has_coe_t.coe CoeT.coe

#align has_coe_to_fun CoeFun
#align has_coe_to_fun.coe CoeFun.coe

#align has_coe_to_sort CoeSort
#align has_coe_to_sort.coe CoeSort.coe

#align has_beq                 BEq

-- This otherwise causes filenames to clash
#align category_theory.Kleisli CategoryTheory.KleisliCat

-- TODO: backport?
#align int.neg_succ_of_nat     Int.negSucc

-- Generic 'has'-stripping
-- Note: we don't currently strip automatically for various reasons.
#align has_pure      Pure
#align has_bind      Bind
#align has_seq       Seq
#align has_seq_left  SeqLeft
#align has_seq_right SeqRight
#align has_bracket   Bracket

-- Implementation detail
#align _sorry_placeholder_     _sorry_placeholder_

end Mathlib.Prelude
