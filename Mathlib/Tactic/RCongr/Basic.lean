/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.RCongr.Attr
import Mathlib.Tactic.Positivity
import Mathlib.Data.Int.ModEq


-- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/hygiene.20question.3F/near/313556764
set_option hygiene false in
/-- A thin wrapper for `aesop`, which adds the `RCongr` rule set. -/
macro (name := rcongr) "rcongr" c:Aesop.tactic_clause*: tactic =>
  `(tactic|
    aesop $c* (rule_sets [rcongr, -default]) (simp_options := { enabled := false }))

-- A congruence rule with one argument gets success probability 90%; the only case when one wouldn't
-- want to apply it is when there is a relevant, complex hypothesis
attribute [aesop unsafe 90% (rule_sets [rcongr]) apply]
  -- Int.ModEq.add_right Int.ModEq.add_left
  -- Int.ModEq.sub_right Int.ModEq.sub_left
  -- Int.ModEq.mul_right Int.ModEq.mul_left
  Int.ModEq.neg Int.ModEq.pow
  Int.ModEq.add Int.ModEq.sub Int.ModEq.mul
  add_le_add sub_le_sub
  add_lt_add_left add_lt_add_right
  sub_lt_sub_left sub_lt_sub_right
  mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right
  --mul_le_mul_of_nonpos_left --mul_le_mul_of_nonpos_right
  mul_lt_mul_of_pos_left mul_lt_mul_of_pos_right
  div_le_div_of_le div_lt_div_of_lt
  pow_le_pow_of_le_left pow_lt_pow_of_lt_left

-- shouldn't need this any more, now that `add_right` is always prioritized over `add`, etc:
  Int.ModEq.refl
  le_refl

-- A congruence rule with two arguments gets success probability 50%
attribute [aesop unsafe 50% (rule_sets [rcongr]) apply]
  add_lt_add_of_le_of_lt add_lt_add_of_lt_of_le
  mul_lt_mul mul_lt_mul' mul_lt_mul''
  mul_le_mul

-- Not sure what probability to give this one.  Note that it creates exponential blowup; is there a
-- way to limit it to hypothesis-applying?
attribute [aesop unsafe 30% (rule_sets [rcongr]) forward]
  Int.ModEq.symm

-- Not sure what probability to give this one.  Note that they weaken hypothesis.
attribute [aesop unsafe 30% (rule_sets [rcongr]) forward]
  le_of_lt le_of_eq

def RCongr.Positivity : Lean.Elab.Tactic.TacticM Unit :=
Lean.Elab.Tactic.liftMetaTactic fun g => do Mathlib.Meta.Positivity.positivity g; pure []

attribute [aesop safe (rule_sets [rcongr]) tactic] RCongr.Positivity
