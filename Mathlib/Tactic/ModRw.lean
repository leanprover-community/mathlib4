/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Int.ModEq

declare_aesop_rule_sets [mod_rules]

-- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/hygiene.20question.3F/near/313556764
set_option hygiene false in
/-- A thin wrapper for `aesop`, which adds the `ModEq` rule set. -/
macro (name := mod_rw) "mod_rw" c:Aesop.tactic_clause*: tactic =>
  `(tactic|
    aesop? $c* (rule_sets [mod_rules, -default, -builtin]) (simp_options := { enabled := false }))

-- A congruence rule with one argument gets success probability 90%; the only case when one wouldn't
-- want to apply it is when there is a relevant, complex hypothesis
attribute [aesop unsafe 90% (rule_sets [mod_rules]) apply]
  Int.ModEq.add_right Int.ModEq.add_left
  Int.ModEq.sub_right Int.ModEq.sub_left
  Int.ModEq.mul_right Int.ModEq.mul_left
  Int.ModEq.neg Int.ModEq.pow

-- shouldn't need this any more, now that `add_right` is always prioritized over `add`, etc:
-- Int.ModEq.refl

attribute [aesop unsafe 75% (tactic (uses_branch_state := false)) (rule_sets [mod_rules])]
  Aesop.BuiltinRules.applyHyps

-- A congruence rule with two arguments gets success probability 50%
attribute [aesop unsafe 50% (rule_sets [mod_rules]) apply]
  Int.ModEq.add Int.ModEq.sub Int.ModEq.mul

-- Not sure what probability to give this one.  Note that it creates exponential blowup; is there a
-- way to limit it to hypothesis-applying?
attribute [aesop unsafe 30% (rule_sets [mod_rules]) apply]
  Int.ModEq.symm
