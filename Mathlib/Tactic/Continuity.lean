/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Tactic.Continuity.Init

/-!
# Continuity

We define the `continuity` tactic using `aesop`. -/

public meta section

attribute [aesop (rule_sets := [Continuous]) unfold norm] Function.comp

/-- `@[continuity]` adds the tagged definition to the set of lemmas used by the `continuity` tactic.
Lemmas are used without backtracking: when the conclusion of this lemma matches the goal, the lemma
is applied unconditionally. Thus a lemma should preserve provability: if the goal can be proven,
then after applying a `@[continuity]` lemma to it, the generated subgoals should remain provable.
-/
macro "continuity" : attr =>
  `(attr|aesop safe apply (rule_sets := [$(Lean.mkIdent `Continuous):ident]))

/--
`continuity` solves goals of the form `Continuous f` by applying lemmas tagged with the attribute
`@[continuity]`. If the goal is not solved after attempting all rules, `continuity` fails.

`fun_prop` is a (usually more powerful) alternative to `continuity`.

This tactic is extensible. Tagging lemmas with the `@[continuity]` attribute can allow `continuity`
to solve more goals.

* `continuity?` reports the proof script found by `continuity`.
-/
macro "continuity" : tactic =>
  `(tactic| aesop (config := { terminal := true })
     (rule_sets := [$(Lean.mkIdent `Continuous):ident]))

@[tactic_alt tacticContinuity]
macro "continuity?" : tactic =>
  `(tactic| aesop? (config := { terminal := true })
    (rule_sets := [$(Lean.mkIdent `Continuous):ident]))

-- Todo: implement `continuity!` and `continuity!?` and add configuration, original
-- syntax was (same for the missing `continuity` variants):
-- syntax (name := continuity) "continuity" optConfig : tactic
