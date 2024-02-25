/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Mathlib.Tactic.Continuity.Init

/-!
# Continuity

We define the `continuity` tactic using `aesop`. -/

attribute [aesop (rule_sets := [Continuous]) unfold norm] Function.comp

/--
The `continuity` attribute used to tag continuity statements for the `continuity` tactic. -/
macro "continuity" : attr =>
  `(attr|aesop safe apply (rule_sets := [$(Lean.mkIdent `Continuous):ident]))

/--
The tactic `continuity` solves goals of the form `Continuous f` by applying lemmas tagged with the
`continuity` user attribute. -/
macro "continuity" : tactic =>
  `(tactic| aesop (config := { terminal := true })
     (rule_sets := [$(Lean.mkIdent `Continuous):ident]))

/--
The tactic `continuity` solves goals of the form `Continuous f` by applying lemmas tagged with the
`continuity` user attribute. -/
macro "continuity?" : tactic =>
  `(tactic| aesop? (config := { terminal := true })
    (rule_sets := [$(Lean.mkIdent `Continuous):ident]))

-- Todo: implement `continuity!` and `continuity!?` and add configuration, original
-- syntax was (same for the missing `continuity` variants):
-- syntax (name := continuity) "continuity" (config)? : tactic
