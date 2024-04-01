/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Lori (based on Measurability, by Miyahara Kō)
-/

import Mathlib.Tactic.Commutativity.Init
import Mathlib.Algebra.Group.Defs

/-!
# Measurability

We define the `commutativity` tactic using `aesop`. -/

open Lean.Parser.Tactic (config)

/--
The `commutativity` attribute used to tag commutativity statements for the `commutativity` tactic. -/
macro "commutativity" : attr =>
  `(attr|aesop safe apply (rule_sets := [$(Lean.mkIdent `Commute):ident]))

/--
The tactic `commutativity` solves goals of the form `Commute a b`
by applying lemmas tagged with the `commutativity` user attribute. -/
macro "commutativity" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true })
    (rule_sets := [$(Lean.mkIdent `Commute):ident]))

/--
The tactic `commutativity?` solves goals of the form `Commute a b`
by applying lemmas tagged with the `commutativity` user attribute,
and suggests a faster proof script that can be substituted
for the tactic call in case of success. -/
macro "commutativity?" (config)? : tactic =>
  `(tactic| aesop? (config := { terminal := true })
    (rule_sets := [$(Lean.mkIdent `Commute):ident]))

-- Todo: implement `commutativity!` and `commutativity!?` and add configuration,
-- original syntax was (same for the missing `commutativity` variants):
syntax (name := commutativity!) "commutativity!" (config)? : tactic
syntax (name := commutativity!?) "commutativity!?" (config)? : tactic
