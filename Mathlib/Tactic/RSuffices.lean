/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Tactic.Basic
/-!
# `rsuffices` tactic

The `rsuffices` tactic is an alternative version of `suffices`, that allows the usage
of any syntax that would be valid in an `obtain` block. This tactic just calls `obtain`
on the expression, and then `rotate_left`.
-/

/--
The `rsuffices` tactic is an alternative version of `suffices`, that allows the usage
of any syntax that would be valid in an `obtain` block. This tactic just calls `obtain`
on the expression, and then `rotate_left`.
-/
syntax (name := rsuffices) "rsuffices"
  (ppSpace Std.Tactic.RCases.rcasesPatMed)? (" : " term)? (" := " term,+)? : tactic

macro_rules
| `(tactic| rsuffices $[$pred]? $[: $foo]? $[:= $bar]?) =>
`(tactic | (obtain $[$pred]? $[: $foo]? $[:= $bar]?; rotate_left))

/--
The `rsufficesI` tactic is an instance-cache aware version of `rsuffices`; it resets the instance
cache on the resulting goals.
-/
syntax (name := rsufficesI) "rsufficesI"
  (ppSpace Std.Tactic.RCases.rcasesPatMed)? (" : " term)? (" := " term,+)? : tactic

macro_rules
| `(tactic| rsufficesI $[$pred]? $[: $foo]? $[:= $bar]?) =>
`(tactic | (rsuffices $[$pred]? $[: $foo]? $[:= $bar]?; resetI))

/-meta def rsufficesI (h : parse obtain_parse) : tactic unit :=
rsuffices h ; resetI-/
