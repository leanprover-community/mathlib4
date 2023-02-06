/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Tactic.Basic


syntax (name := rsuffices) "rsuffices"
  (ppSpace Std.Tactic.RCases.rcasesPatMed)? (" : " term)? (" := " term,+)? : tactic

macro_rules
| `(tactic| rsuffices $[$pred]? $[: $foo]? $[:= $bar]?) =>
`(tactic | (obtain $[$pred]? $[: $foo]? $[:= $bar]?; rotate_left))
