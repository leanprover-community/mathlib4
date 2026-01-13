/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Aesop
public import Mathlib.Tactic.FunProp

/-!

# Tactics for the continuous functional calculus

At the moment, these tactics are just wrappers, but potentially they could be more sophisticated.
-/

public meta section

declare_aesop_rule_sets [CStarAlgebra]

/-- A tactic used to automatically discharge goals relating to the continuous functional calculus,
specifically whether the element satisfies the predicate. -/
syntax (name := cfcTac) "cfc_tac" : tactic
macro_rules
  | `(tactic| cfc_tac) => `(tactic|
         try (first |
              assumption |
              infer_instance |
              aesop (rule_sets := [$(Lean.mkIdent `CStarAlgebra):ident])))

-- we may want to try using `fun_prop` directly in the future.
/-- A tactic used to automatically discharge goals relating to the continuous functional calculus,
specifically concerning continuity of the functions involved. -/
syntax (name := cfcContTac) "cfc_cont_tac" : tactic
macro_rules
  | `(tactic| cfc_cont_tac) =>
    `(tactic| try (first
      | fun_prop (disch := aesop (config := {warnOnNonterminal := false})
                             (rule_sets := [$(Lean.mkIdent `CStarAlgebra):ident]))
      | assumption))

/-- A tactic used to automatically discharge goals relating to the non-unital continuous functional
calculus, specifically concerning whether `f 0 = 0`. -/
syntax (name := cfcZeroTac) "cfc_zero_tac" : tactic
macro_rules
  | `(tactic| cfc_zero_tac) =>
      `(tactic| try
          (first | aesop (rule_sets := [$(Lean.mkIdent `CStarAlgebra):ident]) | assumption))
