/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Edward Ayers, Mario Carneiro
-/
import Lean
import Mathlib.Data.Array.Defs

/--
Uses `checkColGt` to prevent

```lean
have h
exact Nat
```

From being interpreted as
```lean
have h
  exact Nat
```
-/
def Lean.Parser.Term.haveIdLhs' : Parser :=
  optional (ppSpace >> ident >> many (ppSpace >>
    checkColGt "expected to be indented" >>
    letIdBinder)) >> optType

namespace Mathlib.Tactic

open Lean Elab.Tactic Meta

syntax "have" Parser.Term.haveIdLhs' : tactic
syntax "let " Parser.Term.haveIdLhs' : tactic
syntax "suffices" Parser.Term.haveIdLhs' : tactic

open Elab Term in
def haveLetCore (goal : MVarId) (name : Option Syntax) (bis : Array Syntax)
  (t : Option Syntax) (keepTerm : Bool) : TermElabM (MVarId × MVarId) :=
  let declFn := if keepTerm then MVarId.define else MVarId.assert
  goal.withContext do
    let n := if let some n := name then n.getId else `this
    let elabBinders k := if bis.isEmpty then k #[] else elabBinders bis k
    let (goal1, t, p) ← elabBinders fun es => do
      let t ← match t with
      | none => mkFreshTypeMVar
      | some t => Tactic.elabTerm.go t none
      let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
      pure (p.mvarId!, ← mkForallFVars es t, ← mkLambdaFVars es p)
    let (fvar, goal2) ← (← declFn goal n t p).intro1P
    if let some stx := name then
      goal2.withContext do
        Term.addTermInfo' (isBinder := true) stx (mkFVar fvar)
    pure (goal1, goal2)

elab_rules : tactic
| `(tactic| have $[$n:ident $bs*]? $[: $t:term]?) => do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n (bs.getD #[]) t false
  replaceMainGoal [goal1, goal2]

elab_rules : tactic
| `(tactic| suffices $[$n:ident $bs*]? $[: $t:term]?) => do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n (bs.getD #[]) t false
  replaceMainGoal [goal2, goal1]

elab_rules : tactic
| `(tactic| let $[$n:ident $bs*]? $[: $t:term]?) => withMainContext do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n (bs.getD #[]) t true
  replaceMainGoal [goal1, goal2]
