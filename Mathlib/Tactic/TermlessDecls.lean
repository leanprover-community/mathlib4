/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Edward Ayers
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
  optional (ident >> many (ppSpace >>
    checkColGt "expected to be indented" >>
    (simpleBinderWithoutType <|> bracketedBinder))) >> optType

/--
Uses `checkColGt` to prevent

```lean
let h
exact Nat
```

From being interpreted as
```lean
let h
  exact Nat
```
-/
def Lean.Parser.Term.letIdLhs' : Parser :=
  ident >> notFollowedBy (checkNoWsBefore "" >> "[")
    "space is required before instance '[...]' binders to distinguish them from array updates `let x[i] := e; ...`" >>
      many (ppSpace >> checkColGt "expected to be indented" >>
        (simpleBinderWithoutType <|> bracketedBinder)) >> optType

namespace Mathlib.Tactic

open Lean Elab.Tactic Meta

syntax "have " Parser.Term.haveIdLhs' : tactic
syntax "let "  Parser.Term.letIdLhs'  : tactic

private def addToContext (name : Name) (t : Expr) (keepTerm : Bool) : TacticM Unit :=
  let declFn := if keepTerm then define else assert
  liftMetaTactic fun mvarId => do
    let p ← mkFreshExprMVar (userName := name) t
    let mvarIdNew ← declFn mvarId name t p
    let (_, mvarIdNew) ← intro1P mvarIdNew
    return [p.mvarId!, mvarIdNew]

private def elabType (t : Option Syntax) : Elab.TermElabM Expr :=
  match t with
  | none   => mkFreshTypeMVar
  | some t => elabTerm t none

private def getBinderNames (b : Syntax) : Array Syntax :=
  match b.getKind with
  | `Lean.Parser.Term.simpleBinder   => b[0].getArgs
  | `Lean.Parser.Term.explicitBinder => b[1].getArgs
  | _                                => #[]

open Elab.Term in
private def getNameAndType (n t : Option Syntax) (bs : Option (Array Syntax)) :
    TacticM (Name × Expr) := do
  let name := match n with
    | none   => `this
    | some n => n.getId
  let e : Expr ← match bs with
    | none    => elabType t
    | some bs => elabBinders bs $ fun es => do mkForallFVars es (← elabType t)
  pure (name, e)

private def introBinders (bs : Array Syntax) : TacticM Unit := do
  for binderName in bs.map getBinderNames |>.flatten do
    evalTactic $ ← `(tactic|intro $binderName)

elab_rules : tactic
| `(tactic|have $[$n:ident $bs*]? $[: $t:term]?) => withMainContext do
    let (name, e) ← getNameAndType n t bs
    addToContext name e false
    introBinders $ bs.getD #[]

elab_rules : tactic
| `(tactic|let $n:ident $[: $t:term]?)      => withMainContext do
  addToContext n.getId (← elabType t) true
| `(tactic|let $n:ident $bs* $[: $t:term]?) => withMainContext do
    let (name, e) ← getNameAndType (some n) t (some bs)
    addToContext name e true
    introBinders bs
