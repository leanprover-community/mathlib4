/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Tactic.Basic
import Qq

/-!
# `SynthesizeUsing`

This is a slight simplification of the `solve_aux` tactic in Lean3.
-/

open Lean Elab Tactic Meta Qq

/--
`synthesizeUsing type tac` synthesizes an element of type `type` using tactic `tac`.

The tactic `tac` is allowed to leave goals open, and these remain as metavariables in the
returned expression.
-/
-- In Lean3 this was called `solve_aux`,
-- and took a `TacticM α` and captured the produced value in `α`.
-- As this was barely used, we've simplified here.
def synthesizeUsing {u : Level} (type : Q(Sort u)) (tac : TacticM Unit) :
    MetaM (List MVarId × Q($type)) := do
  let m ← mkFreshExprMVar type
  let goals ← (Term.withoutErrToSorry <| run m.mvarId! tac).run'
  return (goals, ← instantiateMVars m)

/--
`synthesizeUsing type tac` synthesizes an element of type `type` using tactic `tac`.

The tactic must solve for all goals, in contrast to `synthesizeUsing`.
-/
def synthesizeUsing' {u : Level} (type : Q(Sort u)) (tac : TacticM Unit) : MetaM Q($type) := do
  let (goals, e) ← synthesizeUsing type tac
  -- Note: doesn't use `tac *> Tactic.done` since that just adds a message
  -- rather than raising an error.
  unless goals.isEmpty do
    throwError m!"synthesizeUsing': unsolved goals\n{goalsToMessageData goals}"
  return e

/--
`synthesizeUsing type tacticSyntax` synthesizes an element of type `type` by evaluating the
given tactic syntax.

Example:
```lean
let (gs, e) ← synthesizeUsingTactic ty (← `(tactic| congr!))
```

The tactic `tac` is allowed to leave goals open, and these remain as metavariables in the
returned expression.
-/
def synthesizeUsingTactic {u : Level} (type : Q(Sort u)) (tac : Syntax) :
    MetaM (List MVarId × Q($type)) := do
  synthesizeUsing type (do evalTactic tac)

/--
`synthesizeUsing' type tacticSyntax` synthesizes an element of type `type` by evaluating the
given tactic syntax.

Example:
```lean
let e ← synthesizeUsingTactic' ty (← `(tactic| norm_num))
```

The tactic must solve for all goals, in contrast to `synthesizeUsingTactic`.

If you need to insert expressions into a tactic proof, then you might use `synthesizeUsing'`
directly, since the `TacticM` monad has access to the `TermElabM` monad. For example, here
is a term elaborator that wraps the `simp at ...` tactic:
```
def simpTerm (e : Expr) : MetaM Expr := do
  let mvar ← Meta.mkFreshTypeMVar
  let e' ← synthesizeUsing' mvar
    (do evalTactic (← `(tactic| have h := $(← Term.exprToSyntax e); simp at h; exact h)))
  -- Note: `simp` does not always insert type hints, so to ensure that we get a term
  -- with the simplified type (as opposed to one that is merely defeq), we should add
  -- a type hint ourselves.
  Meta.mkExpectedTypeHint e' mvar

elab "simpTerm% " t:term : term => do simpTerm (← Term.elabTerm t none)
```
-/
def synthesizeUsingTactic' {u : Level} (type : Q(Sort u)) (tac : Syntax) : MetaM Q($type) := do
  synthesizeUsing' type (do evalTactic tac)
