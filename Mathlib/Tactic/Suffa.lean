/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Meta.Tactic.TryThis

/-!
#  The `suffa` tactic

`suffa tac` runs the tactic sequence `tac` and returns a `Try this:` suggestion
of the form `suffices [target_after_tac] by tac; assumption`.

See the tactic docs for an example.
-/

namespace Mathlib.Tactic.Suffa

open Lean Parser.Tactic in
/-- combines two `Syntaxes` `t1 t2`, assuming that
* `t1` is a `tacticSeq` and
* `t2` is a single tactic to be added as a tail of `t1`.

Returns `t1` otherwise.
-/
def combine (t1 t2 : Syntax) : Syntax :=
  -- we check if `t1` is a `tacticSeq` and further split on whether it ends in `;` or not
  match t1 with
    | .node n1 ``tacticSeq #[.node n2 ``tacticSeq1Indented #[.node n3 `null args]] =>
      let nargs := (if args.size % 2 == 0 then args else args.push mkNullNode).push t2
      .node n1 ``tacticSeq #[.node n2 ``tacticSeq1Indented #[.node n3 `null nargs]]
    | _ => t1

open Lean Parser Elab Tactic

variable (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) in
/--
Run a tactic, optionally restoring the original state, and report the final target expression.
-/
def getTargetAfterTac (revert : Bool := true) : TacticM Expr := do
  let s ← saveState
  evalTactic tac
  let tgt ← getMainTarget
  if revert then restoreState s
  return tgt

open Meta.Tactic.TryThis in
/-- `suffa tac` runs the tactic sequence `tac` and returns a `Try this:` suggestion
of the form `suffices [target_after_tac] by tac; assumption`.

For example
```lean
example {m n : Nat} (h : m = n) : 0 + m = n := by
  suffa rewrite [Nat.zero_add]
  assumption
```
suggests the replacement
```lean
example {m n : Nat} (h : m = n) : 0 + m = n := by
  suffices m = n by
      rewrite [Nat.zero_add]
      assumption
  assumption
```
-/
elab "suffa " tac:tacticSeq : tactic => do
  let finalTgt ← getTargetAfterTac tac
  let stx ← Meta.Tactic.TryThis.delabToRefinableSyntax finalTgt
  let stxa : TSyntax ``tacticSeq := ⟨combine tac (← `(tactic| assumption))⟩
  let suffTac ← `(tacticSeq| suffices $stx by $stxa)
  let sug : Suggestion := { suggestion := suffTac }
  addSuggestion (← getRef) sug
  evalTactic tac
