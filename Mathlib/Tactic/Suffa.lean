/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Meta.Tactic.TryThis
import Mathlib.Tactic.Convert

/-!
#  The `suffa` tactic

`suffa tac` runs the tactic sequence `tac` and returns a `Try this:` suggestion
of the form `suffices [target_after_tac] by tac; exact this`.

There is also a `!`-flag, where `suffa! tac` tries `convert this` instead of `exact this`.

See the tactic docs for an example.

##  TODO
* Better support for `fvar`s.
* Allow `suff ... at ...`?
* Allow `suff_all ...`?
* If the last tactic in the sequence is `simp`, use `simpa` in the suggestion?
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
of the form `suffices [target_after_tac] by tac; exact this`.

The form `suffa! tac` replaces the conclusion with `convert this`.

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
      exact this
  assumption
```
-/
elab "suffa " tk:"!"? tac:tacticSeq : tactic => do
  let finalTgt ← getTargetAfterTac tac
  let stx ← Meta.Tactic.TryThis.delabToRefinableSyntax finalTgt
  let ithis : Syntax.Term := ⟨mkIdent `this⟩
  let conclusion ← match tk with
                    | none   => `(tactic| exact $ithis)
                    | some _ => `(tactic| convert $ithis:term)
  let stxa : TSyntax ``tacticSeq := ⟨combine tac conclusion⟩
  let suffTac ← `(tacticSeq| suffices $stx by $stxa)
  addSuggestion (← getRef) { suggestion := suffTac }
  evalTactic tac

macro "suffa!" tac:tacticSeq : tactic => `(tactic| suffa ! $tac)
