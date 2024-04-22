/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Meta.Tactic.TryThis
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Says

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
elab (name := suffaTac) "suffa " tk:"!"? tac:tacticSeq : tactic => do
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

@[inherit_doc suffaTac]
macro "suffa!" tac:tacticSeq : tactic => `(tactic| suffa ! $tac)

variable (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) in

def repMsgs : CoreM (Array String) := do
  let msgs := (← get).messages.msgs.toArray
  msgs.mapM (·.data.toString)

def cacheTacGoal (tacs : TSyntax `Lean.Parser.Tactic.tacticSeq) : IO Unit := do
  IO.println f!"{tacs}"
--#check Meta.Tactic.TryThis.TryThisInfo
set_option pp.analyze true in
elab "cache " tacs:tacticSeq " with " _tacs2:tacticSeq : tactic => do
  let pat := "@@@"
  let sep := "\n" ++ pat ++ "\n"
  let sepsep := "\n" ++ pat ++ pat ++ "\n"
  let fil : System.FilePath := "NewCache.txt"
  let tgt0 ← getMainTarget
  logInfo tacs
  let tacString := (← repMsgs).back
  dbg_trace tacString
--  let _ ← match Says.parseAsTacticSeq (← getEnv) (s!"simp  ") with
--            | .ok m => logInfo m
--            | _ => logInfo "none"
--evalTacticCapturingMessages
  evalTactic tacs
  let tgt1 ← getMainTarget
--  let pt := Std.MessageData.pretty m!"{tacs}"
  let toStore ← MessageData.toString m!"{← Meta.ppExpr tgt0}{sep}{tacString}{sep}{← Meta.ppExpr tgt1}"
--  logInfo m!"{fil} exists? {← fil.pathExists}"
--  let fil : System.FilePath := "NewCache.txt"
  let contents ←  if ← fil.pathExists then IO.FS.readFile fil else pure ""
  let found := contents.splitOn sepsep

  if found.contains toStore then
    logInfo m!"cache entry already found in '{fil}'"
  else
    logInfo m!"cache entry not found: updating '{fil}':\n{toStore}"
    IO.FS.writeFile fil (contents ++ toStore ++ sepsep)
  let oldEntry := (found.get? (found.length - 3)).getD default
  let oldTac := oldEntry.splitOn sep
  dbg_trace "old: '{oldTac[1]!}'"
--  let mid := mkIdent oldTac[1]!
  let tc := oldTac[1]!
  let pat := Says.parseAsTacticSeq (← getEnv) tc
  match pat with
  | .ok stx => evalTactic stx
  | .error err => throwError m!"Failed to parse tactic output: {tc}\n{err}"
  --let mid : TSyntax `tacticSeq ← `(tacticSeq| $tc)
  --evalTactic mid

--  for t in toStore.splitOn sep do
--    (logInfo m!"{t}" : TacticM Unit)

#check quote
--#check String.find
example (h : False) {n : Nat} : n + 0 = n + 1 := by
  cache
    simp
    skip;
  with
    simp only [Nat.add_zero]
    skip;
  cases h
