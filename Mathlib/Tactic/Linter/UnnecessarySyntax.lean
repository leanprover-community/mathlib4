/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Linter.Util
import Lean.Elab.Command
import Batteries.Tactic.Lint.Simp

/-!
A configurable linter that flags `Syntax` uses that are unnecessary.
-/

open Lean Parser Elab Command

/-- todo: this only removes a `simpNF` from the *first* `nolint ... simpNF ...` in `@[...]`.
It completely ignores
* multiple `simpNF`;
* every `nolint` except for the first.
-/
def getNoLintSimp (stx : Syntax) : CommandElabM (Option Syntax) := do
  -- check if there is a `nolint` and do nothing it there isn't one.
  match stx.find? (·.isOfKind ``Std.Tactic.Lint.nolint) with
    | none => return none
    | some nl =>
      -- check if there is a `simpNF` in the `nolint` and do nothing it there isn't one.
      match nl.find? (· == mkIdent `simpNF) with
        | none => return default
        | some snf =>
          -- here there is a `nolint ... simpNF ...`.
          -- `noLintNumber` is the number of `nolint`s
          let noLintNumber := match nl.getArgs with
            | #[_, .node _ _ nolinted] =>  -- the first `_` is ``atom `nolint``
              nolinted.size
            | _ => 0
          if noLintNumber == 1
          then return nl
          else return snf

/-- `unnecessarySyntax` linter takes as input a `CommandElabM` function `f` assigning to
a command `cmd` syntax an array of triples `(newCmd, positionStx, message)` consisting of
* the syntax `newCmd` of a command;
* the syntax `positionStx` effectively encoding a position for message reporting;
* a `MessageData` `message`.

For each command `cmd`, the linter then computes the array `f cmd`, and, for each entry
`(newCmd, positionStx, message)` of `f cmd` it
* elaborates `newCmd` inside a fresh namespace;
* if `newCmd` reports an error, it continues;
* if `newCmd` reports no error, then it flags `message` warning at `positionStx`.
-/
register_option linter.unnecessarySyntax : Bool := {
  defValue := true
  descr := "enable the unnecessarySyntax linter"
}

@[inherit_doc linter.unnecessarySyntax]
def getUnnecessarySyntax (o : Options) : Bool := Linter.getLinterValue linter.unnecessarySyntax o

@[inherit_doc linter.unnecessarySyntax]
def unnecessarySyntax (f : Syntax → CommandElabM (Array (Syntax × Syntax × MessageData))) :
    Linter where run cmd := do
  unless getUnnecessarySyntax (← getOptions) do
    return
  let news ← f cmd
  if let some nls ← getNoLintSimp cmd then

    if news.isEmpty then
      let tailPos := nls.getHeadInfo.getTailPos?
      let fm ← getFileMap
      let pos := fm.toPosition (tailPos.getD default)
      Linter.logLint linter.unnecessarySyntax nls m!"`{nls}` can be removed {pos}"

/-- Runs `k`.  If it is successful, return the output, otherwise return the error. -/
def runOrMessage {α : Type} (k : MetaM α) :
  MetaM (α ⊕ MessageData) := do
  try
    return Sum.inl (← k)
  catch e =>
    return Sum.inr e.toMessageData

open Std Meta Tactic Lint in
/-- Minor adaptations with respect to the declaration from `Batteries`. -/
def simpNF (declName : Name) : MetaM (Option MessageData) := do
    unless ← isSimpTheorem declName do return none
    let ctx := { ← Simp.Context.mkDefault with config.decide := false }
    let ms := ← checkAllSimpTheoremInfos (← getConstInfo declName).type
      fun {lhs, rhs, isConditional, ..} => do
        let isRfl ← isRflTheorem declName
        match ← runOrMessage <|
            if !isRfl then
              simp lhs ctx
            else do
              let (e, s) ← dsimp lhs ctx
              return (Simp.Result.mk e .none .true, s) with
          | .inl ({ expr := lhs', proof? := prf1, .. }, prf1Stats) =>
            if prf1Stats.usedTheorems.contains (.decl declName) then return default
            match ← runOrMessage <|
                if !isRfl then
                  simp rhs ctx (stats := prf1Stats)
                else do
                  let (e, s) ← dsimp rhs ctx (stats := prf1Stats)
                  return (Simp.Result.mk e .none .true, s) with
              | .inl ({ expr := rhs', .. }, stats) =>
                let lhs'EqRhs' ← isSimpEq lhs' rhs' (whnfFirst := false)
                let lhsInNF ← isSimpEq lhs' lhs
                let simpName := if !isRfl then "simp" else "dsimp"
                if lhs'EqRhs' then
                  if prf1.isNone then
                    return none -- TODO: FP rewriting foo.eq_2 using `simp only [foo]`
                  return m!"{simpName} can prove this:\n\
                            by {← formatLemmas stats.usedTheorems simpName}\n\
                            One of the lemmas above could be a duplicate.\n\
                            If that's not the case try reordering lemmas or adding @[priority].\n"
                else if ¬ lhsInNF then
                  return m!"Left-hand side simplifies from\n  \
                            {lhs}\n\
                            to\n  \
                            {lhs'}\n\
                            using  \n\
                            {← formatLemmas prf1Stats.usedTheorems simpName}\n\
                            Try to change the left-hand side to the simplified term!\n"
                else if !isConditional && lhs == lhs' then
                  return m!"Left-hand side does not simplify, when using the simp lemma on itself.\n\
                            This usually means that it will never apply.\n"
                else
                  return none
              | .inr m2 =>
                return some ("simplify fails on right-hand side:" ++ m2)
          | .inr m1 =>
            return some ("simplify fails on left-hand side:" ++ m1)
    return ms

/-- the actual function used by the linter -/
abbrev snf (cmd : Syntax) : CommandElabM (Array (Syntax × Syntax × MessageData)) := do
  match ← getNoLintSimp cmd with
    | none => return #[]
    | some nl =>
      let (ms, _) ← liftCoreM do Meta.MetaM.run do
        if let some id := cmd.find? (·.isOfKind ``declId) then
          let nm ← realizeGlobalConstNoOverloadWithInfo id[0]
          let ms ← simpNF nm
          match ms with
            | (some msg) =>
              return #[(cmd, nl, msg)]
            | _ => return #[]
        else return #[]
      return ms

initialize addLinter (unnecessarySyntax snf)
