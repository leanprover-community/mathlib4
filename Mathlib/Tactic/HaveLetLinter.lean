/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Std.Data.List.Basic

/-!
#  The `have` vs `let` linter

The `have` vs `let` linter flags uses of `have` to introduce a hypothesis whose Type is not `Prop`.

TODO:
* `replace` implies `have`: should it be ignored?
* `haveI` may need to change to `let/letI`?
* also do `let` vs `have`.
-/

open Lean Elab Command Meta

namespace Mathlib.Linter

/-- The `have` vs `let` linter emits a warning on `have`s introducing a hypothesis whose
Type is not `Prop`. -/
register_option linter.haveLet : Bool := {
  defValue := true
  descr := "enable the `have` vs `let` linter"
}

namespace haveLet

/-- find the `have` syntax. -/
partial
def isHave? : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.tacticHave_ _ => true
  |_ => false

/-- `SyntaxNodeKind`s that imply a `have` but should be ignored anyway. -/
abbrev exclusions : HashSet SyntaxNodeKind := HashSet.empty
  |>.insert ``Lean.Parser.Tactic.replace
  |>.insert `Std.Tactic.classical!
  |>.insert `Mathlib.Tactic.Tauto.tauto

end haveLet

end Mathlib.Linter

namespace Mathlib.Linter.haveLet

/-- given a `LocalContext`, `MetavarContext` and an `Expr`ession `e`, `isType_toFormat`
creates a `MetaM` context, checks whether `e` is a `Prop` and
* if `e` is not a `Prop`, then it returns `some <pp-formatted e>`;
* if `e` is a `Prop`, then it returns `none`.

This essentially runs `inferType` in `CommandElabM`, which is the lift that `nonPropHaves`
uses to decide whether the Type of a `have` is in `Prop` or not.

The output `Format` is just so that the linter displays a better message. -/
def isType_toFormat (lc : LocalContext) (mctx : MetavarContext) (e : Expr) :
    CommandElabM (Option Format) := do
  let res ← liftCoreM do MetaM.run (ctx := { lctx := lc }) (s := { mctx := mctx }) <| do
    let typ ← inferType (← instantiateMVars e)
    match typ.isProp with
      | false => return some (← ppExpr e)
      | true => return none
  return res.1

/-- returns the `have` syntax whose corresponding hypothesis does not have Type `Prop` and
also a `Format`ted version of the corresponding Type. -/
partial
def nonPropHaves : InfoTree → CommandElabM (Array (Syntax × Format))
  | .node i args => do
    let nargs := (← args.toArray.mapM nonPropHaves).flatten
    if let .ofTacticInfo i := i then
      let stx := i.stx
      if exclusions.contains stx.getKind then return #[] else
      if isHave? stx then
        let mctx := i.mctxAfter
        let mvdecls := (i.goalsAfter.map (mctx.decls.find? ·)).reduceOption
        let _ : Ord MetavarDecl := { compare := (compare ·.index ·.index) }
        -- we extract the `MetavarDecl` with largest index after a `have`, since this one
        -- holds information about the metavariable where `have` introduces the new hypothesis.
        let largestIdx := mvdecls.toArray.qsort (·.index > ·.index)
        -- the relevant `LocalContext`
        let lc := (largestIdx.getD 0 default).lctx
        -- and the last declaration introduced: the one that `have` created
        let ld := (lc.lastDecl.getD default).type
        -- now, we get the `MetaM` state up and running to find the type of `ld`
        return match ← isType_toFormat lc mctx ld with
          | none => nargs
          | some fmt => nargs.push (stx, fmt)
      else return nargs
    else return nargs
  | .context _ t => nonPropHaves t
  | .hole _ => return #[]

/-- Gets the value of the `linter.haveLet` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.haveLet o

/-- The main implementation of the `have` vs `let` linter. -/
def haveLetLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  for t in trees.toArray do
    for (s, fmt) in ← nonPropHaves t do
      Linter.logLint linter.haveLet s m!"'{fmt}' is a Type and not a Prop. \
        Consider using 'let' instead of 'have'"

initialize addLinter haveLetLinter
