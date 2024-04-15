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
-/

open Lean Elab Command

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

end haveLet

end Mathlib.Linter

namespace Mathlib.Linter.haveLet

/-- returns the `have` syntax whose corresponding hypothesis does not have Type `Prop` and
also a `Format`ted version of the corresponding Type. -/
partial
def nonPropHaves : InfoTree → CommandElabM (Array (Syntax × Format))
  | .node i args => do
    let nargs := (← args.toArray.mapM nonPropHaves).flatten
    if let .ofTacticInfo i := i then
      let stx := i.stx
      if stx.getKind == `Mathlib.Tactic.Tauto.tauto then return #[] else
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
        let res ← Command.liftCoreM do
          Meta.MetaM.run (ctx := { lctx := lc }) (s := { mctx := mctx }) <| do
            let typ ← Meta.inferType (← instantiateMVars ld)
            if ! typ.isProp then
              return nargs.push (stx, ← Meta.ppExpr ld)
            else return nargs
        return res.1
      else return nargs
    else return nargs
  | .context _ t => nonPropHaves t
  | .hole _ => return #[]

/-- Gets the value of the `linter.haveLet` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.haveLet o

/-- The main implementation of the terminal refine linter. -/
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
