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

The `have` vs `let` linter flags uses of
* `have` to introduce a hypothesis whose Type is not `Prop`;
* `let` to introduce a hypothesis whose Type is `Prop`.

TODO:
* `replace` is ignored always -- should `replace` have a `let`-like analogue?
* `haveI` may need to change to `let`/`letI`?
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

/--
* on input `have`, returns `some true`,
* on input `let`, returns `some false`,
* on all other inputs, returns `none`,
-/
def have_or_let? : Syntax → Option Bool
  | .node _ ``Lean.Parser.Tactic.tacticHave_ _ => true
  | .node _ `Lean.Parser.Tactic.tacticLet_ _ => false
  |_ => none

/-- `SyntaxNodeKind`s that imply a `have` but should be ignored anyway. -/
abbrev exclusions : HashSet SyntaxNodeKind := HashSet.empty
  |>.insert ``Lean.Parser.Tactic.replace
  |>.insert `Std.Tactic.classical!
  |>.insert `Mathlib.Tactic.Tauto.tauto

end haveLet

end Mathlib.Linter

namespace Mathlib.Linter.haveLet

/-- given a `LocalContext`, `MetavarContext` and an `Expr`ession `e`, `isProp_toFormat`
creates a `MetaM` context, and return a pair consisting of
* a `Bool`ean, answering the question of whether the Type of `e` is a `Prop` or not, and
* the pretty-printed `Format` of `e`.

Concretely, `isProp_toFormat` runs `inferType` in `CommandElabM`.
This is the kind of monadic lift that `nonPropHaves` uses to decide whether the Type of a `have`
is in `Prop` or not.

The output `Format` is just so that the linter displays a better message. -/
def isProp_toFormat (lc : LocalContext) (mctx : MetavarContext) (e : Expr) :
    CommandElabM (Bool × Format) := do
  let res ← liftCoreM do MetaM.run (ctx := { lctx := lc }) (s := { mctx := mctx }) <| do
    let typ ← inferType (← instantiateMVars e)
    return (typ.isProp, ← ppExpr e)
  return res.1

/-- returns
* the `have` syntax nodes whose corresponding hypothesis does not have Type `Prop`, and
* the `let` syntax nodes whose corresponding hypothesis has Type `Prop`.
It also returns a `Format`ted version of the corresponding `Type`/`Prop` and a `Bool`ean
that is `true` for `have` and `false` for `let`. -/
partial
def nonPropHaves : InfoTree → CommandElabM (Array (Syntax × Format × Bool))
  | .node i args => do
    let nargs := (← args.toArray.mapM nonPropHaves).flatten
    if let .ofTacticInfo i := i then
      let stx := i.stx
      if exclusions.contains stx.getKind then return #[] else
      if let some haveLet? := have_or_let? stx then
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
        return match haveLet?, ← isProp_toFormat lc mctx ld with
          | true, (true, _) => nargs
          | true, (false, fmt) => nargs.push (stx, fmt, true)
          | false, (false, _) => nargs
          | false, (true, fmt) => nargs.push (stx, fmt, false)
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
    for (s, fmt, haveLet?) in ← nonPropHaves t do
      if haveLet? then
        Linter.logLint linter.haveLet s m!"'{fmt}' is a Type and not a Prop. \
          Consider using 'let' instead of 'have'"
      else
        Linter.logLint linter.haveLet s m!"'{fmt}' is a Prop and not a Type. \
          Consider using 'have' instead of 'let'."

initialize addLinter haveLetLinter
