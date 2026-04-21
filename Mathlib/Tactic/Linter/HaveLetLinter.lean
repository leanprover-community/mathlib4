/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Command
public meta import Lean.Server.InfoUtils

/-!
# The `have` vs `let` linter

The `have` vs `let` linter flags uses of `have` to introduce a hypothesis whose Type is not `Prop`.

The option for this linter is a natural number, but really there are only 3 settings:
* `0` -- inactive;
* `1` -- active only on noisy declarations;
* `2` or more -- always active.

TODO:
* Also lint `let` vs `have`.
* `haveI` may need to change to `let/letI`?
* `replace`, `classical!`, `classical`, `tauto` internally use `have`:
  should the linter act on them as well?
-/
set_option backward.defeqAttrib.useBackward true

meta section

open Lean Elab Command Meta

namespace Mathlib.Linter

/-- The `have` vs `let` linter emits a warning on `have`s introducing a hypothesis whose
Type is not `Prop`.
There are three settings:
* `0` -- inactive;
* `1` -- active only on noisy declarations;
* `2` or more -- always active.

The default value is `1`.
-/
public register_option linter.haveLet : Nat := {
  defValue := 0
  descr := "enable the `have` vs `let` linter:\n\
            * 0 -- inactive;\n\
            * 1 -- active only on noisy declarations;\n\
            * 2 or more -- always active."
}

namespace haveLet

/-- find the `have` syntax. -/
def isHave? : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.tacticHave__ _ => true
  | _ => false

end haveLet

end Mathlib.Linter

namespace Mathlib.Linter.haveLet

/-- a monadic version of `Lean.Elab.InfoTree.foldInfo`.
Used to infer types inside a `CommandElabM`. -/
def InfoTree.foldInfoM {α m} [Monad m] (f : ContextInfo → Info → α → m α) (init : α) :
    InfoTree → m α :=
  InfoTree.foldInfo (fun ctx i ma => do f ctx i (← ma)) (pure init)

/-- given a `ContextInfo`, a `LocalContext` and an `Array` of `Expr`essions `es` with a `Name`,
`toFormat_propTypes` creates a `MetaM` context, and returns an array of
the pretty-printed `Format` of `e`, together with the (unchanged) name
for each `Expr`ession `e` in `es` whose type is a `Prop`.

Concretely, `toFormat_propTypes` runs `inferType` in `CommandElabM`.
This is the kind of monadic lift that `nonPropHaves` uses to decide whether the Type of a `have`
is in `Prop` or not.
The output `Format` is just so that the linter displays a better message. -/
def toFormat_propTypes (ctx : ContextInfo) (lc : LocalContext) (es : Array (Expr × Name)) :
    CommandElabM (Array (Format × Name)) := do
  ctx.runMetaM lc do
    es.filterMapM fun (e, name) ↦ do
      let typ ← inferType (← instantiateMVars e)
      if typ.isProp then return none else return (← ppExpr e, name)

/-- returns the `have` syntax whose corresponding hypothesis does not have Type `Prop` and
also a `Format`ted version of the corresponding Type. -/
public partial
def nonPropHaves : InfoTree → CommandElabM (Array (Syntax × Format)) :=
  InfoTree.foldInfoM (init := #[]) fun ctx info args => return args ++ (← do
    let .ofTacticInfo i := info | return #[]
    let stx := i.stx
    let .original .. := stx.getHeadInfo | return #[]
    unless isHave? stx do return #[]
    let mctx := i.mctxAfter
    let mvdecls := i.goalsAfter.filterMap (mctx.decls.find? ·)
    -- We extract the `MetavarDecl` with largest index after a `have`, since this one
    -- holds information about the metavariable where `have` introduces the new hypothesis,
    -- and determine the relevant `LocalContext`.
    let lc := mvdecls.toArray.getMax? (·.index < ·.index) |>.getD default |>.lctx
    -- we also accumulate all `fvarId`s from all local contexts before the use of `have`
    -- so that we can then isolate the `fvarId`s that are created by `have`
    let oldMvdecls := i.goalsBefore.filterMap (mctx.decls.find? ·)
    let oldFVars := (oldMvdecls.map (·.lctx.decls.toList.reduceOption)).flatten.map (·.fvarId)
    -- `newDecls` are the local declarations whose `FVarID` did not exist before the `have`.
    -- Effectively they are the declarations that we want to test for being in `Prop` or not.
    let newDecls := lc.decls.toList.reduceOption.filter (! oldFVars.contains ·.fvarId)
    -- Now, we get the `MetaM` state up and running to find the types of each entry of `newDecls`.
    -- For each entry which is a `Type`, we print a warning on `have`.
    let fmts ← toFormat_propTypes ctx lc (newDecls.map (fun e ↦ (e.type, e.userName))).toArray
    return fmts.map fun (fmt, na) ↦ (stx, f!"{na} : {fmt}"))

/-- The main implementation of the `have` vs `let` linter. -/
def haveLetLinter : Linter where run := withSetOptionIn fun _stx => do
  let gh := linter.haveLet.get (← getOptions)
  unless gh != 0 && (← getInfoState).enabled do
    return
  unless gh == 1 && (← MonadState.get).messages.unreported.isEmpty do
    let trees ← getInfoTrees
    for t in trees do
      for (s, fmt) in ← nonPropHaves t do
        logLint0Disable linter.haveLet s
          m!"'{fmt}' is a Type and not a Prop. Consider using 'let' instead of 'have'."

initialize addLinter haveLetLinter

end haveLet

end Mathlib.Linter
