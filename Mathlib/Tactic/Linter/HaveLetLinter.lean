/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Data.List.Basic

/-!
#  The `have` vs `let` linter

The `have` vs `let` linter flags uses of
* `have` to introduce a hypothesis whose Type is not `Prop`;
* `let` to introduce a hypothesis whose Type is `Prop`.

The option for this linter is a natural number, but really there are only 3 settings:
* `0` -- inactive;
* `1` -- active only on noisy declarations;
* `2` or more -- always active.

TODO:
* `haveI` may need to change to `let`/`letI`?
* `replace`, `classical!`, `classical`, `tauto` internally use `have`:
  should the linter act on them as well?
-/

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
register_option linter.haveLet : Nat := {
  defValue := 1
  descr := "enable the `have` vs `let` linter:\n\
            * 0 -- inactive;\n\
            * 1 -- active only on noisy declarations;\n\
            * 2 or more -- always active."
}

namespace haveLet

/--
* on input `have`, returns `some true`,
* on input `let`, returns `some false`,
* on all other inputs, returns `none`.
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

/-- a monadic version of `Lean.Elab.InfoTree.foldInfo`.
Used to infer types inside a `CommandElabM`. -/
def InfoTree.foldInfoM {α m} [Monad m] (f : ContextInfo → Info → α → m α) (init : α) :
    InfoTree → m α :=
  InfoTree.foldInfo (fun ctx i ma => do f ctx i (← ma)) (pure init)

/-- given a `LocalContext`, `MetavarContext` and an `Array` of `Expr`essions `es`,
`areProp_toFormat` creates a `MetaM` context, and returns an array of pairs consisting of
* a `Bool`ean, answering the question of whether the Type of `e` is a `Prop` or not, and
* the pretty-printed `Format` of `e`
for each `Expr`ession `e` in `es`.

Concretely, `areProp_toFormat` runs `inferType` in `CommandElabM`.
This is the kind of monadic lift that `nonPropHaves` uses to decide whether the Type of a `have`
is in `Prop` or not.

The output `Format` is just so that the linter displays a better message. -/
def areProp_toFormat (lc : LocalContext) (mctx : MetavarContext) (es : Array Expr) :
    CommandElabM (Array (Bool × Format)) := do
  let res ← liftCoreM do MetaM.run (ctx := { lctx := lc }) (s := { mctx := mctx }) <| do
    es.mapM fun e => do
      let typ ← inferType (← instantiateMVars e)
      return (typ.isProp, ← ppExpr e)
  return res.1

/-- returns
* the `have` syntax nodes whose corresponding hypothesis does not have Type `Prop`, and
* the `let` syntax nodes whose corresponding hypothesis has Type `Prop`.
It also returns a `Format`ted version of the corresponding `Type`/`Prop` and a `Bool`ean
that is `true` for `have` and `false` for `let`. -/
partial
def nonPropHaves : InfoTree → CommandElabM (Array (Syntax × Format × Bool)) :=
  InfoTree.foldInfoM (init := #[]) fun _ctx info args => return args ++ (← do
    let .ofTacticInfo i := info | return #[]
    let stx := i.stx
    let .original .. := stx.getHeadInfo | return #[]
    if exclusions.contains stx.getKind then return #[]
    let some haveLet? := have_or_let? stx | return #[]
    let mctx := i.mctxAfter
    let mvdecls := (i.goalsAfter.map (mctx.decls.find? ·)).reduceOption
    -- we extract the `MetavarDecl` with largest index after a `have`, since this one
    -- holds information about the metavariable where `have` introduces the new hypothesis.
    let largestIdx := mvdecls.toArray.qsort (·.index > ·.index)
    -- the relevant `LocalContext`
    let lc := (largestIdx.getD 0 default).lctx
    -- we also accumulate all `fvarId`s from all local contexts before the use of `have`
    -- so that we can then isolate the `fvarId`s that `have`/`let` introduce
    let oldMvdecls := (i.goalsBefore.map (mctx.decls.find? ·)).reduceOption
    let oldLctx := oldMvdecls.map (·.lctx)
    let oldDecls := (oldLctx.map (·.decls.toList.reduceOption)).join
    let oldFVars := oldDecls.map (·.fvarId)
    -- `newDecls` are the local declarations whose `FVarID` did not exist before the `have`
    -- effectively they are the declarations that we want to test for being in `Prop` or not.
    let newDecls := lc.decls.toList.reduceOption.filter (! oldFVars.contains ·.fvarId)
    -- now, we get the `MetaM` state up and running to find the types of each entry of `newDecls`
    let fmts ← areProp_toFormat lc mctx (newDecls.map (·.type)).toArray
    let (propFmts, typeFmts) := (fmts.zip (newDecls.map (·.userName)).toArray).partition (·.1.1)
    let propFmts := propFmts.map fun ((_, fmt), na) => (na, fmt)
    let typeFmts := typeFmts.map fun ((_, fmt), na) => (na, fmt)
    return if haveLet? then
      -- everything that is a Type triggers a warning on `have`
      (typeFmts.map fun (na, fmt) => (stx, f!"{na} : {fmt}", true))
    else
      -- only if everything is a Prop, we trigger a warning on `let`
      if typeFmts.size == 0 then
        (propFmts.map fun (na, fmt) => (stx, f!"{na} : {fmt}", false))
      else #[])

/-- The main implementation of the `have` vs `let` linter. -/
def haveLetLinter : Linter where run := withSetOptionIn fun _stx => do
  let gh := linter.haveLet.get (← getOptions)
  unless gh != 0 && (← getInfoState).enabled do
    return
  unless gh == 1 && (← MonadState.get).messages.unreported.isEmpty do
    let trees ← getInfoTrees
    for t in trees.toArray do
      for (s, fmt, haveLet?) in ← nonPropHaves t do
        -- Since the linter option is not in `Bool`, the standard `Linter.logLint` does not work.
        -- We emulate it with `logWarningAt`
        if haveLet? then
          logWarningAt s <| .tagged linter.haveLet.name
            m!"'{fmt}' is a Type and not a Prop. Consider using 'let' instead of 'have'.\n\
            You can disable this linter using `set_option linter.haveLet 0`"
        else
          logWarningAt s <| .tagged linter.haveLet.name
            m!"'{fmt}' is a Prop and not a Type. Consider using 'have' instead of 'let'.\n\
            You can disable this linter using `set_option linter.haveLet 0` {s}"

initialize addLinter haveLetLinter
