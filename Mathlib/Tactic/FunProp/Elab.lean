/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public import Mathlib.Tactic.FunProp.Core

/-!
## `funProp` tactic syntax
-/

public meta section

namespace Mathlib
open Lean Meta Elab Tactic

namespace Meta.FunProp

open Lean.Parser.Tactic

/-- `fun_prop` config elaborator -/
declare_config_elab elabFunPropConfig FunProp.Config

/-- `fun_prop` solves a goal of the form `P f`, where `P` is a predicate and `f` is a function,
by decomposing `f` into a composition of elementary functions, and proving `P` on each of those
by matching against a set of `@[fun_prop]` lemmas.

If `fun_prop` fails to solve a goal with the error "No theorems found", you can solve this issue
by importing or adding new theorems tagged with the `@[fun_prop]` attribute. See the module
documentation for `Mathlib/Tactic/FunProp.lean` for a detailed explanation.

* `fun_prop (disch := tac)` uses `tac` to solve potential side goals. Setting this option is
  required to solve `ContinuousAt/On/Within` goals.
* `fun_prop [c, ...]` will unfold the constant(s) `c`, ... before decomposing `f`.
* `fun_prop (config := cfg)` sets advanced configuration options using `cfg : FunProp.Config`
  (see `FunProp.Config` for details).
  These options can be combined: `fun_prop (config := cfg) (disch := tac) [c]`

Examples:

```lean
example : Continuous (fun x : ℝ ↦ x * sin x) := by fun_prop
```

```lean
-- Specify a discharger to solve `ContinuousAt`/`Within`/`On` goals:
example (y : ℝ) (hy : y ≠ 0) : ContinuousAt (fun x : ℝ ↦ 1/x) y := by
  fun_prop (disch := assumption)

example (y : ℝ) (hy : y ≠ 0) : ContinuousAt (fun x => x * (Real.log x) ^ 2 - Real.exp x / x) y := by
  fun_prop (disch := aesop)
```

-/
syntax (name := funPropTacStx)
  "fun_prop" optConfig (discharger)? (" [" withoutPosition(ident,*,?) "]")? : tactic

private def emptyDischarge : Expr → MetaM (Option Expr) :=
  fun e =>
    withTraceNode `Meta.Tactic.fun_prop
      (fun _ => do pure s!"discharging: {← ppExpr e}") do
      pure none

private def assumptionDischarge : Expr → MetaM (Option Expr) :=
  fun e => do tacticToDischarge (← `(tactic| with_reducible assumption)) e

/-- Tactic to prove function properties -/
@[tactic funPropTacStx]
def funPropTac : Tactic
  | `(tactic| fun_prop $cfg:optConfig $[$d]? $[[$names,*]]?) => do

    let goal ← getMainGoal
    goal.withContext do
      let goalType ← goal.getType

      -- the whnf and telescope is here because the goal can be
      -- `∀ y, let f := fun x => x + y; Continuous fun x => x + f x`
      -- However it is still not complete solution. How should we deal with mix of let and forall?
      withReducible <| forallTelescopeReducing (← whnfR goalType) fun _ type => do
        unless (← getFunProp? type).isSome do
          let hint :=
            if let some n := type.getAppFn.constName?
            then s!" Consider marking `{n}` with `@[fun_prop]`."
            else ""
          throwError "`{← ppExpr type}` is not a `fun_prop` goal!{hint}"

      let cfg ← elabFunPropConfig cfg

      let disch ← show MetaM (Expr → MetaM (Option Expr)) from do
        match d with
        | none => pure assumptionDischarge
        | some d =>
          match d with
          | `(discharger| (discharger:=$tac)) =>
            pure <| tacticToDischarge (← `(tactic| first | with_reducible assumption | ($tac)))
          | _ => pure assumptionDischarge

      let namesToUnfold : Array Name :=
        match names with
        | none => #[]
        | some ns => ns.getElems.map (fun n => n.getId)

      let namesToUnfold := namesToUnfold.append defaultNamesToUnfold

      let ctx : Context :=
        { config := cfg,
          disch := disch
          constToUnfold := .ofArray namesToUnfold _}
      let env ← getEnv
      let s := {
        morTheorems        := morTheoremsExt.getState env
        transitionTheorems := transitionTheoremsExt.getState env }
      let (r?, s) ← funProp goalType ctx |>.run s
      if let some r := r? then
        goal.assign r.proof
      else
        let mut msg := s!"`fun_prop` was unable to prove `{← Meta.ppExpr goalType}`\n\n"

        msg := msg ++ "Issues:"
        msg := s.msgLog.foldl (init := msg) (fun msg m => msg ++ "\n  " ++ m)

        throwError msg

  | _ => throwUnsupportedSyntax



/-- Command that prints all function properties attached to a function.

For example
```
#print_fun_prop_theorems HAdd.hAdd
```
might print out
```
Continuous
  continuous_add, args: [4,5], priority: 1000
  continuous_const_add, args: [5], priority: 1000
  continuous_add_const, args [4], priority: 1000
  ...
Differentiable
  Differentiable.add, args: [4,5], priority: 1000
  Differentiable.add_const, args: [4], priority: 1000
  Differentiable.const_add, args: [5], priority: 1000
  ...
```

You can also see only theorems about a concrete function property
```
#print_fun_prop_theorems HAdd.hAdd Continuous
```
-/
elab "#print_fun_prop_theorems " funIdent:ident funProp:(ident)? : command => do

  let funName ← ensureNonAmbiguous funIdent (← resolveGlobalConst funIdent)
  let funProp? ← funProp.mapM (fun stx => do
    ensureNonAmbiguous stx (← resolveGlobalConst stx))

  let theorems := (functionTheoremsExt.getState (← getEnv)).theorems.getD funName {}

  let logTheorems (funProp : Name) (thms : Array FunctionTheorem) : Command.CommandElabM Unit := do
    let mut msg : MessageData := ""
    msg := msg ++ m!"{← Meta.ppOrigin (.decl funProp)}"
    for thm in thms do
      msg := msg ++ m!"\n  {← Meta.ppOrigin (.decl thm.thmOrigin.name)}, \
                 args: {thm.mainArgs}, form: {thm.form}"
      pure ()
    logInfo msg


  match funProp? with
  | none =>
    for (funProp,thms) in theorems do
      logTheorems funProp thms
  | some funProp =>
    logTheorems funProp (theorems.getD funProp #[])


end Meta.FunProp

end Mathlib
