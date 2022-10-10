/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean
import Mathlib.Tactic.Core

/-!
# `simp?` and `squeeze_scope` tactics

The `simp?` tactic is a simple wrapper around the simp with trace behavior implemented in core.

The `squeeze_scope` tactic allows aggregating multiple calls to `simp` coming from the same syntax
but in different branches of execution, such as in `cases x <;> simp`.
The reported `simp` call covers all simp lemmas used by this syntax.
-/
namespace Mathlib.Tactic
open Lean Elab Parser Tactic

/-- The common arguments of `simp?` and `simp?!`. -/
syntax simpTraceArgsRest := (config)? (discharger)? (&" only")? (simpArgs)? (ppSpace location)?

/--
`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.
-/
syntax (name := simpTrace) "simp?" "!"? simpTraceArgsRest : tactic

@[inheritDoc simpTrace]
macro tk:"simp?!" rest:simpTraceArgsRest : tactic => `(tactic| simp?%$tk ! $rest)

macro_rules
  | `(tactic| simp?%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?) =>
    `(tactic| set_option tactic.simp.trace true in
      simp%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?)
  | `(tactic| simp?%$tk ! $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?) =>
    `(tactic| set_option tactic.simp.trace true in
      simp!%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?)

/-- The common arguments of `simp_all?` and `simp_all?!`. -/
syntax simpAllTraceArgsRest := (config)? (discharger)? (&" only")? (dsimpArgs)?

@[inheritDoc simpTrace]
syntax (name := simpAllTrace) "simp_all?" "!"? simpAllTraceArgsRest : tactic

@[inheritDoc simpTrace]
macro tk:"simp_all?!" rest:simpAllTraceArgsRest : tactic => `(tactic| simp_all?%$tk ! $rest)

macro_rules
  | `(tactic| simp_all?%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?) =>
    `(tactic| set_option tactic.simp.trace true in
      simp_all%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?)
  | `(tactic| simp_all?%$tk ! $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?) =>
    `(tactic| set_option tactic.simp.trace true in
      simp_all!%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?)

/-- The common arguments of `dsimp?` and `dsimp?!`. -/
syntax dsimpTraceArgsRest := (config)? (&" only")? (dsimpArgs)? (ppSpace location)?

@[inheritDoc simpTrace]
syntax (name := dsimpTrace) "dsimp?" "!"? dsimpTraceArgsRest : tactic

@[inheritDoc simpTrace]
macro tk:"dsimp?!" rest:dsimpTraceArgsRest : tactic => `(tactic| dsimp?%$tk ! $rest)

macro_rules
  | `(tactic| dsimp?%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?) =>
    `(tactic| set_option tactic.simp.trace true in
      dsimp%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?)
  | `(tactic| dsimp?%$tk ! $(config)? $[only%$o]? $[[$args,*]]? $(loc)?) =>
    `(tactic| set_option tactic.simp.trace true in
      dsimp!%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?)

/--
`squeeze_scope a => tacs` is part of the implementation of `squeeze_scope`.
Inside `tacs`, invocations of `simp` wrapped with `squeeze_wrap a _ => ...` will contribute
to the accounting associated to scope `a`.
-/
local syntax (name := squeezeScopeIn) "squeeze_scope " ident " => " tacticSeq : tactic
/--
`squeeze_wrap a x => tac` is part of the implementation of `squeeze_scope`.
Here `tac` will be a `simp` or `dsimp` syntax, and `squeeze_wrap` will run the tactic
and contribute the generated `usedSimps` to the `squeezeScopes[a][x]` variable.
-/
local syntax (name := squeezeWrap) "squeeze_wrap " ident ident " => " tactic : tactic

open TSyntax.Compat in
/--
The `squeeze_scope` tactic allows aggregating multiple calls to `simp` coming from the same syntax
but in different branches of execution, such as in `cases x <;> simp`.
The reported `simp` call covers all simp lemmas used by this syntax.
```
@[simp] def bar (z : Nat) := 1 + z
@[simp] def baz (z : Nat) := 1 + z

@[simp] def foo : Nat → Nat → Nat
  | 0, z => bar z
  | _+1, z => baz z

example : foo x y = 1 + y := by
  cases x <;> simp? -- two printouts:
  -- "Try this: simp only [foo, bar]"
  -- "Try this: simp only [foo, baz]"

example : foo x y = 1 + y := by
  squeeze_scope
    cases x <;> simp -- only one printout: "Try this: simp only [foo, baz, bar]"
```
-/
macro (name := squeezeScope) "squeeze_scope " seq:tacticSeq : tactic => do
  let a ← withFreshMacroScope `(a)
  let seq ← seq.raw.rewriteBottomUpM fun stx =>
    match stx.getKind with
    | ``dsimp | ``simpAll | ``simp => do
      withFreshMacroScope `(tactic| squeeze_wrap $a x => $stx)
    | _ => pure stx
  `(tactic| squeeze_scope $a => $seq)

open Meta

/--
We implement `squeeze_scope` using a global variable that tracks all `squeeze_scope` invocations
in flight. It is a map `a ↦ (x ↦ (stx, simps))` where `a` is a unique identifier for
the `squeeze_scope` invocation which is shared with all contained simps, and `x` is a unique
identifier for a particular piece of simp syntax (which can be called multiple times).
Within that, `stx` is the simp syntax itself, and `simps` is the aggregated list of simps used
so far.
-/
initialize squeezeScopes : IO.Ref (NameMap (NameMap (Syntax × List Simp.UsedSimps))) ← IO.mkRef {}

elab_rules : tactic
  | `(tactic| squeeze_scope $a => $tac) => do
    let a := a.getId
    let old ← squeezeScopes.modifyGet fun map => (map.find? a, map.insert a {})
    let reset map := match old with | some old => map.insert a old | none => map.erase a
    let new ← try
      Elab.Tactic.evalTactic tac
      squeezeScopes.modifyGet fun map => (map.find? a, reset map)
    catch e =>
      squeezeScopes.modify reset
      throw e
    if let some new := new then
      for (_, stx, usedSimps) in new do
        let usedSimps := usedSimps.foldl (fun s usedSimps => usedSimps.fold .insert s) {}
        Elab.Tactic.traceSimpCall stx usedSimps

-- TODO: move to core
/-- Implementation of `dsimp`. -/
def dsimpLocation' (ctx : Simp.Context) (loc : Location) : TacticM Simp.UsedSimps := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget
  | Location.wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  /-- Implementation of `dsimp`. -/
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Simp.UsedSimps := do
    let mvarId ← getMainGoal
    let (result?, usedSimps) ←
      dsimpGoal mvarId ctx (simplifyTarget := simplifyTarget) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    pure usedSimps

elab_rules : tactic
  | `(tactic| squeeze_wrap $a $x => $tac) => do
    let stx := tac.raw
    let usedSimps ← match stx.getKind with
    | ``Parser.Tactic.simp => do
      let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
      dischargeWrapper.with fun discharge? =>
        simpLocation ctx discharge? (expandOptLocation stx[5])
    | ``Parser.Tactic.simpAll => do
      let { ctx, .. } ← mkSimpContext stx
        (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
      let (result?, usedSimps) ← simpAll (← getMainGoal) ctx
      match result? with
      | none => replaceMainGoal []
      | some mvarId => replaceMainGoal [mvarId]
      pure usedSimps
    | ``Parser.Tactic.dsimp => do
      let { ctx, .. } ← withMainContext <| mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
      dsimpLocation' ctx (expandOptLocation stx[5])
    | _ => Elab.throwUnsupportedSyntax
    let a := a.getId; let x := x.getId
    squeezeScopes.modify fun map => Id.run do
      let some map1 := map.find? a | return map
      let newSimps := match map1.find? x with
      | some (stx, oldSimps) => (stx, usedSimps :: oldSimps)
      | none => (stx, [usedSimps])
      map.insert a (map1.insert x newSimps)
