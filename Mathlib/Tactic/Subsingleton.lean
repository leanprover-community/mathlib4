/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Std.Logic
import Mathlib.Logic.Basic

/-!
# `subsingleton` tactic

The `subsingleton` tactic closes `Eq` or `HEq` goals using an argument
that the types involved are subsingletons.
To first approximation, it does `apply Subsingleton.elim` but it also will try `proof_irrel_heq`,
and it is careful not to accidentally specialize `Sort _` to `Prop.
-/

open Lean Meta

/--
Closes the goal `g` whose target is an `Eq` or `HEq` by appealing to the fact that the types
are subsingletons.
Fails if it cannot find a way to do this.

Has support for showing `BEq` instances are equal if they have `LawfulBEq` instances.
-/
def Lean.MVarId.subsingleton (g : MVarId) : MetaM Unit := commitIfNoEx do
  let g ← g.heqOfEq
  g.withContext do
    let tgt ← whnfR (← g.getType)
    if let some (ty, x, y) := tgt.eq? then
      -- Proof irrelevance. This is not necessary since `rfl` suffices,
      -- but propositions are subsingletons so we may as well.
      if ← Meta.isProp ty then
        g.assign <| mkApp3 (.const ``proof_irrel []) ty x y
        return
      -- Try `Subsingleton.elim`
      let u ← getLevel ty
      let instTy := Expr.app (.const ``Subsingleton [u]) ty
      try
        -- Synthesize a subsingleton instance. The new metacontext depth ensures that universe
        -- level metavariables are not specialized.
        let inst ← withNewMCtxDepth <| Meta.synthInstance instTy
        g.assign <| mkApp4 (.const ``Subsingleton.elim [u]) ty inst x y
        return
      catch _ => pure ()
      -- Try `lawful_beq_subsingleton`
      let ty' ← whnfR ty
      if ty'.isAppOfArity ``BEq 1 then
        let α := ty'.appArg!
        try
          let some u' := u.dec | failure
          let xInst ← withNewMCtxDepth <| Meta.synthInstance <| mkApp2 (.const ``LawfulBEq [u']) α x
          let yInst ← withNewMCtxDepth <| Meta.synthInstance <| mkApp2 (.const ``LawfulBEq [u']) α y
          g.assign <| mkApp5 (.const ``lawful_beq_subsingleton [u']) α x y xInst yInst
          return
        catch _ => pure ()
      throwError "\
        tactic 'subsingleton' could not prove equality since it could not synthesize\
          {indentD instTy}"
    else if let some (xTy, x, yTy, y) := tgt.heq? then
      -- The HEq version of proof irrelevance.
      if ← (Meta.isProp xTy <&&> Meta.isProp yTy) then
        g.assign <| mkApp4 (.const ``proof_irrel_heq []) xTy yTy x y
        return
      throwError "tactic 'subsingleton' could not prove heterogenous equality"
    throwError "tactic 'subsingleton' failed, goal is neither an equality nor heterogenous equality"

/--
Tries to apply `Subsingleton.helim` to the goal, returning the new equality goal.
-/
def Lean.MVarId.subsingletonHElim (g : MVarId) : MetaM MVarId := do
  let tgt ← whnfR (← g.getType)
  let some (xTy, x, yTy, y) := tgt.heq? | failure
  let u ← getLevel xTy
  let instXTy := Expr.app (.const ``Subsingleton [u]) xTy
  let instYTy := Expr.app (.const ``Subsingleton [u]) yTy
  let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq xTy yTy) (← g.getTag)
  try
    let inst ← withNewMCtxDepth <| Meta.synthInstance instXTy
    g.assign <| mkApp6 (.const ``Subsingleton.helim [u]) xTy yTy inst g' x y
    return g'.mvarId!
  catch _ => pure ()
  try
    let inst ← withNewMCtxDepth <| Meta.synthInstance instYTy
    let pf ← mkHEqSymm <|
      mkApp6 (.const ``Subsingleton.helim [u]) yTy xTy inst (← mkEqSymm g') y x
    g.assign pf
    return g'.mvarId!
  catch _ =>
    throwError "\
      tactic 'subsingleton' could not synthesize either{indentD instXTy}\nor{indentD instYTy}\n\
      to make progress on `HEq` goal using `Subsingleton.helim`"

namespace Mathlib.Tactic

/--
The `subsingleton` tactic tries to prove a goal of the form `x = y` or `HEq x y`
using the fact that the types involved are *subsingletons*
(a type with exactly zero or one terms).
To a first approximation, it does `apply Subsingleton.elim`.
As a nicety, `subsingleton` first runs the `intros` tactic.

- If the goal is an equality, it either closes the goal or fails.
- If the goal is a `HEq`, it can try applying `Subsingleton.helim`
  to convert a `@HEq α x β y` goal into an `α = β` goal.
- `subsingleton [inst1, inst2, ...]` can be used to add additional `Subsingleton` instances
  to the local context. This can be more flexible than
  `have := inst1; have := inst2; ...; subsingleton` since the tactic does not require that
  all placeholders be solved for.

Techniques the `subsingleton` tactic can apply:
- proof irrelevance
- heterogenous proof irrelevance (via `proof_irrel_heq`)
- using `Subsingleton` (via `Subsingleton.elim`)
- proving `BEq` instances are equal if they are both lawful (via `lawful_beq_subsingleton`)
- turning a `HEq` of subsingleton types into an equality of types (via `Subsingleton.helim`)

### Properties

The tactic is careful not to accidentally specialize `Sort _` to `Prop`,
avoiding the following surprising behavior of `apply Subsingleton.elim`:
```lean
example (α : Sort _) (x y : α) : x = y := by apply Subsingleton.elim
```
The reason this `example` goes through is that
it applies the `∀ (p : Prop), Subsingleton p` instance,
specializing the universe level metavariable in `Sort _` to `0`.
-/
syntax (name := subsingletonStx) "subsingleton" (ppSpace "[" term,* "]")? : tactic

open Elab Tactic

/--
Elaborates the terms like how `Lean.Elab.Tactic.addSimpTheorem` does,
abstracting their metavariables.
Makes sure they're Subsingleton instances, and adds them to the local context.
-/
def addSubsingletonInsts
    (instTerms? : Option (Array Term)) (g : MVarId) : TermElabM MVarId := do
  if let some instTerms := instTerms? then
    g.withContext <| go instTerms.toList #[] #[]
  else
    return g
where
  /-- Main loop for `addSubsingletonInsts`. -/
  go (instTerms : List Term) (fvars : Array Expr) (insts : Array Expr) : TermElabM MVarId := do
    match instTerms with
    | [] =>
      withNewLocalInstances fvars 0 do
        let g' ← mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign <| mkAppN (← mkLambdaFVars fvars g') insts
        return g'.mvarId!
    | instTerm :: instTerms =>
      let inst ← withNewMCtxDepth <| Term.withoutModifyingElabMetaStateWithInfo do
        withRef instTerm <| Term.withoutErrToSorry do
          let e ← Term.elabTerm instTerm none
          Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
          let e ← instantiateMVars e
          unless (← isClass? (← inferType e)).isSome do
            throwError "Not an instance. Term has type{indentD <| ← inferType e}"
          if e.hasMVar then
            -- Level metavariables are OK.
            -- But if there are *new* level metavariables then the instance will never apply.
            -- TODO(kmill): Should the tactic have a list of universe level metavariables it's
            -- allowed to assign to? (Can depth be used for this?)
            let r ← abstractMVars e
            unless r.paramNames.isEmpty do
              -- Todo: expose the universe level metavariables?
              throwError "\
                Expression contains new universe level metavariables in\
                {indentD e}\n\
                This means 'subsingleton' will not ever apply this instance."
            -- Change all instance arguments corresponding to the mvars to be inst implicit.
            let e' ← forallBoundedTelescope (← inferType r.expr) r.numMVars fun args _ => do
              let newBIs ← args.filterMapM fun arg => do
                if (← isClass? (← inferType arg)).isSome then
                  return some (arg.fvarId!, .instImplicit)
                else
                  return none
              withNewBinderInfos newBIs do
                mkLambdaFVars args (r.expr.beta args)
            pure e'
          else
            pure e
      withLocalDecl `inst .instImplicit (← inferType inst) fun fvar => do
        go instTerms (fvars.push fvar) (insts.push inst)

elab_rules : tactic
  | `(tactic| subsingleton $[[$[$instTerms?],*]]?) => withMainContext do
  let recover := (← read).recover
  let g ← getMainGoal
  let g ← addSubsingletonInsts instTerms? g
  replaceMainGoal [g]
  Elab.Tactic.liftMetaTactic1 fun g => do
    let (fvars, g) ← g.intros
    try
      g.subsingleton
      return none
    catch e =>
      if (← whnfR (← g.getType)).isHEq then
        g.subsingletonHElim
      else
        -- Try `refl` when all else fails, to give a hint to the user
        if recover then
          try
            g.refl <|> g.hrefl
            let tac ← if !fvars.isEmpty then `(tactic| (intros; rfl)) else `(tactic| rfl)
            Meta.Tactic.TryThis.addSuggestion (← getRef) tac (origSpan? := ← getRef)
            return none
          catch _ => pure ()
        throw e

end Mathlib.Tactic
