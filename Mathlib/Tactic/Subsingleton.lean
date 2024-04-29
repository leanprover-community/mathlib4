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
The `subsingleton` tactic attempts to close equality or `HEq` goals
using an argument that the types involved are subsingletons.
To first approximation, it does `apply Subsingleton.elim`.
As a nicety, `subsingleton` first runs the `intros` tactic.

- If the goal is an equality, it either closes the goal or fails.
- If the goal is a `HEq`, it can try applying `Subsingleton.helim`
  to convert a `@HEq α x β y` goal into an `α = β` goal.

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
The reason this goes through is that it applies the `∀ (p : Prop), Subsingleton p` instance,
specializing the universe level metavariable in `Sort _` to `0`.
-/
elab "subsingleton" : tactic => do
  let recover := (← read).recover
  Elab.Tactic.liftMetaTactic fun g => do
  let (fvars, g) ← g.intros
  let didIntros := !fvars.isEmpty
  let g ← g.heqOfEq
  g.withContext do
    let tgt ← whnfR (← g.getType)
    if let some (ty, x, y) := tgt.eq? then
      -- Proof irrelevance. This is not necessary since `rfl` suffices,
      -- but propositions are subsingletons so we may as well.
      if ← Meta.isProp ty then
        g.assign <| mkApp3 (.const ``proof_irrel []) ty x y
        return []
      -- Try `Subsingleton.elim`
      let u ← getLevel ty
      let instTy := Expr.app (.const ``Subsingleton [u]) ty
      try
        -- Synthesize a subsingleton instance. The new metacontext depth ensures that universe
        -- level metavariables are not specialized.
        let inst ← withNewMCtxDepth <| synthInstance instTy
        g.assign <| mkApp4 (.const ``Subsingleton.elim [u]) ty inst x y
        return []
      catch _ => pure ()
      -- Try `lawful_beq_subsingleton`
      let ty' ← whnfR ty
      if ty'.isAppOfArity ``BEq 1 then
        let α := ty'.appArg!
        try
          let some u' := u.dec | failure
          let xInst ← withNewMCtxDepth <| synthInstance <| mkApp2 (.const ``LawfulBEq [u']) α x
          let yInst ← withNewMCtxDepth <| synthInstance <| mkApp2 (.const ``LawfulBEq [u']) α y
          g.assign <| mkApp5 (.const ``lawful_beq_subsingleton [u']) α x y xInst yInst
          return []
        catch _ => pure ()
      -- Try `refl` when all else fails, to give a hint to the user
      if recover then
        try
          g.refl
          let tac ← if didIntros then `(tactic| (intros; rfl)) else `(tactic| rfl)
          Meta.Tactic.TryThis.addSuggestion (← getRef) tac (origSpan? := ← getRef)
          return []
        catch _ => pure ()
      throwError "\
        tactic 'subsingleton' could prove equality since it could not synthesize\
        {indentD instTy}"
    else if let some (xTy, x, yTy, y) := tgt.heq? then
      -- The HEq version of proof irrelevance.
      if ← (Meta.isProp xTy <&&> Meta.isProp yTy) then
        g.assign <| mkApp4 (.const ``proof_irrel_heq []) xTy yTy x y
        return []
      -- Now, try `Subsingleton.helim` by synthesizing a `Subsingleton` instance from either type.
      -- This does not close a goal, but creates a new goal.
      let u ← getLevel xTy
      let instXTy := Expr.app (.const ``Subsingleton [u]) xTy
      let instYTy := Expr.app (.const ``Subsingleton [u]) yTy
      let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq xTy yTy) (← g.getTag)
      try
        let inst ← withNewMCtxDepth <| synthInstance instXTy
        g.assign <| mkApp6 (.const ``Subsingleton.helim [u]) xTy yTy inst g' x y
        return [g'.mvarId!]
      catch _ => pure ()
      try
        let inst ← withNewMCtxDepth <| synthInstance instYTy
        let pf ← mkHEqSymm <|
          mkApp6 (.const ``Subsingleton.helim [u]) xTy yTy inst (← mkEqSymm g') x y
        g.assign pf
        return [g'.mvarId!]
      catch _ => pure ()
      throwError "\
        tactic 'subsingleton' could not prove heterogenous equality since it could not \
        synthesize either{indentD instXTy}\nor{indentD instYTy}"
    throwError "tactic 'subsingleton' failed, goal is neither an equality nor heterogenous equality"
