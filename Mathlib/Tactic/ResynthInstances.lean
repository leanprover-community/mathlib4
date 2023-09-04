/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Basic
import Std.Lean.Meta.Inaccessible

/-!
# The `resynth_instances` tactic

Resynthesizes all typeclasses in the goal or a hypothesis, if possible.
-/

open Lean Elab Meta Tactic

namespace Mathlib.Tactic.ResynthInstances

/-- The state for `ResynthInstancesM`. -/
structure State where
  /-- All the instance problems that could not be resynthesized. -/
  nosynth : ExprSet := {}
  /-- All the instance problems that appear that resynthesized non-defeq. -/
  new : ExprSet := {}
  /-- All the instance problems that appear that resynthesized defeq. -/
  ok : ExprSet := {}

/-- Monad for collecting instance problems from an expression. -/
abbrev ResynthInstancesM := StateT State MetaM

/--
Visit every typeclass instance in the `Expr` and resynthesizes them if possible.
Verifies that the result is still type correct.
-/
def resynthInstances (e : Expr) (record : Bool := true) : ResynthInstancesM (Option Expr) := do
  let e' ← Meta.transform e
    (pre := fun e' => do
      let ty ← inferType e'
      if (← isClass? ty).isSome then
        -- logInfo m!"typeclass{(← mkFreshExprMVar ty).mvarId!}"
        if let some e'' ← synthInstance? ty then
          if record then
            if ← withReducibleAndInstances <| isDefEq e' e'' then
              let ty' ← inferType <| ← mkLambdaFVars (usedOnly := true) (← getLCtx).getFVars e'
              modify fun s => {s with ok := s.ok.insert ty'}
            else
              let ty' ← inferType <| ← mkLambdaFVars (usedOnly := true) (← getLCtx).getFVars e''
              modify fun s => {s with new := s.new.insert ty'}
          return .done e''
        else
          if record then
            let ty' ← inferType <| ← mkLambdaFVars (usedOnly := true) (← getLCtx).getFVars e'
            modify fun s => {s with nosynth := s.nosynth.insert ty'}
          return .done e'
      else
        return .continue)
  try
    Meta.check e'
    return some e'
  catch _ =>
    return none

/-- Resynthesize the instances. Reports information about resynthesis if `info` is true.
Returns the expression with resynthesized instances if it is type correct,
otherwise throws an error. -/
def runResynthInstances (target : Expr) (info : Bool := false) : MetaM Expr := do
  let target ← instantiateMVars target
  let (target'?, s) ← (resynthInstances target (record := info)).run {}
  if info then
    let mut msgs : Array MessageData := #[]
    if some target == target'? then
      msgs := msgs.push m!"resynthesis results in the same expression"
    let defrost (ty : Expr) : MetaM MVarId := do
      let (_, g) ← (← mkFreshExprMVarAt {} {} ty).mvarId!.intros
      let (g, _) ← g.renameInaccessibleFVars
      return g
    for ty in s.nosynth do
      msgs := msgs.push <| m!"💥 failed to resynthesize{indentD <| ← defrost ty}"
    for ty in s.new do
      msgs := msgs.push <| m!"❌ resynthesis is non-defeq for{indentD <| ← defrost ty}"
    for ty in s.ok do
      msgs := msgs.push <| m!"✅ resynthesis is defeq for{indentD <| ← defrost ty}"
    unless msgs.isEmpty do
      logInfo <| .joinSep msgs.toList "\n---\n"
  let some target' := target'?
    | throwError "resynthesis results in a type-incorrect expression"
  return target'

/--
- `resynth_instances` resynthesizes all typeclass instances in the goal, when possible.
  Throws an error if the result is not type correct.
  Uses `convert` to create side goals for non-defeq instances.
- `resynth_instances at h` resynthesizes all typeclass instances in the hypothesis `h`,
  when possible.
  - For local definitions, resynthesizes both the value and the type,
    deletes the old let binding if possible, and then creates a new one.
  - For hypotheses, resynthesizes the type.
    If it is defeq, then it gets changed to the new type.
    If it is not defeq, then deletes the old hypothesis if possible and creates a new one.

The `?` option yields a report about the results of instance resynthesis.
For example, `resynth_instances?` or `resynth_instances? at h`.
-/
elab (name := resynthInstancesStx)
    "resynth_instances" info:"?"? loc:(Parser.Tactic.location)? : tactic =>
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := fun h ↦ liftMetaTactic fun mvarId => do
      if let some val ← h.getValue? then
        let ty ← h.getType
        let ty' ← runResynthInstances ty (info := info.isSome)
        let val' ← runResynthInstances val (info := info.isSome)
        unless ← isDefEq (← inferType val') ty' do
          throwError "Resynthesized type{indentD ty'}\nis not defeq to type of value{indentD val'}"
        let (_, g) ← mvarId.let (← h.getUserName) val' ty'
        let g ← g.tryClear h
        return [g]
      else
        let ty ← h.getType
        let ty' ← runResynthInstances ty (info := info.isSome)
        if ← withReducibleAndInstances <| isDefEq ty ty' then
          let g ← mvarId.changeLocalDecl' h ty' (checkDefEq := false)
          return [g]
        else
          -- Create a new local and clear the old one (if possible)
          let eq ← mkAppM ``Eq #[ty, ty']
          let gEq ← mkFreshExprMVar (some eq)
          let gs ← gEq.mvarId!.congrN!
          let v ← mkAppM ``cast #[gEq, .fvar h]
          let (_, g) ← mvarId.note (← h.getUserName) v ty'
          let g ← g.tryClear h
          return g :: gs)
    (atTarget := liftMetaTactic fun mvarId => do
      let target' ← runResynthInstances (← mvarId.getType) (info := info.isSome)
      let g' ← mkFreshExprSyntheticOpaqueMVar target' (tag := ← mvarId.getTag)
      let gs ← mvarId.convert g' false
      return g'.mvarId! :: gs)
    (failed := fun _ ↦ throwError "resynth_instances failed")

@[inherit_doc resynthInstancesStx]
macro "resynth_instances?" loc:(Parser.Tactic.location)? : tactic =>
  `(tactic| resynth_instances ? $[$loc]?)
