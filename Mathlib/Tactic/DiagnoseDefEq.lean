/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# Diagnostic tool for `isDefEqI` failures

Given two terms that ARE defeq at default transparency but NOT at
`reducibleAndInstances` transparency, `findBlockers` identifies which
non-reducible definitions are causing the failure.

The algorithm runs `isDefEq` at both transparency levels with
`trace.Meta.isDefEq.delta` enabled, then reports names that were
delta-unfolded at `default` but not at `instances` transparency.
It also captures `trace.Meta.isDefEq.stuck` from the `instances` run to
show the specific subterm where the check got stuck.

This is intended to be upstreamed into `checkInst` in lean4.
-/

public meta section

open Lean Meta Elab Command Term

namespace DiagnoseDefEq

/-- Non-destructive defeq check at `reducibleAndInstances` transparency. -/
def isDefEqI (t s : Expr) : MetaM Bool :=
  withReducibleAndInstances <| withNewMCtxDepth <| isDefEq t s

/-- Non-destructive defeq check at default transparency. -/
def isDefEqDefault (t s : Expr) : MetaM Bool :=
  withDefault <| withNewMCtxDepth <| isDefEq t s

/-- Unwrap `.withContext` / `.withNamingContext` wrappers from a `MessageData`. -/
private def stripCtx : MessageData → MessageData
  | .withContext _ m       => stripCtx m
  | .withNamingContext _ m => stripCtx m
  | m                      => m

/-- Recursively collect all delta-unfolded constant name strings from a trace tree. -/
private partial def collectDeltaNames (msg : MessageData) : Array String :=
  match msg with
  | .trace data wrappedInner children =>
    let own :=
      if data.cls == `Meta.isDefEq.delta.unfoldLeft      ||
         data.cls == `Meta.isDefEq.delta.unfoldRight     ||
         data.cls == `Meta.isDefEq.delta.unfoldLeftRight then
        match stripCtx wrappedInner with
        | .ofFormatWithInfos ⟨fmt, _⟩ => #[fmt.pretty]
        | _ => #[]
      else #[]
    children.foldl (fun acc c => acc ++ collectDeltaNames c) own
  | _ => #[]

/-- Recursively collect the inner `MessageData` from all `Meta.isDefEq.stuck` trace nodes. -/
private partial def collectStuckMsgs (msg : MessageData) : Array MessageData :=
  match msg with
  | .trace data inner children =>
    let own := if data.cls == `Meta.isDefEq.stuck then #[inner] else #[]
    children.foldl (fun acc c => acc ++ collectStuckMsgs c) own
  | _ => #[]

/-- Run `isDefEq t s` at transparency `transp` with tracing enabled.
    Returns `(deltaNames, stuckMsgs)` collected from the trace.
    Internal traces are hidden so they don't appear in the user's output. -/
private def runWithTracing (t s : Expr) (transp : TransparencyMode)
    (wantStuck : Bool := false) : MetaM (Array String × Array MessageData) := do
  let savedTraces ← getTraces
  let setOpts (o : Options) :=
    let o := o.setBool `trace.Meta.isDefEq.delta true
    if wantStuck then o.setBool `trace.Meta.isDefEq.stuck true else o
  withOptions setOpts do
    _ ← withNewMCtxDepth <| withTransparency transp <| isDefEq t s
  let newTraces := ((← getTraces).toArray)[savedTraces.size:]
  modifyTraces fun _ => savedTraces  -- restore, hiding internal traces
  let deltaNames := newTraces.foldl (fun acc e => acc ++ collectDeltaNames e.msg) #[]
  let stuckMsgs  := newTraces.foldl (fun acc e => acc ++ collectStuckMsgs e.msg)  #[]
  return (deltaNames, stuckMsgs)

/-- Find which constants block `isDefEqI`.

    Compares delta-unfoldings at `instances` vs `default` transparency.
    Returns names that were delta-unfolded at `default` but not at `instances`. -/
def findBlockers (t s : Expr) : MetaM (Array Name) := do
  let (reducibleSet, _) ← runWithTracing t s .instances
  let (defaultSet,   _) ← runWithTracing t s .default
  -- Blockers: unfolded at default but not at reducibleAndInstances
  let blockerStrs := defaultSet.filter (fun n => !reducibleSet.contains n)
  -- Deduplicate and convert strings to Names
  let unique := blockerStrs.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]
  return unique.map fun s =>
    s.splitOn "." |>.foldl (fun n p => if p.isEmpty then n else .str n p) .anonymous

/-- Descend into `t` and `s` (at `instances` transparency) to find the innermost
    sub-term pair that is not defeq at `instances` but IS defeq at `default`.
    Returns `none` if no stuck pair is found (e.g. the terms are already equal). -/
partial def findStuckPair (t s : Expr) (fuel : Nat := 20) : MetaM (Option (Expr × Expr)) := do
  if fuel == 0 then return some (t, s)
  let t' ← withReducibleAndInstances <| whnf t
  let s' ← withReducibleAndInstances <| whnf s
  if ← withReducibleAndInstances <| withNewMCtxDepth <| isDefEq t' s' then
    return none
  -- Both lambdas: compare binding domains first, then bodies
  if t'.isLambda && s'.isLambda then
    let tDom := t'.bindingDomain!
    let sDom := s'.bindingDomain!
    -- If the domains differ at instances transparency, THEY are the stuck pair
    if !(← withReducibleAndInstances <| withNewMCtxDepth <| isDefEq tDom sDom) then
      if let some stuck ← findStuckPair tDom sDom (fuel - 1) then
        return some stuck
      return some (tDom, sDom)
    -- Domains match: introduce fresh var and recurse on bodies
    let name := t'.bindingName!
    let bi   := t'.bindingInfo!
    return ← withLocalDecl name bi tDom fun x => do
      let tbody := t'.bindingBody!.instantiate1 x
      let sbody := s'.bindingBody!.instantiate1 x
      if ← withReducibleAndInstances <| withNewMCtxDepth <| isDefEq tbody sbody then
        return none
      findStuckPair tbody sbody (fuel - 1)
  -- Same head constant: recurse on first mismatched argument
  if let (.const n_t _, .const n_s _) := (t'.getAppFn, s'.getAppFn) then
    if n_t == n_s && t'.getAppArgs.size == s'.getAppArgs.size then
      let args_t := t'.getAppArgs
      let args_s := s'.getAppArgs
      for i in [:args_t.size] do
        let aᵢ := args_t[i]!
        let bᵢ := args_s[i]!
        if !(← withReducibleAndInstances <| withNewMCtxDepth <| isDefEq aᵢ bᵢ) then
          if let some stuck ← findStuckPair aᵢ bᵢ (fuel - 1) then
            return some stuck
      return none
  -- Different heads or structural mismatch: this is the stuck pair
  return some (t', s')

/-- Collect named-constant applications in `e` whose inferred type contains
    `stuckType` as a sub-expression. Results are in DFS pre-order. -/
private partial def collectInstCandidates (stuckType : Expr) (e : Expr)
    (acc : Array (Name × Expr)) : MetaM (Array (Name × Expr)) :=
  match e with
  | .app .. => do
    let mut acc := acc
    if let some name := e.getAppFn.constName? then
      let ty ← try inferType e catch _ => pure (.sort .zero)
      if ty.find? (· == stuckType) |>.isSome then
        acc := acc.push (name, e)
    for arg in e.getAppArgs do
      acc ← collectInstCandidates stuckType arg acc
    return acc
  | _ => return acc

/-- Find the "leaf" instance in the synthesized LHS that introduced the type mismatch.
    This is the deepest named-constant application in the LHS whose type involves
    `stuckType`, but whose explicit arguments' types do not — meaning it is the root
    cause instance, not a projection of some deeper bad instance. -/
private def findCulpritInst (lhs : Expr) (stuckType : Expr) :
    MetaM (Option (Name × Expr)) := do
  let candidates ← collectInstCandidates stuckType lhs #[]
  for (name, e) in candidates do
    let isLeaf ← e.getAppArgs.allM fun arg => do
      match arg.getAppFn.constName? with
      | none => return true
      | some _ =>
        let ty ← try inferType arg catch _ => pure (.sort .zero)
        return ty.find? (· == stuckType) |>.isNone
    if isLeaf then return some (name, e)
  return none

/-- Full diagnostic report. -/
def diagnose (t s : Expr) : MetaM MessageData := do
  let defeqI       ← isDefEqI t s
  let defeqDefault ← isDefEqDefault t s

  let bodyMsg : MessageData ←
    if !defeqI && defeqDefault then do
      -- Find the innermost sub-term pair where the check gets stuck,
      -- then identify the culprit instance in the LHS that caused it.
      let (stuckMsg, culpritMsg) ←
        match ← findStuckPair t s with
        | none        => pure (m!"", m!"")
        | some (a, b) =>
          let stuckMsg := m!"\nChecking equality of:\n  LHS : {a}\n  RHS : {b}\n"
          let culpritMsg : MessageData ←
            match ← findCulpritInst t b with
            | none => pure m!""
            | some (name, e) =>
              let ty ← inferType e
              let env ← getEnv
              let modInfo : MessageData :=
                match env.getModuleIdxFor? name with
                | none     => m!"(current file)"
                | some idx => m!"`{env.header.moduleNames[idx.toNat]!}`"
              pure m!"\nInstance introducing the mismatch:\
                \n  {name} : {ty}\n  (defined in {modInfo})\n"
          pure (stuckMsg, culpritMsg)
      -- Find blocking definitions via delta trace comparison
      let blockers ← findBlockers t s
      let blockersSection : MessageData :=
        if blockers.isEmpty then m!"\n(no blocking definitions identified)"
        else
          let names := blockers.foldl (init := "")
            fun acc n => acc ++ s!"  • {n}\n"
          m!"\nDefinitions transparent at default but opaque at reducibleAndInstances:\n{names}"
      pure (stuckMsg ++ culpritMsg ++ blockersSection)
    else if defeqI then
      pure m!"(terms are defeq at reducibleAndInstances; no diagnostic needed)"
    else
      pure m!"(terms are NOT defeq at default either; precondition violated)"

  return m!"━━━ DiagnoseDefEqI report ━━━
defeq at reducibleAndInstances : {defeqI}
defeq at default               : {defeqDefault}
{bodyMsg}"

end DiagnoseDefEq

/-- Diagnose why two terms fail to be defeq at `reducibleAndInstances` transparency.

    Typical use: when `grind ring`'s `checkInst` fails, reconstruct the two terms it
    compared and pass them here to find which non-reducible definition is the blocker.

    Example:
      variable (K : Type*) [Field K]
      #diagnoseDefEqI (inferInstance : Inv K)
                   vs ((inferInstance : Lean.Grind.Field K).toInv)
-/
elab "#diagnoseDefEqI " t:term " vs " s:term : command => do
  Command.runTermElabM fun _ => do
    let t_expr ← Term.elabTermAndSynthesize t none
    let s_expr ← Term.elabTermAndSynthesize s none
    let t_expr ← instantiateMVars t_expr
    let s_expr ← instantiateMVars s_expr
    let msg ← DiagnoseDefEq.diagnose t_expr s_expr
    logInfo msg

