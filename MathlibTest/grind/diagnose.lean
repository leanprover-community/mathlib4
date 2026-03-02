/-
Diagnostic tool for `grind ring` `isDefEqI` failures.

Given two terms that ARE defeq at default transparency but NOT at
reducibleAndInstances transparency, this finds which definition is blocking.

Usage:
  #diagnoseDefEqI termA vs termB

or call `DiagnoseDefEq.findBlockers` directly in MetaM.

Intended to be upstreamed into `checkInst` in lean4.
-/
import Lean
import Mathlib.Tactic.Core

open Lean Meta Elab Command Term

namespace DiagnoseDefEq

/-- Non-destructive defeq check at reducibleAndInstances transparency.
    Does not assign metavariables. -/
def isDefEqI (t s : Expr) : MetaM Bool :=
  withReducibleAndInstances <| withNewMCtxDepth <| isDefEq t s

/-- Non-destructive defeq check at default transparency.
    Does not assign metavariables. -/
def isDefEqDefault (t s : Expr) : MetaM Bool :=
  withDefault <| withNewMCtxDepth <| isDefEq t s

/-- Recursively find which constants block `isDefEqI` for two terms.

    Algorithm:
    1. Reduce both terms at reducibleAndInstances transparency (WHNF).
    2. If they're now equal: done, no blockers.
    3. If they have the same head constant: recurse on the mismatched arguments.
    4. If different heads: reduce further at default transparency.
       Any constant whose head changes during that extra reduction step is a blocker.
    5. Recurse on the default-reduced forms if still not equal.

    Assumes `t` and `s` ARE defeq at default transparency. -/
partial def findBlockers (t s : Expr) (fuel : Nat := 50) : MetaM (Array Name) := do
  if fuel == 0 then return #[Name.mkSimple "fuelExhausted"]

  -- Step 1: WHNF at reducibleAndInstances
  let t' ← withReducibleAndInstances <| whnf t
  let s' ← withReducibleAndInstances <| whnf s

  -- Step 2: already equal?
  if ← isDefEqI t' s' then return #[]

  let fn_t := t'.getAppFn
  let fn_s := s'.getAppFn
  let args_t := t'.getAppArgs
  let args_s := s'.getAppArgs

  -- Step 3: same head → recurse on mismatched args
  if let (.const n_t _, .const n_s _) := (fn_t, fn_s) then
    if n_t == n_s && args_t.size == args_s.size then
      let mut blockers := #[]
      for i in [:args_t.size] do
        let aᵢ := args_t[i]!
        let bᵢ := args_s[i]!
        if !(← isDefEqI aᵢ bᵢ) then
          blockers := blockers ++ (← findBlockers aᵢ bᵢ (fuel - 1))
      return blockers

  -- Step 4: different heads → reduce further at default to find what unfolded
  let t_def ← withDefault <| whnf t'
  let s_def ← withDefault <| whnf s'

  let fn_t_def := t_def.getAppFn
  let fn_s_def := s_def.getAppFn

  let mut blockers := #[]

  -- LHS head changed under default reduction → it was a non-reducible blocker
  if fn_t != fn_t_def then
    if let .const n _ := fn_t then
      blockers := blockers.push n

  -- RHS head changed under default reduction → it was a non-reducible blocker
  if fn_s != fn_s_def then
    if let .const n _ := fn_s then
      blockers := blockers.push n

  -- If the further-reduced forms are now equal, we're done
  if ← isDefEqI t_def s_def then return blockers

  -- Step 5: recurse on the further-reduced forms
  return blockers ++ (← findBlockers t_def s_def (fuel - 1))

/-- Pretty-print a term. Use `set_option pp.all true` externally for full detail. -/
private def ppFull (e : Expr) : MetaM MessageData :=
  return m!"{e}"

/-- Full diagnostic report comparing two terms at different transparencies. -/
def diagnose (t s : Expr) : MetaM MessageData := do
  let t' ← withReducibleAndInstances <| whnf t
  let s' ← withReducibleAndInstances <| whnf s
  let t_def ← withDefault <| whnf t
  let s_def ← withDefault <| whnf s

  let defeqI       ← isDefEqI t s
  let defeqDefault ← isDefEqDefault t s

  let blockersMsg : MessageData ←
    if !defeqI && defeqDefault then do
      let blockers ← findBlockers t s
      if blockers.isEmpty then
        pure m!"(no blocking definitions identified; structure may be too complex)"
      else
        let names := blockers.foldl (init := "")
          fun acc n => acc ++ s!"  • {n}\n"
        pure m!"Blocking definitions (consider marking @[reducible]):\n{names}"
    else if defeqI then
      pure m!"(terms are defeq at reducibleAndInstances; no diagnostic needed)"
    else
      pure m!"(terms are NOT defeq at default either; precondition violated)"

  return m!"━━━ DiagnoseDefEqI report ━━━
defeq at reducibleAndInstances : {defeqI}
defeq at default               : {defeqDefault}

LHS (original) :
  {← ppFull t}
RHS (original) :
  {← ppFull s}

LHS whnf at reducibleAndInstances :
  {← ppFull t'}
RHS whnf at reducibleAndInstances :
  {← ppFull s'}

LHS whnf at default :
  {← ppFull t_def}
RHS whnf at default :
  {← ppFull s_def}

{blockersMsg}"

end DiagnoseDefEq

/-- Diagnose why two terms fail to be defeq at reducibleAndInstances transparency.

    Example:
      #diagnoseDefEqI instHAdd (FiniteElement K) someAddInst
                   vs instHAdd (FiniteElement K) (Grind.Semiring.toAdd semiringInst)
-/
elab "#diagnoseDefEqI " t:term " vs " s:term : command => do
  Command.runTermElabM fun _ => do
    let t_expr ← Term.elabTermAndSynthesize t none
    let s_expr ← Term.elabTermAndSynthesize s none
    let t_expr ← instantiateMVars t_expr
    let s_expr ← instantiateMVars s_expr
    let msg ← DiagnoseDefEq.diagnose t_expr s_expr
    logInfo msg

/-- A drop-in for `Lean.Meta.Grind.Arith.CommRing.checkInst` that includes
    diagnostic information in the error message.

    To use: replace `checkInst` calls with `checkInstVerbose` in a local build. -/
def checkInstVerbose (declName : Name) (inst inst' : Expr) : MetaM Unit := do
  if ← DiagnoseDefEq.isDefEqI inst inst' then return
  let blockers ← DiagnoseDefEq.findBlockers inst inst'
  let blockersStr :=
    if blockers.isEmpty then "(none identified)"
    else blockers.foldl (init := "") fun acc n => acc ++ s!"\n  • {n}"
  throwError
    "error while initializing `grind ring` operators:\n\
     instance for `{declName}`\n  {indentExpr inst}\n\
     is not definitionally equal to the expected one\n  {indentExpr inst'}\n\
     when only reducible definitions and instances are reduced\n\
     \n\
     Blocking definitions:{blockersStr}\n\
     \n\
     Tip: set_option pp.all true and re-run to see full implicit arguments."

/-! ### Demonstration

A minimal example: `myNatAdd` wraps `Nat.add` but is NOT `@[reducible]` and NOT an instance.
So at `reducibleAndInstances` transparency it cannot be unfolded, while the synthesized
`Add Nat` instance (which IS an instance) can.  The tool should identify `myNatAdd` as the blocker.
-/

private def myNatAdd : Add Nat := ⟨Nat.add⟩

#diagnoseDefEqI myNatAdd vs (inferInstance : Add Nat)
