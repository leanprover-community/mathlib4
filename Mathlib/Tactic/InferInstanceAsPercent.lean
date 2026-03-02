/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import Mathlib.Init
public meta import Lean.Elab.Term

/-!
# `inferInstanceAs%` term elaborator

`inferInstanceAs%` is a drop-in replacement for `inferInstanceAs` that prevents
"type leakage" in synthesized instances.

## The problem

When `inferInstanceAs` synthesizes an instance for a type alias, the resulting
expression may contain lambda binder domains (and other sub-expressions) that
refer to an unfolded form of the carrier type rather than the declared alias.
For example, defining

```
def B := A
instance : SomeClass B := inferInstanceAs (SomeClass A)
```

may produce an instance whose internal lambdas have domain `A` (or even deeper
unfoldings) instead of `B`. This is invisible at `default` transparency (where
`A` and `B` are defeq), but causes `isDefEq` failures at `reducibleAndInstances`
transparency — which is the level used by `grind`'s `checkInst`.

## The fix

`inferInstanceAs%` synthesizes the instance, then recursively normalizes its
constructor tree: for each class-valued structure, it WHNFs to expose the
constructor, patches the carrier type parameter, and recursively processes
instance-implicit fields. Lambda binder domains matching the source carrier
are replaced with the target carrier.
-/

public meta section

open Lean Meta Elab Term

/-- Compute the chain of delta-unfoldings starting from `e` at default transparency.
    Returns all intermediate forms including `e` itself. -/
private partial def unfoldChain (e : Expr) (fuel : Nat := 100) : MetaM (Array Expr) := do
  if fuel == 0 then return #[e]
  let some e' ← withDefault <| unfoldDefinition? e | return #[e]
  return #[e] ++ (← unfoldChain e' (fuel - 1))

/-- Check whether `e` is defeq (at `default` transparency) to any source expression
    in `replacements`. Returns the target if found. -/
private def matchesAnyDefeq (e : Expr) (replacements : Array (Expr × Expr)) :
    MetaM (Option Expr) := do
  for (from_, to_) in replacements do
    if ← withDefault <| withNewMCtxDepth <| isDefEq e from_ then
      return some to_
  return none

/-- Replace binder domains in a chain of lambdas, stopping at the body.
    Only replaces domains that are defeq to entries in `replacements`. -/
private partial def replaceLamDomains (e : Expr) (replacements : Array (Expr × Expr)) :
    MetaM Expr := do
  match e with
  | .lam name ty body bi =>
    let ty' ← do
      match ← matchesAnyDefeq ty replacements with
      | some r => pure r
      | none => pure ty
    return .lam name ty' (← replaceLamDomains body replacements) bi
  | _ => return e

/-- Recursively normalize a class instance expression:
    1. WHNF at `default` transparency to expose the constructor.
    2. Replace the carrier type parameter(s) in the constructor.
    3. For each instance-implicit, non-proof field: recurse.
    4. For each non-instance function field: replace lambda binder domains only. -/
private partial def normalizeInstance (e : Expr) (replacements : Array (Expr × Expr))
    (fuel : Nat := 50) : MetaM Expr := do
  if fuel == 0 then return e
  let ty ← inferType e
  -- Only process class instances
  let some _className ← isClass? ty | return e
  -- Skip proofs
  if ← withDefault <| Meta.isProp ty then return e
  -- WHNF to expose constructor
  let e' ← withDefault <| whnf e
  let .const c .. := e'.getAppFn | return e
  let some (.ctorInfo ci) := (← getEnv).find? c | return e
  -- Identify which constructor fields are instance-implicit and non-proof
  let params ← withDefault <| forallTelescopeReducing ci.type fun ctorArgs _ =>
    ctorArgs.mapM fun arg => do
      let isInst := (← arg.fvarId!.getBinderInfo).isInstImplicit
      let isProof ← Meta.isProof arg
      return (isInst, isProof)
  let mut args := e'.getAppArgs
  -- Replace carrier type in constructor parameters (using defeq matching)
  for i in [:ci.numParams] do
    if let some r ← matchesAnyDefeq args[i]! replacements then
      args := args.set! i r
  -- Process each field
  for i in [ci.numParams:args.size] do
    if h : i < params.size then
      let (isInst, isProof) := params[i]
      if isProof then
        -- Skip proofs (proof irrelevance)
        pure ()
      else if isInst then
        -- Instance-implicit field: recursively normalize
        args := args.set! i (← normalizeInstance args[i]! replacements (fuel - 1))
      else
        -- Non-instance field (e.g., function): replace lambda binder domains only
        args := args.set! i (← replaceLamDomains args[i]! replacements)
  return mkAppN e'.getAppFn args

/-- `inferInstanceAs%` — like `inferInstanceAs`, but rewrites internal sub-expressions
    (e.g. lambda binder domains) to use the expected carrier type instead of
    intermediate unfoldings that leaked during instance synthesis.

    When `inferInstanceAs (SomeClass A)` is used to define `SomeClass B` (where
    `B` is a non-reducible alias for `A`), the synthesized instance may contain
    sub-expressions referring to `A` or its unfoldings instead of `B`. This
    causes `isDefEq` failures at `reducibleAndInstances` transparency.
    `inferInstanceAs%` fixes this by recursively normalizing the constructor
    tree, patching carrier types and lambda binder domains.

    Example:
    ```
    noncomputable instance : Field (FiniteResidueField K) :=
      inferInstanceAs% (Field (IsLocalRing.ResidueField _))
    ```
-/
elab "inferInstanceAs% " source:term : term <= expectedType => do
  let sourceType ← elabType source
  -- Unify source with expected type to resolve metavariables (e.g., _ placeholders)
  discard <| withDefault <| isDefEq sourceType expectedType
  let sourceType ← instantiateMVars sourceType
  let inst ← synthInstance sourceType
  let inst ← instantiateMVars inst
  let expectedType ← instantiateMVars expectedType
  -- Compare arguments to find differing carrier types
  let sourceArgs := sourceType.getAppArgs
  let expectedArgs := expectedType.getAppArgs
  let mut replacements : Array (Expr × Expr) := #[]
  for i in [:sourceArgs.size.min expectedArgs.size] do
    let sArg := sourceArgs[i]!
    let eArg := expectedArgs[i]!
    if sArg != eArg then
      -- Compute unfolding chain from the expected (target) carrier
      let chain ← unfoldChain eArg
      -- All forms except the first (target) are candidates for replacement
      for j in [1:chain.size] do
        replacements := replacements.push (chain[j]!, eArg)
      -- Also compute unfolding chain from the source carrier
      let sourceChain ← unfoldChain sArg
      for j in [:sourceChain.size] do
        if !replacements.any (·.1 == sourceChain[j]!) then
          replacements := replacements.push (sourceChain[j]!, eArg)
  if replacements.isEmpty then return inst
  normalizeInstance inst replacements
