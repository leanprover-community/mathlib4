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

/-- When `true` (the default), `inferInstanceAs%` warns about sub-instances that are
synthesizable for the target carrier type but leaky at `reducibleAndInstances` transparency.
These warnings suggest defining intermediate instances with `inferInstanceAs%` to produce
smaller, more modular instance terms. -/
register_option inferInstanceAsPercent.leakySubInstWarning : Bool := {
  defValue := true
  descr := "warn about leaky sub-instances in inferInstanceAs%"
}

/-- Compute the chain of delta-unfoldings starting from `e` at default transparency.
Returns all intermediate forms including `e` itself (unless `skipHead` is true). -/
private def unfoldChain (e : Expr) (skipHead : Bool := false) :
    MetaM (Array Expr) := do
  let mut out : Array Expr := #[]
  let mut cur := e
  if !skipHead then out := out.push cur
  repeat do
    let some nxt ← withDefault <| unfoldDefinition? cur | break
    out := out.push nxt
    cur := nxt
  return out

/-- Add all unfoldings of `e` to `acc` as replacement sources mapping to `target`.
If `skipHead` is true, the first element (i.e. `e` itself) is not added. -/
private def addUnfoldings (acc : Array (Expr × Expr)) (e target : Expr)
    (skipHead : Bool := false) : MetaM (Array (Expr × Expr)) := do
  let chain ← unfoldChain e (skipHead := skipHead)
  let mut acc := acc
  for form in chain do
    if !acc.any (·.1 == form) then
      acc := acc.push (form, target)
  return acc

/-- Check whether two expressions have the same head constant name (ignoring universe levels). -/
private def sameHeadConstName (a b : Expr) : Bool :=
  match a.getAppFn, b.getAppFn with
  | .const n₁ _, .const n₂ _ => n₁ == n₂
  | _, _ => false

/-- Try to unfold `sourceType` and `expectedType` until they share a common head constant.
Returns the aligned pair, or throws an error if no common head is found.

This handles two cases:
- Universe-polymorphic aliases: e.g. `DecidableEq.{max 0 u}` vs `DecidableEq.{u}`
  (same constant name, different universe levels)
- Type abbreviations: e.g. `DecidableLT α` vs `DecidableRel (· < ·)`
  (different constants that unfold to a common head) -/
private def alignHeads (sourceType expectedType : Expr) :
    MetaM (Expr × Expr) := do
  -- Fast path: same head constant name (handles universe mismatches)
  if sameHeadConstName sourceType expectedType then
    return (sourceType, expectedType)
  -- Try unfolding both to find a common head
  let sourceChain ← unfoldChain sourceType (skipHead := true)
  let expectedChain ← unfoldChain expectedType (skipHead := true)
  -- Try unfolding source only
  for s in sourceChain do
    if sameHeadConstName s expectedType then
      return (s, expectedType)
  -- Try unfolding expected only
  for e in expectedChain do
    if sameHeadConstName sourceType e then
      return (sourceType, e)
  -- Try unfolding both
  for s in sourceChain do
    for e in expectedChain do
      if sameHeadConstName s e then
        return (s, e)
  throwError "inferInstanceAs%: source type head{indentExpr sourceType.getAppFn}\n\
    does not match expected type head{indentExpr expectedType.getAppFn}"

/-- Build the replacement table for differing arguments between `sourceType` and
`expectedType`. For each differing argument position, all unfoldings of both the
source and expected arguments are mapped to the expected argument. -/
private def buildReplacements (sourceType expectedType : Expr) :
    MetaM (Array (Expr × Expr)) := do
  let sourceArgs := sourceType.getAppArgs
  let expectedArgs := expectedType.getAppArgs
  let mut replacements : Array (Expr × Expr) := #[]
  for sArg in sourceArgs, eArg in expectedArgs do
    if sArg != eArg then
      -- Unfoldings of the expected (target) carrier, skipping the target itself
      replacements ← addUnfoldings replacements eArg eArg (skipHead := true)
      -- Unfoldings of the source carrier (including itself)
      replacements ← addUnfoldings replacements sArg eArg
  return replacements

/-- Check whether `e` is defeq (at `default` transparency) to any source expression
in `replacements`. Returns the target if found. -/
private def matchesAnyDefeq (e : Expr) (replacements : Array (Expr × Expr)) :
    MetaM (Option Expr) := do
  for (from_, to_) in replacements do
    if ← withDefault <| withNewMCtxDepth <| isDefEq e from_ then
      return some to_
  return none

/-- Replace carrier type arguments in a class type expression using the replacement table.
For example, transforms `TestDivInvMonoid Nat` into `TestDivInvMonoid TestNat`. -/
private def replaceCarriersInType (ty : Expr) (replacements : Array (Expr × Expr)) :
    MetaM Expr := do
  let args := ty.getAppArgs
  let mut args' := args
  for i in [:args.size] do
    if let some r ← matchesAnyDefeq args[i]! replacements then
      args' := args'.set! i r
  return mkAppN ty.getAppFn args'

/-- Replace binder domains in a chain of lambdas, stopping at the body.
Only replaces domains that are defeq to entries in `replacements`. -/
private partial def replaceLamDomains (e : Expr) (replacements : Array (Expr × Expr)) :
    MetaM Expr := do
  match e with
  | .lam name ty body bi =>
    let ty' := (← matchesAnyDefeq ty replacements).getD ty
    return .lam name ty' (← replaceLamDomains body replacements) bi
  | _ => return e

/-- WHNF `e` at default transparency and return the constructor info, universe levels,
and arguments, or `none` if `e` doesn't reduce to a constructor application. -/
private def getCtorApp? (e : Expr) :
    MetaM (Option (ConstructorVal × List Level × Array Expr)) := do
  let e' ← withDefault <| whnf e
  let .const c us := e'.getAppFn | return none
  let some (.ctorInfo ci) := (← getEnv).find? c | return none
  return some (ci, us, e'.getAppArgs)

/-- For each constructor parameter, determine whether it is instance-implicit and
whether it is a proof. -/
private def getFieldInfo (ci : ConstructorVal) : MetaM (Array (Bool × Bool)) :=
  withDefault <| forallTelescopeReducing ci.type fun ctorArgs _ =>
    ctorArgs.mapM fun arg => do
      let isInst := (← arg.fvarId!.getBinderInfo).isInstImplicit
      let isProof ← Meta.isProof arg
      return (isInst, isProof)

mutual

/-- Process each constructor argument: replace carrier type parameters, recursively
normalize instance-implicit fields, and patch lambda binder domains in other fields.

When `trySynth` is `true` (used only at the top level), for each instance-implicit field
we first try to find a pre-existing clean sub-instance via `trySynthInstance`. This avoids
diamonds with canonical instances. Recursive calls use `trySynth := false` to avoid
expensive synthesis at every level of the class hierarchy. -/
private partial def normalizeCtorArgs (ci : ConstructorVal) (us : List Level)
    (args : Array Expr) (fieldInfo : Array (Bool × Bool))
    (replacements : Array (Expr × Expr))
    (warnings : IO.Ref (Array MessageData))
    (trySynth : Bool := true) : MetaM Expr := do
  let mut args := args
  -- Replace carrier type in constructor parameters
  for i in *...ci.numParams do
    if let some r ← matchesAnyDefeq args[i]! replacements then
      args := args.set! i r
  -- Process each field
  for i in ci.numParams...args.size do
    if let some (isInst, isProof) := fieldInfo[i]? then
      if isProof then
        pure ()
      else if isInst then
        if trySynth then
          -- At the top level: try to find a pre-existing clean sub-instance
          let fieldType ← inferType args[i]!
          let targetFieldType ← replaceCarriersInType fieldType replacements
          match ← trySynthInstance targetFieldType with
          | .some synthInst =>
            -- Check if the synthesized version is clean by normalizing it
            -- (with trySynth := false to keep this cheap) and comparing
            let synthWarnings ← IO.mkRef #[]
            let normalizedSynth ←
              normalizeInstance synthInst replacements synthWarnings (trySynth := false)
            if ← withReducibleAndInstances <| withNewMCtxDepth <|
                isDefEq normalizedSynth synthInst then
              -- synthInst is already clean (e.g. defined with inferInstanceAs%);
              -- prefer it to avoid diamonds with the canonical instance
              args := args.set! i synthInst
            else
              -- synthInst is leaky: warn and use mechanically patched version
              let patched ←
                normalizeInstance args[i]! replacements warnings (trySynth := false)
              warnings.modify (·.push
                m!"inferInstanceAs%: the synthesized instance for \
                  {targetFieldType} has carrier type leakage \
                  (it uses the source carrier type internally instead of the \
                  target). `inferInstanceAs%` will patch the sub-instance \
                  inline, but consider defining it separately with \
                  `inferInstanceAs%` for cleaner results.{indentD
                  "To suppress this warning: \
                  `set_option inferInstanceAsPercent.leakySubInstWarning false`"}")
              args := args.set! i patched
          | _ =>
            args := args.set! i
              (← normalizeInstance args[i]! replacements warnings (trySynth := false))
        else
          -- Recursive calls: just normalize mechanically (no synthesis)
          args := args.set! i
            (← normalizeInstance args[i]! replacements warnings (trySynth := false))
      else
        args := args.set! i (← replaceLamDomains args[i]! replacements)
  return mkAppN (.const ci.name us) args

/-- Recursively normalize a class instance expression:
1. WHNF at `default` transparency to expose the constructor.
2. Replace the carrier type parameter(s) in the constructor.
3. For each instance-implicit, non-proof field: try synthesis (if `trySynth`), else recurse.
4. For each non-instance function field: replace lambda binder domains only. -/
private partial def normalizeInstance (e : Expr) (replacements : Array (Expr × Expr))
    (warnings : IO.Ref (Array MessageData)) (trySynth : Bool := true) : MetaM Expr := do
  let ty ← inferType e
  let some _className ← isClass? ty | return e
  if ← Meta.isProp ty then return e
  let some (ci, us, args) ← getCtorApp? e | return e
  let fieldInfo ← getFieldInfo ci
  normalizeCtorArgs ci us args fieldInfo replacements warnings (trySynth := trySynth)

end

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
  unless ← withDefault <| isDefEq sourceType expectedType do
    throwError "inferInstanceAs%: source type{indentExpr sourceType}\n\
      is not defeq to expected type{indentExpr expectedType}"
  let sourceType ← instantiateMVars sourceType
  let inst ← synthInstance sourceType
  let inst ← instantiateMVars inst
  let expectedType ← instantiateMVars expectedType
  -- Align heads: unfold both types until they share a common head constant.
  -- This handles universe mismatches and type abbreviations like DecidableLT vs DecidableRel.
  let (sourceType, expectedType) ← alignHeads sourceType expectedType
  -- Build replacement table from differing carrier type arguments
  let replacements ← buildReplacements sourceType expectedType
  if replacements.isEmpty then return inst
  let warnLeaky := inferInstanceAsPercent.leakySubInstWarning.get (← getOptions)
  let warnings ← IO.mkRef #[]
  let result ← normalizeInstance inst replacements warnings
  if warnLeaky then
    for w in ← warnings.get do
      logWarning w
  return result
