/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kyle Miller, Jovan Gerbscheid
-/
module

public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Reduce
public import Mathlib.Init

/-!
# The `fast_instance%`, `inferInstanceAs%`, and `#check_instance` elaborators
-/

meta section

namespace Mathlib.Elab.FastInstance

open Lean Meta Elab Term

initialize registerTraceClass `Elab.fast_instance

/--
Throw an error for `makeFastInstance`. The trace is a list of fields.
Note: with the current implementation, this might not be accurate for multi-structure types,
since `makeFastInstance` just uses `ClassName.paramName` for the trace.
-/
def error {α : Type _} (trace : Array Name) (m : MessageData) : MetaM α :=
  throwError "\
    {m}\n\n\
    Use `set_option trace.Elab.fast_instance true` to analyze the error.\n\n\
    Trace of fields visited: {trace}"

/-- Run `x` in a modified environment where `instName` no longer has the `instance` attribute.

We don't put this in a more generic location (e.g. `Mathlib.Lean.Meta.Basic`) because it will be
moved to Lean 4 core. -/
def withDisabledInstance {α : Type} (instName : Name) (x : MetaM α) : MetaM α := do
  if !(instanceExtension.getState (← getEnv)).instanceNames.contains instName then
    return ← x
  withoutModifyingEnv do
    Attribute.erase instName `instance
    x

/--
Core algorithm for normalizing instances.
* Ideally, the term is replaced with a synthesized instance.
* If not, it is reduced to a constructor
  and each instance implicit field is given the same treatment.

Many reductions for typeclasses are done with reducible transparency, so the entire body
is `withReducible` with some exceptions.
-/
partial def makeFastInstance (inst expectedType : Expr) (trace : Array Name := #[]) :
    MetaM Expr := withReducible do
  withTraceNode `Elab.fast_instance (fun _ => return m!"type: {expectedType}") do
  let some className ← isClass? expectedType
    | error trace m!"Can only be used for classes, but type is{indentExpr expectedType}"
  trace[Elab.fast_instance] "class is {className}"
  if ← isProp expectedType then
    logWarning m!"Provided instance{indentExpr inst}\n\
      is a proof, which does not need normalization."
    return inst

  -- Try to synthesize a total replacement for this term:
  let synth? : Option Expr ← do
    match ← trySynthInstance expectedType with
    | .some e => pure (some e)
    | _ => pure none
  if let .some new := synth? then
    if ← withDefault <| isDefEq inst new then
      trace[Elab.fast_instance] "replaced with synthesized instance"
      return new
    else
      error trace m!"\
        Provided instance{indentExpr inst}\n\
        is not defeq to inferred instance{indentExpr new}"
  -- Otherwise, try to reduce it to a constructor.
  else
    (← whnfI inst).withApp fun f args => do
    let error' (m : MessageData) : MetaM Expr := do
      if isStructure (← getEnv) className then
        error trace m
      else
        error trace m!"{m}\n\n\
          This instance is not a structure and not canonical. \
          Use a separate 'instance' command to define it."
    let .const c _ := f
      | error' m!"\
          Provided instance does not reduce to a constructor application{indentExpr inst}"
    let .ctorInfo ci ← getConstInfo c
      | error' m!"\
          Provided instance does not reduce to a constructor application{indentExpr inst}\n\
          Reduces to an application of {c}."
    let (mvars, bis, cls) ← forallMetaTelescope (← inferType f)
    unless args.size == mvars.size do
      -- This is an invalid term.
      throwError "Incorrect number of arguments for constructor application `{f}`: {args}"
    -- Unify the parameters
    unless ← isDefEq expectedType cls do
      throwError "`{expectedType}` does not unify with the conclusion of `{.ofConstName c}`"
    -- TODO: use structure eta reduction when possible?
    for i in ci.numParams...args.size do
      let bi := bis[i]!
      let mvarId := mvars[i]!.mvarId!
      let mvarDecl ← mvarId.getDecl
      let argExpectedType ← instantiateMVars mvarDecl.type
      let arg := args[i]!
      if ← isProp argExpectedType then
        -- For proofs, create an auxiliary theorem of the expected type.
        if ← withDefault <| isDefEq argExpectedType (← inferType arg) then
          mvarId.assign <| ← mkAuxTheorem argExpectedType arg (zetaDelta := true)
        else
          throwError "Proof `{arg}` does not have expected type `{argExpectedType}`"
      -- Recurse into instance arguments of the constructor.
      else if bi.isInstImplicit then
        let trace' := trace.push (className ++ mvarDecl.userName)
        mvarId.assign (← makeFastInstance arg argExpectedType (trace := trace'))
      else
        -- For data fields, make sure that the lambda binders have the right type.
        forallTelescopeReducing argExpectedType fun xs _ ↦ do
          mvarId.assign <| ← mkLambdaFVars xs (arg.beta xs)
    return mkAppN f (← mvars.mapM instantiateMVars)


/--
`fast_instance% inst` takes an expression for a typeclass instance `inst`, and unfolds it into
constructor applications that leverage existing instances. It uses the expected type to fill in
the constructor applications and lambda binders of data fields.

For instance, when used as
```lean
instance instSemiring : Semiring X := sorry
instance instRing : Ring X := fast_instance% Function.Injective.ring ..
```
this will define `instRing` as a nested constructor application that refers to `instSemiring`
rather than applications of `Function.Injective.ring` or other non-canonical constructors.
The advantage is then that `instRing.toSemiring` unifies almost immediately with `instSemiring`,
rather than having to break it down into smaller pieces.
-/
syntax (name := fastInstance) "fast_instance% " term : term

@[term_elab fastInstance, inherit_doc fastInstance]
public def elabFastInstance : TermElab
  | `(term| fast_instance% $arg), expectedType? => do
    let inst ← withSynthesize <| elabTerm arg expectedType?
    let expectedType ← expectedType?.getDM (inferType inst)
    try
      -- Telescope since it might be a family of instances.
      forallTelescopeReducing expectedType fun xs expectedType => do
        mkLambdaFVars xs <| ← withNewMCtxDepth <| makeFastInstance inst expectedType
    catch e =>
      logException e
      return inst
  | _, _ => Elab.throwUnsupportedSyntax

/-- `inferInstanceAs% A` is shorthand for `fast_instance% inferInstanceAs A`.
This is preferred over `inferInstanceAs` when the instance can be reduced to
constructor applications. In that case, the parameters of the constructors will be filled in
using the expected type, so that the instance will unfold nicely during unification. -/
macro "inferInstanceAs% " source:term : term =>
  `(fast_instance% _root_.inferInstanceAs <| $source)

/-- Find the first data-field binder type mismatch between `inst` and `canonical`
(the constructor-normalized form from `makeFastInstance`). Returns
`(fieldName, some (actualBinderType, expectedBinderType))` for the first field where both forms
are lambdas with different binder types at instances transparency, or `(fieldName, none)` if a
mismatch is found but cannot be characterized as a binder type difference.
`className` is used to look up field names via `getStructureFields`; recursion uses the
constructor prefix as the nested class name. -/
private partial def findFirstBinderMismatch (className : Name) (inst canonical : Expr) :
    MetaM (Option (Name × Option (Expr × Expr))) := do
  let env ← getEnv
  let instWhnf ← withTransparency .instances <| whnf inst
  let canWhnf ← withTransparency .instances <| whnf canonical
  let instArgs := instWhnf.getAppArgs
  let canArgs := canWhnf.getAppArgs
  -- Field names for this class (empty if not a structure or unavailable).
  let fields := if isStructure env className then getStructureFields env className else #[]
  let numParams : Nat :=
    match env.find? (className ++ `mk) with
    | some (.ctorInfo ci) => ci.numParams
    | _ => 0
  -- Start from `numParams` to skip constructor parameters: they are shared between `inst`
  -- and `canonical` (both were built for the same `expectedType`), so any mismatch will be
  -- in a field position. Starting here also makes `i - numParams` safe (no underflow).
  for i in [numParams : min instArgs.size canArgs.size] do
    let instArg := instArgs[i]!
    let canArg := canArgs[i]!
    let same ← withNewMCtxDepth <| withTransparency .instances <| isDefEq instArg canArg
    unless same do
      let fieldIdx := i - numParams  -- safe: i ≥ numParams
      let fieldName : Name :=
        if h : fieldIdx < fields.size then fields[fieldIdx] else `_
      -- If both are lambdas, check for a binder type mismatch at this level.
      if let .lam _ instT _ _ := instArg then
        if let .lam _ canT _ _ := canArg then
          let sameT ← withNewMCtxDepth <| withTransparency .instances <| isDefEq instT canT
          unless sameT do
            return some (fieldName, some (instT, canT))
      -- Recurse into nested constructor sub-expressions (other instance fields).
      -- Identify the nested class from the argument's own constructor, not the outer one.
      let argWhnf ← withTransparency .instances <| whnf instArg
      let nestedClass : Name :=
        match argWhnf.getAppFn with
        | .const ctorName _ => ctorName.getPrefix
        | _ => .anonymous
      if let some result ← findFirstBinderMismatch nestedClass instArg canArg then
        return some result
      -- Fallback: we found a mismatch at this field but couldn't characterize it as a binder
      -- type difference (e.g., not a lambda, or binder types agree but bodies differ).
      return some (fieldName, none)
  return none

/-- Structured result of checking whether an instance has leaky data-field binder types. -/
public inductive CheckInstanceResult where
  /-- The instance is canonical: its data-field binder types match the class declaration. -/
  | canonical : CheckInstanceResult
  /-- The instance has leaky data-field binder types. `detail` describes the first detected
  field mismatch (if identified). -/
  | leaky (detail : MessageData) : CheckInstanceResult
  /-- The instance cannot be verified (e.g., the constant has no definition, or
  `fast_instance%` fails on it). `err` describes why. -/
  | unverifiable (err : MessageData) : CheckInstanceResult

/-- Format a `CheckInstanceResult` as `MessageData` for user display. -/
public def CheckInstanceResult.toMessageData (name : Name) : CheckInstanceResult → MessageData
  | .canonical =>
    m!"✅️ '{name}': canonical (re-inferred form agrees at instances transparency)"
  | .leaky detail =>
    m!"❌️ '{name}': leaky binder types detected.{detail}\n  \
      The `fast_instance%` elaborator may be useful as a repair or band-aid:\n  \
      `instance : ... := fast_instance% <body>`"
  | .unverifiable err =>
    m!"❌️ '{name}': cannot be verified (fast_instance% fails).\
      \n  {err}\
      \n  The `fast_instance%` elaborator may be useful as a repair or band-aid:\
      \n  `instance : ... := fast_instance% <body>`"

/--
Check whether a named instance has leaky data-field binder types.

An instance `foo : C args` is "canonical" if its body, when re-elaborated with the expected
type `C args`, would produce a definitionally equal term at `.instances` transparency.
If not, some data field (e.g. `smul`) has a binder type (e.g. `M`) that differs from the
expected type (e.g. `RestrictScalars R S M`) at instance transparency — a "leak" that causes
`rw` failures with `set_option backward.isDefEq.respectTransparency true`.

The check temporarily evicts `name` from the instance discrimination tree (as though we'd
run `attribute [-instance]`) and then uses constructor normalization to compute the
"canonical" form, comparing with the original at `.instances` transparency.
-/
public def checkInstance (name : Name) : MetaM CheckInstanceResult := do
  let env ← getEnv
  let some info := env.find? name
    | return .unverifiable m!"unknown constant '{name}'"
  let some _ := info.value?
    | return .unverifiable m!"'{name}' has no definition (it is an axiom or opaque)"
  -- Introduce the universally quantified type arguments as free variables,
  -- so we can check the instance in a concrete context.
  forallTelescope info.type fun xs expectedType => do
    let instVal := mkAppN (.const name (info.levelParams.map mkLevelParam)) xs
    -- Temporarily evict `name` from the instance discrimination tree so that
    -- `trySynthInstance` won't trivially find the instance being checked, then run
    -- constructor normalization to get the canonical form.
    -- If normalization fails (e.g. the instance doesn't reduce to a constructor application),
    -- that itself is a sign the instance is not in verifiable canonical form.
    let normalized ← try
        withDisabledInstance name <| withNewMCtxDepth <|
          makeFastInstance instVal expectedType
      catch e =>
        return .unverifiable e.toMessageData
    -- Compare at instances transparency. At this level, the instance unfolds to its body,
    -- and we compare the actual body against the re-inferred canonical form. If they agree,
    -- all data-field binder types are correct. If not, some data field (e.g. `smul`) has a
    -- binder type (e.g. `M`) that differs from the expected type (e.g. `RestrictScalars R S M`)
    -- at instances transparency — `RestrictScalars` is a `def`, not reducible/instance, so
    -- `M` and `RestrictScalars R S M` are not defeq at `.instances`.
    let isCanonical ← withTransparency .instances <| isDefEq instVal normalized
    if isCanonical then
      return .canonical
    else
      -- Try to find the first specific binder type mismatch to help diagnose the leak.
      let className ← isClass? expectedType
      let mismatch ← try
        match className with
        | some c => findFirstBinderMismatch c instVal normalized
        | none => pure none
        catch _ => pure none
      -- Eagerly pretty-print binder types while still in MetaM context so that any
      -- pp failure produces a graceful fallback instead of a raw "failed to pretty print" string.
      let detail : MessageData ← match mismatch with
        | some (field, some (actual, expected)) => do
          let actualStr : String ← try
              let fmt ← ppExpr actual
              pure fmt.pretty
            catch _ => pure "<unprintable>"
          let expectedStr : String ← try
              let fmt ← ppExpr expected
              pure fmt.pretty
            catch _ => pure "<unprintable>"
          pure m!"\n  The data field `{field}` has binder type {actualStr} \
            where {expectedStr} is expected.\n  Other data fields may also be leaky."
        | some (field, none) =>
          pure m!"\n  The data field `{field}` differs from the re-inferred canonical form \
            at instances transparency.\n  Other data fields may also be leaky."
        | none => pure "\n  The body differs from the re-inferred form at instances transparency."
      return .leaky detail

open Elab Command in
/--
`#check_instance foo` checks whether the instance `foo` has leaky data-field binder types.

An instance has leaky binder types when a data field (e.g. `smul`) uses a binder type
(e.g. `M`) that differs from the expected type (e.g. `RestrictScalars R S M`) at instance
transparency. This causes `rw` failures with `set_option backward.isDefEq.respectTransparency true`.

Reports `✅️` if canonical (the body already has the correct binder types) or `❌️` if leaky.
-/
elab "#check_instance " n:ident : command => do
  let name ← liftTermElabM <| resolveGlobalConstNoOverload n
  let result ← runTermElabM fun _ => checkInstance name
  logInfo (result.toMessageData name)

end Mathlib.Elab.FastInstance
