/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kyle Miller, Jovan Gerbscheid
-/
module

public import Mathlib.Init

/-!
# The `fast_instance%` and `inferInstanceAs%` term elaborators
-/

meta section

namespace Mathlib.Elab.FastInstance

open Lean Meta Elab Term

initialize registerTraceClass `Elab.fast_instance

/-- Show a warning if `fast_instance%` can be replaced with `inferInstance`. -/
register_option linter.fast_instance_existing : Bool := {
  defValue := true
  descr := "Show a warning if `fast_instance%` can be replaced with `inferInstance`." }

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

/--
Core algorithm for normalizing instances.
* Ideally, the term is replaced with a synthesized instance.
* If not, it is reduced to a constructor
  and each instance implicit field is given the same treatment.

Many reductions for typeclasses are done with reducible transparency, so the entire body
is `withReducible` with some exceptions.
-/
partial def makeFastInstance (inst expectedType : Expr) (root := true) (trace : Array Name := #[]) :
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
  if let .some new ← trySynthInstance expectedType then
    if root then
      Linter.logLintIf linter.fast_instance_existing (← getRef) m!"\
        An instance of `{expectedType}` already exists.\n\
        Please use `inferInstance` instead of `fast_instance%`"
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
      -- Recurse into instance arguments of the constructor
      else if bi.isInstImplicit then
        let trace' := trace.push (className ++ mvarDecl.userName)
        mvarId.assign (← makeFastInstance arg argExpectedType (root := false) (trace := trace'))
      else
        -- For data fields, make sure that the lambda binders have the right type.
        mvarId.assign <| ← forallTelescopeReducing argExpectedType fun xs _ ↦ do
          mkLambdaFVars xs <| ← withReducibleAndInstances <|
            transform (mkAppN arg xs) (pre := fun e ↦ return .continue (← whnf e))
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

end Mathlib.Elab.FastInstance
