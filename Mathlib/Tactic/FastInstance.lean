/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kyle Miller
-/

import Lean.Elab.SyntheticMVars
import Lean
import Mathlib.Init
/-!
# The `fast_instance%` term elaborator
-/

namespace Mathlib.Elab.FastInstance

open Lean Meta Elab Term

initialize registerTraceClass `Elab.fast_instance

/--
Throw an error for `makeFastInstance`. The trace is a list of fields.
Note: with the current implementation, this might not be accurate for multi-structure types,
since `makeFastInstance` just uses `ClassName.paramName` for the trace.
-/
private def error {α : Type _} (trace : Array Name) (m : MessageData) : MetaM α :=
  throwError "\
    {m}\n\n\
    Use `set_option trace.Elab.fast_instance true` to analyze the error.\n\n\
    Trace of fields visited: {trace}"

/--
Core algorithm for normalizing instances.
* Ideally, the term is replaced with a synthesized instance.
* If not, it is reduced to a constructor
  and each instance implicit field is given the same treatment.
  If the type is a structure, the algorithm throws an error;
  we're more lenient with non-structure classes.

Many reductions for typeclasses are done with reducible transparency, so the entire body
is `withReducible` with some exceptions.
-/
private partial def makeFastInstance (provided : Expr) (trace : Array Name := #[]) :
    MetaM Expr := withReducible do
  let ty ← inferType provided
  withTraceNode `Elab.fast_instance (fun e => return m!"{exceptEmoji e} type: {ty}") do
  let .some className ← isClass? ty
    | error trace m!"Can only be used for classes, but term has type{indentExpr ty}"
  trace[Elab.fast_instance] "class is {className}"
  if ← withDefault <| Meta.isProp ty then
    error trace m!"\
      Provided instance{indentExpr provided}\n\
      is a proof, which does not need normalization."

  -- Try to synthesize a total replacement for this term:
  if let .some new ← trySynthInstance ty then
    if ← withReducibleAndInstances <| isDefEq provided new then
      trace[Elab.fast_instance] "replaced with synthesized instance"
      return new
    else
      if ← withDefault <| isDefEq provided new then
        error trace m!"\
          Provided instance{indentExpr provided}\n\
          is defeq only at default transparency to inferred instance{indentExpr new}"
      else
        error trace m!"\
          Provided instance{indentExpr provided}\n\
          is not defeq to inferred instance{indentExpr new}"
  -- Otherwise, try to reduce it to a constructor.
  else
    -- Telescope since it might be a family of instances.
    forallTelescopeReducing ty fun tyArgs _ => do
      let provided' ← withReducibleAndInstances <| whnf <| mkAppN provided tyArgs
      let error' (m : MessageData) : MetaM Expr := do
        if isStructure (← getEnv) className then
          error trace m
        else
          error trace m!"{m}\n\n\
            This instance is not a structure and not canonical. \
            Use a separate 'instance' command to define it."
      let .const c .. := provided'.getAppFn
        | error' m!"\
            Provided instance does not reduce to a constructor application{indentExpr provided}"
      let some (.ctorInfo ci) := (← getEnv).find? c
        | error' m!"\
            Provided instance does not reduce to a constructor application{indentExpr provided}\n\
            Reduces to an application of {c}."
      let mut args := provided'.getAppArgs
      let params ← withDefault <| forallTelescopeReducing ci.type fun args _ =>
        args.mapM fun arg => do
          let recurse ← (return (← arg.fvarId!.getBinderInfo).isInstImplicit)
                        <&&> not <$> Meta.isProof arg
          return (recurse, ← arg.fvarId!.getUserName)
      unless args.size == params.size do
        -- This is an invalid term.
        throwError "Incorrect number of arguments for constructor application{indentExpr provided'}"
      for i in [ci.numParams:args.size] do
        let (recurse, binderName) := params[i]!
        if recurse then
          let trace' := trace.push (className ++ binderName)
          args := args.set! i (← makeFastInstance args[i]! (trace := trace'))
      let provided' := mkAppN provided'.getAppFn args
      mkLambdaFVars tyArgs provided'

/--
`fast_instance% inst` takes an expression for a typeclass instance `inst`, and unfolds it into
constructor applications that leverage existing instances.

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
syntax (name := fastInstance) "fast_instance%" term : term

@[term_elab fastInstance, inherit_doc fastInstance]
def elabFastInstance : TermElab
  | `(term| fast_instance%%$tk $arg), expectedType => do
    let provided ← withSynthesize <| elabTerm arg expectedType
    withRef tk do
      try
        makeFastInstance provided
      catch e =>
        logException e
        return provided
  | _, _ => Elab.throwUnsupportedSyntax

end Mathlib.Elab.FastInstance
