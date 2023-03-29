/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean

/-!
# The `variable!` command

This defines a command like `variable` that automatically adds all missing typeclass
arguments. For example, `variable! [Module R M]` is the same as
`variable [Semiring R] [AddCommMonoid M] [Module R M]`.
-/

namespace Mathlib.Command
open Lean Lean.Elab Lean.Elab.Command Lean.Parser.Term Lean.Meta

initialize registerTraceClass `variable!

private def bracketedBinderType : Syntax → Option (TSyntax `term)
  | `(bracketedBinderF|($_* $[: $ty?]? $(_annot?)?)) => ty?
  | `(bracketedBinderF|{$_* $[: $ty?]?})             => ty?
  | `(bracketedBinderF|⦃$_* $[: $ty?]?⦄)             => ty?
  | `(bracketedBinderF|[$[$_ :]? $ty])               => some ty
  | _                                                => none

syntax (name := «variable!») "variable!" "?"? (bracketedBinder)* : command
macro "variable!?" binders:bracketedBinder* : command => `(command| variable! ? $binders*)

/--
Attribute to record aliases for the `variable!` command. It should be placed on a structure.

Example:
```
@[variable_alias]
structure VectorSpace (k V : Type _)
  [Field k] [AddCommGroup V] [Module k V]
```
Then `variable! [VectorSpace k V]` introduces these three typeclasses.
-/
initialize variableAliasAttr : TagAttribute ←
  registerTagAttribute `variable_alias "Attribute to record aliases for the `variable!` command."

/-- Find a synthetic typeclass metavariable with no metavariables in its type. -/
private def pendingActionableSynthMVar (binder : TSyntax `Lean.Parser.Term.bracketedBinder) :
    TermElabM (Option MVarId) := do
  let pendingMVars := (← get).pendingMVars
  if pendingMVars.isEmpty then
    return none
  for mvarId in pendingMVars.reverse do
    let some decl ← Term.getSyntheticMVarDecl? mvarId | continue
    match decl.kind with
    | .typeClass =>
      let mvars ← getMVars (← mvarId.getType)
      if mvars.isEmpty then
        return mvarId
    | _ => pure ()
  throwErrorAt binder "Can not satisfy requirements for {binder} due to metavariables."

/-- Try elaborating `ty`. Returns `none` if it doesn't need any additional typeclasses,
or it returns a new binder that needs to come first. Does not add info unless it throws
an error. -/
private partial def getSubproblem
    (binder : TSyntax `Lean.Parser.Term.bracketedBinder) (ty : TSyntax `term) :
    TermElabM (Option (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let res : Term.TermElabResult (Option (TSyntax `Lean.Parser.Term.bracketedBinder)) ←
    Term.observing do
    withTheReader Term.Context (fun ctx => {ctx with ignoreTCFailures := true}) do
    Term.withAutoBoundImplicit do
      _ ← Term.elabType ty
      Term.synthesizeSyntheticMVars (mayPostpone := true) (ignoreStuckTC := true)
      let fvarIds := (← getLCtx).getFVarIds
      if let some mvarId ← pendingActionableSynthMVar binder then
        let fvarIds' := (← mvarId.getDecl).lctx.getFVarIds.filter
                          (fun fvar => not (fvarIds.contains fvar))
        -- TODO alter goal based on configuration, for example Semiring -> CommRing
        let goal ← mvarId.withContext do instantiateMVars <|
                    (← mkForallFVars (usedOnly := true) (fvarIds'.map .fvar) (← mvarId.getType))
        -- Note: this is not guaranteed to round-trip, but it's what we can do.
        let ty' ← PrettyPrinter.delab goal
        let binder' ← withRef binder `(bracketedBinderF| [$ty'])
        return some binder'
      else
        return none
  match res with
  | .ok v _ => return v
  | .error .. => Term.applyResult res

/-- Tries elaborating binders, inserting new binders whenever typeclass inference fails.
`i` is the index of the next binder that needs to be checked. -/
private partial def completeBinders (gas : Nat)
    (binders : TSyntaxArray `Lean.Parser.Term.bracketedBinder)
    (toOmit : Array Bool) (i : Nat) :
    TermElabM (TSyntaxArray `Lean.Parser.Term.bracketedBinder × Array Bool) := do
  if 0 < gas && i < binders.size then
    let binder := binders[i]!
    trace[«variable!»]
      "looking at {binder} ({(← getLCtx).getFVarIds.size}, {(← getLocalInstances).size})"
    if let some binder' ← getSubproblem binder (bracketedBinderType binder).get! then
      trace[«variable!»] m!"new subproblem {binder'}"
      if binders.contains binder' then
        throwErrorAt binder "Binder {binder} proposes adding {binder'} but it is already present. {
          ""}This can either be due to {binder'} occurring later as a variable or due to {
          ""}instance inference failure."
      let binders := binders.insertAt! i binder'
      completeBinders (gas - 1) binders toOmit i
    else
      withOptions (fun opts => Term.checkBinderAnnotations.set opts false) <| -- for aliases
      Term.withAutoBoundImplicit <|
      Term.elabBinders #[binder] fun bindersElab => do
        let types : Array Expr ← bindersElab.mapM (inferType ·)
        trace[«variable!»] m!"elaborated binder types: {types}"
        Term.synthesizeSyntheticMVarsNoPostponing -- checkpoint for withAutoBoundImplicit
        Term.withoutAutoBoundImplicit do
        let (binders, toOmit) := ← do
          match binder with
          | `(bracketedBinderF|[$[$ident? :]? $ty]) =>
            -- Check if it's an alias
            let type ← instantiateMVars (← inferType bindersElab[bindersElab.size - 1]!)
            if let some name := type.getAppFn.constName? then
              if variableAliasAttr.hasTag (← getEnv) name then
                if ident?.isSome then
                  throwErrorAt binder "Variable aliases can't have an explicit name"
                -- switch to implicit so that it passes a full `elabBinders`.
                let binder' ← withRef binder `(bracketedBinderF|{_ : $ty})
                return (binders.set! i binder', toOmit.push true)
            return (binders, toOmit.push false)
          | _ => return (binders, toOmit.push false)
        completeBinders gas binders toOmit (i + 1)
  else
    if gas == 0 && i < binders.size then
      logErrorAt binders[i]! "Maximum recursion depth for variables! reached, likely due to a bug."
    return (binders, toOmit)

/--
Like `variable` but inserts missing typeclasses automatically as extra variables.
Use `variable!?` to see an equivalent `variable` command.

Structures tagged with the `variable_alias` attribute can serve as aliases for a collection
of typeclasses. For example, `variable!? [VectorSpace k V]` is
equivalent to `variable {k V : Type _} [Field k] [AddCommGroup V] [Module k V]` given
```lean
@[variable_alias]
structure VectorSpace (k V : Type _)
  [Field k] [AddCommGroup V] [Module k V]
```

Unlike `variable`, the `variable!` command will not change binder types for variables.
-/
@[command_elab «variable!»] def elabVariables : CommandElab
  | `(variable! $[?%$info]? $binders*) => do
    for binder in binders do
      if (bracketedBinderType binder).isNone then
        throwErrorAt binder "variable! cannot update pre-existing variables"
    let (binders, toOmit) ← runTermElabM fun _ => do completeBinders 10 binders #[] 0
    -- One last check with the correct configuration, which also adds info.
    runTermElabM fun _ => Term.withAutoBoundImplicit <| Term.elabBinders binders fun _ => pure ()
    let binders' := (binders.zip toOmit).filterMap (fun (b, omit) => if omit then none else some b)
    if info.isSome then
      logInfo m!"Try this: {← `(variable $binders'*)}"
    for binder in binders' do
      let varUIds ← getBracketedBinderIds binder |>.mapM
        (withFreshMacroScope ∘ MonadQuotation.addMacroScope)
      modifyScope fun scope =>
        { scope with varDecls := scope.varDecls.push binder, varUIds := scope.varUIds ++ varUIds }
  | _ => throwUnsupportedSyntax

end Mathlib.Command

/-- Hint for the unused variables linter. -/
-- TODO: why is this not registering in other modules? Is it because it's a builtin attribute?
@[unused_variables_ignore_fn]
def ignoreVariable! : Lean.Linter.IgnoreFunction :=
  fun _ stack _ => stack.matches [`null, none, `null, `Mathlib.Command.variable!]
