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
open Lean Lean.Elab Lean.Elab.Command Lean.Parser.Term

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
Then `variables! [VectorSpace k V]` introduces these three typeclasses.
-/
initialize variableAliasAttr : TagAttribute ←
 registerTagAttribute `variable_alias
  "Attribute to record aliases for the `variable!` command."

/-- Tries elaborating binders, inserting new binders whenever typeclass inference fails.
`i` is the index of the next binder that needs to be checked. -/
private partial def completeBinders (gas : Nat)
    (binders : TSyntaxArray `Lean.Parser.Term.bracketedBinder)
    (toOmit : Array Bool) (i : Nat) :
    CommandElabM (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
  if 0 < gas && i < binders.size then
    -- Try elaborating the binders so far and see if they create any pending metavariables.
    let info ← getInfoState
    -- TODO this algorithm has quadratic complexity. It doesn't need to be this way, since
    -- we can commit to binders eventually.
    let (newBinders, omitLast) ← runTermElabM fun _ => do
      withTheReader Term.Context (fun ctx => {ctx with ignoreTCFailures := true})
      <| withOptions (fun opts => Term.checkBinderAnnotations.set opts false) -- for aliases
      <| Term.withAutoBoundImplicit
      <| Term.withSynthesize (mayPostpone := true)
      <| Term.elabBinders (binders.extract 0 (i + 1)) fun bindersElab => do
        let mut binders' := #[]
        let pendingSet : MVarIdSet := (← get).pendingMVars.foldl MVarIdSet.insert RBMap.empty
        for mvarId in (← get).pendingMVars.reverse do
          let some decl ← Term.getSyntheticMVarDecl? mvarId | continue
          match decl.kind with
          | .typeClass =>
            let ty ← instantiateMVars (← mvarId.getType)
            -- Only want to consider those that don't have natural metavariables, which helps
            -- prevent infinite regress.
            let nonSynthMVar? := ty.findMVar? fun mvar => not (RBMap.contains pendingSet mvar)
            if nonSynthMVar?.isNone then
              let bi ← `(bracketedBinderF| [$(← PrettyPrinter.delab ty)])
              binders' := binders'.push bi
          | _ => pure ()
        -- Is the last elaborated binder tagged with `variableAliasAttr`?
        let skipLast : Bool ← do
          if bindersElab.isEmpty then
            pure false
          else
            let last ← instantiateMVars (← Meta.inferType bindersElab[bindersElab.size - 1]!)
            if let some name := last.getAppFn.constName? then
              pure <| variableAliasAttr.hasTag (← getEnv) name
            else
              pure false
        return (binders', skipLast)
    setInfoState info
    if newBinders.isEmpty then
      let mut binders := binders
      if omitLast then
        -- Switch instance implicit for the omitted binder to anything else
        -- for elaboration (and info) purposes. This binder will eventually be omitted anyway.
        binders ← binders.modifyM i fun binder => withRef binder <|
                    match binder with
                    | `(bracketedBinderF|[$i : $ty]) => `(bracketedBinderF|{$i : $ty})
                    | `(bracketedBinderF|[$ty])      => `(bracketedBinderF|{_ : $ty})
                    | binder => pure binder
      completeBinders gas binders (toOmit.push omitLast) (i + 1)
    else
      let binders := binders.extract 0 i ++ newBinders ++ binders.extract i binders.size
      completeBinders (gas - newBinders.size) binders toOmit i
  else
    if gas == 0 then
      logError "Maximum recursion depth for variables! reached, likely due to a bug."
    -- One last check with the correct configuration.
    runTermElabM fun _ => Term.withAutoBoundImplicit <| Term.elabBinders binders fun _ => pure ()
    let mut binders' := #[]
    for binder in binders, omit in toOmit do
      if not omit then
        binders' := binders'.push binder
    return binders'

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
    let binders' ← completeBinders 10 binders #[] 0
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
