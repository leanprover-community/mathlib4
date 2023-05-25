/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
import Std.Tactic.TryThis

/-!
# The `variable!` command

This defines a command like `variable` that automatically adds all missing typeclass
arguments. For example, `variable! [Module R M]` is the same as
`variable [Semiring R] [AddCommMonoid M] [Module R M]`.

The `variable!?` command gives a "try this" suggestion for a complete `variable` command.
The `variable?` command relies on typeclass inference failure to decide to add new variables.
Failing typeclass inference can be slow, so `variable!?` can be used to save the result and
speed things up.
-/

namespace Mathlib.Command
open Lean Elab Command Parser.Term Meta

initialize registerTraceClass `variable!

register_option variable!.maxSteps : Nat :=
  { defValue := 15
    group := "variable!"
    descr :=
      "The maximum number of instance arguments `variable!` will try to insert before giving up" }

private def bracketedBinderType : Syntax → Option Term
  | `(bracketedBinderF|($_* $[: $ty?]? $(_annot?)?)) => ty?
  | `(bracketedBinderF|{$_* $[: $ty?]?})             => ty?
  | `(bracketedBinderF|⦃$_* $[: $ty?]?⦄)             => ty?
  | `(bracketedBinderF|[$[$_ :]? $ty])               => some ty
  | _                                                => none

/-- The `variable!` command has the same syntax as `variable`, but it will auto-insert
missing instance arguments wherever they are needed.
Warning: the command does not check that earlier variables aren't implied by later ones.

The `variable!?` variant suggests a completed `variable` command. -/
syntax (name := «variable!») "variable!" "?"? (ppSpace bracketedBinder)* : command

macro "variable!?" binders:bracketedBinder* : command => `(command| variable! ? $binders*)

/--
Attribute to record aliases for the `variable!` command. It should be placed on a structure.

Example:
```
@[variable_alias]
structure VectorSpace (k V : Type _)
  [Field k] [AddCommGroup V] [Module k V]
```
Then `variable! [VectorSpace k V]` ensures that these three typeclasses are present in
the current scope.

Notice that `VectorSpace` is not a class, but `variable!` allows non-classes with the
`variable_alias` attribute to use instance binders.
-/
initialize variableAliasAttr : TagAttribute ←
  registerTagAttribute `variable_alias "Attribute to record aliases for the `variable!` command."

/-- Find a synthetic typeclass metavariable with no expr metavariables in its type. -/
private def pendingActionableSynthMVar (binder : TSyntax `Lean.Parser.Term.bracketedBinder) :
    TermElabM (Option MVarId) := do
  let pendingMVars := (← get).pendingMVars
  if pendingMVars.isEmpty then
    return none
  for mvarId in pendingMVars.reverse do
    let some decl ← Term.getSyntheticMVarDecl? mvarId | continue
    match decl.kind with
    | .typeClass =>
      let ty ← instantiateMVars (← mvarId.getType)
      if !ty.hasExprMVar then
        return mvarId
    | _ => pure ()
  throwErrorAt binder "Can not satisfy requirements for {binder} due to metavariables."

/-- Try elaborating `ty`. Returns `none` if it doesn't need any additional typeclasses,
or it returns a new binder that needs to come first. Does not add info unless it throws
an exception. -/
private partial def getSubproblem
    (binder : TSyntax `Lean.Parser.Term.bracketedBinder) (ty : Term) :
    TermElabM (Option (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let res : Term.TermElabResult (Option (TSyntax `Lean.Parser.Term.bracketedBinder)) ←
    Term.observing do
    withTheReader Term.Context (fun ctx => {ctx with ignoreTCFailures := true}) do
    Term.withAutoBoundImplicit do
      _ ← Term.elabType ty
      Term.synthesizeSyntheticMVars (mayPostpone := true) (ignoreStuckTC := true)
      let fvarIds := (← getLCtx).getFVarIds
      if let some mvarId ← pendingActionableSynthMVar binder then
        trace[«variable!»] "Actionable mvar:{mvarId}"
        -- TODO alter goal based on configuration, for example Semiring -> CommRing
        -- Find the new fvars that this instance problem depends on
        let fvarIds' := (← mvarId.getDecl).lctx.getFVarIds.filter
                          (fun fvar => !(fvarIds.contains fvar))
        -- Abstract the instance problem with respect to these fvars
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
`i` is the index of the next binder that needs to be checked.

The `toOmit` array keeps track of which binders should be removed at the end,
in particular the `variable_alias` binders. -/
private partial def completeBinders (maxSteps : Nat) (gas : Nat)
    (binders : TSyntaxArray `Lean.Parser.Term.bracketedBinder)
    (toOmit : Array Bool) (i : Nat) :
    TermElabM (TSyntaxArray `Lean.Parser.Term.bracketedBinder × Array Bool) := do
  if 0 < gas && i < binders.size then
    let binder := binders[i]!
    trace[«variable!»]
      "Have {(← getLCtx).getFVarIds.size} fvars and {(← getLocalInstances).size} local instances{
      ""}. Looking at{indentD binder}"
    if let some binder' ← getSubproblem binder (bracketedBinderType binder).get! then
      trace[«variable!»] m!"new subproblem:{indentD binder'}"
      if binders.contains binder' then
        throwErrorAt binder "Binder{indentD binder}\nproposes adding{indentD binder'}\nbut it is {
          ""}already present. {
          ""}This can either be due to the proposed binder occurring later as a variable or due to {
          ""}instance inference failure.\n\n{
          ""}Current binder list:{indentD (← `(command| variable! $binders*))}"
      let binders := binders.insertAt! i binder'
      completeBinders maxSteps (gas - 1) binders toOmit i
    else
      withOptions (fun opts => Term.checkBinderAnnotations.set opts false) <| -- for variable_alias
      Term.withAutoBoundImplicit <|
      Term.elabBinders #[binder] fun bindersElab => do
        let types : Array Expr ← bindersElab.mapM (inferType ·)
        trace[«variable!»] m!"elaborated binder types array = {types}"
        Term.synthesizeSyntheticMVarsNoPostponing -- checkpoint for withAutoBoundImplicit
        Term.withoutAutoBoundImplicit do
        let (binders, toOmit) := ← do
          match binder with
          | `(bracketedBinderF|[$[$ident? :]? $ty]) =>
            -- Check if it's an alias
            let type ← instantiateMVars (← inferType bindersElab[bindersElab.size - 1]!)
            if ← isAlias type then
              if ident?.isSome then
                throwErrorAt binder "`variable_alias` binders can't have an explicit name"
              -- Switch to implicit so that `elabBinders` succeeds.
              -- We keep it around so that it gets infotrees
              let binder' ← withRef binder `(bracketedBinderF|{_ : $ty})
              return (binders.set! i binder', toOmit.push true)
            return (binders, toOmit.push false)
          | _ => return (binders, toOmit.push false)
        completeBinders maxSteps gas binders toOmit (i + 1)
  else
    if gas == 0 && i < binders.size then
      logErrorAt binders[i]! m!"Maximum recursion depth for variables! reached. This might be a {
        ""}bug, or you can try adjusting `set_option variable!.maxSteps {maxSteps}`."
    return (binders, toOmit)
where
  isAlias (type : Expr) : MetaM Bool := do
    forallTelescope type fun _ type => do
      if let some name := type.getAppFn.constName? then
        if variableAliasAttr.hasTag (← getEnv) name then
          return true
      return false

/--
Like `variable` but inserts missing typeclasses automatically as extra variables.
Use `variable!?` to see an equivalent `variable` command.

Structures tagged with the `variable_alias` attribute can serve as aliases for a collection
of typeclasses. For example, given
```lean
@[variable_alias]
structure VectorSpace (k V : Type _)
  [Field k] [AddCommGroup V] [Module k V]
```
then `variable!? [VectorSpace k V]` is
equivalent to `variable {k V : Type _} [Field k] [AddCommGroup V] [Module k V]`.
Note that this is not a simple replacement: it will only add new instances given the
current scope.

Unlike `variable`, the `variable!` command does not support changing variable binder types.
-/
@[command_elab «variable!»] def elabVariables : CommandElab := fun stx =>
  match stx with
  | `(variable! $[?%$info]? $binders*) => do
    let maxSteps := Mathlib.Command.variable!.maxSteps.get (← getOptions)
    trace[«variable!»] "variable!.maxSteps = {maxSteps}"
    for binder in binders do
      if (bracketedBinderType binder).isNone then
        throwErrorAt binder "variable! cannot update pre-existing variables"
    let (binders, toOmit) ← runTermElabM fun _ => completeBinders maxSteps maxSteps binders #[] 0
    -- Elaborate the binders again, which also adds the infotrees.
    runTermElabM fun _ => Term.withAutoBoundImplicit <| Term.elabBinders binders fun _ => pure ()
    -- Filter out omitted binders and then add the remaining binders to the scope
    let binders' := (binders.zip toOmit).filterMap (fun (b, omit) => if omit then none else some b)
    let varComm ← `(command| variable $binders'*)
    trace[«variable!»] "derived{indentD varComm}"
    if info.isSome then
      liftTermElabM <| Std.Tactic.TryThis.addSuggestion stx (origSpan? := stx) varComm
    for binder in binders' do
      let varUIds ← getBracketedBinderIds binder |>.mapM
        (withFreshMacroScope ∘ MonadQuotation.addMacroScope)
      modifyScope fun scope =>
        { scope with varDecls := scope.varDecls.push binder, varUIds := scope.varUIds ++ varUIds }
  | _ => throwUnsupportedSyntax

end Mathlib.Command

/-- Hint for the unused variables linter. Copies the one for `variable`. -/
@[unused_variables_ignore_fn]
def ignoreVariable! : Lean.Linter.IgnoreFunction := fun _ stack _ =>
  stack.matches [`null, none, `null, `Mathlib.Command.variable!]
