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
`variable [Semiring R] [AddCommMonoid M] [Module R M]`. If any of these three instance arguments
can be inferred from previous variables then they will be omitted.

An inherent limitation with this command is that variables are recorded in the scope as
*syntax*. This means that `variable!` needs to pretty print the expressions we get
from typeclass synthesis errors, and these might fail to round trip.
-/

namespace Mathlib.Command
open Lean Elab Command Parser.Term Meta

initialize registerTraceClass `variable!

register_option variable!.maxSteps : Nat :=
  { defValue := 15
    group := "variable!"
    descr :=
      "The maximum number of instance arguments `variable!` will try to insert before giving up" }

register_option variable!.checkRedundant : Bool :=
  { defValue := true
    group := "variable!"
    descr := "Warn if instance arguments can be inferred from preceding ones" }

/-- Get the type out of a bracketed binder. -/
private def bracketedBinderType : Syntax → Option Term
  | `(bracketedBinderF|($_* $[: $ty?]? $(_annot?)?)) => ty?
  | `(bracketedBinderF|{$_* $[: $ty?]?})             => ty?
  | `(bracketedBinderF|⦃$_* $[: $ty?]?⦄)             => ty?
  | `(bracketedBinderF|[$[$_ :]? $ty])               => some ty
  | _                                                => none

/-- The basic `variable!` command has the same syntax as `variable`, but it will auto-insert
missing instance arguments wherever they are needed.
Warning: the command does not check that earlier variables aren't implied by later ones.

The `variable! binders => binders'` command is the same as `variable binders'`. The `binders'`
are meant to be the completed list of `binders` without any missing instances.
When the `=> binders'` clause is not present, then `variable!` suggests a completion.
The purpose of this is to cache the sometimes slow computation.

The `variable!?` variant checks that the `binders'` clause is exactly what was inferred.
It can also be used to recompute the cache. -/
syntax (name := «variable!») "variable!" "?"? (ppSpace bracketedBinder)*
  (" => " ppLine (ppSpace bracketedBinder)*)? : command

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
private def pendingActionableSynthMVar (binder : TSyntax ``bracketedBinder) :
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
    TermElabM (Option (MessageData × TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let res : Term.TermElabResult (Option (MessageData × TSyntax `Lean.Parser.Term.bracketedBinder)) ←
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
        return some (← addMessageContext m!"{mvarId}", binder')
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
    let sub? ← getSubproblem binder (bracketedBinderType binder).get!
    if let some (goalMsg, binder') := sub? then
      trace[«variable!»] m!"new subproblem:{indentD binder'}"
      if binders.any (stop := i) (· == binder') then
        let binders' := binders.extract 0 i
        throwErrorAt binder
          "Binder{indentD binder}\nwas not able to satisfy one of its dependencies using {
          ""}the pre-existing binder{indentD binder'}\n\n{
          ""}This might be due to differences in implicit arguments, which are not represented {
          ""}in binders since they are generated by pretty printing unsatisfied dependencies.\n\n{
          ""}Current variable command:{indentD (← `(command| variable $binders'*))}\n\n{
          ""}Local context for the unsatisfied dependency:{goalMsg}"
      let binders := binders.insertAt! i binder'
      completeBinders maxSteps (gas - 1) binders toOmit i
    else
      let lctx ← getLCtx
      let linst ← getLocalInstances
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
            let type ← instantiateMVars (← inferType bindersElab.back)
            if ← isVariableAlias type then
              if ident?.isSome then
                throwErrorAt binder "`variable_alias` binders can't have an explicit name"
              -- Switch to implicit so that `elabBinders` succeeds.
              -- We keep it around so that it gets infotrees
              let binder' ← withRef binder `(bracketedBinderF|{_ : $ty})
              return (binders.set! i binder', toOmit.push true)
            -- Check that this wasn't already an instance
            if variable!.checkRedundant.get (← getOptions) then
              let res ← try withLCtx lctx linst <| trySynthInstance type catch _ => pure .none
              if let .some _ := res then
                let mvar ← mkFreshExprMVarAt lctx linst type
                logWarningAt binder
                  m!"Instance argument can be inferred from earlier arguments.{mvar.mvarId!}"
            return (binders, toOmit.push false)
          | _ => return (binders, toOmit.push false)
        completeBinders maxSteps gas binders toOmit (i + 1)
  else
    if gas == 0 && i < binders.size then
      let binders' := binders.extract 0 i
      logErrorAt binders[i]! m!"Maximum recursion depth for variables! reached. This might be a {
        ""}bug, or you can try adjusting `set_option variable!.maxSteps {maxSteps}`{
        ""}\n\nCurrent variable command:{indentD (← `(command| variable $binders'*))}"
    return (binders, toOmit)
where
  isVariableAlias (type : Expr) : MetaM Bool := do
    forallTelescope type fun _ type => do
      if let .const name _ := type.getAppFn then
        if variableAliasAttr.hasTag (← getEnv) name then
          return true
      return false

/-- Strip off whitespace and comments. -/
def cleanBinders (binders : TSyntaxArray ``bracketedBinder) :
    TSyntaxArray ``bracketedBinder := Id.run do
  let mut binders' := #[]
  for binder in binders do
    binders' := binders'.push <| ⟨binder.raw.unsetTrailing⟩
  return binders'

/--
Like `variable` but inserts missing instances automatically as extra variables.
It does not add variables that can already be deduced from others in the current context.
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
  | `(variable! $_* => $binders*) => do
    elabCommand <| ← `(variable $binders*)
  | `(variable! $[?%$info]? $binders*) => do
    let maxSteps := variable!.maxSteps.get (← getOptions)
    trace[«variable!»] "variable!.maxSteps = {maxSteps}"
    let binders := cleanBinders binders
    for binder in binders do
      if (bracketedBinderType binder).isNone then
        throwErrorAt binder "variable! cannot update pre-existing variables"
    let (binders, toOmit) ← runTermElabM fun _ => completeBinders maxSteps maxSteps binders #[] 0
    -- Elaborate the binders again, which also adds the infotrees.
    -- This also makes sure the list works with auto-bound implicits at the front.
    runTermElabM fun _ => Term.withAutoBoundImplicit <| Term.elabBinders binders fun _ => pure ()
    -- Filter out omitted binders and then add the remaining binders to the scope
    let binders' := (binders.zip toOmit).filterMap (fun (b, omit) => if omit then none else some b)
    let varComm ← `(command| variable! $binders* => $binders'*)
    trace[«variable!»] "derived{indentD varComm}"
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
