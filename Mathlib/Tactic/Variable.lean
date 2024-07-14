/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Meta.Tactic.TryThis

/-!
# The `variable?` command

This defines a command like `variable` that automatically adds all missing typeclass
arguments. For example, `variable? [Module R M]` is the same as
`variable [Semiring R] [AddCommMonoid M] [Module R M]`, though if any of these three instance
arguments can be inferred from previous variables then they will be omitted.

An inherent limitation with this command is that variables are recorded in the scope as
*syntax*. This means that `variable?` needs to pretty print the expressions we get
from typeclass synthesis errors, and these might fail to round trip.
-/

namespace Mathlib.Command.Variable
open Lean Elab Command Parser.Term Meta

initialize registerTraceClass `variable?

register_option variable?.maxSteps : Nat :=
  { defValue := 15
    group := "variable?"
    descr :=
      "The maximum number of instance arguments `variable?` will try to insert before giving up" }

register_option variable?.checkRedundant : Bool :=
  { defValue := true
    group := "variable?"
    descr := "Warn if instance arguments can be inferred from preceding ones" }

/-- Get the type out of a bracketed binder. -/
def bracketedBinderType : Syntax → Option Term
  | `(bracketedBinderF|($_* $[: $ty?]? $(_annot?)?)) => ty?
  | `(bracketedBinderF|{$_* $[: $ty?]?})             => ty?
  | `(bracketedBinderF|⦃$_* $[: $ty?]?⦄)             => ty?
  | `(bracketedBinderF|[$[$_ :]? $ty])               => some ty
  | _                                                => none

/-- The `variable?` command has the same syntax as `variable`, but it will auto-insert
missing instance arguments wherever they are needed.
It does not add variables that can already be deduced from others in the current context.
By default the command checks that variables aren't implied by earlier ones, but it does *not*
check that earlier variables aren't implied by later ones.
Unlike `variable`, the `variable?` command does not support changing variable binder types.

The `variable?` command will give a suggestion to replace itself with a command of the form
`variable? ...binders... => ...binders...`.  The binders after the `=>` are the completed
list of binders. When this `=>` clause is present, the command verifies that the expanded
binders match the post-`=>` binders.  The purpose of this is to help keep code that uses
`variable?` resilient against changes to the typeclass hierarchy, at least in the sense
that this additional information can be used to debug issues that might arise.
One can also replace `variable? ...binders... =>` with `variable`.

The core algorithm is to try elaborating binders one at a time, and whenever there is a
typeclass instance inference failure, it synthesizes binder syntax for it and adds it to
the list of binders and tries again, recursively. There are no guarantees that this
process gives the "correct" list of binders.

Structures tagged with the `variable_alias` attribute can serve as aliases for a collection
of typeclasses. For example, given
```lean
@[variable_alias]
structure VectorSpace (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
```
then `variable? [VectorSpace k V]` is
equivalent to `variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]`, assuming
that there are no pre-existing instances on `k` and `V`.
Note that this is not a simple replacement: it only adds instances not inferrable
from others in the current scope.

A word of warning: the core algorithm depends on pretty printing, so if terms that appear
in binders do not round trip, this algorithm can fail. That said, it has some support
for quantified binders such as `[∀ i, F i]`. -/
syntax (name := «variable?»)
  "variable?" (ppSpace bracketedBinder)* (" =>" (ppSpace bracketedBinder)*)? : command

/--
Attribute to record aliases for the `variable?` command. Aliases are structures that have no
fields, and additional typeclasses are recorded as *arguments* to the structure.

Example:
```
@[variable_alias]
structure VectorSpace (k V : Type*)
  [Field k] [AddCommGroup V] [Module k V]
```
Then `variable? [VectorSpace k V]` ensures that these three typeclasses are present in
the current scope. Notice that it's looking at the arguments to the `VectorSpace` type
constructor. You should not have any fields in `variable_alias` structures.

Notice that `VectorSpace` is not a class; the `variable?` command allows non-classes with the
`variable_alias` attribute to use instance binders.
-/
initialize variableAliasAttr : TagAttribute ←
  registerTagAttribute `variable_alias "Attribute to record aliases for the `variable?` command."

/-- Find a synthetic typeclass metavariable with no expr metavariables in its type. -/
def pendingActionableSynthMVar (binder : TSyntax ``bracketedBinder) :
    TermElabM (Option MVarId) := do
  let pendingMVars := (← get).pendingMVars
  if pendingMVars.isEmpty then
    return none
  for mvarId in pendingMVars.reverse do
    let some decl ← Term.getSyntheticMVarDecl? mvarId | continue
    match decl.kind with
    | .typeClass _ =>
      let ty ← instantiateMVars (← mvarId.getType)
      if !ty.hasExprMVar then
        return mvarId
    | _ => pure ()
  throwErrorAt binder "Can not satisfy requirements for {binder} due to metavariables."

/-- Try elaborating `ty`. Returns `none` if it doesn't need any additional typeclasses,
or it returns a new binder that needs to come first. Does not add info unless it throws
an exception. -/
partial def getSubproblem
    (binder : TSyntax ``bracketedBinder) (ty : Term) :
    TermElabM (Option (MessageData × TSyntax ``bracketedBinder)) := do
  let res : Term.TermElabResult (Option (MessageData × TSyntax ``bracketedBinder)) ←
    Term.observing do
    withTheReader Term.Context (fun ctx => {ctx with ignoreTCFailures := true}) do
    Term.withAutoBoundImplicit do
      _ ← Term.elabType ty
      Term.synthesizeSyntheticMVars (postpone := .yes) (ignoreStuckTC := true)
      let fvarIds := (← getLCtx).getFVarIds
      if let some mvarId ← pendingActionableSynthMVar binder then
        trace[«variable?»] "Actionable mvar:{mvarId}"
        -- TODO alter goal based on configuration, for example Semiring -> CommRing.
        -- 1. Find the new fvars that this instance problem depends on:
        let fvarIds' := (← mvarId.getDecl).lctx.getFVarIds.filter
                          (fun fvar => !(fvarIds.contains fvar))
        -- 2. Abstract the instance problem with respect to these fvars
        let goal ← mvarId.withContext do instantiateMVars <|
                    (← mkForallFVars (usedOnly := true) (fvarIds'.map .fvar) (← mvarId.getType))
        -- Note: pretty printing is not guaranteed to round-trip, but it's what we can do.
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
in particular the `variable_alias` binders and any redundant binders. -/
partial def completeBinders' (maxSteps : Nat) (gas : Nat)
    (checkRedundant : Bool)
    (binders : TSyntaxArray ``bracketedBinder)
    (toOmit : Array Bool) (i : Nat) :
    TermElabM (TSyntaxArray ``bracketedBinder × Array Bool) := do
  if 0 < gas && i < binders.size then
    let binder := binders[i]!
    trace[«variable?»] "\
      Have {(← getLCtx).getFVarIds.size} fvars and {(← getLocalInstances).size} local instances. \
      Looking at{indentD binder}"
    let sub? ← getSubproblem binder (bracketedBinderType binder).get!
    if let some (goalMsg, binder') := sub? then
      trace[«variable?»] m!"new subproblem:{indentD binder'}"
      if binders.any (stop := i) (· == binder') then
        let binders' := binders.extract 0 i
        throwErrorAt binder "\
          Binder{indentD binder}\nwas not able to satisfy one of its dependencies using \
          the pre-existing binder{indentD binder'}\n\n\
          This might be due to differences in implicit arguments, which are not represented \
          in binders since they are generated by pretty printing unsatisfied dependencies.\n\n\
          Current variable command:{indentD (← `(command| variable $binders'*))}\n\n\
          Local context for the unsatisfied dependency:{goalMsg}"
      let binders := binders.insertAt! i binder'
      completeBinders' maxSteps (gas - 1) checkRedundant binders toOmit i
    else
      let lctx ← getLCtx
      let linst ← getLocalInstances
      withOptions (fun opts => Term.checkBinderAnnotations.set opts false) <| -- for variable_alias
      Term.withAutoBoundImplicit <|
      Term.elabBinders #[binder] fun bindersElab => do
        let types : Array Expr ← bindersElab.mapM (inferType ·)
        trace[«variable?»] m!"elaborated binder types array = {types}"
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
            let res ← try withLCtx lctx linst <| trySynthInstance type catch _ => pure .none
            if let .some _ := res then
              if checkRedundant then
                let mvar ← mkFreshExprMVarAt lctx linst type
                logWarningAt binder
                  m!"Instance argument can be inferred from earlier arguments.\n{mvar.mvarId!}"
              return (binders, toOmit.push true)
            else
              return (binders, toOmit.push false)
          | _ => return (binders, toOmit.push false)
        completeBinders' maxSteps gas checkRedundant binders toOmit (i + 1)
  else
    if gas == 0 && i < binders.size then
      let binders' := binders.extract 0 i
      logErrorAt binders[i]! m!"Maximum recursion depth for variables! reached. This might be a \
        bug, or you can try adjusting `set_option variable?.maxSteps {maxSteps}`\n\n\
        Current variable command:{indentD (← `(command| variable $binders'*))}"
    return (binders, toOmit)
where
  isVariableAlias (type : Expr) : MetaM Bool := do
    forallTelescope type fun _ type => do
      if let .const name _ := type.getAppFn then
        if variableAliasAttr.hasTag (← getEnv) name then
          return true
      return false

def completeBinders (maxSteps : Nat) (checkRedundant : Bool)
    (binders : TSyntaxArray ``bracketedBinder) :
    TermElabM (TSyntaxArray ``bracketedBinder × Array Bool) :=
  completeBinders' maxSteps maxSteps checkRedundant binders #[] 0

/-- Strip off whitespace and comments. -/
def cleanBinders (binders : TSyntaxArray ``bracketedBinder) :
    TSyntaxArray ``bracketedBinder := Id.run do
  let mut binders' := #[]
  for binder in binders do
    binders' := binders'.push <| ⟨binder.raw.unsetTrailing⟩
  return binders'

@[command_elab «variable?», inherit_doc «variable?»]
def elabVariables : CommandElab := fun stx =>
  match stx with
  | `(variable? $binders* $[=> $expectedBinders?*]?) => do
    let checkRedundant := variable?.checkRedundant.get (← getOptions)
    process stx checkRedundant binders expectedBinders?
  | _ => throwUnsupportedSyntax
where
  extendScope (binders : TSyntaxArray ``bracketedBinder) : CommandElabM Unit := do
    for binder in binders do
      let varUIds ← getBracketedBinderIds binder |>.mapM
        (withFreshMacroScope ∘ MonadQuotation.addMacroScope)
      modifyScope fun scope =>
        { scope with varDecls := scope.varDecls.push binder, varUIds := scope.varUIds ++ varUIds }
  process (stx : Syntax) (checkRedundant : Bool)
      (binders : TSyntaxArray ``bracketedBinder)
      (expectedBinders? : Option <| TSyntaxArray ``bracketedBinder) : CommandElabM Unit := do
    let binders := cleanBinders binders
    let maxSteps := variable?.maxSteps.get (← getOptions)
    trace[«variable?»] "variable?.maxSteps = {maxSteps}"
    for binder in binders do
      if (bracketedBinderType binder).isNone then
        throwErrorAt binder "variable? cannot update pre-existing variables"
    let (binders', suggest) ← runTermElabM fun _ => do
      let (binders, toOmit) ← completeBinders maxSteps checkRedundant binders
      /- Elaborate the binders again, which also adds the infotrees.
      This also makes sure the list works with auto-bound implicits at the front. -/
      Term.withAutoBoundImplicit <| Term.elabBinders binders fun _ => pure ()
      -- Filter out omitted binders
      let binders' : TSyntaxArray ``bracketedBinder :=
        (binders.zip toOmit).filterMap fun (b, omit) => if omit then none else some b
      if let some expectedBinders := expectedBinders? then
        trace[«variable?»] "checking expected binders"
        /- We re-elaborate the binders to create an expression that represents the entire resulting
        local context (auto-bound implicits mean we can't just the `binders` array). -/
        let elabAndPackageBinders (binders : TSyntaxArray ``bracketedBinder) :
            TermElabM AbstractMVarsResult :=
          withoutModifyingStateWithInfoAndMessages <| Term.withAutoBoundImplicit <|
            Term.elabBinders binders fun _ => do
              let e ← mkForallFVars (← getLCtx).getFVars (.sort .zero)
              let res ← abstractMVars e
              -- Throw in the level names from the current state since `Type*` produces new
              -- level names.
              return {res with paramNames := (← get).levelNames.toArray ++ res.paramNames}
        let ctx1 ← elabAndPackageBinders binders'
        let ctx2 ← elabAndPackageBinders expectedBinders
        trace[«variable?»] "new context: paramNames = {ctx1.paramNames}, {
          ""}numMVars = {ctx1.numMVars}\n{indentD ctx1.expr}"
        trace[«variable?»] "expected context: paramNames = {ctx2.paramNames}, {
          ""}numMVars = {ctx2.numMVars}\n{indentD ctx2.expr}"
        if ctx1.paramNames == ctx2.paramNames && ctx1.numMVars == ctx2.numMVars then
          if ← isDefEq ctx1.expr ctx2.expr then
            return (binders', false)
        logWarning "Calculated binders do not match the expected binders given after `=>`."
        return (binders', true)
      else
        return (binders', true)
    extendScope binders'
    let varComm ← `(command| variable? $binders* => $binders'*)
    trace[«variable?»] "derived{indentD varComm}"
    if suggest then
      liftTermElabM <| Lean.Meta.Tactic.TryThis.addSuggestion stx (origSpan? := stx) varComm

/-- Hint for the unused variables linter. Copies the one for `variable`. -/
@[unused_variables_ignore_fn]
def ignorevariable? : Lean.Linter.IgnoreFunction := fun _ stack _ =>
  stack.matches [`null, none, `null, ``Mathlib.Command.Variable.variable?]
  || stack.matches [`null, none, `null, `null, ``Mathlib.Command.Variable.variable?]
