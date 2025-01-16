/-
Copyright (c) 2024 Andrew Yang, Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Calle Sönne
-/
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# The `addMorphismPropertyInstances` command

We define a command `addMorphismPropertyInstances` that goes through all the lemmas tagged with
`morphismPropertyInstance` and attempts to add the relevant instances of a morphism property,
provided that the appropriate stability instances on the morphism property are present.

-/
open CategoryTheory

open Lean Meta Elab Tactic
open Mathlib.Tactic

namespace AddMorphismPropertyInstances

/-- Configuration options for `@[morphisProperty]` -/
structure Config where
  /-- The priority of the generated lemma -/
  priority : Nat := 1000
  deriving Inhabited

/-- Function elaborating `Config` -/
declare_command_config_elab elabConfig Config

/-- The syntax for the `morphismPropertyInstance` attribute. -/
syntax (name := morphismPropertyInstance) "morphismPropertyInstance" Parser.Tactic.optConfig : attr

/--
Theorems tagged with `morphismPropertyInstance` are used in the `addMorphismPropertyInstances`
command, which goes through all the tagged lemma and attempts to add the relevant instances of a
morphism property, provided that the appropriate stability instances
on the morphism property are present.

For example, given
```
@[morphismPropertyInstance]
lemma foo {P : MorphismProperty C} [P.ContainsIdentities] {X} : P (𝟙 X)
```
Then the following command
```
addMorphismPropertyInstances Bar
```
would generate the instance
```
instance {X} : Bar (𝟙 X)
```
if `Bar` is a class and a `Bar.ContainsIdentities` instance is available.
-/
initialize thmAttr : ParametricAttribute Config ←
  registerParametricAttribute {
    name := `morphismPropertyInstance
    descr := "Register a lemma to be used in `addMorphismPropertyInstances`.",
    getParam := fun nm stx ↦ match stx with
      | `(attr| morphismPropertyInstance $c:optConfig) => liftCommandElabM (elabConfig c)
      | _ => throwUnsupportedSyntax }

-- initialize thmAttr : TagAttribute ←
--   registerTagAttribute `morphismPropertyInstance
--     "Register a lemma to be used in `addMorphismPropertyInstances`"

/--
We attempt to feed `classExpr` into `lemmaName` and fill in all typeclass arguments
of `lemmaName` about `classExpr`, except the ones mentioned in `skip`.
-/
def getArgs (lemmaExpr : Expr) (classExpr : Expr) : TermElabM (Array Expr) := do
  -- We go through the arguments of the type of `lemmaName`.
  let (mvars, _, _) ← forallMetaTelescope (← inferType lemmaExpr)
  -- For each argument of the form `MorphismProperty _`, we attempt to assign `classExpr` to it.
  for mvar in mvars do
    if let .const ``MorphismProperty _ := (← inferType mvar).getAppFn then
      unless ← isDefEq mvar classExpr do
        throwError m!"Failed to assign morphism property {classExpr} to {mvar}."
  -- We turn all remaining universe metavariable into parameters.
  let mvars ← mvars.mapM Term.levelMVarToParam
  -- For each remaining argument that is a type class and has no metavariables,
  -- (i.e. the typeclass requirements on `classExpr`)
  -- we attempt to synthesize an instance.
  for mvar in mvars do
    let mvarType ← (instantiateMVars (← inferType mvar))
    if (← isClass? mvarType).isSome && !(← hasAssignableMVar mvarType) then
      if let .some val ← trySynthInstance mvarType then
        unless ← isDefEq mvar val do
          throwError m!"Synthesized instance {val} does not match {mvar}."
      else
        throwError m!"Failed to synthesize {mvarType}."
  let mvars ← mvars.mapM instantiateMVars
  -- We take `mvars` while its metavariables are contained in `classExpr`.
  let allowedMVars ← Term.collectUnassignedMVars (← instantiateMVars classExpr)
  let mvars := Prod.fst <| ← mvars.foldlM (init := (#[], true)) fun (arr, ind) x ↦ do
    if ind && (← Term.collectUnassignedMVars x).all allowedMVars.contains then
      return (arr.push x, ind)
    else
      return (arr, false)
  if mvars.isEmpty then
    throwError m!"Failed to find a field of type `MorphismProperty _` in {lemmaExpr}."
  return mvars

/--
The main procedure of `addMorphismPropertyInstances`.
It runs through all the lemmas tagged with `morphismPropertyInstance` and attempt to
generate an instance lemma with the morphism property in the lemma substituted with `classTerm`.
-/
def addMorphismPropertyInstancesAux (classTerm : TSyntax `term) (verbose : Bool := false) :
    Command.CommandElabM PUnit := Command.runTermElabM fun fvars ↦ do
  let env ← getEnv
  -- Get the set of lemmas tagged with `thmAttr`
  let lemmas := (thmAttr.ext.getState env).fold (·.push (·, ·))
    (thmAttr.ext.toEnvExtension.getState env).importedEntries.flatten
  let mut logMsg : MessageData := ""
  let mut success := 0
  -- `classExpr` is the morphism property class, elaborated as an `Expr`.
  let classExpr ← Term.elabTerm classTerm none
  -- We first check if the type of `classExpr` is defeq to `MorphismProperty _`.
  do
    let mp ← mkConstWithFreshMVarLevels ``MorphismProperty
    let (args, _, _) ← forallMetaTelescope (← inferType mp)
    let mp ← mkAppOptM ``MorphismProperty (args.map some)
    unless ← isDefEq mp (← inferType classExpr) do
      throwError m!"{classExpr} is not of type `MorphismProperty _`."
  -- We only continue if `classExpr` is the application of some
  -- `morphismPropertyClass` to some arguments.
  if let .const morphismPropertyClass _lvl := classExpr.getAppFn then
    for (lemmaName, config) in lemmas do
      try
        -- First we check if the lemma already exists.
        let name := .str morphismPropertyClass lemmaName.toString
        checkNotAlreadyDeclared name
        -- We attempt to feed `classExpr` into `lemmaName` and fill in all typeclass arguments
        -- of `lemmaName` about `classExpr`.
        let classExpr ← Term.elabTerm classTerm none
        let lemmaExpr ← mkConstWithFreshMVarLevels lemmaName
        let args ← getArgs lemmaExpr classExpr
        let proofTerm ← mkAppOptM' lemmaExpr (args.map some)
        -- We run through the type of the constructed `proofTerm` and convert
        -- all type class arguments into `instImplicit`.
        let statement ← forallTelescope (← inferType proofTerm) fun xs ty => do
          let xs' := xs.filterMapM fun x ↦ do
            if (← isClass? (← inferType x)).isSome then
              return (x.fvarId!, BinderInfo.instImplicit)
            else
              return none
          withNewBinderInfos (← xs') <| liftMetaM do
            mkForallFVars xs ty
        -- We add back all the scoped variable used in the statement and proof.
        let fvars := (← Term.collectUnassignedMVars proofTerm) ++ fvars
        let proofTerm ← instantiateMVars (← Term.levelMVarToParam
          (← mkLambdaFVars (usedOnly := true) fvars proofTerm))
        let statement ← instantiateMVars (← mkForallFVars (usedOnly := true) fvars statement)
        let decl : TheoremVal :=
        { name := name
          levelParams := (collectLevelParams {} proofTerm).params.toList
          type := statement
          value := proofTerm }
        -- We add the declaration and add it as an instance
        addAndCompile (.thmDecl decl)
        addInstance name .global config.priority
        logMsg := logMsg ++ m!"Added instance {name}:{indentExpr statement}\n\n"
        success := success + 1
      catch
      | err => logMsg :=
        logMsg ++ m!"Failed to add instance for {lemmaName}:\n{err.toMessageData}\n\n"
    if success == 0 then
      throwError m!"Failed to add any instances:\n\n" ++ logMsg
    if verbose then
      logMsg := m!"Successfully added {success} instances out of {lemmas.size}.\n\n" ++ logMsg
      logInfo logMsg
  else
    throwError m!"Failed to generate lemmas. {classExpr} is not a class."

/--
`addMorphismPropertyInstances P` is a command that
generates instance lemmas for `P : MorphismProperty _`.

It runs through all the lemmas tagged with `morphismPropertyInstance` and attempt to
generate a lemma with the morphism property in the lemma substituted with `P`, provided that
the appropriate stability instances on the morphism property are present.

For example, given
```
@[morphismPropertyInstance]
lemma foo {P : MorphismProperty C} [P.ContainsIdentities] {X} : P (𝟙 X)
```
Then the following command
```
addMorphismPropertyInstances Bar
```
would generate the instance
```
instance {X} : Bar (𝟙 X)
```
if `Bar` is a class and a `Bar.ContainsIdentities` instance is available.

Use `addMorphismPropertyInstances?` to print the list of generated lemmas.
-/
elab "addMorphismPropertyInstances" classTerm:term : command =>
  addMorphismPropertyInstancesAux classTerm

/--
`addMorphismPropertyInstances? P` is the verbose version of `addMorphismPropertyInstances P`,
which is a command that generates instance lemmas for `P : MorphismProperty _`.

It runs through all the lemmas tagged with `morphismPropertyInstance` and attempt to
generate a lemma with the morphism property in the lemma substituted with `P`, provided that
the appropriate stability instances on the morphism property are present.

For example, given
```
@[morphismPropertyInstance]
lemma foo {P : MorphismProperty C} [P.ContainsIdentities] {X} : P (𝟙 X)
```
Then the following command
```
addMorphismPropertyInstances Bar
```
would generate the instance
```
instance {X} : Bar (𝟙 X)
```
if `Bar` is a class and a `Bar.ContainsIdentities` instance is available.
-/
elab "addMorphismPropertyInstances?" classTerm:term : command =>
  addMorphismPropertyInstancesAux (verbose := true) classTerm

end AddMorphismPropertyInstances
