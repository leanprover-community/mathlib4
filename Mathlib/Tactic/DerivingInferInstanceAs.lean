/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Declaration
public meta import Lean.Compiler.NoncomputableAttr
public import Mathlib.Tactic.InferInstanceAsPercent

/-!
# Deriving hook for `inferInstanceAs%` normalization

This module intercepts `def ... deriving ...` declarations and the
`deriving instance ... for ...` command for definitions, replacing the standard
delta deriving handler with a version that normalizes instances using
`inferInstanceAs%`.

This prevents "carrier type leakage" in derived instances: when
`def Foo := Bar deriving SomeClass`, the standard handler may produce
instances whose internal lambda binder domains refer to `Bar` instead of `Foo`,
causing `isDefEq` failures at `reducibleAndInstances` transparency.

## Implementation

The implementation copies `mkInst` and `processDefDeriving` from
`Lean.Elab.Deriving.Basic` (as of Lean 4.29.0-rc6) and adds a normalization step
using `normalizeInstance` from `Mathlib.Tactic.InferInstanceAsPercent`.
This is intentionally a temporary copy: once we settle on the right behavior,
it will be upstreamed into Lean 4.
-/

public meta section

open Lean Meta Elab Term Command

namespace Mathlib.Deriving

/-- Result for `mkInstNormalized` -/
private structure MkInstResult where
  instType   : Expr
  instVal    : Expr

private def throwDeltaDeriveFailure {α : Type} (className declName : Name)
    (msg? : Option MessageData) (suffix : MessageData := "") : MetaM α :=
  let suffix := if let some msg := msg? then m!", {msg}{suffix}" else m!".{suffix}"
  throwError "Failed to delta derive `{.ofConstName className}` instance for \
    `{.ofConstName declName}`{suffix}"

/--
Constructs an instance of the class `classExpr` by figuring out the correct position to insert
`val` to create a type `className ... val ...` such that there is already an instance for it.

This is a copy of `Lean.Elab.Term.mkInst` from `Lean.Elab.Deriving.Basic`, modified to normalize
the synthesized instance using `normalizeInstance` from `InferInstanceAsPercent`.
-/
private partial def mkInstNormalized (classExpr : Expr) (declName : Name) (declVal val : Expr) :
    TermElabM MkInstResult := do
  let classExpr ← whnfCore classExpr
  let cls := classExpr.getAppFn
  let (xs, bis, _) ← forallMetaTelescopeReducing (← inferType cls)
  for x in xs, y in classExpr.getAppArgs do
    x.mvarId!.assign y
  let classExpr := mkAppN cls xs
  let some className ← isClass? classExpr
    | throwError "Failed to delta derive instance for `{.ofConstName declName}`, \
        not a class:{indentExpr classExpr}"
  let mut instMVars := #[]
  for x in xs, bi in bis do
    if !(← x.mvarId!.isAssigned) then
      if bi.isInstImplicit then
        x.mvarId!.setKind .synthetic
        instMVars := instMVars.push x.mvarId!
  let instVal ← mkFreshExprMVar classExpr (kind := .synthetic)
  instMVars := instMVars.push instVal.mvarId!
  let rec go (val : Expr) : TermElabM MkInstResult := do
    let val ← whnfCore val
    trace[Elab.Deriving] "Looking for arguments to `{classExpr}` that can be used for \
      the value{indentExpr val}"
    let state ← saveState
    let valTy ← inferType val
    let mut anyDefEqSuccess := false
    let mut messages : MessageLog := {}
    for x in xs, bi in bis, i in 0...xs.size do
      unless bi.isExplicit do
        continue
      let decl ← x.mvarId!.getDecl
      if decl.type.isOutParam then
        continue
      unless ← isMVarApp x do
        continue
      unless ← isDefEqGuarded decl.type valTy <&&> isDefEqGuarded x val do
        restoreState state
        continue
      anyDefEqSuccess := true
      trace[Elab.Deriving] "Argument {i} gives option{indentExpr classExpr}"
      try
        synthesizeAppInstMVars instMVars classExpr
        Term.synthesizeSyntheticMVarsNoPostponing
      catch ex =>
        trace[Elab.Deriving] "Option for argument {i} failed"
        logException ex
        messages := messages ++ (← Core.getMessageLog)
        restoreState state
        continue
      if (← MonadLog.hasErrors) then
        trace[Elab.Deriving] "Option for argument {i} failed, logged errors"
        messages := messages ++ (← Core.getMessageLog)
        restoreState state
        continue
      trace[Elab.Deriving] "Argument {i} option succeeded{indentExpr classExpr}"
      let mut xs' := xs.set! i declVal
      for j in [:xs'.size], bi in bis do
        if bi.isInstImplicit then
          let origInst ← instantiateMVars xs[j]!
          let argTy ← instantiateMVars (← inferType xs[j]!)
          let targetArgTy := argTy.replace fun e =>
            if e == val then declVal else none
          if let some targetInst ← synthInstance? targetArgTy then
            unless ← isDefEq origInst targetInst do
              throwDeltaDeriveFailure className declName
                (m!"instance diamond: the instance for the target type\
                  {indentExpr targetInst}\nis not definitionally equal to the instance for the \
                  underlying type\
                  {indentExpr origInst}\nfor{indentExpr targetArgTy}")
            xs' := xs'.set! j targetInst
      let instType := mkAppN cls xs'
      -- *** BEGIN NORMALIZATION ***
      -- Normalize the synthesized instance value to fix carrier type leakage.
      -- Build replacements directly from the class args (source = classExpr with
      -- underlying type, target = instType with definition type), avoiding
      -- `inferType` which may unfold abbreviations like `DecidableEq` into Pi types.
      let instVal ← instantiateMVars instVal
      let sourceClassExpr ← instantiateMVars classExpr
      let replacements := buildReplacements sourceClassExpr instType
      let instVal ←
        if replacements.isEmpty then
          pure instVal
        else
          let warnLeaky := inferInstanceAsPercent.leakySubInstWarning.get (← getOptions)
          let warnings ← IO.mkRef #[]
          let result ← normalizeInstance instVal replacements warnings
          if warnLeaky then
            for w in ← warnings.get do
              logWarning w
          pure result
      -- *** END NORMALIZATION ***
      return { instType, instVal }
    try
      if let some val' ← unfoldDefinition? val then
        return ← withTraceNode `Elab.Deriving
          (fun _ => return m!"Unfolded value to {val'}") <| go val'
    catch ex =>
      if !messages.hasErrors then
        throw ex
      Core.resetMessageLog
    if !anyDefEqSuccess then
      throwDeltaDeriveFailure className declName
        (m!"the class has no explicit non-out-param parameters where\
          {indentExpr declVal}\n\
          can be inserted.")
    else
      Core.setMessageLog (messages ++ (← Core.getMessageLog))
      throwDeltaDeriveFailure className declName none
        (.note m!"Delta deriving tries the following strategies: \
            (1) inserting the definition into each explicit non-out-param parameter of a class \
            and (2) unfolding definitions further.")
  go val

/--
Delta deriving handler with `inferInstanceAs%` normalization.

This is a copy of `Lean.Elab.Term.processDefDeriving` from `Lean.Elab.Deriving.Basic`,
modified to use `mkInstNormalized` instead of `mkInst`.
-/
def processDefDerivingNormalized (view : DerivingClassView) (decl : Expr) :
    TermElabM Unit := do
  let { cls := classStx, hasExpose := _ /- todo? -/, .. } := view
  let decl ← whnfCore decl
  let .const declName _ := decl.getAppFn
    | throwError "Failed to delta derive instance, expecting a term of the form `C ...` where \
        `C` is a constant, given{indentExpr decl}"
  let exposed := (← getEnv).setExporting true |>.find? declName |>.any (·.hasValue)
  withExporting (isExporting := exposed) do
  let ConstantInfo.defnInfo info ← getConstInfo declName
    | throwError "Failed to delta derive instance, `{.ofConstName declName}` is not a definition."
  let value := info.value.beta decl.getAppArgs
  let result : Closure.MkValueTypeClosureResult ←
    lambdaTelescope value fun xs value => withoutErrToSorry do
      let decl := mkAppN decl xs
      let lctx ← xs.foldlM (init := ← getLCtx) fun lctx x => do
        pure <| lctx.setUserName x.fvarId!
          (← mkFreshUserName <| (lctx.find? x.fvarId!).get!.userName)
      withLCtx' lctx do
        let msgLog ← Core.getMessageLog
        Core.resetMessageLog
        try
          let classExpr ← elabTerm classStx none
          synthesizeSyntheticMVars (postpone := .partial)
          if (← MonadLog.hasErrors) then
            throwAbortTerm
          forallTelescope classExpr fun _ classExpr => do
            let result ← mkInstNormalized classExpr declName decl value
            Closure.mkValueTypeClosure result.instType result.instVal (zetaDelta := true)
        finally
          Core.setMessageLog (msgLog ++ (← Core.getMessageLog))
  let env ← getEnv
  let mut instName :=
    (← getCurrNamespace) ++ (← NameGen.mkBaseNameWithSuffix "inst" result.type)
  instName ← liftMacroM <| mkUnusedBaseName instName
  if isPrivateName declName then
    instName := mkPrivateName env instName
  let hints := ReducibilityHints.regular (getMaxHeight env result.value + 1)
  let decl ← mkDefinitionValInferringUnsafe instName result.levelParams.toList result.type
    result.value hints
  addAndCompile (logCompileErrors := !(← read).isNoncomputableSection) <|
    Declaration.defnDecl decl
  trace[Elab.Deriving] "Derived instance `{.ofConstName instName}`"
  registerInstance instName AttributeKind.global (eval_prio default)
  addDeclarationRangesFromSyntax instName (← getRef)

/-- Like `Lean.Elab.elabDefDeriving`, but uses `processDefDerivingNormalized`. -/
private def elabDefDerivingNormalized (classes : Array DerivingClassView) (decls : Array Syntax) :
    CommandElabM Unit := runTermElabM fun _ => do
  for decl in decls do
    withRef decl <| withLogging do
      let declExpr ←
        if decl.isIdent then
          let declName ← realizeGlobalConstNoOverload decl
          let info ← getConstInfo declName
          unless info.isDefinition do
            throwError (m!"Declaration `{.ofConstName declName}` is not a definition."
              ++ .note m!"When any declaration is a definition, this command goes into delta \
                    deriving mode, which applies only to definitions. \
                    Delta deriving unfolds definitions and infers pre-existing instances.")
          mkConstWithLevelParams declName
        else
          Term.elabTermAndSynthesize decl none
      for cls in classes do
        withLogging do
        withTraceNode `Elab.Deriving (fun _ => return m!"running normalized delta deriving \
            handler for `{cls.cls}` and definition `{declExpr}`") do
          processDefDerivingNormalized cls declExpr

/-- Override the `deriving instance ... for ...` command to use normalized delta deriving
for definitions. For non-definitions, falls through to the builtin handler. -/
@[command_elab «deriving»] def elabDerivingNormalized : CommandElab
  | `(deriving instance $[$classes],* for $[$decls],*) => do
    let classes ← liftCoreM <| classes.mapM DerivingClassView.ofSyntax
    let decls : Array Syntax := decls
    if decls.all Syntax.isIdent then
      let declNames ← liftCoreM <| decls.mapM (realizeGlobalConstNoOverloadWithInfo ·)
      let infos ← declNames.mapM getConstInfo
      if infos.any (·.isDefinition) then
        elabDefDerivingNormalized classes decls
      else
        -- Not definitions: fall through to builtin handler (for registered deriving handlers)
        throwUnsupportedSyntax
    else
      elabDefDerivingNormalized classes decls
  | _ => throwUnsupportedSyntax

/-- Intercept `def ... deriving ...` declarations to use normalized delta deriving.
Strips the deriving clause from the `def`, elaborates it, then emits
`deriving instance ... for ...` which our `elabDerivingNormalized` handles. -/
def elabDefWithNormalizedDeriving : CommandElab := fun stx => do
  -- declaration = declModifiers >> (definition | ...)
  -- definition = "def " >> declId >> optDeclSig >> declVal >> optDefDeriving
  let defStx := stx[1]
  unless defStx.isOfKind ``Lean.Parser.Command.definition do throwUnsupportedSyntax
  let derivStx := defStx[4]
  if derivStx.isNone then throwUnsupportedSyntax
  -- Elaborate the def without deriving (strip optDefDeriving)
  Command.elabDeclaration (stx.setArg 1 (defStx.setArg 4 mkNullNode))
  -- Now emit `deriving instance ... for ...` which our handler will catch
  let (nm, _) := Elab.expandDeclIdCore defStx[1]
  let derivClasses : Array (TSyntax ``Lean.Parser.Command.derivingClass) :=
    derivStx[1].getSepArgs.map .mk
  elabCommand <| ← `(deriving instance $[$derivClasses],* for $(mkIdent nm))

-- Register this as a handler for the `declaration` command.
-- It takes priority over the builtin handler for the specific case of `def ... deriving ...`.
attribute [command_elab declaration] elabDefWithNormalizedDeriving

end Mathlib.Deriving
