/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Basic

/-!
# Attributes for `inclusion` extensions

This file defines the attributes used to register inclusion extensions, inclusion and hypothesis
operations, hypothesis extensions, and inclusion parameters.
-/

public meta section

open Lean Meta Elab Term DiscrTreeExt

namespace Inclusion

private def analyzeTheoremArgs (declName : Name) (pattern outputSet : Expr)
    (args : Array Expr) (binderInfos : Array BinderInfo) (sourceIdx : Option Nat := none) :
    MetaM (Array InclusionHypothesisArg × Array ParamArg) := do
  let registeredParams := inclusionParamExt.getState (← getEnv)
  let mut inputs := #[]
  let mut params := #[]
  for h : i in [:args.size] do
    let arg := args[i]
    let argDecl ← arg.mvarId!.getDecl
    let argType := argDecl.type
    if let some (inputExpr, inputSet, _) := toSetMem? argType then
      let some exprIndex := args.findIdx? (· == inputExpr)
        | throwError "The member '{inputExpr}' in premise '{argType}' of theorem \
            '{declName}' is not a theorem variable"
      let some setIndex := args.findIdx? (· == inputSet)
        | throwError "The set '{inputSet}' in premise '{argType}' of theorem \
            '{declName}' is not a theorem variable"
      let exprId := args[exprIndex]!.mvarId!
      let setId := args[setIndex]!.mvarId!
      let proofId := arg.mvarId!
      unless (pattern.findMVar? (· == exprId)).isSome do
        throwError "The recursive input '{inputExpr}' of theorem '{declName}' does not occur in \
          the matched expression"
      if (outputSet.findMVar? (· == exprId)).isSome then
        throwError "The recursive input '{inputExpr}' of theorem '{declName}' occurs in its \
          output inclusion"
      if (pattern.findMVar? (· == setId)).isSome then
        throwError "The input set '{inputSet}' of theorem '{declName}' occurs in the matched \
          expression"
      unless (outputSet.findMVar? (· == setId)).isSome do
        throwError "The input set '{inputSet}' of theorem '{declName}' does not occur in its \
          output inclusion"
      if (pattern.findMVar? (· == proofId)).isSome then
        throwError "The inclusion hypothesis '{argType}' of theorem '{declName}' occurs in the \
          matched expression"
      if (outputSet.findMVar? (· == proofId)).isSome then
        throwError "The inclusion hypothesis '{argType}' of theorem '{declName}' occurs in its \
          output inclusion"
      if inputs.any fun input => input.exprIdx == exprIndex then
        throwError "The recursive input '{inputExpr}' occurs in more than one premise of theorem \
          '{declName}'"
      if inputs.any fun input => input.setIdx == setIndex then
        throwError "The input set '{inputSet}' occurs in more than one premise of theorem \
          '{declName}'"
      inputs := inputs.push { exprIdx := exprIndex, setIdx := setIndex, proofIdx := i }
    else if sourceIdx != some i then
      let userName := argDecl.userName
      if let some param := registeredParams.find? userName then
        unless ← isDefEq argType param.type do
          throwError "Inclusion parameter '{userName}' in '{declName}' has \
            type {argType}, expected {param.type}"
        if (pattern.findMVar? fun mvarId => mvarId == arg.mvarId!).isSome then
          throwError "Inclusion parameter '{userName}' in '{declName}' occurs in the matched \
            expression"
        if params.any (·.name == userName) then
          throwError "Inclusion parameter '{userName}' occurs more than once in '{declName}'"
        params := params.push { name := userName, idx := i }
      else if ← isProp argType then
        unless binderInfos[i]!.isInstImplicit ||
            (pattern.findMVar? fun mvarId => mvarId == arg.mvarId!).isSome do
          throwError "Unsupported premise '{argType}' in theorem '{declName}'"
  return (inputs, params)

section InclusionExt

syntax (name := inclusionExtAttr) "inclusionExt " ident " | " term,+ : attr

syntax (name := inclusionOpAttr) "inclusionOp " ident (prio)? : attr

/-- Add the inclusion extension `declName` to `familyName` under `keys`. -/
def addInclusionExt (familyName declName : Name) (keys : Array (Array DiscrTree.Key))
    (kind : AttributeKind) : AttrM Unit := do
  let family ← getInclusionFamily familyName
  let ext ← evalDecl InclusionExt ``InclusionExt declName
  family.inclusionExt.add ((keys, declName), ext) kind

private def analyzeInclusionTheorem (declName : Name) :
    MetaM (Array DiscrTree.Key × Array InclusionHypothesisArg × Array ParamArg) := do
  let theoremExpr ← mkConstWithFreshMVarLevels declName
  let (args, binderInfos, conclusion) ←
    forallMetaTelescopeReducing (← inferType theoremExpr)
  let some (pattern, outputSet, _) := toSetMem? conclusion
    | throwError "The conclusion of '{declName}' is not an inclusion using a `ToSet` instance"
  let (inputs, params) ← analyzeTheoremArgs declName pattern outputSet args binderInfos
  return (← DiscrTree.mkPath pattern, inputs, params)

private def addInclusionOp (theoremName familyName : Name) (priority : Nat)
    (kind : AttributeKind) : AttrM Unit := do
  let (path, inputs, params) ← MetaM.run' <| analyzeInclusionTheorem theoremName
  let declName := Name.str ((← getEnv).mainModule ++ theoremName) "_inclusionExt"
  unless (← getEnv).contains declName do
    let derive := mkAppN (mkConst ``deriveInclusionOp)
      #[toExpr theoremName, toExpr inputs, toExpr params]
    let value := mkAppN (mkConst ``InclusionExt.mk)
      #[toExpr declName, toExpr theoremName, derive, toExpr priority]
    let decl ← mkDefinitionValInferringUnsafe declName [] (mkConst ``InclusionExt) value .opaque
    addAndCompile (markMeta := true) (.defnDecl decl)
  addInclusionExt familyName declName #[path] kind

/-- The `inclusionExt` attribute registers a handwritten inclusion extension. -/
initialize registerBuiltinAttribute {
  name := `inclusionExtAttr
  descr := "adds an inclusion-function extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let env ← getEnv
    if (IR.getSorryDep env declName).isSome then return
    match stx with
    | `(attr| inclusionExt $familyName:ident | $es,*) => do
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute `inclusionExt`, declaration is in an imported module"
      ensureAttrDeclIsMeta `inclusionExt declName kind
      let keys ← elabExtKeys (es.getElems.map (·.raw))
      addInclusionExt familyName.getId declName keys kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Inclusion extensions cannot be erased by declaration"
}

/-- The `inclusionOp` attribute generates an inclusion extension from an inclusion theorem. -/
initialize registerBuiltinAttribute {
  name := `inclusionOpAttr
  descr := "adds an inclusion operation"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    if (IR.getSorryDep (← getEnv) declName).isSome then return
    match stx with
    | `(attr| inclusionOp $familyName:ident $[$_prio:prio]?) =>
      addInclusionOp declName familyName.getId (← getAttrParamOptPrio stx[2]) kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Inclusion operations cannot be erased by declaration"
}

end InclusionExt

section HypothesisExt

syntax (name := hypothesisExtAttr) "hypothesisExt " ident " | " term,+ : attr

syntax (name := hypothesisOpAttr) "hypothesisOp " ident (prio)? : attr

/-- Add the hypothesis extension `declName` to `familyName` under `keys`. -/
def addHypothesisExt (familyName declName : Name) (keys : Array (Array DiscrTree.Key))
    (kind : AttributeKind) : AttrM Unit := do
  let family ← getInclusionFamily familyName
  let ext ← evalDecl HypothesisExt ``HypothesisExt declName
  family.hypothesisExt.add ((keys, declName), ext) kind

private def analyzeHypothesisTheorem (declName : Name) :
    MetaM (Array DiscrTree.Key × Nat × Array InclusionHypothesisArg × Array ParamArg) := do
  let theoremExpr ← mkConstWithFreshMVarLevels declName
  let (args, binderInfos, conclusion) ←
    forallMetaTelescopeReducing (← inferType theoremExpr)
  let some (outputExpr, outputSet, _) := toSetMem? conclusion
    | throwError "The conclusion of '{declName}' is not an inclusion using a `ToSet` instance"
  let mut sourceIdx? := none
  for h : i in [:args.size] do
    let argType ← args[i].mvarId!.getType
    if binderInfos[i]!.isExplicit && (← isProp argType) && (toSetMem? argType).isNone then
      if sourceIdx?.isSome then
        throwError "Hypothesis theorem '{declName}' has more than one non-inclusion premise"
      sourceIdx? := some i
  let some sourceIdx := sourceIdx?
    | throwError "Hypothesis theorem '{declName}' has no non-inclusion premise"
  let sourceId := args[sourceIdx]!.mvarId!
  if (outputExpr.findMVar? (· == sourceId)).isSome ||
      (outputSet.findMVar? (· == sourceId)).isSome then
    throwError "The source hypothesis of '{declName}' occurs in its output inclusion"
  let pattern ← args[sourceIdx]!.mvarId!.getType
  let (inputs, params) ←
    analyzeTheoremArgs declName pattern outputSet args binderInfos (some sourceIdx)
  for ⟨name, idx⟩ in params do
    if (outputExpr.findMVar? (· == args[idx]!.mvarId!)).isSome then
      throwError "Inclusion parameter '{name}' in '{declName}' occurs in the output expression"
  return (← DiscrTree.mkPath pattern, sourceIdx, inputs, params)

private def addHypothesisOp (theoremName familyName : Name) (priority : Nat)
    (kind : AttributeKind) : AttrM Unit := do
  let (path, sourceIdx, inputs, params) ←
    MetaM.run' <| analyzeHypothesisTheorem theoremName
  let declName := Name.str ((← getEnv).mainModule ++ theoremName) "_hypothesisExt"
  unless (← getEnv).contains declName do
    let derive := mkAppN (mkConst ``deriveHypothesisOp)
      #[toExpr theoremName, toExpr sourceIdx, toExpr inputs, toExpr params]
    let value := mkAppN (mkConst ``HypothesisExt.mk)
      #[toExpr declName, toExpr theoremName, derive, toExpr priority]
    let decl ← mkDefinitionValInferringUnsafe declName [] (mkConst ``HypothesisExt) value .opaque
    addAndCompile (markMeta := true) (.defnDecl decl)
  addHypothesisExt familyName declName #[path] kind

/-- The `hypothesisExt` attribute registers a hypothesis extension. -/
initialize registerBuiltinAttribute {
  name := `hypothesisExtAttr
  descr := "adds a hypothesis extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let env ← getEnv
    if (IR.getSorryDep env declName).isSome then return
    match stx with
    | `(attr| hypothesisExt $familyName:ident | $es,*) => do
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute `hypothesisExt`, declaration is in an imported module"
      ensureAttrDeclIsMeta `hypothesisExt declName kind
      let keys ← elabExtKeys (es.getElems.map (·.raw))
      addHypothesisExt familyName.getId declName keys kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Hypothesis extensions cannot be erased by declaration"
}

/-- The `hypothesisOp` attribute generates a hypothesis extension from an inclusion theorem. -/
initialize registerBuiltinAttribute {
  name := `hypothesisOpAttr
  descr := "adds an inclusion-hypothesis operation"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    if (IR.getSorryDep (← getEnv) declName).isSome then return
    match stx with
    | `(attr| hypothesisOp $familyName:ident $[$_prio:prio]?) =>
      addHypothesisOp declName familyName.getId (← getAttrParamOptPrio stx[2]) kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Hypothesis operations cannot be erased by declaration"
}

end HypothesisExt

section Param

syntax (name := inclusionParamAttr) "inclusionParam" : attr

private def validateInclusionParamDecl (decl : InclusionParamDecl) : MetaM Unit := do
  if decl.type.hasFVar || decl.type.hasMVar then
    throwError "The type of inclusion parameter '{decl.name}' is not closed"
  unless (← inferType decl.type).isSort do
    throwError "The declared type {decl.type} of inclusion parameter '{decl.name}' is not a type"
  if let some value := decl.defaultValue? then
    if value.hasFVar || value.hasMVar then
      throwError "The default value of inclusion parameter '{decl.name}' is not closed"
    unless ← isDefEq (← inferType value) decl.type do
      throwError "The default value {value} of inclusion parameter '{decl.name}' does not have \
        type {decl.type}"

/-- Add the inclusion parameter declared by `declName`. -/
def addInclusionParam (declName : Name) (kind : AttributeKind) : AttrM Unit := do
  let env ← getEnv
  ensureAttrDeclIsMeta `inclusionParam declName kind
  unless (env.getModuleIdxFor? declName).isNone do
    throwError "invalid attribute `inclusionParam`, declaration is in an imported module"
  if (IR.getSorryDep env declName).isSome then return
  let decl ← mkInclusionParamDecl declName
  MetaM.run' <| validateInclusionParamDecl decl
  let params := inclusionParamExt.getState env
  if params.decls.contains decl.name then
    throwError "Inclusion parameter '{decl.name}' is already registered"
  inclusionParamExt.add (declName, decl) kind

/-- The `inclusionParam` attribute registers a typed inclusion-tactic parameter. -/
initialize registerBuiltinAttribute {
  name := `inclusionParamAttr
  descr := "registers an inclusion-tactic parameter"
  applicationTime := .afterCompilation
  add := fun declName _ kind => addInclusionParam declName kind
}

end Param

end Inclusion
