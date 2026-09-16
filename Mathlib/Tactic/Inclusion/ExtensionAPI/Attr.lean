/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Basic

/-!
# Attributes for `inclusion` extensions

This file defines the attributes used to register inclusion and hypothesis extensions.
-/

public meta section

open Lean Meta Elab Term DiscrTreeExt

namespace Inclusion

/-- Syntax for registering an inclusion parameter using the `inclusion_param` attribute. -/
syntax (name := inclusionParamAttr) "inclusion_param" : attr

/-- Validate an inclusion parameter declaration. -/
private def validateInclusionParamDecl (decl : InclusionParamDecl) : MetaM Unit := do
  unless ← isType decl.type do
    throwError "The declared type {decl.type} of inclusion parameter `{decl.name}` is not a type"
  if let some value := decl.defaultValue? then
    unless ← isDefEq (← inferType value) decl.type do
      throwError "The default value {value} of inclusion parameter `{decl.name}` does not have \
        type {decl.type}"

/-- Add the inclusion parameter declared by `declName`. -/
def addInclusionParam (declName : Name) (kind : AttributeKind) : AttrM Unit := do
  let env ← getEnv
  ensureAttrDeclIsMeta `inclusion_param declName kind
  unless (env.getModuleIdxFor? declName).isNone do
    throwAttrDeclInImportedModule `inclusion_param declName
  if (IR.getSorryDep env declName).isSome then return
  let decl ← mkInclusionParamDecl declName
  MetaM.run' <| validateInclusionParamDecl decl
  let params := inclusionParamExt.getState env
  if params.contains decl.name then
    throwError "Inclusion parameter `{decl.name}` is already registered"
  inclusionParamExt.add (declName, decl) kind

initialize registerBuiltinAttribute {
  name := `inclusionParamAttr
  descr := "registers an inclusion-tactic parameter"
  applicationTime := .afterCompilation
  add := fun declName _ kind => addInclusionParam declName kind
}

/-- Syntax for declaring an inclusion extension using the `inclusion_ext` attribute. -/
syntax (name := inclusionExtAttr) "inclusion_ext" term,+ : attr

/-- Add the inclusion extension `declName` under `keys`. -/
def addInclusionExt (declName : Name) (keys : Array (Array DiscrTree.Key))
    (kind : AttributeKind) : AttrM Unit := do
  let ext ← evalDecl InclusionExt ``InclusionExt declName
  let family ← getInclusionFamily ext.family
  family.inclusionExt.add ((keys, declName), ext) kind

initialize registerBuiltinAttribute {
  name := `inclusionExtAttr
  descr := "adds an inclusion extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| inclusion_ext $es,*) => do
      let env ← getEnv
      ensureAttrDeclIsMeta `inclusion_ext declName kind
      unless (env.getModuleIdxFor? declName).isNone do
        throwAttrDeclInImportedModule `inclusion_ext declName
      if (IR.getSorryDep env declName).isSome then return
      let keys ← elabExtKeys (es.getElems.map (·.raw))
      addInclusionExt declName keys kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Inclusion extensions cannot be erased by declaration"
}

/-- Syntax for declaring a hypothesis extension using the `hypothesis_ext` attribute. -/
syntax (name := hypothesisExtAttr) "hypothesis_ext" term,+ : attr

/-- Add the hypothesis extension `declName` under `keys`. -/
def addHypothesisExt (declName : Name) (keys : Array (Array DiscrTree.Key))
    (kind : AttributeKind) : AttrM Unit := do
  let ext ← evalDecl HypothesisExt ``HypothesisExt declName
  let family ← getInclusionFamily ext.family
  family.hypothesisExt.add ((keys, declName), ext) kind

/-- Register the `hypothesis_ext` attribute. -/
initialize registerBuiltinAttribute {
  name := `hypothesisExtAttr
  descr := "adds a hypothesis extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| hypothesis_ext $es,*) => do
      let env ← getEnv
      ensureAttrDeclIsMeta `hypothesis_ext declName kind
      unless (env.getModuleIdxFor? declName).isNone do
        throwAttrDeclInImportedModule `hypothesis_ext declName
      if (IR.getSorryDep env declName).isSome then return
      let keys ← elabExtKeys (es.getElems.map (·.raw))
      addHypothesisExt declName keys kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Hypothesis extensions cannot be erased by declaration"
}

/-- The argument indices of an element `x`, a set `s`, and an inclusion hypothesis `x ∈ s`
in some theorem statement. -/
structure HypArg where
  /-- The index of the element argument. -/
  elemIdx : Nat
  /-- The index of the set argument. -/
  setIdx : Nat
  /-- The index of the membership proof argument. -/
  proofIdx : Nat
  deriving Inhabited, ToExpr

/-- The name of an inclusion parameter and its index in some theorem statement. -/
structure ParamArg where
  /-- The name of the registered inclusion parameter. -/
  name : Name
  /-- The index of the corresponding theorem argument. -/
  idx : Nat
  deriving Inhabited, ToExpr

/-- Apply the inclusion theorem `theoremName` to `e`, recursively constructing the inclusion bodies
specified by `hypArgs` and filling the registered parameter arguments specified by `paramArgs`. -/
def deriveInclusionOp (theoremName : Name) (hypArgs : Array HypArg) (paramArgs : Array ParamArg)
    (e : Expr) : InclusionM ExprInclusionBody := do
  let theoremExpr ← mkConstWithFreshMVarLevels theoremName
  let (args, binderInfos, conclusion) ← forallMetaTelescopeReducing (← inferType theoremExpr)
  let some (expr, inclusionBody, _) := toSetMem? conclusion | failure
  unless ← isDefEq expr e do failure
  for ⟨name, idx⟩ in paramArgs do
    unless ← isDefEq args[idx]! (← InclusionM.getParam name) do failure
  for ⟨elemIdx, setIdx, proofIdx⟩ in hypArgs do
    let inputExpr ← instantiateMVars args[elemIdx]!
    let body ← mkExprInclusionBody inputExpr
    unless ← isDefEq args[setIdx]! body.inclusionBody do failure
    unless ← isDefEq args[proofIdx]! body.proofBody do failure
  for h : i in [:args.size] do
    let argId := args[i].mvarId!
    unless ← argId.isAssigned do
      if binderInfos[i]!.isInstImplicit then
        argId.assign (← synthInstance (← argId.getType))
      else
        throwError "Could not infer theorem argument `{(← argId.getDecl).userName}` in inclusion \
          extension generated from `{.ofConstName theoremName}`"
  let inclusionBody ← instantiateMVars inclusionBody
  let proofBody ← instantiateMVars (mkAppN theoremExpr args)
  return { inclusionBody, proofBody }

/-- Apply the hypothesis theorem `theoremName` to `h` as its source hypothesis at `sourceIdx`,
recursively constructing the closed inclusion bodies specified by `hypArgs` and filling the
registered parameter arguments specified by `paramArgs`. -/
def deriveHypothesisOp (theoremName : Name) (sourceIdx : Nat) (hypArgs : Array HypArg)
    (paramArgs : Array ParamArg) (h : Expr) : HypothesisM Unit := do
  let hypType ← instantiateMVars (← inferType h)
  let theoremExpr ← mkConstWithFreshMVarLevels theoremName
  let (args, binderInfos, conclusion) ← forallMetaTelescopeReducing (← inferType theoremExpr)
  let sourceId := args[sourceIdx]!.mvarId!
  unless ← isDefEq (← sourceId.getType) hypType do failure
  sourceId.assign h
  let some (e, s, _) := toSetMem? conclusion | failure
  let e ← instantiateMVars e
  let some iVar ← findIVar? e | failure
  for ⟨name, idx⟩ in paramArgs do
    unless ← isDefEq args[idx]! (← HypothesisM.getParam name) do failure
  for ⟨elemIdx, setIdx, proofIdx⟩ in hypArgs do
    let inputExpr ← instantiateMVars args[elemIdx]!
    let body ← mkHypExprInclusionBody inputExpr
    unless ← isDefEq args[setIdx]! body.inclusionBody do failure
    unless ← isDefEq args[proofIdx]! body.proofBody do failure
  for h : i in [:args.size] do
    let argId := args[i].mvarId!
    unless ← argId.isAssigned do
      if binderInfos[i]!.isInstImplicit then
        argId.assign (← synthInstance (← argId.getType))
      else
        throwError "Could not infer theorem argument `{(← argId.getDecl).userName}` in \
          hypothesis extension generated from `{.ofConstName theoremName}`"
  let inclusionBody ← instantiateMVars s
  let proofBody ← instantiateMVars (mkAppN theoremExpr args)
  addInclusionHyp iVar.iExpr { inclusionBody, proofBody }

/-- Extract the `HypArg` and `ParamArg` metadata from a theorem declaration. -/
private def getOpArgInfo (declName : Name) (matchExpr : Expr)
    (args : Array Expr) (sourceIdx? : Option Nat := none) :
    MetaM (Array HypArg × Array ParamArg) := do
  let registeredParams := inclusionParamExt.getState (← getEnv)
  let mut hypArgs := #[]
  let mut params := #[]
  for h : i in [:args.size] do
    let argId := args[i].mvarId!
    let argDecl ← argId.getDecl
    let argType := argDecl.type
    if let some (e, s, _) := toSetMem? argType then
      let some elemIdx := args.findIdx? (· == e)
        | throwError "The member `{e}` in premise `{argType}` of theorem `{.ofConstName declName}` \
            is not a theorem variable"
      let some setIdx := args.findIdx? (· == s)
        | throwError "The set `{s}` in premise `{argType}` of theorem `{.ofConstName declName}` \
            is not a theorem variable"
      let elemId := args[elemIdx]!.mvarId!
      unless (matchExpr.findMVar? (· == elemId)).isSome do
        throwError "The recursive input `{e}` of theorem \
          `{.ofConstName declName}` does not occur in the matched expression"
      hypArgs := hypArgs.push { elemIdx, setIdx, proofIdx := i }
    else if sourceIdx? != some i then
      let userName := argDecl.userName
      if let some param := registeredParams.find? userName then
        unless ← isDefEq argType param.type do
          throwError "Inclusion parameter `{userName}` in `{.ofConstName declName}` has \
            type {argType}, expected {param.type}"
        if (matchExpr.findMVar? (· == argId)).isSome then
          throwError "Inclusion parameter `{userName}` in `{.ofConstName declName}` occurs in the \
            matched expression"
        params := params.push { name := userName, idx := i }
  return (hypArgs, params)

/-- Validate an inclusion theorem and return its discrimination-tree path and argument metadata. -/
private def getInclusionOpInfo (declName : Name) :
    MetaM (Array DiscrTree.Key × Array HypArg × Array ParamArg) := do
  let theoremExpr ← mkConstWithFreshMVarLevels declName
  let (args, _, conclusion) ← forallMetaTelescopeReducing (← inferType theoremExpr)
  let some (e, _, _) := toSetMem? conclusion
    | throwError "The conclusion of `{.ofConstName declName}` is not an inclusion using a `ToSet` \
        instance"
  let (hypArgs, params) ← getOpArgInfo declName e args
  return (← DiscrTree.mkPath e, hypArgs, params)

/-- Generate and register an inclusion extension from `theoremName` in `familyName`. -/
private def addInclusionOp (theoremName familyName : Name) (priority : Nat)
    (kind : AttributeKind) : AttrM Unit := do
  let (path, hypArgs, params) ← MetaM.run' <| getInclusionOpInfo theoremName
  let extName ← withDeclNameForAuxNaming theoremName do mkAuxDeclName `_inclusionExt
  let derive := mkAppN (mkConst ``deriveInclusionOp)
    #[toExpr theoremName, toExpr hypArgs, toExpr params]
  let value := mkAppN (mkConst ``InclusionExt.mk)
    #[toExpr extName, toExpr familyName, toExpr theoremName, derive, toExpr priority]
  let decl ← mkDefinitionValInferringUnsafe extName [] (mkConst ``InclusionExt) value .opaque
  addAndCompile (.defnDecl decl) (markMeta := true)
  addInclusionExt extName #[path] kind

/-- Syntax for registering an inclusion extension from a theorem using the `inclusion_op`
attribute. -/
syntax (name := inclusionOpAttr) "inclusion_op " ident (prio)? : attr

initialize registerBuiltinAttribute {
  name := `inclusionOpAttr
  descr := "adds an inclusion operation"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| inclusion_op $familyName:ident $[$_prio:prio]?) => do
      if (IR.getSorryDep (← getEnv) declName).isSome then return
      addInclusionOp declName familyName.getId (← getAttrParamOptPrio stx[2]) kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Inclusion operations cannot be erased by declaration"
}

/-- Validate a hypothesis theorem and return its discrimination-tree path and argument metadata. -/
private def getHypothesisOpInfo (declName : Name) :
    MetaM (Array DiscrTree.Key × Nat × Array HypArg × Array ParamArg) := do
  let theoremExpr ← mkConstWithFreshMVarLevels declName
  let (args, binderInfos, conclusion) ← forallMetaTelescopeReducing (← inferType theoremExpr)
  let some (e, s, _) := toSetMem? conclusion
    | throwError "The conclusion of `{.ofConstName declName}` is not an inclusion using a `ToSet` \
        instance"
  let mut sourceIdx? := none
  for h : i in [:args.size] do
    let argType ← args[i].mvarId!.getType
    if binderInfos[i]!.isExplicit && (toSetMem? argType).isNone && (← isProp argType) then
      if sourceIdx?.isSome then
        throwError "Hypothesis theorem `{.ofConstName declName}` has more than one non-inclusion \
          premise"
      sourceIdx? := some i
  let some sourceIdx := sourceIdx?
    | throwError "Hypothesis theorem `{.ofConstName declName}` has no non-inclusion premise"
  let sourceId := args[sourceIdx]!.mvarId!
  let sourceType ← sourceId.getType
  if (e.findMVar? (· == sourceId)).isSome then
    throwError "The source hypothesis of `{.ofConstName declName}` occurs in its represented \
      expression"
  if (s.findMVar? (· == sourceId)).isSome then
    throwError "The source hypothesis of `{.ofConstName declName}` occurs in its output inclusion"
  let (hypArgs, params) ← getOpArgInfo declName sourceType args (some sourceIdx)
  for ⟨name, idx⟩ in params do
    let paramId := args[idx]!.mvarId!
    if (e.findMVar? (· == paramId)).isSome then
      throwError "Inclusion parameter `{name}` in `{.ofConstName declName}` occurs in the \
        represented expression"
  return (← DiscrTree.mkPath sourceType, sourceIdx, hypArgs, params)

/-- Generate and register a hypothesis extension from `theoremName` in `familyName`. -/
private def addHypothesisOp (theoremName familyName : Name) (priority : Nat)
    (kind : AttributeKind) : AttrM Unit := do
  let (path, sourceIdx, hypArgs, params) ← MetaM.run' <| getHypothesisOpInfo theoremName
  let extName ← withDeclNameForAuxNaming theoremName do mkAuxDeclName `_hypothesisExt
  let derive := mkAppN (mkConst ``deriveHypothesisOp)
    #[toExpr theoremName, toExpr sourceIdx, toExpr hypArgs, toExpr params]
  let value := mkAppN (mkConst ``HypothesisExt.mk)
    #[toExpr extName, toExpr familyName, toExpr theoremName, derive, toExpr priority]
  let decl ← mkDefinitionValInferringUnsafe extName [] (mkConst ``HypothesisExt) value .opaque
  addAndCompile (.defnDecl decl) (markMeta := true)
  addHypothesisExt extName #[path] kind

/-- Syntax for registering a hypothesis extension from a theorem using the `hypothesis_op`
attribute. -/
syntax (name := hypothesisOpAttr) "hypothesis_op " ident (prio)? : attr

initialize registerBuiltinAttribute {
  name := `hypothesisOpAttr
  descr := "adds an inclusion-hypothesis operation"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| hypothesis_op $familyName:ident $[$_prio:prio]?) => do
      if (IR.getSorryDep (← getEnv) declName).isSome then return
      addHypothesisOp declName familyName.getId (← getAttrParamOptPrio stx[2]) kind
    | _ => throwUnsupportedSyntax
  erase := fun _ => throwError "Hypothesis operations cannot be erased by declaration"
}

end Inclusion
