import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
-- todo: clean up a lot

open Lean Meta Elab Command PrettyPrinter Delaborator Parser.Command
open Lean.Meta
open Lean.Parser.Term
open SubExpr
open TSyntax.Compat

def shouldGroupWithNext (bis : Array Expr) (k : Nat) : DelabM Bool := do
  if h : k + 1 < bis.size then
    let ppEType ← getPPOption getPPPiBinderTypes
    let fvarId := bis[k]!.fvarId!
    let fvarId' := bis[k+1].fvarId!
    return (← fvarId.getBinderInfo) == (← fvarId'.getBinderInfo) &&
      (← fvarId.getType) == (← fvarId'.getType) &&
      (← fvarId.getBinderInfo) != BinderInfo.instImplicit &&
      ((← fvarId.getBinderInfo) != BinderInfo.default || ppEType)
  else
    return false

/-- `info` optionally contains the identifier and type. -/
partial def delabParamsImpl (groups : TSyntaxArray ``bracketedBinder)
    (curIds : Array Ident) (bis : Array Expr) (k : Nat) : Delab := do
  if h : k < bis.size then
    let fvarId := bis[k].fvarId!
    let n ← fvarId.getUserName
    let d ← fvarId.getType
    let i ← fvarId.getBinderInfo
    let stxN ← annotateCurPos (mkIdent n)
    let curIds := curIds.push ⟨mkIdent n⟩
    if ← shouldGroupWithNext bis k then
      delabParamsImpl groups curIds bis (k+1)
    else
      let delabTy := withOptions (pp.piBinderTypes.set · true) <| delab d
      let group ← do
        match i with
        | .implicit       => `(bracketedBinderF|{$curIds* : $(← delabTy)})
        | .strictImplicit => `(bracketedBinderF|⦃$curIds* : $(← delabTy)⦄)
        | .instImplicit   =>
          if n.hasMacroScopes then
            `(bracketedBinderF|[$(← delabTy)])
          else
            `(bracketedBinderF|[$curIds.back : $(← delabTy)])
        | _ =>
          if d.isOptParam then
            `(bracketedBinderF|($curIds* : $(← withAppFn <| withAppArg delabTy) := $(← withAppArg delabTy)))
          else if let some (.const tacticDecl _) := d.getAutoParamTactic? then
            let tacticSyntax ← ofExcept <| evalSyntaxConstant (← getEnv) (← getOptions) tacticDecl
            `(bracketedBinderF|($curIds* : $(← withAppFn <| withAppArg delabTy) := by $tacticSyntax))
          else
            `(bracketedBinderF|($curIds* : $(← delabTy)))
      delabParamsImpl (groups.push group) #[] bis (k+1)
  else
    `(optDeclSig| $groups*)

def delabParams (bis : Array Expr) : MetaM FormatWithInfos := do
  let (stx, infos) ← delabCore default (delab := delabParamsImpl #[] #[] bis 0)
  -- delabParamsImpl info #[] #[] bis 0
  --   { optionsPerPos := .empty
  --     currNamespace := (← getCurrNamespace)
  --     openDecls := (← getOpenDecls)
  --     subExpr := ⟨default, Pos.root⟩
  --     inPattern := (← getOptions).getInPattern } |>.run {}
  return ⟨← ppTerm ⟨stx⟩, infos⟩

/-- Pretty-prints a constant `c` as `c.{<levels>} <params> : <type>`. -/
partial def delabConstOfTypeWithSignature (eType : Expr) : Delab := do
  let e ← getExpr
  -- use virtual expression node of arity 2 to separate name and type info
  let idStx ← descend e 0 <|
    withOptions (/-pp.universes.set · true |>-/ (pp.fullNames.set · true)) delabConst
  descend eType 1 <|
    delabConstWithSignature.delabParams idStx #[] #[]

def delabExplicits (eValue e : Expr) : MetaM FormatWithInfos := do
  let (stx, infos) ← delabCore eValue (delab := delabConstOfTypeWithSignature e)
  return ⟨← ppTerm ⟨stx⟩, infos⟩

def ofFormatWithInfos (t : MetaM FormatWithInfos) : MessageData :=
.ofPPFormat { pp := fun
  | some ctx => ctx.runMetaM t
  | none     => pure "" }

syntax (name := myshow) "#show" term : command

def showCmd (eValue : Expr) : MetaM MessageData := do
  let e ← inferType eValue
  forallTelescope e fun bis t => do
    let explicits ← bis.filterM fun bi => return (← bi.fvarId!.getBinderInfo) == BinderInfo.default
    let implicits ← bis.filterM fun bi =>
      return [BinderInfo.implicit, BinderInfo.strictImplicit].contains (← bi.fvarId!.getBinderInfo)
    let insts ← bis.filterM fun bi => return (← bi.fvarId!.getBinderInfo) == BinderInfo.instImplicit
    let explicittype ← mkForallFVars explicits t
    let explicitMsg : MessageData :=
      m!"{ofFormatWithInfos <| delabExplicits eValue explicittype}"
    let implicitMsg : MessageData :=
      if implicits.isEmpty then "" else m!"\nimplicits:{ofFormatWithInfos <| delabParams implicits}"
    let instMsg : MessageData :=
      if insts.isEmpty then "" else m!"\ninstances:{ofFormatWithInfos <| delabParams insts}"
    logInfo m!"{explicitMsg}{implicitMsg}{instMsg}"
    return ""

elab "#show " stx:term : command =>
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_show do
    -- show signature for `#show id`/`#show @id`
    if let `($_:ident) := stx then
      try
        for c in (← resolveGlobalConstWithInfos stx) do
          addCompletionInfo <| .id stx c (danglingDot := false) {} none
          let decl ← getConstInfo c
          let e := .const c (decl.levelParams.map mkLevelParam)
          logInfo m!"{← showCmd e}"
          return
      catch _ => pure ()  -- identifier might not be a constant but constant + projection
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    if e.isSyntheticSorry then
      return
    logInfo m!"{← showCmd e}"

-- todo: mouseover on (inst)implicits doesn't work yet

#show smoothManifoldWithCorners_of_contDiffOn
#show extChartAt_source_mem_nhdsWithin
#show ContDiff.of_le
#show Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
#check ContDiff.of_le
