import Mathlib.Geometry.Manifold.IsManifold.Basic

open Lean Meta Elab Command PrettyPrinter Delaborator Parser.Command
open Parser.Term SubExpr TSyntax.Compat

open private shouldGroupWithNext from Lean.PrettyPrinter.Delaborator.Builtins

namespace Std.Command.Show

/-- Almost the same as `Lean.PrettyPrinter.Delaborator.delabConstWithSignature.delabParams`
but with the option to not print the type or identifier -/
partial def delabParamsImpl (idStx? : Option Ident) (groups : TSyntaxArray ``bracketedBinder)
    (curIds : Array Ident) := do
  if let .forallE n d _ i ← getExpr then
    let stxN ← annotateCurPos (mkIdent n)
    let curIds := curIds.push ⟨stxN⟩
    if ← shouldGroupWithNext then
      withBindingBody n <| delabParamsImpl idStx? groups curIds
    else
      let delabTy := withOptions (pp.piBinderTypes.set · true) delab
      let group ← withBindingDomain do
        match i with
        | .implicit       => `(bracketedBinderF|{$curIds* : $(← delabTy)})
        | .strictImplicit => `(bracketedBinderF|⦃$curIds* : $(← delabTy)⦄)
        | .instImplicit   => `(bracketedBinderF|[$curIds.back! : $(← delabTy)])
        | _ =>
          if d.isOptParam then
            `(bracketedBinderF|
                ($curIds* : $(← withAppFn <| withAppArg delabTy) := $(← withAppArg delabTy)))
          else if let some (.const tacticDecl _) := d.getAutoParamTactic? then
            let tacticSyntax ← ofExcept <| evalSyntaxConstant (← getEnv) (← getOptions) tacticDecl
            `(bracketedBinderF|
                ($curIds* : $(← withAppFn <| withAppArg delabTy) := by $tacticSyntax))
          else
            `(bracketedBinderF|($curIds* : $(← delabTy)))
      withBindingBody n <| delabParamsImpl idStx? (groups.push group) #[]
  else
    if let some idStx := idStx? then
      let type ← delab
      `(declSigWithId| $idStx:ident $groups* : $type)
    else
      `(optDeclSig| $groups*)

/-- Pretty-prints a constant `c` as `c <params> : <type>`.
Here `type` need not be the actual type of `c`.
If `c` is `none`, then only print `<params>`.
This is similar to `delabConstWithSignature`, but with an explicit type `eType` given,
and the flexibility to not print `c` and `<type>`. -/
def delabWithType (e : Option Expr) (eType : Expr) : MetaM FormatWithInfos := do
  let (stx, infos) ← delabCore default (delab := delabConstOfTypeWithSignature e eType)
  return ⟨← ppTerm ⟨stx⟩, infos⟩
where
  /- Delaborator for `delabWithType`. -/
  delabConstOfTypeWithSignature (c : Option Expr) (type : Expr) : Delab := do
    -- use virtual expression node of arity 2 to separate name and type info
    let idStx ← c.mapM (descend · 0 <| withOptions (pp.fullNames.set · true) delabConst)
    descend type 1 <| delabParamsImpl idStx #[] #[]

open MessageData
/- Returns a pretty-printed version of the type of `e`,
but only printing the arguments satisfying `p`.
If `showName` is false, then the name and the conclusion are not printed.
-/
def printFilteredDecl (e : Expr) (p : Expr → MetaM Bool) (showName := true) :
    MetaM (Option MessageData) := do
  forallTelescope (← inferType e) fun bis t => do
    let args ← bis.filterM p
    if args.isEmpty && !showName then
      return none
    let filteredType ← mkForallFVars args t
    return  m!"{ofFormatWithInfosM <| delabWithType (if showName then e else none) filteredType}"

/-- `print sep m?` prints `m?` if it is not `none`, with separator `sep`. -/
def print : MessageData → Option MessageData → MessageData
  | _, none => ""
  | sep, some msg => sep ++ msg

/-- The implementation for the `#show` command. `e` must be a constant. -/
def showCmd (e : Expr) : MetaM MessageData := do
  let some explicitMsg ← printFilteredDecl e
    fun bi => return (← bi.fvarId!.getBinderInfo) == BinderInfo.default | unreachable!
  let instMsg ← printFilteredDecl e (showName := false)
    fun bi => return (← bi.fvarId!.getBinderInfo) == BinderInfo.instImplicit
  let implicitMsg ← printFilteredDecl e (showName := false) fun bi =>
    return [BinderInfo.implicit, BinderInfo.strictImplicit].contains (← bi.fvarId!.getBinderInfo)
  return explicitMsg ++ print "\ninstances: " instMsg ++ print "\nimplicits: " implicitMsg

/- The `#show <id>` prints the identifier `<id>` in a similar way to `#check <id>`,
but separates the arguments into explicit, instance and implicit arguments,
so that the most important information is more easily seen at a glance. -/
elab "#show " stx:ident : command =>
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_show do
    try
      for c in (← resolveGlobalConst stx) do -- was: resolveGlobalConstWithInfos
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

-- todo: don't show instance names. I think it worked in a previous commit.

#show smoothManifoldWithCorners_of_contDiffOn
#show ContDiff.of_le
#show Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
-- #show 1 + 1
-- #show Prod.mk
-- #check ContDiff.of_le

end Std.Command.Show
