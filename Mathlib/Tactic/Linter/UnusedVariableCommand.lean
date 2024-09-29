import Lean.Elab.Command
import Lean.Linter.Util
import Mathlib.adomaniLeanUtils.inspect_syntax
import Mathlib.adomaniLeanUtils.inspect_rec

/-!
#  The "unusedVariableCommand" linter

The "unusedVariableCommand" linter emits a warning when a variable declared in `variable ...`
is globally unused.
-/

open Lean Parser Elab Command

namespace Lean.Syntax
/-!
# `Syntax` filters
-/

partial
def filterMapM {m : Type → Type} {α : Type} [Monad m] (stx : Syntax) (f : Syntax → m (Option α)) :
    m (Array α) := do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs

def filterMap {α : Type} (stx : Syntax) (f : Syntax → Option α) : Array α :=
  stx.filterMapM (m := Id) f

def filter (stx : Syntax) (f : Syntax → Bool) : Array Syntax :=
  stx.filterMap (fun s => if f s then some s else none)

end Lean.Syntax

namespace Mathlib.Linter

/--
The "unusedVariableCommand" linter emits a warning when a variable declared in `variable ...`
is globally unused.
-/
register_option linter.unusedVariableCommand : Bool := {
  defValue := true
  descr := "enable the unusedVariableCommand linter"
}

def getODS (stx : Syntax) : Option Syntax :=
  match stx.find? (·.isOfKind ``optDeclSig) with
    | some ds => some ds
    | none => stx.find? (·.isOfKind ``declSig)

namespace UnusedVariableCommand

initialize usedVarsRef : IO.Ref NameSet ← IO.mkRef {}

open Lean.Parser.Term in
/-- Return identifier names in the given bracketed binder. -/
def getBracketedBinderIdsAndTypes (stx : Syntax) : CommandElabM (Array Name × Array Name) := do
  let (ids, stxs) := match stx with
    | `(bracketedBinderF|($ids* $[: $ty?]? $(annot?)?)) =>
      (ids.map Syntax.getId, [ty?.map (·.raw), annot?.map (·.raw)])
    | `(bracketedBinderF|{$ids* $[: $ty?]?})             =>
      (ids.map Syntax.getId, [ty?.map (·.raw)])
    | `(bracketedBinderF|⦃$ids* : $ty⦄)                   =>
      (ids.map Syntax.getId, [ty])
    | `(bracketedBinderF|[$id : $ty])                     => (#[id.getId], [ty])
    | `(bracketedBinderF|[$_])                           => (#[Name.anonymous], [])
    | _                                                  => default --throwUnsupportedSyntax
  if ids.isEmpty then throwUnsupportedSyntax
  let x := stxs.reduceOption.map (·.filterMap fun d => if d.isIdent then some d.getId else none)
  return (ids, x.toArray.flatten)



def showInfoTree : Info → MessageData
  | .ofTacticInfo i => m!"TacticInfo stx: '{i.stx}'"
  | .ofTermInfo i => m!"TermInfo expr: '{i.expr}' expType: '{i.expectedType?}' stx: '{i.stx}'"
  | .ofCommandInfo i => m!"CommandInfo stx: '{i.stx}'"
  | .ofMacroExpansionInfo i => m!"MacroExpansionInfo stx: '{i.stx}'"
  | .ofOptionInfo i => m!"OptionInfo stx: '{i.stx}'"
  | .ofFieldInfo i => m!"FieldInfo stx: '{i.stx}'"
  | .ofCompletionInfo i => m!"CompletionInfo stx: '{i.stx}'"
  | .ofUserWidgetInfo i => m!"UserWidgetInfo stx: '{i.stx}'"
  | .ofCustomInfo i => m!"CustomInfo stx: '{i.stx}'"
  | .ofFVarAliasInfo i => m!"FVarAliasInfo username: '{i.userName}'"
  | .ofFieldRedeclInfo i => m!"FieldRedeclInfo stx: '{i.stx}'"
  | .ofOmissionInfo i => m!"OmissionInfo stx: '{i.stx}'"

/--  `treeM ex` takes an expression and returns a pair consisting of
*  `MessageData` for the non-`Expr` arguments of `ex`,
*  an array of the `Expr` arguments to `ex`.

If `ex` is of the form `(Expr.app ..)`, then the array of arguments is `ex.getAppArgs`.
-/
def treeM : InfoTree → MessageData × Array InfoTree
  | .context i t =>
    let ctx := if let .parentDeclCtx n := i then m!"parentDeclCtx {n}" else "commandCtx"
    (m!"context '{ctx}'", #[t])
  | .node i children => (m!"node '{showInfoTree i}'", children.toArray)
  | .hole _mvarId => (m!"hole _", #[])

/--  `treeR ex` recursively formats the output of `treeM`. -/
partial
def treeR (stx : InfoTree) (indent : MessageData := "\n") (sep : MessageData := "  ") :
    MessageData :=
  let (msg, es) := treeM stx
  let mes := es.map (treeR (indent := indent ++ sep) (sep := sep))
  mes.foldl (fun x y => (x.compose indent).compose ((m!"|-").compose y)) msg

/-- `inspect ex` calls `logInfo` on the output of `treeR ex`.
Setting to `false` the optional boolean argument `ctor?` omits printing the various `ctorName`s. -/
def IT.inspect {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (stx : InfoTree) : m Unit :=
  logInfo (m!"inspecting InfoTree: 'stx'\n\n".compose (treeR stx (sep := "|   ")))

elab (name := inspectStx) "inspectit " cmd:command : command => do
  Command.elabCommand cmd
  let its ← getInfoTrees
  for it in its do
    logInfo (m!"inspect infotrees: '{← it.format}'\n\n".compose (treeR it (sep := "|   ")))


/-- returns the unique `Name`, the user `Name` and the `Expr` of each `variable` that is
present in the current context. -/
def includedVariables : TermElabM (Array (Name × Name × Expr)) := do
  let c ← read
  let fvs := c.sectionFVars
  let mut varIds := #[]
  let lctx ← getLCtx
  for (a, b) in fvs do
    if (lctx.findFVar? b).isSome then
      let mut fd := .anonymous
      for (x, y) in c.sectionVars do
        if y == a then fd := x
      varIds := varIds.push (a, fd, b)
  return varIds

elab "included_variables" plumb:(ppSpace "plumb")? : tactic => Tactic.withMainContext do
    let (plb, usedUserIds) := (← includedVariables).unzip
    let msgs ← usedUserIds.mapM fun (userName, expr) =>
      return m!"'{userName}' of type '{← Meta.inferType expr}'"
    if ! msgs.isEmpty then
      if plumb.isNone then
        logInfo m!"{msgs.foldl (m!"{·}\n" ++ m!"* {·}") "Included variables:"}"
      else
        --logInfo m!"{plb.foldl (m!"{·}\n" ++ m!"{·}") ""}"
        --logWarning m!"{plb.foldl (m!"{·}\n" ++ m!"{·}") ""}"
        --logError m!"{plb.foldl (m!"{·}\n" ++ m!"{·}") ""}"
        let mut ps : Syntax ← `(#[])
        --let c ← readThe Term.Context
        --let sNames := c.sectionVars.toList.map Prod.snd
        --let sNamesRev : List (Name × Name) := c.sectionVars.toList.map fun (a, b) => (b, a)
        --let mut pex : Expr ← Meta.mkAppOptM ``Array.empty #[some (mkConst ``String)]
        for n in plb do
          --pex ← Meta.mkAppM ``Array.push #[pex, .lit (.strVal n.toString)]
          --logInfo m!"n: {n}"
          --let sname := (sNames.find? (· == n)).getD default
          --logInfo m!"sname: {sname}"
          --let sname := (sNamesRev.find? (·.1 == n)).getD default
          --dbg_trace "visiting"

          ps ← `($(mkIdent `Array.push) $(⟨ps⟩) $(Syntax.mkStrLit n.toString)) --sname.2))
        --logInfo m!"ps: {ps}\npex: {pex}"
        --let s : TSyntaxArray `term  := plb.map fun n => Syntax.mkNameLit "n.toString"
        --let s : TSyntaxArray `term  := default
        --let hi := mkIdent `n
        --let pexS ← Term.exprToSyntax pex
        let dh ← `(command|
          def $(mkIdent `DoneHere) : $(mkIdent `Array) $(mkIdent `String) := $(⟨ps⟩))
            --#[`hi].push `hi) --#[$s,*])
        --logInfo m!"pex: {pex}\npexS: {pexS}"
        --let dh ← `(command| def $(mkIdent `DoneHere) : $(mkIdent `Array) $(mkIdent `String) := $pexS) --$(⟨ps⟩)) --#[$s,*])
        --liftCommandElabM do elabCommand (← `(#check $(⟨ps⟩)))
        liftCommandElabM do
          elabCommand dh
          elabCommand (← `(#check $(mkIdent `DoneHere)))
        --dbg_trace plb
        --logInfo dh
        --IO.eprint s!"{plb}"
        --dbg_trace "{plb}"
        --throwError m!"{plb.foldl (m!"{·}\n" ++ m!"{·}") ""}"
--#check mkNameLit
--#check Meta.mkAppM
--#check Term.exprToSyntax
--#check Name.eraseMacroScopes
set_option pp.rawOnError true
variable (n : Nat)
example : n = n := by
  included_variables plumb
  rfl
  --exact .intro
--include n in
--#check #[n]
--#print DoneHere

#check mkArray
partial
def getFVars : InfoTree → TermElabM NameSet
  | .context (.commandCtx c) t => do
    --let metavarCtx := c.mctx
    --dbg_trace "context, commandCtx"
    --for (mv, d) in metavarCtx.decls do
    --  dbg_trace d.type
    let fvs ← includedVariables
    if !fvs.isEmpty then
    --  dbg_trace "oh no!"
    --else
      dbg_trace "\n** included vars: {fvs}\n"
    getFVars t
  | .context _i t => do
    let fvs ← includedVariables
    if !fvs.isEmpty then
    --  dbg_trace "oh no!"
    --else
      dbg_trace "\n** included vars: {fvs}\n"
    getFVars t
  | .node i ts => do
    let fvs ← includedVariables
    if !fvs.isEmpty then
    --  dbg_trace "oh no!"
    --else
      dbg_trace "\n** included vars: {fvs}\n"
    let base := (← ts.toArray.mapM getFVars)
    if let .ofTermInfo ti := i then
      --dbg_trace "TermInfo"
      --dbg_trace "elaborator: ({ti.elaborator}, {ti.stx})"
      --dbg_trace "decls names:\n{ti.lctx.decls.toList.reduceOption.map fun d => (d.fvarId.name, d.userName)}\nExpr and extype:\n'{(ti.expr, ti.expectedType?)}'"
      let is := i.stx.filterMap fun d => if d.isIdent then some d.getId else none
      --dbg_trace "this stage: {is} {[i.stx.getPos?, i.stx.getTailPos?].reduceOption}"
      --dbg_trace "FVars names:\n{ti.lctx.getFVarIds.map (·.name)}\n"
      --dbg_trace "fvars: {ti.lctx.getFVars}"
      --Meta.inspect i.stx
      return base.foldl (·.append ·) (.ofList is.toList)
    if let .ofCommandInfo ti := i then
      --dbg_trace "CommandInfo {ti.stx}"
    --if let .ofContextInfo ti := i then
    --  dbg_trace "ContextInfo {ti.stx}"

      return base.foldl (·.append ·) {}
    else return base.foldl (·.append ·) {}
  | .hole _m => dbg_trace _m.name; return {}
--#check declId

def easyStr : Expr → Array String
  | .app f g => easyStr f ++ easyStr g
  | .lit (.strVal v) => #[v]
  | _ => #[]

@[inherit_doc Mathlib.Linter.linter.unusedVariableCommand]
def unusedVariableCommandLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.unusedVariableCommand (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  if stx[1].isOfKind ``Lean.Parser.Command.example then
    logInfo "skipping examples: they have access to all the variables anyway"
    return
  unless stx.isOfKind ``declaration do
    return
  let renStx ← stx.replaceM fun s => do
    match s.getKind with
      | ``declId =>
        let nid ← `(declId| $(mkIdentFrom s[0] (s[0].getId ++ `_hello)))
        return some nid
      | ``declValSimple =>
        let newPf ← `(declValSimple| := by included_variables plumb; sorry)
        return some newPf
      | _ => return none

  --logInfo renStx
  --let mut msgs := #[]
  let s ← get
  --logInfo renStx
    --renStx ← `()
  elabCommand renStx
  --elabCommand (← `(#print $(mkIdent `DoneHere)))
  --msgs := (← get).messages.toArray --.filter (·.severity == .information)
  --set s
  --dbg_trace "msgs: '{← msgs.mapM (·.toString)}'"
  --dbg_trace "stdOut: '{← (← IO.getStderr).getLine}'"
  --dbg_trace "{((← getEnv).find? `DoneHere).isSome}"
  --logInfo m!"{← msgs.mapM (·.toString)}"
  if let .defnInfo val := ((← getEnv).find? `DoneHere).getD default then
    let varAsStrings := easyStr val.value
    --dbg_trace "defnInfo"
    --dbg_trace val.value
    dbg_trace "\nvalues:\n{varAsStrings}\n"
    --dbg_trace val.value.find? (·.isLit)
  else
    dbg_trace "not a defnInfo"
  set s

#eval (default : ConstantInfo).ctorName

#check Expr.find?
--#check visit

@[inherit_doc Mathlib.Linter.linter.unusedVariableCommand]
def unusedVariableCommandLinter1 : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.unusedVariableCommand (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let its := (← getInfoTrees).toArray
  --for it in its do IT.inspect it
  --dbg_trace "showInfoTree"
  --dbg_trace its.map showInfoTree
  --dbg_trace "\n"
  dbg_trace "getFVars output:\n{(← liftTermElabM do its.mapM getFVars).map (·.toArray)}\n"
  dbg_trace "UIds: {(← getScope).varUIds}"
  let varsInScope := (← getScope).varDecls
--  let (consVars1, typeVars1) := (← varsInScope.mapM getBracketedBinderIdsAndTypes).unzip
  let consVars := (← varsInScope.mapM getBracketedBinderIds)
  let mut varIdsToStx : Std.HashMap Name String.Range := {}
  for v in varsInScope do
    let vs ← getBracketedBinderIds v
    for w in vs do
      varIdsToStx := varIdsToStx.insert w (v.raw.getRange?.getD default)
  --let varsIdsInScope := Array.flatten <| ← varsInScope.mapM getBracketedBinderIds
  match getODS stx with
    | none => pure ()
    | some ds =>
      -- `include`d variables are added by

      let vars := ds[0].getArgs
      let varsInDecl := Array.flatten <| ← vars.mapM getBracketedBinderIds
      for v in (← getScope).includedVars do
        --dbg_trace "available vars: {(← getScope).varUIds}"
        let vVarIdx := (← getScope).varUIds.findIdx? (· == v) |>.getD 0
        let varName := consVars.getD vVarIdx default --.anonymous
        dbg_trace "included {v} <--> {varName}"
--      if stx.isOfKind ``Lean.Parser.Command.include then
--        for v in stx[1].getArgs do
        --usedVarsRef.modify (·.insert varName)
        --idx := idx+1
      let explicitIdents := ds[1].filterMap fun i => if i.isIdent then some i.getId else none
      for (e, _rg) in varIdsToStx do
        if explicitIdents.contains e && ! varsInDecl.contains e then
          usedVarsRef.modify (·.insert e)
          --dbg_trace "inserted {e}"
  if isTerminalCommand stx then
    --dbg_trace (← usedVarsRef.get).toArray
    let usedVars ← usedVarsRef.get
    for (e, rg) in varIdsToStx do
      if !usedVars.contains e then
        --dbg_trace e
        --let rg := varIdsToStx[e]?.getD default
        Linter.logLint linter.unusedVariableCommand (.ofRange rg) m!"'{e}' is unused"
      --dbg_trace (varsInDecl, explicitIdents)
      --let mut usedVars : NameSet := {}
      --for e in explicitIdents do
        --if varsInDecl.contains e then --continue
          --usedVars := usedVars.insert e
      --Linter.logLint linter.unusedVariableCommand (vars.getD 0 default)
      --  (m!"Used variables: '{usedVars.toArray}'")

initialize addLinter unusedVariableCommandLinter

end UnusedVariableCommand

end Mathlib.Linter
