import Lean.Elab.Command
import Lean.Linter.Util

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
      usedVarsRef.modify (·.insert a)
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
        dbg_trace "decls: {(← getLCtx).decls.toArray.toList.reduceOption.map (·.userName)}"
        let newName := `DoneHere ++ (← liftCommandElabM do liftCoreM do mkFreshUserName `D) ++
          ((← getLCtx).decls.toArray.toList.reduceOption.getLastD default).userName
        dbg_trace "newName: {newName}"
        let dh ← `(command|
          def $(mkIdent newName) : $(mkIdent `Array) $(mkIdent `String) := $(⟨ps⟩))
        liftCommandElabM do
          elabCommand dh
          elabCommand (← `(#check $(mkIdent newName)))

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
  dbg_trace "elaborated renStx"
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

initialize addLinter unusedVariableCommandLinter

end UnusedVariableCommand

end Mathlib.Linter
