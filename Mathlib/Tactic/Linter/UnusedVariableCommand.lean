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

namespace UnusedVariableCommand

initialize usedVarsRef : IO.Ref NameSet ← IO.mkRef {}

/-- returns the unique `Name`, the user `Name` and the `Expr` of each `variable` that is
present in the current context. -/
def includedVariables (plumb : Bool) : TermElabM (Array (Name × Name × Expr)) := do
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
      if plumb then usedVarsRef.modify (·.insert a)
  return varIds

elab "included_variables" plumb:(ppSpace "plumb")? : tactic => Tactic.withMainContext do
    let (_plb, usedUserIds) := (← includedVariables plumb.isSome).unzip
    let msgs ← usedUserIds.mapM fun (userName, expr) =>
      return m!"'{userName}' of type '{← Meta.inferType expr}'"
    if ! msgs.isEmpty then
      logInfo m!"{msgs.foldl (m!"{·}\n" ++ m!"* {·}") "Included variables:"}"

@[inherit_doc Mathlib.Linter.linter.unusedVariableCommand]
def unusedVariableCommandLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.unusedVariableCommand (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  unless stx.isOfKind ``declaration do
    return
  if stx[1].isOfKind ``Lean.Parser.Command.example then
    logInfo "skipping examples: they have access to all the variables anyway"
    return
  let renStx ← stx.replaceM fun s => match s.getKind with
      | ``declId        => return some (← `(declId| $(mkIdentFrom s[0] (s[0].getId ++ `_hello))))
      | ``declValSimple => return some (← `(declValSimple| := by included_variables plumb; sorry))
      | _               => return none
  let s ← get
  elabCommand renStx
  set s

initialize addLinter unusedVariableCommandLinter

end UnusedVariableCommand

end Mathlib.Linter
