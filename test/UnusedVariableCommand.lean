import Mathlib.Tactic.Linter.UnusedVariableCommand
import Mathlib.adomaniLeanUtils.inspect_syntax
import Lean.Elab.Syntax

open Lean Elab Command Mathlib.Linter.UnusedVariableCommand in
elab "mkt " cmd:command : command => do
  elabCommand cmd
  let thm ← mkThm cmd
  logInfo m!"{thm}"
  elabCommand thm
def toFalse (_S : Sort _) := False

set_option linter.unusedVariableCommand true
/--
info: theorem XX.sfx {a b : Nat} (c d : Int) [Add Int] : toFalse True := by included_variables plumb; sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
mkt
theorem XX {a b : Nat} (c d : Int) [Add Int] : True := .intro

/--
info: theorem D.sfx [Add Nat] [Mul Int] : False := by included_variables plumb; sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
mkt
structure D extends Add Nat, Mul Int where mk'::
  a : Nat
  b : Int
#check Lean.Elab.Command.elabSyntax
section
set_option pp.rawOnError true
open Lean Elab Command
universe u
run_cmd
  let stx ← `(command| def $(mkIdent `A).{u} := 0)
  --let elS ← elabSyntax stx
  let did := (stx.raw.find? (·.isOfKind ``Parser.Command.declId)).getD default
  let prt := did.prettyPrint.pretty
  if "A" == prt then
    logInfo "Equal"
  else
    let simplStx ← stx.raw.replaceM fun s => do
      if s.isOfKind ``Parser.Command.declId then
        `(declId|$(mkIdentFrom s s[0].getId))
      else return none
    logWarning m!"Different {prt} {did[0]}\n{simplStx}"
#check Parser.Term.explicitUniv
--inspect
variable {R : Type u} [Zero.{u} R]
set_option showDefs true in
example : (0 : R) = 0 := rfl

/-
inspect: 'variable [Zero.{u} R]'

|   |   |-node Lean.Parser.Term.app, none
|   |   |   |-node Lean.Parser.Term.explicitUniv, none
|   |   |   |   |-ident original: ⟨⟩⟨⟩-- (Zero,Zero)
|   |   |   |   |-atom original: ⟨⟩⟨⟩-- '.{'
|   |   |   |   |-node null, none
|   |   |   |   |   |-ident original: ⟨⟩⟨⟩-- (u,u)
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '}'
|   |   |   |-node null, none
|   |   |   |   |-ident original: ⟨⟩⟨⟩-- (R,R)
|   |   |-atom original: ⟨⟩⟨⏎⏎⏎⟩-- ']'
-/
/-
inspect: 'variable [Zero R]'

|   |   |-node Lean.Parser.Term.app, none
|   |   |   |-ident original: ⟨⟩⟨ ⟩-- (Zero,Zero)
|   |   |   |-node null, none
|   |   |   |   |-ident original: ⟨⟩⟨⟩-- (R,R)
|   |   |-atom original: ⟨⟩⟨⏎⏎⏎⟩-- ']'
-/
inspect
variable [Zero R]


end
