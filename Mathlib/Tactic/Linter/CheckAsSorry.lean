import Lean.Linter.Util
import Lean.Elab.Command
import Mathlib.Tactic.Lemma

/-!
#  The "checkAsSorry" linter

The "checkAsSorry" linter emits a warning when replacing the proof of a `theorem` or `lemma` by
`sorry` yields a declaration whose type is not equal to the original declaration.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- The "checkAsSorry" linter emits a warning when there are multiple active goals. -/
register_option linter.checkAsSorry : Bool := {
  defValue := true
  descr := "enable the checkAsSorry linter"
}

def toExample {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Option (Syntax × Syntax))
  | `($dm:declModifiers theorem $did:declId $ds* : $t := $_t:term) => do
    return some (← `($dm:declModifiers theorem $did $ds* : $t := sorry), did.raw[0])
  | `($dm:declModifiers lemma $did:declId $ds* : $t := $_t:term) => do
    return some (← `($dm:declModifiers lemma $did $ds* : $t := sorry), did.raw[0])
--  | `($dm:declModifiers example $ds:optDeclSig $dv:declVal) => do
--    return some (← `($dm:declModifiers example $ds $dv:declVal), mkIdent `example)
  | _ => return none

namespace CheckAsSorry

/-- Gets the value of the `linter.checkAsSorry` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.checkAsSorry o

@[inherit_doc Mathlib.Linter.linter.checkAsSorry]
def checkAsSorryLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some stx :=
      stx.find? ([`lemma, ``Lean.Parser.Command.declaration].contains ·.getKind)
    then
      let nm ← liftCoreM do mkFreshUserName `asSorry
      let sc ← getScope
      let ns := sc.currNamespace ++ nm
      if let some (newCmd, id) ← toExample stx then
        let declName ← resolveGlobalConstNoOverload id
        let refType := (((← getEnv).find? declName).getD default).type
        withScope (fun _ => { sc with currNamespace := ns }) do
          let s ← modifyGet fun st => (st, { st with messages := {} })
          elabCommand newCmd
          let _ ← modifyGet fun st => (s, { st with messages := s.messages })

          match (← getEnv).find? (ns ++ id.getId) with
            | none => logWarningAt id "could not find the 'asSorried' declaration"
            | some decl =>
              if refType == decl.type then
                return --logInfoAt id m!"'{declName}' works"
              else
                let types := m!"actual type:      '{refType}'\n\
                                'asSorry'ed type: '{decl.type}'"
                let defEq? := ← liftCoreM do
                  let (a, _b) ← Meta.MetaM.run do Meta.isDefEq refType decl.type
                  return a
                if defEq? then
                  Linter.logLint linter.checkAsSorry id
                    m!"'{declName}' is not equal but is defeq to its 'asSorry'ed version.\n{types}"
                else
                  logErrorAt stx ""
                  Linter.logLint linter.checkAsSorry id
                    m!"'{declName}' is not defeq to its 'asSorry'ed version\n{types}"

initialize addLinter checkAsSorryLinter

end CheckAsSorry

end Mathlib.Linter
