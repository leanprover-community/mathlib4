import Lean.Elab.Command
import Mathlib.Util.CountHeartbeats
open Lean Elab Command

/-!
# The "countHeartbeats'" linter

The "countHeartbeats'" linter reports the output of `#count_heartbeats in` for every declaration.
-/

namespace Mathlib.Linter

/--
The "countHeartbeats'" linter reports the output of `#count_heartbeats in` for every declaration.
-/
register_option linter.countHeartbeats' : Bool := {
  defValue := true
  descr := "enable the countHeartbeats' linter"
}

initialize warnIfRef : IO.Ref Nat ← IO.mkRef 0

open Lean Elab Command in
/--
Using `#count_at_least n` makes the `linter.countHeartbeats'` report a warning on commands that
take at least `n` heartbeats.
-/
elab "#count_at_least " n:num : command => do
  logInfo m!"Warn when the heartbeats exceed {n}"
  warnIfRef.set n.getNat

/-- Add string `a` at the start of the first component of the name `n`. -/
private partial def prepend (n : Name) (a : String := "_") : Name :=
  n.modifyBase fun
    | .anonymous => .str .anonymous a
    | .str .anonymous s => .str .anonymous (a ++ s)
    | .str p s => .str (prepend p a) s
    | .num p n => .num (.str p a) n

namespace CountHeartbeats'

@[inherit_doc Mathlib.Linter.linter.countHeartbeats']
def countHeartbeatsLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.countHeartbeats' (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let some ID := stx.find? (·.isOfKind ``Parser.Command.declId) | return
  let newID := prepend ID[0].getId
  let stx' : Syntax := stx.replaceM (m := Id) fun s =>
    if s.getKind == ``Parser.Command.declId then
      some (s.modifyArg 0 (mkIdentFrom · newID))
    else
      none

  let oldState ← get
  let (errors?, report, chb) := ← do
    elabCommand (← `(command|#count_heartbeats in $(⟨stx'⟩)))
    let msgs := (← get).messages
    let allErrors := (← msgs.reported.toArray.mapM (·.toString))
    let (unknownId, chb) := (← msgs.reportedPlusUnreported.toArray.mapM (·.toString)).partition
      (if let [_, id] := ·.splitOn "unknown identifier" then true else false)
    return (msgs.hasErrors, unknownId, chb)
  set oldState
  let nm ← liftCoreM do realizeGlobalConstNoOverloadWithInfo ID[0] <|> return ID[0].getId
  for d in chb do
    if d.startsWith "Used " then
      let num := d.drop "Used ".length |>.takeWhile (!·.isWhitespace) |>.toNat!
      if num ≤ (← warnIfRef.get) then
        logInfoAt ID m!"{.ofConstName nm}: {d}"
      else
        logWarningAt ID m!"{.ofConstName nm}: {d}"
  if !report.isEmpty then
    logErrorAt stx[0] "Probably unreliable results!"

initialize addLinter countHeartbeatsLinter

end CountHeartbeats'

end Mathlib.Linter
