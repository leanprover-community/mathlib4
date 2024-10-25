import Mathlib.Util.CompileInductive
import Mathlib.Data.Fin.Fin2

compile_inductive% Fin2

example := @Nat.rec
example := @List.rec
example := @Fin2.rec
example := @PUnit.rec
example := @PEmpty.rec

example := @Nat.recOn
example := @List.recOn
example := @Fin2.recOn
example := @PUnit.recOn
example := @PEmpty.recOn
example := @And.recOn
example := @False.recOn
example := @Empty.recOn

example := @Nat.brecOn
example := @List.brecOn
example := @Fin2.brecOn

example := @List._sizeOf_1

open Lean Elab Term

def tryToCompileAllInductives : TermElabM Unit := do
  let ivs := (← getEnv).constants.toList.filterMap fun | (_, .inductInfo iv) => some iv | _ => none
  let mut success := 0
  for iv in ivs do
    try
      withCurrHeartbeats <| Mathlib.Util.compileInductive iv
      success := success + 1
    catch | e => logError m!"[{iv.name}] {e.toMessageData}"
  modifyThe Core.State fun s =>
    { s with messages.unreported := s.messages.unreported.filter (·.severity != .warning) }
  modifyThe Core.State fun s => { s with messages := s.messages.errorsToWarnings }
  logInfo m!"{success} / {ivs.length}"

-- #eval Command.liftTermElabM tryToCompileAllInductives
