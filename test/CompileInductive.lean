import Mathlib.Util.CompileInductive
import Mathlib.Data.Fin.Fin2

compile_inductive% Fin2

example := @Nat.rec
example := @List.rec
example := @Fin2.rec
example := @PUnit.rec
example := @PEmpty.rec

-- Adaptation note: nightly-2024-03-11.
-- Currently we can't run `compile_inductive% Nat`,
-- as `Nat.rec` already has a `@[csimp]` lemma.
-- However this means that we don't generate code for `Nat.recOn` and `Nat.brecOn`.
-- example := @Nat.recOn
example := @List.recOn
example := @Fin2.recOn
example := @PUnit.recOn
example := @PEmpty.recOn
example := @And.recOn
example := @False.recOn
example := @Empty.recOn

-- Adaptation note: nightly-2024-03-11.
-- Currently we can't run `compile_inductive% Nat`,
-- as `Nat.rec` already has a `@[csimp]` lemma.
-- However this means that we don't generate code for `Nat.recOn` and `Nat.brecOn`.
-- example := @Nat.brecOn
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
  modifyThe Core.State fun s => { s with messages.msgs := s.messages.msgs.filter (·.severity != .warning) }
  modifyThe Core.State fun s => { s with messages := s.messages.errorsToWarnings }
  logInfo m!"{success} / {ivs.length}"

-- #eval Command.liftTermElabM tryToCompileAllInductives
