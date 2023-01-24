import Mathlib

#compile inductive Nat
#compile inductive List
#compile inductive Fin2
#compile inductive PUnit
#compile inductive PEmpty
#compile inductive And
#compile inductive Or
#compile inductive False
#compile inductive Empty

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

#compile def List._sizeOf_1

example := @List._sizeOf_1

open Lean

#eval Elab.Command.liftTermElabM do
  let ivs := (← getEnv).constants.toList |>.filterMap λ | (_, .inductInfo iv) => some iv | _ => none
  let mut success := 0
  let mut skipped := 0
  for iv in ivs do
    try
      unless (← getConstInfoRec <| mkRecName iv.name).numMotives == 1 do
        skipped := skipped + 1
        continue
      withCurrHeartbeats <| Mathlib.Util.compileInductive iv
      success := success + 1
    catch | e => logError m!"[{iv.name}] {e.toMessageData}"
  modifyThe Core.State λ s => { s with messages.msgs := s.messages.msgs.filter (·.severity != .warning) }
  modifyThe Core.State λ s => { s with messages := s.messages.errorsToWarnings }
  logInfo m!"{success} / {ivs.length - skipped}"
