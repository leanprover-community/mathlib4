import Mathlib.Tactic.Linarith

/-!
# Test that tactics respond to a cancellation request
-/


variable {α}

open Lean Elab Tactic

/-! versions of try/catch that catch `interrupted` too  -/
section catch_interrupted
attribute [-instance]
  Lean.instMonadExceptOfExceptionCoreM Lean.Elab.Tactic.instMonadExceptExceptionTacticM

def Meta.tryCatchAll (m : MetaM α) (h : Exception → MetaM α) : MetaM α := tryCatch m h
def Term.tryCatchAll (m : TermElabM α) (h : Exception → TermElabM α) : TermElabM α := tryCatch m h
def Tactic.tryCatchAll (x : TacticM α) (h : Exception → TacticM α) : TacticM α := do
  let b ← saveState
  try x catch ex => b.restore; h ex

end catch_interrupted

section test_infra

def Tactic.withTimeout (ms : UInt32) (t : TacticM α) : TacticM (α ⊕ Nat) := do
  let tk ← IO.CancelToken.new
  withTheReader Core.Context (fun s => { s with cancelTk? := some tk }) do
    let t0 ← IO.monoMsNow
    let watchdog ← IO.asTask do
      IO.sleep ms
      tk.set
    let r ← Tactic.tryCatchAll (.inl <$> t)
      (fun e => do
        IO.cancel watchdog
        if !e.isInterrupt || !(← tk.isSet) then
          throw e
        else
          let duration := (← IO.monoMsNow) - t0
          return .inr duration)
    IO.cancel watchdog
    return r

/-- `with_timeout 100 => tac` allows `tac` only 100ms to run. -/
elab "with_timeout " ms:num "=>" tac:tacticSeq : tactic => do
  let ms := ms.getNat.toUInt32
  if let .inr _duration ← Tactic.withTimeout ms (evalTactic tac) then
    throwError f!"Tactic took more than {ms}ms"

set_option linter.unusedTactic false

/-- error: Tactic took more than 500ms -/
#guard_msgs in
example : True := by
  with_timeout 500 =>
    sleep 1000
    trivial

example: True := by
  with_timeout 500 =>
    sleep 100
    trivial

end test_infra

/-- `check_timeouts 100 => tac` checks that `tac` never goes longer than `100ms` without checking
for cancellation. -/
elab "check_timeouts " tol_ms:num "=>" tac:tacticSeq : tactic => do
  let mut t := 0
  let tol_ms := tol_ms.getNat
  repeat do
    if let .inr duration ← Tactic.withTimeout t.toUInt32 (evalTactic tac) then
      if duration > t + tol_ms then
        logError f!"Tactic took much more than {t}ms ({duration}ms)"
      trace[debug] "Tactic overran from {t}ms to {duration}ms"
    else
      break
    t := t + tol_ms

set_option maxHeartbeats 0
set_option linter.unusedTactic false
set_option linter.unusedVariables false

theorem linear_combination_with_10_terms
    (a b c d e f g h i j : Int)
    (h0 : -e + g + -h + i = 0)
    (h1 : b + -d + -e + f + g + i = 0)
    (h2 : -b + j = 0)
    (h3 : c + d + -f + -i = 0)
    (h4 : b + c + e + -g + -h + i + j = 0)
    (h5 : -a + b + d + f + -h + -i = 0)
    (h6 : a + d + e + -g + -h = 0)
    (h7 : -a + d + -f + -h + j = 0)
    (h8 : a + -d + e + f + g + h + -i + j = 0)
    (h9 : -a + b + c + -e + -f + h + j = 0) :
      -2*a + b + 2*c + d + -3*f + -g + 3*h + -3*i = 0 := by
  check_timeouts 250 => nlinarith
