import Mathlib.Lean.MessageData.ForExprs
import Qq

open Qq

/--
info: ["quo" ++ "ted", 37, ¬True]
---
info: some (37)
-/
#guard_msgs in
run_meta do
  let msg ← Lean.addMessageContext
    m!"Hello {q("quo" ++ "ted")} world {q(37)} {.lazy fun _ => return m!"{q(¬True)}"}"
  Lean.logInfo m!"{← msg.getExprs}"
  let s : Option Q(Nat) ← msg.firstExpr? fun e => do
    let ⟨1, ~q(Nat), e⟩ ← inferTypeQ e | return none
    return some e
  Lean.logInfo m!"{s}"
