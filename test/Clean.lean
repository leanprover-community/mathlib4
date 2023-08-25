import Mathlib.Tactic.Clean
import Std

namespace Tests

def withClean : 2 + 2 = 4 := by clean id rfl

def withExact : 2 + 2 = 4 := by exact id rfl

/--
info: theorem Tests.withClean.proof_1 : 2 + 2 = 2 + 2 :=
rfl
-/
#guard_msgs in
#print Tests.withClean.proof_1

/--
info: theorem Tests.withExact.proof_1 : 2 + 2 = 4 :=
id rfl
-/
#guard_msgs in
#print Tests.withExact.proof_1

example : True := by
  let x : id Nat := by dsimp; exact 1
  guard_hyp x :ₛ id Nat := id (1 : Nat)
  let y : id Nat := by clean by dsimp; exact 1
  guard_hyp y :ₛ id Nat := (1 : Nat)
  trivial
