import Mathlib.Tactic.Clean
import Batteries

namespace Tests

def x : Id Nat := by dsimp [Id]; exact 1
def x' : Id Nat := clean% by dsimp [Id]; exact 1

/--
info: def Tests.x : Id Nat :=
id 1
-/
#guard_msgs in #print x

/--
info: def Tests.x' : Id Nat :=
1
-/
#guard_msgs in #print x'
-- def x : Id Nat := 1

theorem withClean : 2 + 2 = 4 := clean% by exact id rfl
theorem withoutClean : 2 + 2 = 4 := by exact id rfl

/--
info: theorem Tests.withClean : 2 + 2 = 4 :=
rfl
-/
#guard_msgs in
#print Tests.withClean

/--
info: theorem Tests.withoutClean : 2 + 2 = 4 :=
id rfl
-/
#guard_msgs in
#print Tests.withoutClean

example : True := by
  let x : id Nat := by dsimp; exact 1
  guard_hyp x :ₛ id Nat := id (1 : Nat)
  let x' : id Nat := clean% by dsimp; exact 1
  guard_hyp x' :ₛ id Nat := (1 : Nat)

  let y := show Nat from 1
  guard_hyp y :ₛ Nat := let_fun this := 1; this
  let y' := clean% show Nat from 1
  guard_hyp y' :ₛ Nat := 1

  -- Not a tautological let_fun:
  let z := clean% let_fun x := 1; x + x
  guard_hyp z :ₛ Nat := let_fun x := 1; x + x

  trivial
