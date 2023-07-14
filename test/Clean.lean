import Mathlib.Tactic.Clean
import Std

def this : 2 + 2 = 4 := by clean id rfl

def this1 : 2 + 2 = 4 := by exact id rfl

/--
info: theorem this1.proof_1 : 2 + 2 = 4 :=
id rfl
-/
#guard_msgs in
#print this1.proof_1

/--
info: theorem this.proof_1 : 2 + 2 = 2 + 2 :=
rfl
-/
#guard_msgs in
#print this.proof_1
