import MathlibTest.Tactic.DuplicateDeclsAux

open Lean Mathlib.Tactic.DuplicateDecls

/--
-- MathlibTest.Tactic.DuplicateDeclsAux

int_nat_add_comm : ∀ (m : Int) (n : Nat), ↑n + m = m + ↑n
nat_int_add_comm : ∀ (n : Nat) (m : Int), ↑n + m = m + ↑n

Eq.trans : ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
Eq.trans_Type : ∀ {α : Type u} {a b c : α}, a = b → b = c → a = c

of_one_add_one_of_two_add_two : 1 + 1 = 2 → 2 + 2 = 4 → True
of_two_add_two_of_one_add_one : 2 + 2 = 4 → 1 + 1 = 2 → True

one_add_one : 1 + 1 = 2
one_add_one' : 1 + 1 = 2
-/
#guard_msgs (substring := true) in
run_meta do logInfo m!"{← lintDuplicateDeclarations .theorems}"

/--
-- MathlibTest.Tactic.DuplicateDeclsAux

instAddNat : Add Nat
instAddNat' : Add Nat
instAddNat'' : Add Nat
-/
#guard_msgs (substring := true) in
run_meta do logInfo m!"{← lintDuplicateDeclarations .instances}"

/--
-- MathlibTest.Tactic.DuplicateDeclsAux

addTen : Nat → Nat
addTen' : Nat → Nat
-/
#guard_msgs (substring := true) in
run_meta do logInfo m!"{← lintDuplicateDeclarations .defs}"
