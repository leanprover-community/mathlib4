import Mathlib.Util.PrintSorries

set_option pp.mvars false

/-!
Direct use of `sorry`
-/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem thm1 : 1 = 2 := by sorry

/--
info: thm1 has sorry of type
  1 = 2
-/
#guard_msgs in
#print sorries thm1

/-!
Indirect use of `sorry`
-/
theorem thm2 : 1 = 2 := thm1

/--
info: thm1 has sorry of type
  1 = 2
-/
#guard_msgs in
#print sorries thm2

/-!
Print all uses of `sorry` in the current module.
-/
/--
info: thm1 has sorry of type
  1 = 2
-/
#guard_msgs in
#print sorries

/-!
Don't overreport. Remembers that `thm1` already reported the `sorry`.
-/
/--
info: thm1 has sorry of type
  1 = 2
-/
#guard_msgs in
#print sorries thm1 thm2

/-!
Reports sorries (indirectly) appearing in the types of theorems.
-/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def f (n : Nat) : Nat := sorry
theorem thm3 : f 1 = f 2 := rfl -- (!) This works since it's a fixed `sorry : Nat`

/--
info: f has sorry of type
  Nat
-/
#guard_msgs in
#print sorries thm3

/-!
If `sorry` appears in the type of a theorem, when it's used, it reports the theorem
with the `sorry`, even though `sorry` appears in the theorem that used it as well.
-/
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem thm_sorry (n : Nat) : n = sorry := sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem thm_use_it (m n : Nat) : m = n := by
  rw [thm_sorry m, thm_sorry n]

/--
info: thm_sorry has sorry of type
  Nat
thm_sorry has sorry of type
  n = sorry
-/
#guard_msgs in
#print sorries thm_use_it

/-!
Reports synthetic sorries specially.
-/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def f' : Nat → Nat := sorry
/--
error: Not a definitional equality: the left-hand side
  f' 1
is not definitionally equal to the right-hand side
  f' 2
---
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  f' 1 = f' 2
-/
#guard_msgs in
theorem thm3' : f' 1 = f' 2 := rfl -- fails as expected, `f'` is an unknown `sorry : Nat → Nat`

/--
info: f' has sorry of type
  Nat → Nat
thm3' has sorry (from error) of type
  f' 1 = f' 2
-/
#guard_msgs in
#print sorries thm3'

/-!
Unfolding functions can lead to many copies of `sorry` in a term.
This proof contains 4 sorry terms.
-/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem thm : True := by
  let f : Nat → Nat := sorry
  have : f 1 = f 2 := sorry
  unfold f at this
  change id _ at this
  trivial

/--
info: thm has sorry of type
  Nat → Nat
thm has sorry of type
  f 1 = f 2
-/
#guard_msgs in
#print sorries thm

/-!
Raw, unlabeled sorry.
Its "go to definition" unfortunately goes to `sorryAx` itself.
-/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem thm' : True := sorryAx _ false

/--
info: thm' has sorry of type
  True
-/
#guard_msgs in
#print sorries thm'

/-!
The `sorry` pretty printing can handle free variables.
-/
/-- warning: declaration uses 'sorry' -/
#guard_msgs in def g (α : Type) : α := sorry

/--
info: g has sorry of type
  α
-/
#guard_msgs in #print sorries g

/-!
`#print sorries in`
-/

/--
info: in_test_1 has sorry of type
  True
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#print sorries in theorem in_test_1 : True := sorry

/-- info: Declarations are sorry-free! -/
#guard_msgs in
#print sorries in theorem in_test_2 : True := trivial

/-!
### Other sorry-producing commands

Check that `admit` and `stop` are correctly handled
-/

/-- info: thm4 has sorry of type
  True
---
warning: declaration uses 'sorry'
---
warning: 'admit' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false` -/
#guard_msgs in
#print sorries in
theorem thm4 : True := by admit

/-- info: thm5 has sorry of type
  True
---
warning: declaration uses 'sorry'
---
warning: 'stop admit' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false` -/
#guard_msgs in
#print sorries in
theorem thm5 : True := by stop admit
