import Mathlib.Tactic.HaveLetLinter
import Mathlib.Tactic.Tauto

/-- a tactic that simply logs an empty message.  Useful for testing the chattiness of the
`haveLet` linter. -/
elab "noise" : tactic => do Lean.logInfo ""

#guard_msgs(drop info) in
-- check that `tauto` does not trigger the linter
example : True := by
  noise
  tauto

#guard_msgs in
-- replace is ignored, no matter what
example : True := by
  let zero := 0
  replace _zero := zero
  let eq := (rfl : 0 = 0)
  replace _eq := eq
  exact .intro

/--
info:

---
warning: '_zero : Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'.
[linter.haveLet]
-/
#guard_msgs in
example : True := by
  noise
  have ⟨_zero, _⟩ : Fin 1 := ⟨0, Nat.zero_lt_one⟩
  exact .intro

#guard_msgs in
example : True := by
  have ⟨_zero, _⟩ : Fin 1 := ⟨0, Nat.zero_lt_one⟩
  exact .intro

/--
info:

---
warning: '_zero : Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'.
[linter.haveLet]
-/
#guard_msgs in
example : True := by
  have ⟨_zero, _⟩ : Fin 1 := ⟨0, Nat.zero_lt_one⟩
  noise
  exact .intro

/--
info:

---
warning:
'_zero : Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'. [linter.haveLet]
-/
-- when `have` introduces several hypotheses, the linter flags the non-`Prop` ones.
#guard_msgs in
example : True := by
  have ⟨_zero, _⟩ : Fin 1 := ⟨0, Nat.zero_lt_one⟩
  noise
  exact .intro

/--
info:

---
warning: '_a : Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'.
[linter.haveLet]
---
warning: '_b : Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'.
[linter.haveLet]
---
warning: '_oh : Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'.
[linter.haveLet]
---
warning: '_b : Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'.
[linter.haveLet]
-/
#guard_msgs in
example : True := by
  noise
  have _a := 0
  have _b : Nat := 0
  have _b : 0 = 0 := rfl
  have _oh : Nat := 0
  have _b : Nat := 2
  tauto

set_option linter.haveLet false in
set_option linter.haveLet true in
/--
info:

---
warning: 'this : Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'.
[linter.haveLet]
-/
#guard_msgs in
example : True := by
  have := Nat.succ ?_;
  noise
  exact .intro
  exact 0

/-- info:-/
#guard_msgs in
example : True := by
  have := And.intro (Nat.add_comm ?_ ?_) (Nat.add_comm ?_ ?_)
  apply True.intro
  noise
  repeat exact 0

#guard_msgs(warning, drop info) in
example (h : False) : True := by
  have : False := h
  noise
  exact .intro

set_option linter.haveLet false in
set_option linter.haveLet true in
/--
info:

---
warning: 'this : Nat' is a Type and not a Prop. Consider using 'let' instead of 'have'.
[linter.haveLet]
-/
#guard_msgs in
theorem ghi : True := by
  noise
  have : Nat := Nat.succ 1;
  exact .intro
