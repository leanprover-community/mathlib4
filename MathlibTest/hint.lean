import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.TautoSet

/--
info: Try these:
• linarith
-/
#guard_msgs in
example (h : 1 < 0) : False := by hint

/--
info: Try these:
• exact f p
• norm_num
-/
#guard_msgs in
example {P Q : Prop} (p : P) (f : P → Q) : Q := by hint

/--
info: Try these:
• simp_all only [and_self]
• norm_num
-/
#guard_msgs in
example {P Q R : Prop} (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by hint

/--
info: Try these:
• linarith
-/
#guard_msgs in
example {a b : ℚ} (h : a < b) : ¬ b < a := by hint

/--
info: Try these:
• norm_num
-/
#guard_msgs in
example : 37^2 - 35^2 = 72 * 2 := by hint

/--
info: Try these:
• decide
• norm_num
-/
#guard_msgs in
example : Nat.Prime 37 := by hint

/--
info: Try these:
• aesop
• norm_num
• simp_all only [zero_le, and_true]
-/
#guard_msgs in
example {P : Nat → Prop} (h : { x // P x }) : ∃ x, P x ∧ 0 ≤ x := by hint

section multiline_hint

local macro "this_is_a_multiline_exact" ppLine t:term : tactic => `(tactic| exact $t)

local elab tk:"long_trivial" : tactic => do
  let triv := Lean.mkIdent ``trivial
  let actual ← `(tactic| this_is_a_multiline_exact $triv)
  Lean.Meta.Tactic.TryThis.addSuggestion tk { suggestion := .tsyntax actual}
  Lean.Elab.Tactic.evalTactic actual

register_hint long_trivial

/--
info: Try these:
• this_is_a_multiline_exact
    trivial
-/
#guard_msgs in
example : True := by
  hint

end multiline_hint

section tauto_set

register_hint tauto_set

/--
info: Try these:
• tauto_set
-/
#guard_msgs in
example {α} (A B C : Set α) (h1 : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by hint

/--
info: Try these:
• aesop
• norm_num
• simp_all only [Nat.not_ofNat_le_one]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 2 ≤ 1 := by hint

end tauto_set
