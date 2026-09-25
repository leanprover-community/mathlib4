import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Common
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.TautoSet

/--
info: Try these:
  [apply] 🎉️ trivial
  [apply] norm_num
  Remaining subgoals:
  ⊢ False
-/
#guard_msgs in
example (h : 1 < 0) : False := by hint

/--
info: Try these:
  [apply] 🎉️ simp_all only [forall_const]
  [apply] norm_num
  Remaining subgoals:
  ⊢ Q
  [apply] group
  Remaining subgoals:
  ⊢ Q
-/
#guard_msgs in
example {P Q : Prop} (p : P) (f : P → Q) : Q := by hint

/--
info: Try these:
  [apply] 🎉️ simp_all only [and_self]
  [apply] norm_num
  Remaining subgoals:
  ⊢ Q ∧ P ∧ R
  [apply] group
  Remaining subgoals:
  ⊢ Q ∧ P ∧ R
-/
#guard_msgs in
example {P Q R : Prop} (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by hint

/--
info: Try these:
  [apply] 🎉️ exact Std.not_gt_of_lt h
  [apply] norm_num
  Remaining subgoals:
  ⊢ a ≤ b
  [apply] intro
  Remaining subgoals:
  ⊢ False
  [apply] group
  Remaining subgoals:
  ⊢ ¬b < a
  [apply] simp_all only [not_lt]
  Remaining subgoals:
  ⊢ a ≤ b
-/
#guard_msgs in
example {a b : ℚ} (h : a < b) : ¬ b < a := by hint

/--
info: Try these:
  [apply] 🎉️ norm_num
  [apply] noncomm_ring
  Remaining subgoals:
  ⊢ 1369 • 1 - 1225 • 1 = 72 • 2
-/
#guard_msgs in
example : 37^2 - 35^2 = 72 * 2 := by hint

/--
info: Try these:
  [apply] 🎉️ decide
  [apply] norm_num
  Remaining subgoals:
  ⊢ Nat.Prime 37
  [apply] ring_nf
  Remaining subgoals:
  ⊢ Nat.Prime 37
-/
#guard_msgs in
example : Nat.Prime 37 := by hint

/--
info: Try these:
  [apply] 🎉️ grind
  [apply] norm_num
  Remaining subgoals:
  ⊢ ∃ x, P x
  [apply] ring_nf
  Remaining subgoals:
  ⊢ ∃ x, P x ∧ 0 ≤ x
  [apply] group
  Remaining subgoals:
  ⊢ ∃ x, P x ∧ 0 ≤ x
  [apply] simp_all only [zero_le, and_true]
  Remaining subgoals:
  ⊢ ∃ x, P x
-/
#guard_msgs in
example {P : Nat → Prop} (h : { x // P x }) : ∃ x, P x ∧ 0 ≤ x := by hint

def f (p : Nat × Nat) := (p.fst, p.snd)
/--
info: Try these:
  [apply] 🎉️ trivial
  [apply] norm_num
  Remaining subgoals:
  ⊢ f = id
-/
#guard_msgs in
example : f = id := by hint

section multiline_hint

local macro "this_is_a_multiline_exact" ppLine t:term : tactic => `(tactic| exact $t)

local elab tk:"long_trivial" : tactic => do
  let triv := Lean.mkIdent ``trivial
  let actual ← `(tactic| this_is_a_multiline_exact $triv)
  Lean.Meta.Tactic.TryThis.addSuggestion tk { suggestion := .tsyntax actual}
  Lean.Elab.Tactic.evalTactic actual

register_hint 1000 long_trivial

/--
info: Try these:
  [apply] 🎉️ long_trivial
-/
#guard_msgs in
example : True := by
  hint

end multiline_hint

section finiteness
/--
info: Try these:
  [apply] 🎉️ norm_num
-/
#guard_msgs in
open ENNReal in
example : (1 : ℝ≥0∞) < ∞ := by hint
end finiteness

section tauto_set

register_hint 1000 tauto_set

/--
info: Try these:
  [apply] 🎉️ tauto_set
-/
#guard_msgs in
example {α} (A B C : Set α) (h1 : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by hint

/--
info: Try these:
  [apply] aesop
  Remaining subgoals:
  ⊢ False
  [apply] norm_num
  Remaining subgoals:
  ⊢ False
  [apply] ring_nf
  Remaining subgoals:
  ⊢ 2 ≤ 1
  [apply] group
  Remaining subgoals:
  ⊢ 2 ≤ 1
  [apply] simp_all only [Nat.not_ofNat_le_one]
  Remaining subgoals:
  ⊢ False
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : 2 ≤ 1 := by hint

section compute_degree
/--
info: Try these:
  [apply] 🎉️ compute_degree
  [apply] norm_num
  Remaining subgoals:
  ⊢ (X + 1).natDegree ≤ 1
-/
#guard_msgs in
open Polynomial in
example : natDegree ((X + 1) : Nat[X]) ≤ 1 := by hint
end compute_degree

section field_simp
#adaptation_note
/--
As of nightly-2025-08-27,
this test no longer reports `field_simp` amongst the successful tactics.
-/

/--
info: Try these:
  [apply] 🎉️ exact Units.divp_add_divp_same a b u₁
  [apply] norm_num
  Remaining subgoals:
  ⊢ a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁
  [apply] ring_nf
  Remaining subgoals:
  ⊢ a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁
  [apply] abel_nf
  Remaining subgoals:
  ⊢ a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁
  [apply] group
  Remaining subgoals:
  ⊢ a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁
-/
#guard_msgs in
example (R : Type) (a b : R) [CommRing R] (u₁ : Rˣ) : a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁ := by hint
end field_simp

-- This test was originally here to ensure `finiteness` closed the goal,
-- but apparently `tauto_set` also works.
/--
info: Try these:
  [apply] 🎉️ tauto_set
-/
#guard_msgs in
open ENNReal in
example : (1 : ℝ≥0∞) < ∞ := by hint
