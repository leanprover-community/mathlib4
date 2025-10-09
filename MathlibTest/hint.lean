import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Common
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.TautoSet

/--
info: Try these:
  • 🎉 trivial
  • norm_num
    Remaining subgoals:
    ⊢ False
-/
#guard_msgs in
example (h : 1 < 0) : False := by hint

/--
info: Try these:
  • 🎉 simp_all only [forall_const]
  • norm_num
    Remaining subgoals:
    ⊢ Q
-/
#guard_msgs in
example {P Q : Prop} (p : P) (f : P → Q) : Q := by hint

/--
info: Try these:
  • 🎉 simp_all only [and_self]
  • norm_num
    Remaining subgoals:
    ⊢ Q ∧ P ∧ R
-/
#guard_msgs in
example {P Q R : Prop} (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by hint

/--
info: Try these:
  • 🎉 exact Std.not_gt_of_lt h
  • norm_num
    Remaining subgoals:
    ⊢ a ≤ b
  • intro
    Remaining subgoals:
    ⊢ False
  • simp_all only [not_lt]
    Remaining subgoals:
    ⊢ a ≤ b
-/
#guard_msgs in
example {a b : ℚ} (h : a < b) : ¬ b < a := by hint

/--
info: Try these:
  • 🎉 ring
-/
#guard_msgs in
example : 37^2 - 35^2 = 72 * 2 := by hint

/--
info: Try these:
  • 🎉 decide
  • ring_nf
    Remaining subgoals:
    ⊢ Nat.Prime 37
-/
#guard_msgs in
example : Nat.Prime 37 := by hint

/--
info: Try these:
  • 🎉 grind
  • ring_nf
    Remaining subgoals:
    ⊢ ∃ x, P x ∧ 0 ≤ x
  • norm_num
    Remaining subgoals:
    ⊢ ∃ x, P x
  • simp_all only [zero_le,
      and_true]
    Remaining subgoals:
    ⊢ ∃ x, P x
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

register_hint 1000 long_trivial

/--
info: Try these:
  • 🎉 long_trivial
-/
#guard_msgs in
example : True := by
  hint

end multiline_hint

section tauto_set

register_hint 1000 tauto_set

/--
info: Try these:
  • 🎉 tauto_set
-/
#guard_msgs in
example {α} (A B C : Set α) (h1 : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by hint

/--
info: Try these:
  • aesop
    Remaining subgoals:
    ⊢ False
  • ring_nf
    Remaining subgoals:
    ⊢ 2 ≤ 1
  • norm_num
    Remaining subgoals:
    ⊢ False
  • simp_all only [Nat.not_ofNat_le_one]
    Remaining subgoals:
    ⊢ False
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 2 ≤ 1 := by hint

end tauto_set

section compute_degree
/--
info: Try these:
  • 🎉 compute_degree
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
  • 🎉 exact
      Units.divp_add_divp_same a b u₁
  • ring_nf
    Remaining subgoals:
    ⊢ a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁
  • abel_nf
    Remaining subgoals:
    ⊢ a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁
  • norm_num
    Remaining subgoals:
    ⊢ a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁
-/
#guard_msgs in
example (R : Type) (a b : R) [CommRing R] (u₁ : Rˣ) : a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁ := by hint
end field_simp

section finiteness
/--
info: Try these:
  • 🎉 finiteness
-/
#guard_msgs in
open ENNReal in
example : (1 : ℝ≥0∞) < ∞ := by hint
end finiteness
