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
  • group
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
  • group
    Remaining subgoals:
    ⊢ Q ∧ P ∧ R
-/
#guard_msgs in
example {P Q R : Prop} (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by hint

/--
info: Try these:
  • 🎉 exact Std.not_gt_of_lt h
  • intro
    Remaining subgoals:
    ⊢ False
  • norm_num
    Remaining subgoals:
    ⊢ a ≤ b
  • group
    Remaining subgoals:
    ⊢ ¬b < a
  • simp_all only [not_lt]
    Remaining subgoals:
    ⊢ a ≤ b
-/
#guard_msgs in
example {a b : ℚ} (h : a < b) : ¬ b < a := by hint

/--
info: Try these:
  • 🎉 ring
  • noncomm_ring
    Remaining subgoals:
    ⊢ 1369 • 1 - 1225 • 1 = 72 • 2
-/
#guard_msgs in
example : 37^2 - 35^2 = 72 * 2 := by hint

/--
info: Try these:
  • 🎉 decide
  • ring_nf
    Remaining subgoals:
    ⊢ Nat.Prime 37
  • norm_num
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
  • group
    Remaining subgoals:
    ⊢ ∃ x, P x ∧ 0 ≤ x
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
  • group
    Remaining subgoals:
    ⊢ 2 ≤ 1
  • simp_all only [Nat.not_ofNat_le_one]
    Remaining subgoals:
    ⊢ False
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 2 ≤ 1 := by hint

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
  • group
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

section ring
/--
info: Try these:
  • 🎉 ring
  • noncomm_ring
    Remaining subgoals:
    ⊢ X * (X * (X * (X * (X * X ^ (8 • 1))))) + (X ^ (8 • 1) + (X * (X * (X * (X * (X * X)))) + X)) =
      X * (X * (X * (X * (X * X)))) +
        (X +
          (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * (X * X))))))))))) +
            X * (X * (X * (X * (X * (X * (X * X))))))))
-/
#guard_msgs in
example (X : ℤ) : (X^5 + 1) * (X^2^3 + X) = X^13 + X^8 + X^6 + X := by hint
end ring

section abel
/--
info: Try these:
  • 🎉 abel
-/
#guard_msgs in
example {α} [AddCommMonoid α] (a b c d: α) : a + b + c + d + 0 = d + (c + b) + (0 + 0 + a) := by hint
end abel

section bound
/--
info: Try these:
  • 🎉 bound
  • noncomm_ring
    Remaining subgoals:
    ⊢ ‖b * b + a‖ ≥ ‖b * b‖ + -1 • ‖a‖ ∧ ‖b * b‖ + -1 • ‖a‖ ≥ ‖b * b‖ + -1 • ‖b‖ ∧ -1 • ‖b‖ + ‖b‖ * ‖b‖ ≥ 2 • ‖b‖
  • ring_nf
    Remaining subgoals:
    ⊢ ‖b ^ 2 + a‖ ≥ ‖b ^ 2‖ - ‖a‖ ∧ ‖b ^ 2‖ - ‖a‖ ≥ ‖b ^ 2‖ - ‖b‖ ∧ -‖b‖ + ‖b‖ ^ 2 ≥ ‖b‖ * 2
  • field_simp
    Remaining subgoals:
    ⊢ ‖b ^ 2‖ - ‖a‖ ≤ ‖b ^ 2 + a‖ ∧ ‖b ^ 2‖ - ‖b‖ ≤ ‖b ^ 2‖ - ‖a‖ ∧ 2 ≤ ‖b‖ - 1
  • abel_nf
    Remaining subgoals:
    ⊢ ‖b ^ 2 + a‖ ≥ ‖b ^ 2‖ + -1 • ‖a‖ ∧ ‖b ^ 2‖ + -1 • ‖a‖ ≥ ‖b ^ 2‖ + -1 • ‖b‖ ∧ (‖b‖ + -1 • 1) * ‖b‖ ≥ 2 * ‖b‖
  • norm_num
    Remaining subgoals:
    ⊢ b ^ 2 ≤ |b ^ 2 + a| + |a| ∧ b ^ 2 ≤ b ^ 2 - |a| + |b| ∧ 2 * |b| ≤ (|b| - 1) * |b|
  • group
    Remaining subgoals:
    ⊢ ‖b ^ 2 + a‖ ≥ ‖b ^ 2‖ - ‖a‖ ∧ ‖b ^ 2‖ - ‖a‖ ≥ ‖b ^ 2‖ - ‖b‖ ∧ -‖b‖ + ‖b‖ ^ 2 ≥ ‖b‖ * 2
  • simp_all only [Real.norm_eq_abs,
      abs_pow, sq_abs, ge_iff_le, tsub_le_iff_right]
    Remaining subgoals:
    ⊢ b ^ 2 ≤ |b ^ 2 + a| + |a| ∧ b ^ 2 ≤ b ^ 2 - |a| + |b| ∧ 2 * |b| ≤ (|b| - 1) * |b|
  • aesop
    Remaining subgoals:
    ⊢ b ^ 2 ≤ |b ^ 2 + a| + |a|
    ⊢ b ^ 2 ≤ b ^ 2 - |a| + |b|
    ⊢ 2 * |b| ≤ (|b| - 1) * |b|
-/
#guard_msgs in
example (a b : ℝ) (h1 : ‖a‖ ≤ ‖b‖) (h2 : 3 ≤ ‖b‖) : ‖b ^ 2 + a‖ ≥ ‖b ^ 2‖ - ‖a‖ ∧ ‖b ^ 2‖ - ‖a‖ ≥ ‖b ^ 2‖ - ‖b‖ ∧ (‖b‖ - 1) * ‖b‖ ≥ 2 * ‖b‖ := by hint
end bound

section group
/--
info: Try these:
  • 🎉 group
  • norm_num
    Remaining subgoals:
    ⊢ c⁻¹ * (b * c⁻¹) * c * (a * b) * (b⁻¹ * a⁻¹ * b⁻¹) * c = 1
-/
#guard_msgs in
example (G : Type) (a b c : G) [Group G] : c⁻¹ * (b * c⁻¹) * c * (a * b) * (b⁻¹ * a⁻¹ * b⁻¹) * c = 1 := by hint
end group

section noncomm_ring
/--
info: Try these:
  • 🎉 noncomm_ring
-/
#guard_msgs in
example (R : Type) (a b : R) [Ring R] : (a + b) ^ 3 = a ^ 3 + a ^ 2 * b + a * b * a + a * b ^ 2 + b * a ^ 2 + b * a * b + b ^ 2 * a + b ^ 3 := by hint
end noncomm_ring

section norm_num
/--
info: Try these:
  • 🎉 norm_num
  • ring_nf
    Remaining subgoals:
    ⊢ 2 < 5 / 2 ∧ 2 < 3
  • field_simp
    Remaining subgoals:
    ⊢ 2 ^ 2 < 5 ∧ 5 / 2 < 3
-/
#guard_msgs in
example : (2 : ℝ) < 5 / 2 ∧ 5 / 2 < 3 := by hint
end norm_num

section positivity
/--
info: Try these:
  • 🎉 positivity
-/
#guard_msgs in
example (a : ℤ) : 0 < |a| + 3 := by hint
end positivity

section trivial
/--
info: Try these:
  • 🎉 trivial
  • ring_nf
    Remaining subgoals:
    ⊢ True ∧ m ≠ 1 ∧ ∀ n < 100, n ^ 2 < 10000
  • norm_num
    Remaining subgoals:
    ⊢ ¬m = 1 ∧ ∀ n < 100, n ^ 2 < 10000
-/
#guard_msgs in
example (m : Nat) (h : m ≠ 1) : True ∧ m ≠ 1 ∧ ∀ n < 100, n^2 < 10000 := by hint
end trivial

section tauto
/--
info: Try these:
  • 🎉 tauto
  • ring_nf
    Remaining subgoals:
    ⊢ P n → n = 7 ∨ n = 0 ∨ ¬(n = 7 ∨ n = 0) ∧ P n
  • intro
    Remaining subgoals:
    ⊢ n = 7 ∨ n = 0 ∨ ¬(n = 7 ∨ n = 0) ∧ P n
  • norm_num
    Remaining subgoals:
    ⊢ P n → n = 7 ∨ n = 0 ∨ (¬n = 7 ∧ ¬n = 0) ∧ P n
  • group
    Remaining subgoals:
    ⊢ P n → n = 7 ∨ n = 0 ∨ ¬(n = 7 ∨ n = 0) ∧ P n
  • simp_all only [not_or,
      and_true]
    Remaining subgoals:
    ⊢ P n → n = 7 ∨ n = 0 ∨ ¬n = 7 ∧ ¬n = 0
-/
#guard_msgs in
example (P : Nat → Prop) (n : Nat) : P n → n = 7 ∨ n = 0 ∨ ¬ (n = 7 ∨ n = 0) ∧ P n := by hint
end tauto

section tauto_set
register_hint 450 tauto_set
/--
info: Try these:
  • 🎉 tauto_set
  • norm_num
    Remaining subgoals:
    ⊢ A ∩ B ∪ A ∩ C = A
  • group
    Remaining subgoals:
    ⊢ A ∩ B ∪ A ∩ C = A
-/
#guard_msgs in
example {α} (A B C : Set α) (h1 : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by hint
end tauto_set
