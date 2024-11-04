/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, David Renshaw
-/
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Part

set_option autoImplicit true
section tauto₀

variable (p q r : Prop)
variable (h : p ∧ q ∨ p ∧ r)

example : p ∧ p := by tauto

end tauto₀

section tauto₁

variable (α : Type) (p q r : α → Prop)
variable (h : (∃ x, p x ∧ q x) ∨ (∃ x, p x ∧ r x))

example : ∃ x, p x := by tauto

end tauto₁

section tauto₂

variable (α : Type)
variable (x : α)
variable (p q r : α → Prop)
variable (h₀ : (∀ x, p x → q x → r x) ∨ r x)
variable (h₁ : p x)
variable (h₂ : q x)

example : ∃ x, r x := by tauto

end tauto₂

section tauto₃

example (p : Prop) : p ∧ True ↔ p := by tauto
example (p : Prop) : p ∨ False ↔ p := by tauto

example (p q : Prop) (h : p ≠ q) : ¬ p ↔ q := by tauto
example (p q : Prop) (h : ¬ p = q) : ¬ p ↔ q := by tauto

example (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto
example (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto

example (p q : Prop) (h : ¬ (p ↔ q)) (h' : ¬ p) : q := by tauto
example (p q : Prop) (h : ¬ (p ↔ q)) (h' : p) : ¬ q := by tauto
example (p q : Prop) (h : ¬ (p ↔ q)) (h' : q) : ¬ p := by tauto
example (p q : Prop) (h : ¬ (p ↔ q)) (h' : ¬ q) : p := by tauto

example (p q : Prop) (h : ¬ (p ↔ q)) (h' : ¬ q) (h'' : ¬ p) : False := by
  tauto

example (p q r : Prop) (h : p ↔ q) (h' : r ↔ q) (h'' : ¬ r) : ¬ p := by
  tauto

example (p q r : Prop) (h : p ↔ q) (h' : r ↔ q) : p ↔ r := by tauto

example (p q r : Prop) (h : ¬ p = q) (h' : r = q) : p ↔ ¬ r := by tauto

example (p : Prop) : p → ¬ (p → ¬ p) := by tauto
example (p : Prop) (em : p ∨ ¬ p) : ¬ (p ↔ ¬ p) := by tauto

-- reported at https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/weird.20tactic.20bug/near/370505747
open scoped Classical in
example (hp : p) (hq : q) : (if p ∧ q then 1 else 0) = 1 := by
  -- split_ifs creates a hypothesis with a type that's a metavariable
  split_ifs
  · rfl
  · tauto

example (hp : p) (hq : q) (h : ¬ (p ∧ q)) : False := by
  -- causes `h'` to have a type that's a metavariable:
  have h' := h
  clear h
  tauto

example (p : Prop) (h : False) : p := by
  -- causes `h'` to have a type that's a metavariable:
  have h' := h
  clear h
  tauto

example (hp : p) (hq : q) : p ∧ q := by
  -- causes goal to have a type that's a metavariable:
  suffices h : ?foo by exact h
  tauto

-- Checking `tauto` can deal with annotations:
example (hp : ¬ p) (hq : ¬ (q ↔ p) := by sorry) : q := by
  tauto

example (P : Nat → Prop) (n : Nat) : P n → n = 7 ∨ n = 0 ∨ ¬ (n = 7 ∨ n = 0) ∧ P n := by
  tauto

section implementation_detail_ldecl
variable (a b c : Nat)

/--
Mathlib.Tactic.Tauto.distribNot must ignore any LocalDecl where isImplementationDetail
is true. Otherwise, this example yields an error saying "well-founded recursion cannot
be used".
-/
example : ¬(¬a ≤ b ∧ a ≤ c ∨ ¬a ≤ c ∧ a ≤ b) ↔ a ≤ b ∧ a ≤ c ∨ ¬a ≤ c ∧ ¬a ≤ b := by
  tauto

end implementation_detail_ldecl

section modulo_symmetry

variable {p q r : Prop} {α : Type} {x y : α}
variable (h : x = y)
variable (h'' : (p ∧ q ↔ q ∨ r) ↔ (r ∧ p ↔ r ∨ q))

-- Currently this hits a "failed to show termination error"
-- because it erroneously used a recursive hypothesis.
-- See https://github.com/leanprover-community/mathlib4/issues/1061 and
-- https://github.com/leanprover/lean4/issues/1963
-- example (h' : ¬ y = x) : p ∧ q := by tauto

/-
example (h' : p ∧ ¬ y = x) : p ∧ q := by tauto
example : y = x := by tauto
example (h' : ¬ x = y) : p ∧ q := by tauto
example : x = y := by tauto
-/
end modulo_symmetry

section pair_eq_pair_iff

variable (α : Type)
variable (x y z w : α)

-- This example is taken from pair_eq_pair_iff in Data.Set.Basic.
-- It currently doesn't work because `tauto` does not apply `symm`.
--example : ((x = z ∨ x = w) ∧ (y = z ∨ y = w)) ∧
--           (z = x ∨ z = y) ∧ (w = x ∨ w = y) → x = z ∧ y = w ∨ x = w ∧ y = z := by
--  tauto

end pair_eq_pair_iff

end tauto₃

/-
section closer

example {α : Type*} {β : Type*} (a : α) {s_1 : Set α} :
    (∃ (a_1 : α), a_1 = a ∨ a_1 ∈ s_1) := by
  tauto {closer := `[simp]}

variable {p q r : Prop} {α : Type} {x y z w : α}
variable (h : x = y) (h₁ : y = z) (h₂ : z = w)
variable (h'' : (p ∧ q ↔ q ∨ r) ↔ (r ∧ p ↔ r ∨ q))
-- include h h₁ h₂ h''

example : (((r ∧ p ↔ r ∨ q) ∧ (q ∨ r)) → (p ∧ (x = w) ∧ (¬ x = w → p ∧ q ∧ r))) := by
  tauto {closer := `[cc]}

end closer
-/

/-  Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/tauto!.20fails.20on.20ne
-/
example {x y : Nat} (h : ¬x ≠ y) : x = y := by
  tauto

/-
Test the case where the goal depends on a hypothesis
https://github.com/leanprover-community/mathlib4/issues/10590
-/
section goal_depends_on_hyp
open Part
example (p : Prop) (o : Part α) (h : p → o.Dom) (a : α) :
    a ∈ restrict p o h ↔ p ∧ a ∈ o := by
  dsimp [restrict, mem_eq]
  tauto
end goal_depends_on_hyp
