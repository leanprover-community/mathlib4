/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

import MathlibTest.ClickSuggestions.TestImpl
import Mathlib.Order.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Insert
import MathlibTest.ClickSuggestions.TestImpl
import Mathlib.Data.Finset.Max
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-!
This file tests some basic features of `#click_search`
-/

set_option linter.all false

#click_suggestions

set_option click_suggestions.debug true

axiom test_sorry {α : Sort*} : α

variable (n m k : Nat)

example (h : 0 + n = n) : n = n + 0 := by
  click_test "/1" =>
    "rw [show n + 0 = n from rfl]"
    "rw [Nat.add_zero]"
  click_test =>
    "rw [Nat.left_eq_add]"
    "apply Nat.dvd_antisymm"
  click_test h "" => "apply Nat.le.intro at h" "rw [← Nat.beq_eq] at h"
  click_test h "/0/1" => "rw [Nat.add_comm] at h"
  rfl

example : n - 3 ≤ m - 3 := by
  click_test => "apply Nat.sub_le_sub_right"
  exact test_sorry

example {α} [LinearOrder α] (a b : α) (h : a ≤ b) (h' : b ≤ a) : a ≤ b := by
  click_test => "exact h"
  click_test "/1" => "grw [← h]"
  click_test "/0/1" => "grw [h]"
  apply le_of_lt
  click_test "/1" => "grw [← h]"
  click_test "/0/1" => "grw [h]"
  click_test h "/1" => "grw [h'] at h"
  exact test_sorry

example {α} [LinearOrder α] (a b : α) (h : a < b) (h' : b < a) : a ≤ b := by
  click_test "/1" => "grw [← h]"
  click_test "/0/1" => "grw [h]"
  apply le_of_lt
  click_test => "exact h"
  click_test "/1" => "grw [← h]"
  click_test "/0/1" => "grw [h]"
  click_test h "/1" => "grw [h'] at h"
  exact h

example (h : m ≡ k [MOD n]) (h' : m ≡ k + 1 [MOD n]) (h'' : m = k + 1) : m ≡ k [MOD n] := by
  click_test => "exact h"
  click_test "/1" => "grw [← h]"
  click_test h' "/0/1" => "grw [h] at h'"
  click_test h' "/0/1" => "rw [h''] at h'"
  exact test_sorry

example {p q r : Prop} (h₁ : p → q → r) (h₂ : p → q) (h₃ : p) : r := by
  click_test h₃ "" => "apply h₂ at h₃"
  -- TODO: support `apply_rw`:
  -- click_test h₁ "/1/0" => "apply_rw [← h₂]"
  exact test_sorry

-- Test with bound variables:
example : ∀ n m : Nat, n + m = m + n := by
  click_test "/1/1/1" => "simp_rw [Nat.add_comm]"
  intro n m
  -- The arguments are only inserted when needed:
  click_test "/1" => "rw [Nat.add_comm m n]"
  click_test "/0/1" => "rw [Nat.add_comm]"
  exact test_sorry

example {α} [Lattice α] [AddGroup α] (f : ℕ → α) (c : α)
    (h : ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| ≤ ε) :
    ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| < ε := by
  intro ε hε n
  obtain ⟨N, hN, h⟩ := h ε hε n
  click_test "/1/1/1/1/1/1" => "grw [← h]"
  -- TODO: this should be suggested:
  fail_if_success click_test "/1/1/1/1/1/1" => "grw [hε]"
  exact test_sorry

example {α} [Lattice α] [AddGroup α] (f : ℕ → α) (c : α)
    (h : ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| < ε) :
    ∀ ε > 0, ∀ n, ∃ N > n, ∀ m ≥ N, |f N - f m| ≤ ε := by
  intro ε hε n
  obtain ⟨N, hN, h⟩ := h ε hε n
  click_test "/1/1/1/1/1/1" => "grw [← h]"
  exact test_sorry

example (s t : Set α) (h : s ⊆ t) (h' : t ⊂ s) : s ⊆ t ∪ s := by
  click_test "/0/1" => "nth_grw 1 [h]"
  click_test "/1/0/1" => "grw [← h]"
  exact test_sorry

namespace AntiSymmRelTest

variable {α : Type u} [Preorder α] {a b c : α}

local infix:50 " ≈ " => AntisymmRel (· ≤ ·)

axiom f : α → α

@[gcongr]
axiom f_congr' : a ≤ b → f a ≤ f b

example (h : a ≈ b) (h' : b ≈ c) : f a ≤ f c := by
  click_test "/0/1/1" => "grw [h]"
  grw [h]
  click_test "/0/1/1" => "grw [← h]" "grw [h']"
  grw [h']

end AntiSymmRelTest

-- Test for over-applications
example (f g : Nat → Nat) : (f + g) 2 = f 2 + g 2 := by
  click_test "/0/1" => "rw [add_comm]"
  click_test "/0/1/0" => "rw [add_comm]"
  rw [add_comm]
  click_test "/1" =>
    "rw [Nat.add_comm]"
    "rw [add_comm (f 2) (g 2)]"
  exact test_sorry

-- When the motive is not type correct, suggest `rw!`
example (a b : Nat) (l : List Nat) (hl : a + b < l.length) (h : l[a + b] = 5) :
    l[b + a] = 5 := by
  click_test "/0/1/0/1" => "rw! [Nat.add_comm]" "rw! [add_comm]"
  rw! [Nat.add_comm]
  exact h

example (a b : Nat) (l : List Nat) (hl : a + b < l.length) (h : l[a + b] = 5) :
    b + a + l[b + a] = b + a + 5 := by
  click_test "/0/1/1/0/1" =>
    "rw! (occs := .pos [2]) [Nat.add_comm b a]"
    "rw! (occs := .pos [2]) [add_comm b a]"
  rw! (occs := .pos [2])  [Nat.add_comm b a]
  rw [h]

lemma Nat.my_inj (n m : Nat) (h : n.succ = m.succ) : n = m := Nat.succ.inj h

-- Test which lemmas are and aren't filtered out:
example (n m : Nat) (h : n.succ = m.succ) : True := by
  click_test h "" =>
    "rw [Nat.succ_inj] at h" "rw [Nat.succ.injEq] at h" "apply Nat.my_inj at h"
  -- we do not suggest the automatically generated `.inj` lemma,
  -- because the `.injEq` version is stronger.
  fail_if_success
    click_test h "" => "apply Nat.succ.inj at h  "
  trivial
