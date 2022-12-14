/-!
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Tactic.Wlog
import Mathlib.Data.Nat.Order.Basic

/-!
# Set enumeration
This file allows enumeration of sets given a choice function.
The definition does not assume `sel` actually is a choice function, i.e. `sel s ∈ s` and
`sel s = none ↔ s = ∅`. These assumptions are added to the lemmas needing them.
-/


noncomputable section

open Function

namespace Set

section Enumerate

parameter {α : Type _}(sel : Set α → Option α)

/-- Given a choice function `sel`, enumerates the elements of a set in the order
`a 0 = sel s`, `a 1 = sel (s \ {a 0})`, `a 2 = sel (s \ {a 0, a 1})`, ... and stops when
`sel (s \ {a 0, ..., a n}) = none`. Note that we don't require `sel` to be a choice function. -/
def enumerate : Set α → ℕ → Option α
  | s, 0 => sel s
  | s, n + 1 => do
    let a ← sel s
    enumerate (s \ {a}) n
#align set.enumerate Set.enumerate

theorem enumerate_eq_none_of_sel {s : Set α} (h : sel s = none) : ∀ {n}, enumerate s n = none
  | 0 => by simp [h, enumerate] <;> rfl
  | n + 1 => by simp [h, enumerate] <;> rfl
#align set.enumerate_eq_none_of_sel Set.enumerate_eq_none_of_sel

theorem enumerate_eq_none : ∀ {s n₁ n₂}, enumerate s n₁ = none → n₁ ≤ n₂ → enumerate s n₂ = none
  | s, 0, m => fun h _ => enumerate_eq_none_of_sel h
  | s, n + 1, m => fun h hm => by
    cases hs : sel s
    · exact enumerate_eq_none_of_sel sel hs
    · cases m
      case zero =>
        have : n + 1 = 0 := Nat.eq_zero_of_le_zero hm
        contradiction
      case succ m' =>
        simp [hs, enumerate] at h⊢
        have hm : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact enumerate_eq_none h hm
#align set.enumerate_eq_none Set.enumerate_eq_none

theorem enumerate_mem (h_sel : ∀ s a, sel s = some a → a ∈ s) :
    ∀ {s n a}, enumerate s n = some a → a ∈ s
  | s, 0, a => h_sel s a
  | s, n + 1, a => by
    cases h : sel s
    case none => simp [enumerate_eq_none_of_sel, h]
    case some a' =>
      simp [enumerate, h]
      exact fun h' : enumerate _ (s \ {a'}) n = some a =>
        have : a ∈ s \ {a'} := enumerate_mem h'
        this.left
#align set.enumerate_mem Set.enumerate_mem

theorem enumerate_inj {n₁ n₂ : ℕ} {a : α} {s : Set α} (h_sel : ∀ s a, sel s = some a → a ∈ s)
    (h₁ : enumerate s n₁ = some a) (h₂ : enumerate s n₂ = some a) : n₁ = n₂ := by
  wlog hn : n₁ ≤ n₂
  · rcases Nat.le.dest hn with ⟨m, rfl⟩
    clear hn
    induction n₁ generalizing s
    case zero =>
      cases m
      case zero => rfl
      case succ m =>
        have : enumerate sel (s \ {a}) m = some a := by simp_all [enumerate]
        have : a ∈ s \ {a} := enumerate_mem _ h_sel this
        · simpa
    case succ => cases h : sel s <;> simp_all [enumerate, Nat.add_succ, add_comm] <;> tauto
#align set.enumerate_inj Set.enumerate_inj

end Enumerate

end Set
