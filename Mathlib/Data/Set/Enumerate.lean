/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Common
import Mathlib.Data.Set.Insert

/-!
# Set enumeration
This file allows enumeration of sets given a choice function.
The definition does not assume `sel` actually is a choice function, i.e. `sel s ∈ s` and
`sel s = none ↔ s = ∅`. These assumptions are added to the lemmas needing them.
-/

assert_not_exists RelIso

noncomputable section

open Function

namespace Set

section Enumerate

variable {α : Type*} (sel : Set α → Option α)

/-- Given a choice function `sel`, enumerates the elements of a set in the order
`a 0 = sel s`, `a 1 = sel (s \ {a 0})`, `a 2 = sel (s \ {a 0, a 1})`, ... and stops when
`sel (s \ {a 0, ..., a n}) = none`. Note that we don't require `sel` to be a choice function. -/
def enumerate : Set α → ℕ → Option α
  | s, 0 => sel s
  | s, n + 1 => do
    let a ← sel s
    enumerate (s \ {a}) n

theorem enumerate_eq_none_of_sel {s : Set α} (h : sel s = none) : ∀ {n}, enumerate sel s n = none
  | 0 => by simp [h, enumerate]
  | n + 1 => by simp [h, enumerate]

theorem enumerate_eq_none :
    ∀ {s n₁ n₂}, enumerate sel s n₁ = none → n₁ ≤ n₂ → enumerate sel s n₂ = none
  | _, 0, _ => fun h _ ↦ enumerate_eq_none_of_sel sel h
  | s, n + 1, m => fun h hm ↦ by
    cases hs : sel s
    · exact enumerate_eq_none_of_sel sel hs
    · cases m with
      | zero => contradiction
      | succ m' =>
        simp? [hs, enumerate] at h ⊢ says
          simp only [enumerate, hs, Option.bind_eq_bind, Option.bind_some] at h ⊢
        have hm : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact enumerate_eq_none h hm

theorem enumerate_mem (h_sel : ∀ s a, sel s = some a → a ∈ s) :
    ∀ {s n a}, enumerate sel s n = some a → a ∈ s
  | s, 0, a => h_sel s a
  | s, n + 1, a => by
    cases h : sel s with
    | none => simp [enumerate_eq_none_of_sel, h]
    | some a' =>
      simp only [enumerate, h]
      exact fun h' : enumerate sel (s \ {a'}) n = some a ↦
        have : a ∈ s \ {a'} := enumerate_mem h_sel h'
        this.left

theorem enumerate_inj {n₁ n₂ : ℕ} {a : α} {s : Set α} (h_sel : ∀ s a, sel s = some a → a ∈ s)
    (h₁ : enumerate sel s n₁ = some a) (h₂ : enumerate sel s n₂ = some a) : n₁ = n₂ := by
  wlog hn : n₁ ≤ n₂ generalizing n₁ n₂
  · exact (this h₂ h₁ (lt_of_not_ge hn).le).symm
  rcases Nat.le.dest hn with ⟨m, rfl⟩
  clear hn
  induction n₁ generalizing s with
  | zero =>
    cases m with
    | zero => rfl
    | succ m =>
      have h' : enumerate sel (s \ {a}) m = some a := by
        simp_all only [enumerate, Nat.add_eq, zero_add]; exact h₂
      have : a ∈ s \ {a} := enumerate_mem sel h_sel h'
      simp_all
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 by omega] at h₂
    cases h : sel s <;> simp_all [enumerate] ; tauto

end Enumerate

end Set
