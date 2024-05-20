/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Common

#align_import data.set.enumerate from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

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

/- Porting note: The original used parameters -/
variable {α : Type*} (sel : Set α → Option α)

/-- Given a choice function `sel`, enumerates the elements of a set in the order
`a 0 = sel s`, `a 1 = sel (s \ {a 0})`, `a 2 = sel (s \ {a 0, a 1})`, ... and stops when
`sel (s \ {a 0, ..., a n}) = none`. Note that we don't require `sel` to be a choice function. -/
def enumerate : Set α → ℕ → Option α
  | s, 0 => sel s
  | s, n + 1 => do
    let a ← sel s
    enumerate (s \ {a}) n
#align set.enumerate Set.enumerate

theorem enumerate_eq_none_of_sel {s : Set α} (h : sel s = none) : ∀ {n}, enumerate sel s n = none
  | 0 => by simp [h, enumerate]
  | n + 1 => by simp [h, enumerate]
#align set.enumerate_eq_none_of_sel Set.enumerate_eq_none_of_sel

theorem enumerate_eq_none :
    ∀ {s n₁ n₂}, enumerate sel s n₁ = none → n₁ ≤ n₂ → enumerate sel s n₂ = none
  | s, 0, m => fun h _ ↦ enumerate_eq_none_of_sel sel h
  | s, n + 1, m => fun h hm ↦ by
    cases hs : sel s
    · exact enumerate_eq_none_of_sel sel hs
    · cases m with
      | zero => contradiction
      | succ m' =>
        simp? [hs, enumerate] at h ⊢ says
          simp only [enumerate, hs, Option.bind_eq_bind, Option.some_bind] at h ⊢
        have hm : n ≤ m' := Nat.le_of_succ_le_succ hm
        exact enumerate_eq_none h hm
#align set.enumerate_eq_none Set.enumerate_eq_none

theorem enumerate_mem (h_sel : ∀ s a, sel s = some a → a ∈ s) :
    ∀ {s n a}, enumerate sel s n = some a → a ∈ s
  | s, 0, a => h_sel s a
  | s, n + 1, a => by
    cases h : sel s with
    | none => simp [enumerate_eq_none_of_sel, h]
    | some a' =>
      simp only [enumerate, h, Nat.add_eq, add_zero]
      exact fun h' : enumerate sel (s \ {a'}) n = some a ↦
        have : a ∈ s \ {a'} := enumerate_mem h_sel h'
        this.left
#align set.enumerate_mem Set.enumerate_mem

theorem enumerate_inj {n₁ n₂ : ℕ} {a : α} {s : Set α} (h_sel : ∀ s a, sel s = some a → a ∈ s)
    (h₁ : enumerate sel s n₁ = some a) (h₂ : enumerate sel s n₂ = some a) : n₁ = n₂ := by
  /- Porting note: The `rcase, on_goal, all_goals` has been used instead of
     the not-yet-ported `wlog` -/
  rcases le_total n₁ n₂ with (hn|hn)
  on_goal 2 => swap_var n₁ ↔ n₂, h₁ ↔ h₂
  all_goals
    rcases Nat.le.dest hn with ⟨m, rfl⟩
    clear hn
    induction n₁ generalizing s with
    | zero =>
      cases m with
      | zero => rfl
      | succ m =>
        have h' : enumerate sel (s \ {a}) m = some a := by
          simp_all only [enumerate, Nat.zero_eq, Nat.add_eq, zero_add]; exact h₂
        have : a ∈ s \ {a} := enumerate_mem sel h_sel h'
        simp_all [Set.mem_diff_singleton]
    | succ k ih =>
      cases h : sel s with
      /- Porting note: The original covered both goals with just `simp_all <;> tauto` -/
      | none =>
        simp_all only [add_comm, self_eq_add_left, Nat.add_succ, enumerate_eq_none_of_sel _ h]
      | some =>
        simp_all only [add_comm, self_eq_add_left, enumerate, Option.some.injEq,
                       Nat.add_succ, Nat.succ.injEq]
        exact ih h₁ h₂
#align set.enumerate_inj Set.enumerate_inj

end Enumerate

end Set
