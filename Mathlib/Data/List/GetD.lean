/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn,
Mario Carneiro
-/
import Mathlib.Data.List.Defs
import Mathlib.Data.Option.Basic
import Mathlib.Init.Data.List.Basic
import Mathlib.Util.AssertExists

/-! # getD and getI

This file provides theorems for working with the `getD` and `getI` functions. These are used to
access an element of a list by numerical index, with a default value as a fallback when the index
is out of range.

-/

-- Make sure we haven't imported `Data.Nat.Order.Basic`
assert_not_exists OrderedSub

namespace List

universe u v

variable {α : Type u} {β : Type v} (l : List α) (x : α) (xs : List α) (n : ℕ)

section getD

variable (d : α)

theorem getD_eq_get {n : ℕ} (hn : n < l.length) : l.getD n d = l.get ⟨n, hn⟩ := by
  induction l generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
    cases n
    · exact getD_cons_zero
    · exact ih _

theorem getD_map {n : ℕ} (f : α → β) : (map f l).getD n (f d) = f (l.getD n d) := by simp

theorem getD_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getD n d = d := by
  induction l generalizing n with
  | nil => exact getD_nil
  | cons head tail ih =>
    cases n
    · simp at hn
    · exact ih (Nat.le_of_succ_le_succ hn)

/-- An empty list can always be decidably checked for the presence of an element.
Not an instance because it would clash with `DecidableEq α`. -/
def decidableGetDNilNe (a : α) : DecidablePred fun i : ℕ => getD ([] : List α) i a ≠ a :=
  fun _ => isFalse fun H => H getD_nil

@[simp]
theorem getElem?_getD_singleton_default_eq (n : ℕ) : [d][n]?.getD d = d := by cases n <;> simp

@[deprecated (since := "2024-06-12")]
alias getD_singleton_default_eq := getElem?_getD_singleton_default_eq

@[simp]
theorem getElem?_getD_replicate_default_eq (r n : ℕ) : (replicate r d)[n]?.getD d = d := by
  induction r generalizing n with
  | zero => simp
  | succ n ih => simp at ih; cases n <;> simp [ih, replicate_succ]

@[deprecated (since := "2024-06-12")]
alias getD_replicate_default_eq := getElem?_getD_replicate_default_eq

set_option linter.deprecated false in
theorem getD_append (l l' : List α) (d : α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  rw [getD_eq_get _ _ (Nat.lt_of_lt_of_le h (length_append _ _ ▸ Nat.le_add_right _ _)),
    get_append _ h, getD_eq_get]

theorem getD_append_right (l l' : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  cases Nat.lt_or_ge n (l ++ l').length with
  | inl h' =>
    rw [getD_eq_get (l ++ l') d h', get_eq_getElem, getElem_append_right, getD_eq_get,
      get_eq_getElem]
    · rw [length_append] at h'
      exact Nat.sub_lt_left_of_lt_add h h'
    · exact Nat.not_lt_of_le h
  | inr h' =>
    rw [getD_eq_default _ _ h', getD_eq_default]
    rwa [Nat.le_sub_iff_add_le' h, ← length_append]

theorem getD_eq_getD_get? (n : ℕ) : l.getD n d = (l.get? n).getD d := by
  cases Nat.lt_or_ge n l.length with
  | inl h => rw [getD_eq_get _ _ h, get?_eq_get h, Option.getD_some]
  | inr h => rw [getD_eq_default _ _ h, get?_eq_none.mpr h, Option.getD_none]

end getD

section getI

variable [Inhabited α]

@[simp]
theorem getI_nil : getI ([] : List α) n = default :=
  rfl

@[simp]
theorem getI_cons_zero : getI (x :: xs) 0 = x :=
  rfl

@[simp]
theorem getI_cons_succ : getI (x :: xs) (n + 1) = getI xs n :=
  rfl

theorem getI_eq_get {n : ℕ} (hn : n < l.length) : l.getI n = l.get ⟨n, hn⟩ :=
  getD_eq_get ..

theorem getI_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getI n = default :=
  getD_eq_default _ _ hn

theorem getD_default_eq_getI {n : ℕ} : l.getD n default = l.getI n :=
  rfl

theorem getI_append (l l' : List α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getI n = l.getI n := getD_append _ _ _ _ h

theorem getI_append_right (l l' : List α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getI n = l'.getI (n - l.length) :=
  getD_append_right _ _ _ _ h

theorem getI_eq_iget_get? (n : ℕ) : l.getI n = (l.get? n).iget := by
  rw [← getD_default_eq_getI, getD_eq_getD_get?, Option.getD_default_eq_iget]

theorem getI_zero_eq_headI : l.getI 0 = l.headI := by cases l <;> rfl

end getI
