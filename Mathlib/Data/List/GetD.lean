/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn,
Mario Carneiro
-/
import Mathlib.Data.List.Defs
import Mathlib.Data.Option.Basic
import Mathlib.Util.AssertExists

/-! # getD and getI

This file provides theorems for working with the `getD` and `getI` functions. These are used to
access an element of a list by numerical index, with a default value as a fallback when the index
is out of range.
-/

assert_not_imported Mathlib.Algebra.Order.Group.Nat

namespace List

universe u v

variable {α : Type u} {β : Type v} (l : List α) (x : α) (xs : List α) (n : ℕ)

section getD

variable (d : α)

theorem getD_eq_getElem {n : ℕ} (hn : n < l.length) : l.getD n d = l[n] := by
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

theorem getD_reverse {l : List α} (i) (h : i < length l) :
    getD l.reverse i = getD l (l.length - 1 - i) := by
  funext a
  rwa [List.getD_eq_getElem?_getD, List.getElem?_reverse, ← List.getD_eq_getElem?_getD]

/-- An empty list can always be decidably checked for the presence of an element.
Not an instance because it would clash with `DecidableEq α`. -/
def decidableGetDNilNe (a : α) : DecidablePred fun i : ℕ => getD ([] : List α) i a ≠ a :=
  fun _ => isFalse fun H => H getD_nil

@[simp]
theorem getElem?_getD_singleton_default_eq (n : ℕ) : [d][n]?.getD d = d := by cases n <;> simp

@[simp]
theorem getElem?_getD_replicate_default_eq (r n : ℕ) : (replicate r d)[n]?.getD d = d := by
  induction r generalizing n with
  | zero => simp
  | succ n ih => simp at ih; cases n <;> simp [ih, replicate_succ]

theorem getD_replicate {y i n} (h : i < n) :
    getD (replicate n x) i y = x := by
  rw [getD_eq_getElem, getElem_replicate]
  rwa [length_replicate]

theorem getD_append (l l' : List α) (d : α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  rw [getD_eq_getElem _ _ (Nat.lt_of_lt_of_le h (length_append ▸ Nat.le_add_right _ _)),
    getElem_append_left h, getD_eq_getElem]

theorem getD_append_right (l l' : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  cases Nat.lt_or_ge n (l ++ l').length with
  | inl h' =>
    rw [getD_eq_getElem (l ++ l') d h', getElem_append_right h, getD_eq_getElem]
  | inr h' =>
    rw [getD_eq_default _ _ h', getD_eq_default]
    rwa [Nat.le_sub_iff_add_le' h, ← length_append]

theorem getD_eq_getD_getElem? (n : ℕ) : l.getD n d = l[n]?.getD d := by
  cases Nat.lt_or_ge n l.length with
  | inl h => rw [getD_eq_getElem _ _ h, getElem?_eq_getElem h, Option.getD_some]
  | inr h => rw [getD_eq_default _ _ h, getElem?_eq_none_iff.mpr h, Option.getD_none]

@[deprecated (since := "2025-02-14")] alias getD_eq_getD_get? := getD_eq_getD_getElem?

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

theorem getI_eq_getElem {n : ℕ} (hn : n < l.length) : l.getI n = l[n] :=
  getD_eq_getElem l default hn

theorem getI_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getI n = default :=
  getD_eq_default _ _ hn

theorem getD_default_eq_getI {n : ℕ} : l.getD n default = l.getI n :=
  rfl

theorem getI_append (l l' : List α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getI n = l.getI n := getD_append _ _ _ _ h

theorem getI_append_right (l l' : List α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getI n = l'.getI (n - l.length) :=
  getD_append_right _ _ _ _ h

theorem getI_eq_iget_getElem? (n : ℕ) : l.getI n = l[n]?.iget := by
  rw [← getD_default_eq_getI, getD_eq_getD_getElem?, Option.getD_default_eq_iget]

@[deprecated (since := "2025-02-14")] alias getI_eq_iget_get? := getI_eq_iget_getElem?

theorem getI_zero_eq_headI : l.getI 0 = l.headI := by cases l <;> rfl

end getI

end List
