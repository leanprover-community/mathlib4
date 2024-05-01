/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn,
Mario Carneiro
-/
import Mathlib.Data.List.Defs
import Mathlib.Data.Option.Basic
import Mathlib.Data.Nat.Defs
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

#align list.nthd_nil List.getD_nilₓ -- argument order
#align list.nthd_cons_zero List.getD_cons_zeroₓ -- argument order
#align list.nthd_cons_succ List.getD_cons_succₓ -- argument order

theorem getD_eq_get {n : ℕ} (hn : n < l.length) : l.getD n d = l.get ⟨n, hn⟩ := by
  induction l generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
    cases n
    · exact getD_cons_zero
    · exact ih _

@[simp]
theorem getD_map {n : ℕ} (f : α → β) : (map f l).getD n (f d) = f (l.getD n d) := by
  induction l generalizing n with
  | nil => rfl
  | cons head tail ih =>
    cases n
    · rfl
    · simp [ih]

#align list.nthd_eq_nth_le List.getD_eq_get

theorem getD_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getD n d = d := by
  induction l generalizing n with
  | nil => exact getD_nil
  | cons head tail ih =>
    cases n
    · simp at hn
    · exact ih (Nat.le_of_succ_le_succ hn)
#align list.nthd_eq_default List.getD_eq_defaultₓ -- argument order

/-- An empty list can always be decidably checked for the presence of an element.
Not an instance because it would clash with `DecidableEq α`. -/
def decidableGetDNilNe {α} (a : α) : DecidablePred fun i : ℕ => getD ([] : List α) i a ≠ a :=
  fun _ => isFalse fun H => H getD_nil
#align list.decidable_nthd_nil_ne List.decidableGetDNilNeₓ -- argument order

@[simp]
theorem getD_singleton_default_eq (n : ℕ) : [d].getD n d = d := by cases n <;> simp
#align list.nthd_singleton_default_eq List.getD_singleton_default_eqₓ -- argument order

@[simp]
theorem getD_replicate_default_eq (r n : ℕ) : (replicate r d).getD n d = d := by
  induction r generalizing n with
  | zero => simp
  | succ n ih => cases n <;> simp [ih]
#align list.nthd_replicate_default_eq List.getD_replicate_default_eqₓ -- argument order

theorem getD_append (l l' : List α) (d : α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  rw [getD_eq_get _ _ (Nat.lt_of_lt_of_le h (length_append _ _ ▸ Nat.le_add_right _ _)),
    get_append _ h, getD_eq_get]
#align list.nthd_append List.getD_appendₓ -- argument order

theorem getD_append_right (l l' : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  cases Nat.lt_or_ge n (l ++ l').length with
  | inl h' =>
    rw [getD_eq_get (l ++ l') d h', get_append_right, getD_eq_get]
    · rw [length_append] at h'
      exact Nat.sub_lt_left_of_lt_add h h'
    · exact Nat.not_lt_of_le h
  | inr h' =>
    rw [getD_eq_default _ _ h', getD_eq_default]
    rwa [Nat.le_sub_iff_add_le' h, ← length_append]
#align list.nthd_append_right List.getD_append_rightₓ -- argument order

theorem getD_eq_getD_get? (n : ℕ) : l.getD n d = (l.get? n).getD d := by
  cases Nat.lt_or_ge n l.length with
  | inl h => rw [getD_eq_get _ _ h, get?_eq_get h, Option.getD_some]
  | inr h => rw [getD_eq_default _ _ h, get?_eq_none.mpr h, Option.getD_none]
#align list.nthd_eq_get_or_else_nth List.getD_eq_getD_get?ₓ -- argument order

end getD

section getI

variable [Inhabited α]

@[simp]
theorem getI_nil : getI ([] : List α) n = default :=
  rfl
#align list.inth_nil List.getI_nil

@[simp]
theorem getI_cons_zero : getI (x :: xs) 0 = x :=
  rfl
#align list.inth_cons_zero List.getI_cons_zero

@[simp]
theorem getI_cons_succ : getI (x :: xs) (n + 1) = getI xs n :=
  rfl
#align list.inth_cons_succ List.getI_cons_succ

theorem getI_eq_get {n : ℕ} (hn : n < l.length) : l.getI n = l.get ⟨n, hn⟩ :=
  getD_eq_get ..
#align list.inth_eq_nth_le List.getI_eq_get

theorem getI_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getI n = default :=
  getD_eq_default _ _ hn
#align list.inth_eq_default List.getI_eq_default

theorem getD_default_eq_getI {n : ℕ} : l.getD n default = l.getI n :=
  rfl
#align list.nthd_default_eq_inth List.getD_default_eq_getIₓ -- new argument `n`

theorem getI_append (l l' : List α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getI n = l.getI n := getD_append _ _ _ _ h
#align list.inth_append List.getI_append

theorem getI_append_right (l l' : List α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getI n = l'.getI (n - l.length) :=
  getD_append_right _ _ _ _ h
#align list.inth_append_right List.getI_append_right

theorem getI_eq_iget_get? (n : ℕ) : l.getI n = (l.get? n).iget := by
  rw [← getD_default_eq_getI, getD_eq_getD_get?, Option.getD_default_eq_iget]
#align list.inth_eq_iget_nth List.getI_eq_iget_get?

theorem getI_zero_eq_headI : l.getI 0 = l.headI := by cases l <;> rfl
#align list.inth_zero_eq_head List.getI_zero_eq_headI

end getI
