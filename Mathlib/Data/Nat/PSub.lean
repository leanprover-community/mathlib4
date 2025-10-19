/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic

/-!
# Partial predecessor and partial subtraction on the natural numbers

The usual definition of natural number subtraction (`Nat.sub`) returns 0 as a "garbage value" for
`a - b` when `a < b`. Similarly, `Nat.pred 0` is defined to be `0`. The functions in this file
wrap the result in an `Option` type instead:

## Main definitions

- `Nat.ppred`: a partial predecessor operation
- `Nat.psub`: a partial subtraction operation

-/

namespace Nat

/-- Partial predecessor operation. Returns `ppred n = some m`
  if `n = m + 1`, otherwise `none`. -/
def ppred : ℕ → Option ℕ
  | 0 => none
  | n + 1 => some n

@[simp]
theorem ppred_zero : ppred 0 = none := rfl

@[simp]
theorem ppred_succ {n : ℕ} : ppred (succ n) = some n := rfl

/-- Partial subtraction operation. Returns `psub m n = some k`
  if `m = n + k`, otherwise `none`. -/
def psub (m : ℕ) : ℕ → Option ℕ
  | 0 => some m
  | n + 1 => psub m n >>= ppred

@[simp]
theorem psub_zero {m : ℕ} : psub m 0 = some m := rfl

@[simp]
theorem psub_succ {m n : ℕ} : psub m (succ n) = psub m n >>= ppred := rfl

theorem pred_eq_ppred (n : ℕ) : pred n = (ppred n).getD 0 := by cases n <;> rfl

theorem sub_eq_psub (m : ℕ) : ∀ n, m - n = (psub m n).getD 0
  | 0 => rfl
  | n + 1 => (pred_eq_ppred (m - n)).trans <| by rw [sub_eq_psub m n, psub]; cases psub m n <;> rfl

@[simp]
theorem ppred_eq_some {m : ℕ} : ∀ {n}, ppred n = some m ↔ succ m = n
  | 0 => by constructor <;> intro h <;> contradiction
  | n + 1 => by constructor <;> intro h <;> injection h <;> subst m <;> rfl

@[simp]
theorem ppred_eq_none : ∀ {n : ℕ}, ppred n = none ↔ n = 0
  | 0 => by simp
  | n + 1 => by constructor <;> intro <;> contradiction

theorem psub_eq_some {m : ℕ} : ∀ {n k}, psub m n = some k ↔ k + n = m
  | 0, k => by simp [eq_comm]
  | n + 1, k => by
    apply Option.bind_eq_some_iff.trans
    simp only [psub_eq_some, ppred_eq_some]
    simp [add_comm, add_left_comm]

theorem psub_eq_none {m n : ℕ} : psub m n = none ↔ m < n := by
  rcases s : psub m n
  · simp only [true_iff]
    refine lt_of_not_ge fun h => ?_
    obtain ⟨k, e⟩ := le.dest h
    injection s.symm.trans (psub_eq_some.2 <| (add_comm _ _).trans e)
  · grind [psub_eq_some]

theorem ppred_eq_pred {n} (h : 0 < n) : ppred n = some (pred n) :=
  ppred_eq_some.2 <| succ_pred_eq_of_pos h

theorem psub_eq_sub {m n} (h : n ≤ m) : psub m n = some (m - n) :=
  psub_eq_some.2 <| Nat.sub_add_cancel h

theorem psub_add (m n k) :
    psub m (n + k) = (do psub (← psub m n) k) := by
    induction k with
    | zero => simp
    | succ n ih => simp only [ih, add_succ, psub_succ, bind_assoc]

/-- Same as `psub`, but with a more efficient implementation. -/
@[inline]
def psub' (m n : ℕ) : Option ℕ :=
  if n ≤ m then some (m - n) else none

theorem psub'_eq_psub (m n) : psub' m n = psub m n := by
  rw [psub']
  split_ifs with h
  · exact (psub_eq_sub h).symm
  · exact (psub_eq_none.2 (not_le.1 h)).symm

end Nat
