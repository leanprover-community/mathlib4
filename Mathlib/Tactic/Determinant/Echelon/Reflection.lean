/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Matrix.OfLists

/-!
# Reflection certificates for determinants of echelon decompositions

The diagonal product of a matrix given as a list of rows, with a bridge lemma to the product over
`Fin m` of an `ofLists` matrix, and the sign of a permutation given as a chain of swaps.
-/

public section

open Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Determinant

variable {α : Type*}

/-! ### Diagonal products -/

section

variable [Zero α] [One α] [Mul α]

/-- The product of the `c` entries at columns `k, k + 1, …` of successive rows. A missing row or
entry makes it `0`. -/
@[expose] def diagProd (k : ℕ) : ℕ → List (List α) → α
  | 0, _ => 1
  | _ + 1, [] => 0
  | c + 1, row :: rows =>
    match row.drop k with
    | [] => 0
    | a :: _ => a * diagProd (k + 1) c rows

theorem diagProd_zero (k : ℕ) (rows : List (List α)) : diagProd k 0 rows = 1 :=
  rfl

theorem diagProd_succ_cons {k c : ℕ} {row : List α} {rows : List (List α)} {a e : α}
    {suffix : List α} (hd : row.drop k = a :: suffix) (h : diagProd (k + 1) c rows = e) :
    diagProd k (c + 1) (row :: rows) = a * e := by
  simp [diagProd, hd, h]

end

section CommMonoidWithZero

variable [CommMonoidWithZero α]

theorem prod_getD_eq_diagProd (k c : ℕ) (rows : List (List α)) :
    ∏ i : Fin c, (rows.getD i []).getD (k + i) 0 = diagProd k c rows := by
  induction c generalizing k rows with
  | zero => simp [diagProd]
  | succ c ih =>
    cases rows with
    | nil => simp [diagProd]
    | cons row rows =>
      have := List.getElem?_drop (xs := row) (i := k) (j := 0)
      rw [Fin.prod_univ_succ]
      grind [diagProd, zero_mul]

theorem prod_diag_ofLists (m : ℕ) (rows : List (List α)) :
    ∏ i, ofLists m m rows i i = diagProd 0 m rows := by
  simpa using prod_getD_eq_diagProd 0 m rows

end CommMonoidWithZero

/-! ### Signs of chains of swaps -/

variable {n : Type*} [DecidableEq n] [Fintype n] {σ : Equiv.Perm n} {x y : n}

theorem intCast_sign_refl [Ring α] : ((Equiv.Perm.sign (Equiv.refl n) : ℤ) : α) = 1 := by
  simp

theorem intCast_sign_swap_trans [Ring α] {s : α} (h : ((Equiv.Perm.sign σ : ℤ) : α) = s)
    (hxy : x ≠ y) : ((Equiv.Perm.sign ((Equiv.swap x y).trans σ) : ℤ) : α) = -s := by
  simp [Equiv.Perm.sign_trans, Equiv.Perm.sign_swap hxy, ← h]

end Mathlib.Tactic.Determinant
