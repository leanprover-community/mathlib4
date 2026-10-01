/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition
public import Mathlib.Tactic.Matrix.OfLists

/-!
# Reflection certificates for determinants of echelon decompositions

The diagonal product of a matrix given as a list of rows, with a bridge lemma to the product over
`Fin m` of an `ofLists` matrix, and the sign of a permutation given as a chain of swaps. The
determinant of a matrix follows from these pieces of an echelon decomposition.
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
def diagProd (k c : ℕ) (rows : List (List α)) : α :=
  match c, rows with
  | 0, _ => 1
  | _ + 1, [] => 0
  | c + 1, row :: rows =>
    match row.drop k with
    | [] => 0
    | d :: _ => d * diagProd (k + 1) c rows

theorem diagProd_zero (k : ℕ) (rows : List (List α)) : diagProd k 0 rows = 1 := by
  rw [diagProd]

theorem diagProd_add_one_cons {k c : ℕ} {row : List α} {rows : List (List α)} {d e : α}
    {suffix : List α} (hdrop : row.drop k = d :: suffix) (h : diagProd (k + 1) c rows = e) :
    diagProd k (c + 1) (row :: rows) = d * e := by
  simp [diagProd, hdrop, h]

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
  simp [← prod_getD_eq_diagProd]

end CommMonoidWithZero

/-! ### Signs of chains of swaps -/

variable {n : Type*} [DecidableEq n] [Fintype n] {σ : Equiv.Perm n} {x y : n}

theorem intCast_sign_refl [AddGroupWithOne α] :
    ((Equiv.Perm.sign (Equiv.refl n) : ℤ) : α) = 1 := by
  simp

theorem intCast_sign_swap_trans [AddGroupWithOne α] {s : α}
    (h : ((Equiv.Perm.sign σ : ℤ) : α) = s) (hxy : x ≠ y) :
    ((Equiv.Perm.sign ((Equiv.swap x y).trans σ) : ℤ) : α) = -s := by
  simp [hxy, ← h]

/-! ### Determinants from echelon decompositions -/

/-- Computing determinant from a decomposition. The statement is written in this form to avoid
mentioning division. -/
theorem det_eq_of_decomposition {m : ℕ} {R : Type*} [CommRing R] [NoZeroDivisors R]
    {A : Matrix (Fin m) (Fin m) R} (cert : Echelon.Decomposition A) {rowsL rowsU : List (List R)}
    {l u s v : R} (hL : cert.L = ofLists m m rowsL)
    (hU : cert.L * A.submatrix cert.σ id = ofLists m m rowsU) (hl : diagProd 0 m rowsL = l)
    (hu : diagProd 0 m rowsU = u) (hs : ((Equiv.Perm.sign cert.σ : ℤ) : R) = s)
    (hv : l * (s * v) = u) : A.det = v := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  have hl0 : l ≠ 0 := by
    rw [← hl, ← prod_diag_ofLists, ← hL]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ cert.L_diag_ne_zero i
  have h := cert.prod_diag_mul_det
  rw [hU, prod_diag_ofLists, hu, hL, prod_diag_ofLists, hl, hs, ← hv] at h
  have hsu : IsUnit s := hs ▸ (Equiv.Perm.sign cert.σ).isUnit.map (Int.castRingHom R)
  exact hsu.mul_left_cancel (mul_left_cancel₀ hl0 h)

end Mathlib.Tactic.Determinant
