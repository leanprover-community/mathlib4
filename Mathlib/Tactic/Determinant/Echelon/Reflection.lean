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

/-- The product of the entries of rows at positions `(i, k + i)` for `i < c`. Missing entries
are padded with 0. -/
def diagProd (k c : ℕ) (rows : List (List α)) : α :=
  match c with
  | 0 => 1
  | c + 1 => ((rows.headD []).drop k).headD 0 * diagProd (k + 1) c rows.tail

theorem diagProd_zero (k : ℕ) (rows : List (List α)) : diagProd k 0 rows = 1 := by
  rw [diagProd]

theorem diagProd_add_one_cons {k c : ℕ} {row : List α} {rows : List (List α)} {d e : α}
    {suffix : List α} (hdrop : row.drop k = d :: suffix) (h : diagProd (k + 1) c rows = e) :
    diagProd k (c + 1) (row :: rows) = d * e := by
  simp [diagProd, hdrop, h]

end

section CommMonoid

variable [CommMonoid α] [Zero α]

theorem prod_getD_eq_diagProd (k c : ℕ) (rows : List (List α)) :
    ∏ i : Fin c, (rows.getD i []).getD (k + i) 0 = diagProd k c rows := by
  induction c generalizing k rows with
  | zero => simp [diagProd]
  | succ c ih =>
    rw [Fin.prod_univ_succ, diagProd, ← ih]
    cases rows <;> simp [Nat.add_assoc, Nat.add_comm 1]

theorem prod_diag_ofLists (m : ℕ) (rows : List (List α)) :
    ∏ i, ofLists m m rows i i = diagProd 0 m rows := by
  simp [← prod_getD_eq_diagProd]

end CommMonoid

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

/-- Compute determinant from a decomposition. The statement is written in this shape to avoid
mentioning division. -/
theorem det_eq_of_decomposition {m : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    {A : Matrix (Fin m) (Fin m) R} (cert : Echelon.Decomposition A) {rowsL rowsU : List (List R)}
    {l u s v : R} (hL : cert.L = ofLists m m rowsL)
    (hU : cert.L * A.submatrix cert.σ id = ofLists m m rowsU) (hl : diagProd 0 m rowsL = l)
    (hu : diagProd 0 m rowsU = u) (hs : ((Equiv.Perm.sign cert.σ : ℤ) : R) = s)
    (hv : l * (s * v) = u) : A.det = v := by
  rw [cert.det_eq_iff, hU, hL, prod_diag_ofLists, prod_diag_ofLists, hl, hu, hs]
  exact hv

end Mathlib.Tactic.Determinant
