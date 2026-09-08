/-
Copyright (c) 2025 Maria Joseph. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maria Joseph, Divakaran D, Janav Gupta
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.DMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.PEquiv
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Gaussian Elimination

In this file we define row exchange matrices as matrices obtained by swapping the ith and jth
column of the identity matrix.  We show that multiplying a matrix M on the left by a row exchange
matrix leads to swapping the ith and jth rows of M.  Building on Mathlib.LinearAlgebra.Matrix.
Transvection we obtain a proof of the Gaussian elimination.  More precisely, we show that:

Given any matrix `M`, we can find a product of transvections and row exchange matrices `L` such
that `L * M` is an lower triangular matrix.

## Main definitions and results

* `rowEx (i j : n)` the matrix obtained by swapping the ith and jth row of an nxn identity matrix

* `EliminationStruct` a structure that contains all the information to construct an elimination matrix

* `mul_rowEx_eq_swap` states that multiplying a matrix M with rowEx i j on the left exchanges
  the ith row and the jth row of M with each other

* `rowEx_respects_inclusion` states that if `M` is the matrix obtained by exchanging the ith and
jth rows of the `rxr` identity matrix, then the matrix obtained by exchanging the ith and jth rows
of an `(r+1)x(r+1)` identity matrix is the block matrix whose blocks are `M`, `0`, `0`, `1`.

* `transvec_mul_rowEx_mul_lastcol` states that for every (r+1)x(r+1) matrix M ,there is a list of
  transvections and a row exchange matrix such that multiplying on the left with the rowEx and then
  the list of transvections will make M₍ᵢ,ᵣ₊₁₎ = 0 for every 1 ≤ i < r+1

* `exists_list_elim_matrix_mul_eq_lowerTriangular` states that given any matrix `M`, we can find a
  product of transvections and row exchange matrices `L` such that `L * M` is an lower triangular
  matrix.

## Tags

linear algerba, matrix, matrices, linear equations, Gaussian Elimination

-/

open Matrix BigOperators
open Equiv Equiv.Perm Finset Function

namespace Matrix
open Matrix
variable {m n k : Type*} [DecidableEq n] [DecidableEq m] [Fintype m]

variable {R : Type*} [CommRing R]

variable {𝕜 : Type*} [Field 𝕜]

/-- `rowEx i j` is the matrix obtained by swapping the ith and jth row of an nxn identity matrix. -/
def rowEx (i j : n) : Matrix n n R :=
  (Equiv.swap i j).toPEquiv.toMatrix

/-- `rowEx i i` is the identity matrix -/
theorem rowEx_self (i : n) : rowEx i i = (1 : Matrix n n R) := by simp [rowEx]

/-- `rowEx i j` is precisely swapping the ith row of the identity matrix with the jth one and
swapping the jth row of the identity matrix with the ith one -/
theorem updateRow_eq_swap (i j : n) :
    updateRow (updateRow (1 : Matrix n n R) i ((1 : Matrix n n R) j)) j ((1 : Matrix n n R) i) =
    rowEx i j := by
  ext a b
  by_cases ha : i = a
  · by_cases hb : j = b
    · simp [ha, hb]
      rw [rowEx, PEquiv.toMatrix_toPEquiv_eq]
      dsimp only [submatrix_apply]
      rw [Equiv.swap_apply_left, Matrix.updateRow_apply, Matrix.updateRow_self]
      by_cases hab : a = b
      · rw [if_pos hab, ha, hab]
        rfl
      · rw [if_neg hab, hb]
        rfl
    · rw [ha, rowEx, PEquiv.toMatrix_toPEquiv_eq]
      dsimp only [submatrix_apply]
      rw [Equiv.swap_apply_left, Matrix.updateRow_apply, Matrix.updateRow_self]
      by_cases haj : a = j
      · rw [if_pos haj, haj]
        rfl
      · rw [if_neg haj]
        rfl
  · rw [rowEx]
    rw [PEquiv.toMatrix_toPEquiv_eq, Matrix.updateRow_apply, Matrix.updateRow_apply]
    dsimp only [submatrix_apply]
    rw [Equiv.swap_apply_def]
    by_cases haj : a = j
    · rw [if_pos haj, if_neg (ne_comm.mp ha), if_pos haj]
      rfl
    · rw [if_neg haj, if_neg (ne_comm.mp ha), if_neg haj, if_neg (ne_comm.mp ha)]
      rfl

/-- Multiplying a matrix `M` on the left with `rowEx i j` exchanges the ith row and the jth row of `M`
 with each other -/
theorem rowEx_mul_eq_swap (i j : n) (M : Matrix n n R) [Fintype n] :
    (rowEx i j : Matrix n n R) * M = updateRow (updateRow (M) i (M j)) j (M i) := by
  ext a b
  by_cases ha : i = a
  · by_cases hb : j = b
    · simp [ha, hb]
      simp [Matrix.updateRow_apply]
      by_cases hab : a = b
      · simp [if_pos hab, rowEx, PEquiv.toMatrix_toPEquiv_mul, hab]
      · simp [if_neg hab, rowEx]
        rw [PEquiv.toMatrix_toPEquiv_mul]
        simp only [submatrix_apply, swap_apply_left, id_eq]
    · simp [Matrix.updateRow_apply, ha]
      by_cases haj : a = j
      · rw [if_pos haj, rowEx,PEquiv.toMatrix_toPEquiv_mul]
        simp [haj]
      · rw [if_neg haj, rowEx,PEquiv.toMatrix_toPEquiv_mul]
        simp only [submatrix_apply, swap_apply_left, id_eq]
  · simp [Matrix.updateRow_apply]
    by_cases haj : a = j
    · rw [if_pos haj, rowEx,PEquiv.toMatrix_toPEquiv_mul]
      simp [haj]
    · rw [if_neg haj, if_neg (ne_comm.mp ha), rowEx, PEquiv.toMatrix_toPEquiv_mul]
      simp [Equiv.swap_apply_def,if_neg (ne_comm.mp ha), if_neg haj]

/-- Multiplying a matrix `M` on the left by `rowEx i i` returns `M` -/
theorem mul_rowEx_i_i_eq (i : m) (M : Matrix m m R) : (rowEx i i : Matrix m m R) * M = M := by
  simp [rowEx_mul_eq_swap]

namespace struct

open Sum Fin TransvectionStruct Pivot Matrix
variable (R n r)

/-- Let `A` be the block matrix with blocks `M`, `0`, `0`, `1` and `M'` be the matrix obtained by
exchanging the ith and jth row of `M`.  Then, the block matrix with blocks `M'`, `0`, `0`, `1` is
equal to the matrix `A'` obtained by exchanging the ith and jth row of `A`. -/
theorem rowEx_respects_inclusion_1 (M : Matrix (Fin r) (Fin r) 𝕜) (i j : Fin r) :
    fromBlocks ((rowEx i j) * M) 0 0 (1 : Matrix Unit Unit 𝕜) =
    (rowEx (inl i) (inl j)) * (fromBlocks M 0 0 (1 : Matrix Unit Unit 𝕜)) := by
  ext a b
  rcases a with ⟨ha1, ha2⟩
  · rcases b with ⟨hb1, hb2⟩
    · simp [rowEx_mul_eq_swap,Matrix.updateRow_apply]
    · simp [rowEx_mul_eq_swap,Matrix.updateRow_apply]
  · rcases b with ⟨hb1, hb2⟩
    · simp [rowEx_mul_eq_swap,Matrix.updateRow_apply]
    · simp [rowEx_mul_eq_swap,Matrix.updateRow_apply]


/-- Let `I'` be the matrix obtained by exchanging the ith and jth row of the rxr identity matrix.
Then, the block matrix formed by blocks `I'`, `0`, `0`, `1` is equal to the matrix obtained by
exchaning the ith and jth row row of (r+1)x(r+1) identity matrix -/
theorem rowEx_respects_inclusion (i j : Fin r) :
    fromBlocks (rowEx i j) 0 0 (1 : Matrix Unit Unit 𝕜) = (rowEx (inl i) (inl j)) := by
  suffices fromBlocks ((rowEx i j) * (1 : Matrix (Fin r) (Fin r) 𝕜)) 0 0 (1 : Matrix Unit Unit 𝕜) =
    (rowEx (inl i) (inl j)) * (1 : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜) by
      simpa [Matrix.mul_one]
  rw [rowEx_respects_inclusion_1,Matrix.mul_one]
  simp only [fromBlocks_one, mul_one]

/-- A structure that contains all the information to construct an elimination matrix-/
structure EliminationStruct where
  /-- A list of transvection structures-/
  (L : List (TransvectionStruct n R))
  /-- and a single row exchange -/
  (i j : n)

namespace EliminationStruct

variable {p n R} [Fintype p] [Fintype n] [DecidableEq p]

/-- Converts an elimination structure to the corresponding elimination matrix -/
def toElim (e : EliminationStruct n R) : Matrix n n R :=
  List.prod (List.map toMatrix (e.L)) * (rowEx e.i e.j)

theorem toElim_mk (i j : n) (L : List (TransvectionStruct n R)) :
    toElim ⟨L, i, j⟩ = List.prod (List.map toMatrix L) * (rowEx i j):=
  rfl

/-- Converts an elimination structure for nxn matrix to an elimination structure for (n+k)x(n+k)
matrix -/
def elimBlkIncl (e : EliminationStruct n R) : (EliminationStruct (n ⊕ k) R) where
  L := (List.map (sumInl k) (e.L))
  i := inl e.i
  j := inl e.j

/-- Reindexing-/
def elimStrReindex (e : n ≃ p) (e' : EliminationStruct n 𝕜) : EliminationStruct p 𝕜 where
  i := e e'.i
  j := e e'.j
  L := (List.map (TransvectionStruct.reindexEquiv e) (e'.L))

/-- Reindexing commutes with toElim-/
theorem toMatrix_elimStrReindex (e : n ≃ p) (E : EliminationStruct n 𝕜) :
    toElim (elimStrReindex e E) = reindexAlgEquiv 𝕜 _ e (toElim E) := by
  rcases E with ⟨ L, i, j⟩
  simp only [toElim, elimStrReindex]
  have : (reindexAlgEquiv 𝕜 𝕜 e) ((List.map toMatrix L).prod * rowEx i j) =
  (reindexAlgEquiv 𝕜 𝕜 e) ((List.map toMatrix L).prod) * (reindexAlgEquiv 𝕜 𝕜 e) (rowEx i j) := by
    simp [AlgEquiv.map_mul']
  rw [this]
  have h2: rowEx (e i) (e j) = (reindexAlgEquiv 𝕜 𝕜 e) (rowEx i j):= by
    rw [reindexAlgEquiv_apply]
    rw [reindex_apply]
    ext a b
    rw [submatrix_apply]
    simp [PEquiv.toMatrix_toPEquiv_eq, rowEx]
    split_ifs with h1 h2 h3
    any_goals rfl
    any_goals rw [Equiv.swap_apply_def] at h1
    any_goals rw [Equiv.swap_apply_def] at h2
    any_goals rw [Equiv.swap_apply_def] at h3
    any_goals simp
    any_goals split_ifs at h1 with h11 h12
    any_goals split_ifs at h2 with h21 h22
    any_goals split_ifs at h3 with h31 h32
    any_goals apply e.apply_eq_iff_eq_symm_apply.mp at h1
    any_goals apply e.symm_apply_eq.mpr at h11
    exact absurd h1 h2
    exact absurd h11 h21
    exact absurd h11 h21
    any_goals apply e.symm_apply_eq.mp at h21
    exact absurd h21 h11
    exact absurd h1 h2
    any_goals apply e.symm_apply_eq.mpr at h12
    exact absurd h12 h22
    exact absurd h21 h11
    any_goals apply e.symm_apply_eq.mp at h22
    exact absurd h22 h12
    rw [h1] at h2
    rw [←ne_eq] at h2
    exact h2 rfl
    any_goals apply e.apply_eq_iff_eq_symm_apply.mpr at h3
    exact absurd h3 h1
    exact absurd h11 h31
    any_goals apply e.symm_apply_eq.mp at h31
    exact absurd h11 h31
    exact absurd h31 h11
    exact absurd h3 h1
    any_goals apply e.symm_apply_eq.mp at h32
    exact absurd h12 h32
    exact absurd h31 h11
    exact absurd h32 h12
    apply e.eq_symm_apply.mpr at h3
    simp at h3
    exact absurd h3 h1
  rw [←h2]
  simp only [toElim, reindexAlgEquiv_apply, reindex_apply]
  simp [toMatrix_reindexEquiv_prod]

/-- Reindexing commutes with toElim on a list of elimination structures-/
theorem toMatrix_elimStrReindex_list (e : n ≃ p) (LE : List (EliminationStruct n 𝕜)):
    List.map toElim (List.map (elimStrReindex e) LE) =
    List.map (reindexAlgEquiv 𝕜 𝕜 e) (List.map toElim LE) := by
  rw [List.map_map, List.map_map]
  simp only [reindexAlgEquiv_apply, reindex_apply, List.map_inj_left, Function.comp_apply]
  intro e he
  rw [toMatrix_elimStrReindex]
  simp only [reindexAlgEquiv_apply, reindex_apply]

/--  Let `L` be a list of elimination structure for rxr matrices, `M` be an rxr matrix, `N` be a 1x1 matrix, `0` be a
rx1 zero matrix, and `O` be a 1xr matrix. Let `M'` be the block matrix with blocks `M`, `0`, `O`, `N`.
Let `A` be the matrix obtained by converting each element of `L` into a matrix and taking their product.
Let `L'` be the list of r+1 elimination structures by applying elimBlkIncl to each element of `L`.
Let `A'` be the matrix obtained by converting each element of `L'` to a matrix and taking their product.
Then, A'M' is the matrix whose blocks are (AM,0,O,N)-/

theorem elimBlkIncl_toElim_prod_mul (M : Matrix (Fin r) (Fin r) 𝕜) (L : List (EliminationStruct (Fin r) 𝕜))
    (N : Matrix Unit Unit 𝕜) (O : Matrix Unit (Fin r) 𝕜) :
    List.prod (List.map (toElim ∘ elimBlkIncl) L) * fromBlocks M (0 : Matrix (Fin r) Unit 𝕜) O N =
    fromBlocks (List.prod (List.map toElim L) * M) (0 : Matrix (Fin r) Unit 𝕜) O N := by
  induction' L with e L IH
  · simp only [List.map_nil, List.prod_nil, one_mul]
  · simp [Matrix.mul_assoc, IH, toElim,elimBlkIncl, ←rowEx_respects_inclusion, sumInl_toMatrix_prod_mul, fromBlocks_multiply]

/-- List of k trivial (c is zero) transvections -/
def listId (k : ℕ) : List (Matrix (Sum (Fin k) Unit) (Sum (Fin k) Unit) 𝕜) :=
  List.ofFn fun i : Fin k ↦ transvection (inl i) (inr Unit.unit) (0:𝕜)

/--Product of listId is an identity matrix -/
theorem listId_prod_eq_id (r : ℕ) :
    List.prod (listId r) = (1 : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) := by
  simp [listId]

/-- For every r+1 by r+1 matrix M ,there is a list of transvections and a rowEx matrix such that
 multiplying on the left with the rowEx and then the list of transvections will make
 M₍ᵢ,ᵣ₊₁₎ = 0 for every 1 ≤ i < r+1 -/
theorem transvec_mul_rowEx_mul_last_col (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃ i : Fin r ⊕ Unit, ∃ L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜), ∀ j : Fin r,
    (List.prod (List.map toMatrix L) * (((rowEx i (inr 1) :
    Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)) * M)) (inl j) (inr 1) = 0 := by
  by_cases hMne0 : M (inr 1) (inr 1) ≠ 0
  --Case 1: Bottom-right entry is non-zero
  --Begin by creating the i and L that is required and inserting it in the goal
  · use inr 1
    let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
      List.ofFn fun i : Fin r ↦
      ⟨inl i, inr 1, by simp only [PUnit.one_eq, ne_eq, reduceCtorEq, not_false_eq_true], - M (inl i) (inr 1) / M (inr 1) (inr 1)⟩
    use L
    intro j
    have hLN : List.map toMatrix L = listTransvecCol M := by
        simp [L,transvection, listTransvecCol]
        rfl
    have ha: rowEx (inr 1) (inr 1) * M = M := by exact mul_rowEx_i_i_eq (inr 1) M
    rw [hLN, ha, listTransvecCol_mul_last_col]
    exact hMne0
  --Case 2: Bottom-right entry is zero
  · push_neg at hMne0
    by_cases hexistsNon0: (∃ i : Fin r, M (inl i) (inr 1) ≠ 0)
    --Case 2.1: atleast one entry in the last column is non-zero
    · cases' hexistsNon0 with i hi
      /-if there is atleast one non-zero element in last column, you can make the M₍ᵣ₊₁,ᵣ₊₁₎
       non-zero using rowEx -/
      · have hn : (((rowEx (inl i) (inr 1) : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)
          * M) (inr 1) (inr 1) ≠ 0) := by
         rw [rowEx_mul_eq_swap]
         rw [Matrix.updateRow_self]
         exact hi
         --Repeating a proof similar to Case 1 since M₍ᵣ₊₁,ᵣ₊₁₎ is non-zero
        use inl i
        let N : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜 := (rowEx (inl i) (inr 1)) * M
        let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
         List.ofFn fun i : Fin r ↦
           ⟨inl i, inr 1, by simp only [PUnit.one_eq, ne_eq, reduceCtorEq, not_false_eq_true], - N (inl i) (inr 1) / N (inr 1) (inr 1)⟩
        use L
        intro j
        have hLN : List.map toMatrix L = listTransvecCol N := by
          simp [L,N,listTransvecCol, transvection]
          rfl
        rw [hLN, listTransvecCol_mul_last_col]
        exact hn
    --Case 2.2:  all entries in the last column are zero
    · push_neg at hexistsNon0
      use inr 1
      ---if all entries in the last column are zero L can be a list of identity matrices
      let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
       List.ofFn fun i : Fin r ↦
         ⟨inl i, inr 1, by simp only [PUnit.one_eq, ne_eq, reduceCtorEq, not_false_eq_true], 0⟩
      use L
      intro j
      have hL : List.map toMatrix L = listId r := by
        refine List.map_eq_iff.mpr ?_
        intro i
        simp [listId, L]
        exact List.getElem?_replicate
      rw [hL, listId_prod_eq_id, Matrix.one_mul, rowEx_self, Matrix.one_mul]
      exact hexistsNon0 j

/-- Given a matrix `M`, there exists an elimination structure `N` such that when we multiply `M` on
the left with the corresponding elimination matrix (`toElim N`), the first r entries of the last
column of the resultant matrix are zero -/
theorem exists_elim_matrix_mul_last_col (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃ N : EliminationStruct (Fin r ⊕ Unit) 𝕜,
    ∀ j : Fin r, ((toElim N) * M) (inl j) (inr 1) = 0 := by
  rcases transvec_mul_rowEx_mul_last_col r M with ⟨k, L', hLC⟩
  let N' : EliminationStruct (Fin r ⊕ Unit) 𝕜 := ⟨L', k, inr 1⟩
  use N'
  simp [toElim, N', Matrix.mul_assoc]
  exact hLC


end EliminationStruct

open EliminationStruct

/-- This is the induction step for the main result of this work.  If given any rxr matrix `M`, we can find a product
of transvections and row exchange matrices `L` such that `L * M` is an lower triangular matrix, then given any
(r+1)x(r+1) matrix 'M', we can find a a product of transvections and row exchange matrices `L` such that `L * M` is an
lower triangular matrix  -/

theorem exists_list_elim_matrix_mul_eq_lowerTriangular_induction
    (IH : ∀ (M : Matrix (Fin r) (Fin r) 𝕜),
      ∃ E : List (EliminationStruct (Fin r) 𝕜),
      (List.prod (List.map toElim E) * M).BlockTriangular OrderDual.toDual)
    (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃(E₁ : List (EliminationStruct (Fin r ⊕ Unit) 𝕜)),
      (List.prod (List.map toElim E₁) * M).BlockTriangular (OrderDual.toDual ∘ toLex) := by
  have hNLC : ∃ N : EliminationStruct (Fin r ⊕ Unit) 𝕜, ∀ (j : Fin r),
    (toElim N * M) (inl j) (inr Unit.unit) = 0 := by
   exact exists_elim_matrix_mul_last_col r M
  cases hNLC with
  |intro N hLC =>
  let M' := N.toElim * M
  let M'' := toBlocks₁₁ M'
  rcases IH M'' with ⟨L, h₀⟩
  set Mₐ := toBlocks₂₁ M'
  set c := toBlocks₂₂ M'
  refine'⟨List.map (elimBlkIncl) L ++ [N],_⟩
  suffices (List.prod (List.map (toElim ∘ elimBlkIncl) L) * M').BlockTriangular (OrderDual.toDual ∘ toLex) by
    simpa [Matrix.mul_assoc]
  have hM' : M' = fromBlocks (M'') 0 Mₐ c := by
    have X : toBlocks₁₂ (M') = 0 := by
      ext a b
      simp [toBlocks₁₂]
      exact hLC a
    rw [←X]
    exact Eq.symm (fromBlocks_toBlocks M')
  rw [hM']
  rw [elimBlkIncl_toElim_prod_mul]
  simpa [BlockTriangular]


variable {p} [Fintype p] [Fintype n] [DecidableEq p]

/-- If `M` reindexed using `f` can be reduced to a lower triangular matrix using an elimination matrix, then `M` can also be reduced to a lower triangular matrix using an elimination matrix -/

theorem reindexing [LT pᵒᵈ] (M : Matrix p p 𝕜) (f : p ≃ n)
    (H : ∃ E : EliminationStruct n 𝕜,
      ((toElim E) * (Matrix.reindexAlgEquiv 𝕜 _ f M)).BlockTriangular (OrderDual.toDual ∘ f.symm)):
    ∃ E : EliminationStruct p 𝕜,
      ((toElim E) * M).BlockTriangular OrderDual.toDual := by
  rcases H with ⟨E, hE⟩
  refine ⟨elimStrReindex f.symm E, ?_⟩
  simp only [toMatrix_elimStrReindex]
  have h2: (reindexAlgEquiv 𝕜 𝕜 f.symm E.toElim * M) = (reindexAlgEquiv 𝕜 𝕜 f.symm (E.toElim * reindexAlgEquiv 𝕜 𝕜 f M)) := by
    rw [reindexAlgEquiv_mul, reindexAlgEquiv_apply, reindexAlgEquiv_apply]
    simp only [reindex_apply, symm_symm, reindexAlgEquiv_apply, submatrix_submatrix, symm_comp_self,
      submatrix_id_id]
  rw [h2]
  simp only [reindexAlgEquiv_apply] at hE
  simp only [reindexAlgEquiv_apply, blockTriangular_reindex_iff]
  exact hE

/-- If `M` reindexed using `f` can be reduced to a lower triangular matrix using a list of elimination matrices, then `M` can also be reduced to a lower triangular matrix using a list of elimination matrices -/

theorem reindexing_list_elimStr [LT pᵒᵈ] (M : Matrix p p 𝕜) (f : p ≃ n)
    (H : ∃ LE : List (EliminationStruct n 𝕜),
      (List.prod (List.map toElim LE) * (Matrix.reindexAlgEquiv 𝕜 _ f M)).BlockTriangular (OrderDual.toDual ∘ f.symm)):
    ∃ LE : List (EliminationStruct p 𝕜), (List.prod (List.map toElim LE) * M).BlockTriangular OrderDual.toDual := by
  rcases H with ⟨LE, hLE⟩
  refine ⟨LE.map (elimStrReindex f.symm), ?_⟩
  simp only [List.map_map]
  rw [List.comp_map toElim (elimStrReindex f.symm) LE]
  rw [toMatrix_elimStrReindex_list]
  have h1 : M = reindexAlgEquiv 𝕜 _ f.symm (reindexAlgEquiv 𝕜 _ f M) := by
    exact (AlgEquiv.symm_apply_eq (reindexAlgEquiv 𝕜 𝕜 f.symm)).mp rfl
  rw [Eq.symm (map_list_prod (reindexAlgEquiv 𝕜 𝕜 f.symm) (List.map toElim LE))]
  rw [h1]
  rw [Eq.symm (reindexAlgEquiv_mul 𝕜 𝕜 f.symm (LE.map toElim).prod ((reindexAlgEquiv 𝕜 𝕜 f) M))]
  simp only [reindexAlgEquiv_apply] at hLE
  simp only [reindexAlgEquiv_apply, blockTriangular_reindex_iff]
  exact hLE

/-- An order isomorphism mapping `Fin r ⊕ₗ Unit` to `Fin (r + 1)`, used to manage reindexing during the induction step of Gaussian elimination. -/
def checkOrderIso (r : ℕ) : (Fin r ⊕ₗ Unit) ≃o Fin (r + 1) :=
  { toEquiv :=
    { toFun := fun x =>
      match x with
      | Sum.inl a => castSucc a
      | Sum.inr 1 => ⟨r, Nat.lt_succ_self r⟩,

      invFun := fun i =>
      if h : i < r then Sum.inl ⟨i, h⟩ else Sum.inr 1,

      left_inv := by
        intro x
        rcases x with ⟨n, hn⟩ | k
        · simp [hn]
        · simp only [lt_self_iff_false, ↓reduceDIte, PUnit.one_eq]

      right_inv := by
        intro i
        dsimp only [PUnit.one_eq]
        split_ifs with h
        · simp only [castSucc_mk, Fin.eta]
        apply Fin.eq_of_val_eq
        simp only [Fin.castSucc]
        have hir : i < r + 1 := by
          simp [i.isLt]
        apply not_lt.mp at h
        apply le_antisymm h (Nat.lt_succ_iff.mp hir)
    },
      map_rel_iff' := by
        intro x y
        dsimp [Equiv.toFun]
        constructor
        · rcases x with n | k
          · rcases y with m | k
            · simp only [lt_self_iff_false, ↓reduceDIte, PUnit.one_eq]
              intro h
              exact Lex.inl_le_inl_iff.mpr h
            · intro h
              apply Lex.inl_le_inr
          · rcases y with ⟨m, hm⟩ | k
            · simp [hm]
            · simp only [le_refl, imp_self]
        · rcases x with n | k
          · rcases y with m | k
            · simp only [castSucc_le_castSucc_iff]
              intro h
              exact Lex.inl_le_inl_iff.mp h
            · intro h
              rcases n with ⟨n,hn⟩
              simp only [castSucc_mk, mk_le_mk]
              exact le_of_lt hn
          · rcases y with m | k
            · intro h
              exfalso
              cases h
            · simp only [le_refl, imp_self]
  }

/-- Given any matrix `M`, we can find a product of transvections and row exchange matrices `L` such that `L * M` is an
lower triangular matrix -/

theorem exists_list_elim_matrix_mul_eq_lowerTriangular (n : ℕ) (M : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ LE : List (EliminationStruct (Fin n) 𝕜), (List.prod (List.map toElim LE) * M).BlockTriangular (OrderDual.toDual) := by
  induction' n with r hr
  · use []
    simp [EliminationStruct.toElim, rowEx_self, Matrix.one_mul, BlockTriangular]
  · let f := (checkOrderIso r).symm.toEquiv
    have IH := exists_list_elim_matrix_mul_eq_lowerTriangular_induction r hr (Matrix.reindexAlgEquiv 𝕜 𝕜 f M)
    have IH2 : ∃ LE, ((List.map toElim LE).prod * (reindexAlgEquiv 𝕜 𝕜 f) M).BlockTriangular (⇑OrderDual.toDual ∘ ⇑f.symm) := by
      rcases IH with ⟨E₁, hE₁⟩
      use E₁
      intro i j hij
      apply hE₁
      have h1 : f.symm i < f.symm j := hij
      have h2 : @LT.lt (Lex (Fin r ⊕ Unit)) _ i j := (checkOrderIso r).lt_iff_lt.mp h1
      exact OrderDual.toDual_lt_toDual.mpr h2
    exact reindexing_list_elimStr _ M f IH2
