/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.DMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FieldSimp

#align_import linear_algebra.matrix.transvection from "leanprover-community/mathlib"@"0e2aab2b0d521f060f62a14d2cf2e2c54e8491d6"

/-!
# Transvections

Transvections are matrices of the form `1 + stdBasisMatrix i j c`, where `stdBasisMatrix i j c`
is the basic matrix with a `c` at position `(i, j)`. Multiplying by such a transvection on the left
(resp. on the right) amounts to adding `c` times the `j`-th row to the `i`-th row
(resp `c` times the `i`-th column to the `j`-th column). Therefore, they are useful to present
algorithms operating on rows and columns.

Transvections are a special case of *elementary matrices* (according to most references, these also
contain the matrices exchanging rows, and the matrices multiplying a row by a constant).

We show that, over a field, any matrix can be written as `L * D * L'`, where `L` and `L'` are
products of transvections and `D` is diagonal. In other words, one can reduce a matrix to diagonal
form by operations on its rows and columns, a variant of Gauss' pivot algorithm.

## Main definitions and results

* `transvection i j c` is the matrix equal to `1 + stdBasisMatrix i j c`.
* `TransvectionStruct n R` is a structure containing the data of `i, j, c` and a proof that
  `i ≠ j`. These are often easier to manipulate than straight matrices, especially in inductive
  arguments.

* `exists_list_transvec_mul_diagonal_mul_list_transvec` states that any matrix `M` over a field can
  be written in the form `t_1 * ... * t_k * D * t'_1 * ... * t'_l`, where `D` is diagonal and
  the `t_i`, `t'_j` are transvections.

* `diagonal_transvection_induction` shows that a property which is true for diagonal matrices and
  transvections, and invariant under product, is true for all matrices.
* `diagonal_transvection_induction_of_det_ne_zero` is the same statement over invertible matrices.

## Implementation details

The proof of the reduction results is done inductively on the size of the matrices, reducing an
`(r + 1) × (r + 1)` matrix to a matrix whose last row and column are zeroes, except possibly for
the last diagonal entry. This step is done as follows.

If all the coefficients on the last row and column are zero, there is nothing to do. Otherwise,
one can put a nonzero coefficient in the last diagonal entry by a row or column operation, and then
subtract this last diagonal entry from the other entries in the last row and column to make them
vanish.

This step is done in the type `Fin r ⊕ Unit`, where `Fin r` is useful to choose arbitrarily some
order in which we cancel the coefficients, and the sum structure is useful to use the formalism of
block matrices.

To proceed with the induction, we reindex our matrices to reduce to the above situation.
-/


universe u₁ u₂

namespace Matrix

open Matrix

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]
variable [DecidableEq n] [DecidableEq p]
variable [CommRing R]

section Transvection

variable {R n} (i j : n)

/-- The transvection matrix `transvection i j c` is equal to the identity plus `c` at position
`(i, j)`. Multiplying by it on the left (as in `transvection i j c * M`) corresponds to adding
`c` times the `j`-th row of `M` to its `i`-th row. Multiplying by it on the right corresponds
to adding `c` times the `i`-th column to the `j`-th column. -/
def transvection (c : R) : Matrix n n R :=
  1 + Matrix.stdBasisMatrix i j c
#align matrix.transvection Matrix.transvection

@[simp]
theorem transvection_zero : transvection i j (0 : R) = 1 := by simp [transvection]
#align matrix.transvection_zero Matrix.transvection_zero

section

/-- A transvection matrix is obtained from the identity by adding `c` times the `j`-th row to
the `i`-th row. -/
theorem updateRow_eq_transvection [Finite n] (c : R) :
    updateRow (1 : Matrix n n R) i ((1 : Matrix n n R) i + c • (1 : Matrix n n R) j) =
      transvection i j c := by
  cases nonempty_fintype n
  ext a b
  by_cases ha : i = a
  · by_cases hb : j = b
    · simp only [ha, updateRow_self, Pi.add_apply, one_apply, Pi.smul_apply, hb, ↓reduceIte,
        smul_eq_mul, mul_one, transvection, add_apply, StdBasisMatrix.apply_same]
    · simp only [ha, updateRow_self, Pi.add_apply, one_apply, Pi.smul_apply, hb, ↓reduceIte,
        smul_eq_mul, mul_zero, add_zero, transvection, add_apply, and_false, not_false_eq_true,
        StdBasisMatrix.apply_of_ne]
  · simp only [updateRow_ne, transvection, ha, Ne.symm ha, StdBasisMatrix.apply_of_ne, add_zero,
      Algebra.id.smul_eq_mul, Ne, not_false_iff, DMatrix.add_apply, Pi.smul_apply,
      mul_zero, false_and_iff, add_apply]
#align matrix.update_row_eq_transvection Matrix.updateRow_eq_transvection

variable [Fintype n]

theorem transvection_mul_transvection_same (h : i ≠ j) (c d : R) :
    transvection i j c * transvection i j d = transvection i j (c + d) := by
  simp [transvection, Matrix.add_mul, Matrix.mul_add, h, h.symm, add_smul, add_assoc,
    stdBasisMatrix_add]
#align matrix.transvection_mul_transvection_same Matrix.transvection_mul_transvection_same

@[simp]
theorem transvection_mul_apply_same (b : n) (c : R) (M : Matrix n n R) :
    (transvection i j c * M) i b = M i b + c * M j b := by simp [transvection, Matrix.add_mul]
#align matrix.transvection_mul_apply_same Matrix.transvection_mul_apply_same

@[simp]
theorem mul_transvection_apply_same (a : n) (c : R) (M : Matrix n n R) :
    (M * transvection i j c) a j = M a j + c * M a i := by
  simp [transvection, Matrix.mul_add, mul_comm]
#align matrix.mul_transvection_apply_same Matrix.mul_transvection_apply_same

@[simp]
theorem transvection_mul_apply_of_ne (a b : n) (ha : a ≠ i) (c : R) (M : Matrix n n R) :
    (transvection i j c * M) a b = M a b := by simp [transvection, Matrix.add_mul, ha]
#align matrix.transvection_mul_apply_of_ne Matrix.transvection_mul_apply_of_ne

@[simp]
theorem mul_transvection_apply_of_ne (a b : n) (hb : b ≠ j) (c : R) (M : Matrix n n R) :
    (M * transvection i j c) a b = M a b := by simp [transvection, Matrix.mul_add, hb]
#align matrix.mul_transvection_apply_of_ne Matrix.mul_transvection_apply_of_ne

@[simp]
theorem det_transvection_of_ne (h : i ≠ j) (c : R) : det (transvection i j c) = 1 := by
  rw [← updateRow_eq_transvection i j, det_updateRow_add_smul_self _ h, det_one]
#align matrix.det_transvection_of_ne Matrix.det_transvection_of_ne

end

variable (R n)

/-- A structure containing all the information from which one can build a nontrivial transvection.
This structure is easier to manipulate than transvections as one has a direct access to all the
relevant fields. -/
-- porting note (#5171): removed @[nolint has_nonempty_instance]
structure TransvectionStruct where
  (i j : n)
  hij : i ≠ j
  c : R
#align matrix.transvection_struct Matrix.TransvectionStruct

instance [Nontrivial n] : Nonempty (TransvectionStruct n R) := by
  choose x y hxy using exists_pair_ne n
  exact ⟨⟨x, y, hxy, 0⟩⟩

namespace TransvectionStruct

variable {R n}

/-- Associating to a `transvection_struct` the corresponding transvection matrix. -/
def toMatrix (t : TransvectionStruct n R) : Matrix n n R :=
  transvection t.i t.j t.c
#align matrix.transvection_struct.to_matrix Matrix.TransvectionStruct.toMatrix

@[simp]
theorem toMatrix_mk (i j : n) (hij : i ≠ j) (c : R) :
    TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ = transvection i j c :=
  rfl
#align matrix.transvection_struct.to_matrix_mk Matrix.TransvectionStruct.toMatrix_mk

@[simp]
protected theorem det [Fintype n] (t : TransvectionStruct n R) : det t.toMatrix = 1 :=
  det_transvection_of_ne _ _ t.hij _
#align matrix.transvection_struct.det Matrix.TransvectionStruct.det

@[simp]
theorem det_toMatrix_prod [Fintype n] (L : List (TransvectionStruct n 𝕜)) :
    det (L.map toMatrix).prod = 1 := by
  induction' L with t L IH
  · simp
  · simp [IH]
#align matrix.transvection_struct.det_to_matrix_prod Matrix.TransvectionStruct.det_toMatrix_prod

/-- The inverse of a `TransvectionStruct`, designed so that `t.inv.toMatrix` is the inverse of
`t.toMatrix`. -/
@[simps]
protected def inv (t : TransvectionStruct n R) : TransvectionStruct n R where
  i := t.i
  j := t.j
  hij := t.hij
  c := -t.c
#align matrix.transvection_struct.inv Matrix.TransvectionStruct.inv

section

variable [Fintype n]

theorem inv_mul (t : TransvectionStruct n R) : t.inv.toMatrix * t.toMatrix = 1 := by
  rcases t with ⟨_, _, t_hij⟩
  simp [toMatrix, transvection_mul_transvection_same, t_hij]
#align matrix.transvection_struct.inv_mul Matrix.TransvectionStruct.inv_mul

theorem mul_inv (t : TransvectionStruct n R) : t.toMatrix * t.inv.toMatrix = 1 := by
  rcases t with ⟨_, _, t_hij⟩
  simp [toMatrix, transvection_mul_transvection_same, t_hij]
#align matrix.transvection_struct.mul_inv Matrix.TransvectionStruct.mul_inv

theorem reverse_inv_prod_mul_prod (L : List (TransvectionStruct n R)) :
    (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod = 1 := by
  induction' L with t L IH
  · simp
  · suffices
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (t.inv.toMatrix * t.toMatrix) *
          (L.map toMatrix).prod = 1
      by simpa [Matrix.mul_assoc]
    simpa [inv_mul] using IH
#align matrix.transvection_struct.reverse_inv_prod_mul_prod Matrix.TransvectionStruct.reverse_inv_prod_mul_prod

theorem prod_mul_reverse_inv_prod (L : List (TransvectionStruct n R)) :
    (L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod = 1 := by
  induction' L with t L IH
  · simp
  · suffices
      t.toMatrix *
            ((L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod) *
          t.inv.toMatrix = 1
      by simpa [Matrix.mul_assoc]
    simp_rw [IH, Matrix.mul_one, t.mul_inv]
#align matrix.transvection_struct.prod_mul_reverse_inv_prod Matrix.TransvectionStruct.prod_mul_reverse_inv_prod

/-- `M` is a scalar matrix if it commutes with every nontrivial transvection (elementary matrix). -/
theorem _root_.Matrix.mem_range_scalar_of_commute_transvectionStruct {M : Matrix n n R}
    (hM : ∀ t : TransvectionStruct n R, Commute t.toMatrix M) :
    M ∈ Set.range (Matrix.scalar n) := by
  refine mem_range_scalar_of_commute_stdBasisMatrix ?_
  intro i j hij
  simpa [transvection, mul_add, add_mul] using (hM ⟨i, j, hij, 1⟩).eq

theorem _root_.Matrix.mem_range_scalar_iff_commute_transvectionStruct {M : Matrix n n R} :
    M ∈ Set.range (Matrix.scalar n) ↔ ∀ t : TransvectionStruct n R, Commute t.toMatrix M := by
  refine ⟨fun h t => ?_, mem_range_scalar_of_commute_transvectionStruct⟩
  rw [mem_range_scalar_iff_commute_stdBasisMatrix] at h
  refine (Commute.one_left M).add_left ?_
  convert (h _ _ t.hij).smul_left t.c using 1
  rw [smul_stdBasisMatrix, smul_eq_mul, mul_one]

end

open Sum

/-- Given a `TransvectionStruct` on `n`, define the corresponding `TransvectionStruct` on `n ⊕ p`
using the identity on `p`. -/
def sumInl (t : TransvectionStruct n R) : TransvectionStruct (Sum n p) R where
  i := inl t.i
  j := inl t.j
  hij := by simp [t.hij]
  c := t.c
#align matrix.transvection_struct.sum_inl Matrix.TransvectionStruct.sumInl

theorem toMatrix_sumInl (t : TransvectionStruct n R) :
    (t.sumInl p).toMatrix = fromBlocks t.toMatrix 0 0 1 := by
  cases t
  ext a b
  cases' a with a a <;> cases' b with b b
  · by_cases h : a = b <;> simp [TransvectionStruct.sumInl, transvection, h, stdBasisMatrix]
  · simp [TransvectionStruct.sumInl, transvection]
  · simp [TransvectionStruct.sumInl, transvection]
  · by_cases h : a = b <;> simp [TransvectionStruct.sumInl, transvection, h]
#align matrix.transvection_struct.to_matrix_sum_inl Matrix.TransvectionStruct.toMatrix_sumInl

@[simp]
theorem sumInl_toMatrix_prod_mul [Fintype n] [Fintype p] (M : Matrix n n R)
    (L : List (TransvectionStruct n R)) (N : Matrix p p R) :
    (L.map (toMatrix ∘ sumInl p)).prod * fromBlocks M 0 0 N =
      fromBlocks ((L.map toMatrix).prod * M) 0 0 N := by
  induction' L with t L IH
  · simp
  · simp [Matrix.mul_assoc, IH, toMatrix_sumInl, fromBlocks_multiply]
#align matrix.transvection_struct.sum_inl_to_matrix_prod_mul Matrix.TransvectionStruct.sumInl_toMatrix_prod_mul

@[simp]
theorem mul_sumInl_toMatrix_prod [Fintype n] [Fintype p] (M : Matrix n n R)
    (L : List (TransvectionStruct n R)) (N : Matrix p p R) :
    fromBlocks M 0 0 N * (L.map (toMatrix ∘ sumInl p)).prod =
      fromBlocks (M * (L.map toMatrix).prod) 0 0 N := by
  induction' L with t L IH generalizing M N
  · simp
  · simp [IH, toMatrix_sumInl, fromBlocks_multiply]
#align matrix.transvection_struct.mul_sum_inl_to_matrix_prod Matrix.TransvectionStruct.mul_sumInl_toMatrix_prod

variable {p}

/-- Given a `TransvectionStruct` on `n` and an equivalence between `n` and `p`, define the
corresponding `TransvectionStruct` on `p`. -/
def reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) : TransvectionStruct p R where
  i := e t.i
  j := e t.j
  hij := by simp [t.hij]
  c := t.c
#align matrix.transvection_struct.reindex_equiv Matrix.TransvectionStruct.reindexEquiv

variable [Fintype n] [Fintype p]

theorem toMatrix_reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) :
    (t.reindexEquiv e).toMatrix = reindexAlgEquiv R e t.toMatrix := by
  rcases t with ⟨t_i, t_j, _⟩
  ext a b
  simp only [reindexEquiv, transvection, mul_boole, Algebra.id.smul_eq_mul, toMatrix_mk,
    submatrix_apply, reindex_apply, DMatrix.add_apply, Pi.smul_apply, reindexAlgEquiv_apply]
  by_cases ha : e t_i = a <;> by_cases hb : e t_j = b <;> by_cases hab : a = b <;>
    simp [ha, hb, hab, ← e.apply_eq_iff_eq_symm_apply, stdBasisMatrix]
#align matrix.transvection_struct.to_matrix_reindex_equiv Matrix.TransvectionStruct.toMatrix_reindexEquiv

theorem toMatrix_reindexEquiv_prod (e : n ≃ p) (L : List (TransvectionStruct n R)) :
    (L.map (toMatrix ∘ reindexEquiv e)).prod = reindexAlgEquiv R e (L.map toMatrix).prod := by
  induction' L with t L IH
  · simp
  · simp only [toMatrix_reindexEquiv, IH, Function.comp_apply, List.prod_cons,
      reindexAlgEquiv_apply, List.map]
    exact (reindexAlgEquiv_mul _ _ _ _).symm
#align matrix.transvection_struct.to_matrix_reindex_equiv_prod Matrix.TransvectionStruct.toMatrix_reindexEquiv_prod

end TransvectionStruct

end Transvection

/-!
# Reducing matrices by left and right multiplication by transvections

In this section, we show that any matrix can be reduced to diagonal form by left and right
multiplication by transvections (or, equivalently, by elementary operations on lines and columns).
The main step is to kill the last row and column of a matrix in `Fin r ⊕ Unit` with nonzero last
coefficient, by subtracting this coefficient from the other ones. The list of these operations is
recorded in `list_transvec_col M` and `list_transvec_row M`. We have to analyze inductively how
these operations affect the coefficients in the last row and the last column to conclude that they
have the desired effect.

Once this is done, one concludes the reduction by induction on the size
of the matrices, through a suitable reindexing to identify any fintype with `Fin r ⊕ Unit`.
-/


namespace Pivot

variable {R} {r : ℕ} (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)

open Sum Unit Fin TransvectionStruct

/-- A list of transvections such that multiplying on the left with these transvections will replace
the last column with zeroes. -/
def listTransvecCol : List (Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :=
  List.ofFn fun i : Fin r =>
    transvection (inl i) (inr unit) <| -M (inl i) (inr unit) / M (inr unit) (inr unit)
#align matrix.pivot.list_transvec_col Matrix.Pivot.listTransvecCol

/-- A list of transvections such that multiplying on the right with these transvections will replace
the last row with zeroes. -/
def listTransvecRow : List (Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :=
  List.ofFn fun i : Fin r =>
    transvection (inr unit) (inl i) <| -M (inr unit) (inl i) / M (inr unit) (inr unit)
#align matrix.pivot.list_transvec_row Matrix.Pivot.listTransvecRow

/-- Multiplying by some of the matrices in `listTransvecCol M` does not change the last row. -/
theorem listTransvecCol_mul_last_row_drop (i : Sum (Fin r) Unit) {k : ℕ} (hk : k ≤ r) :
    (((listTransvecCol M).drop k).prod * M) (inr unit) i = M (inr unit) i := by
  -- Porting note: `apply` didn't work anymore, because of the implicit arguments
  refine Nat.decreasingInduction' ?_ hk ?_
  · intro n hn _ IH
    have hn' : n < (listTransvecCol M).length := by simpa [listTransvecCol] using hn
    rw [List.drop_eq_getElem_cons hn']
    simpa [listTransvecCol, Matrix.mul_assoc]
  · simp only [listTransvecCol, List.length_ofFn, le_refl, List.drop_eq_nil_of_le, List.prod_nil,
      Matrix.one_mul]
#align matrix.pivot.list_transvec_col_mul_last_row_drop Matrix.Pivot.listTransvecCol_mul_last_row_drop

/-- Multiplying by all the matrices in `listTransvecCol M` does not change the last row. -/
theorem listTransvecCol_mul_last_row (i : Sum (Fin r) Unit) :
    ((listTransvecCol M).prod * M) (inr unit) i = M (inr unit) i := by
  simpa using listTransvecCol_mul_last_row_drop M i (zero_le _)
#align matrix.pivot.list_transvec_col_mul_last_row Matrix.Pivot.listTransvecCol_mul_last_row

/-- Multiplying by all the matrices in `listTransvecCol M` kills all the coefficients in the
last column but the last one. -/
theorem listTransvecCol_mul_last_col (hM : M (inr unit) (inr unit) ≠ 0) (i : Fin r) :
    ((listTransvecCol M).prod * M) (inl i) (inr unit) = 0 := by
  suffices H :
    ∀ k : ℕ,
      k ≤ r →
        (((listTransvecCol M).drop k).prod * M) (inl i) (inr unit) =
          if k ≤ i then 0 else M (inl i) (inr unit) by
    simpa only [List.drop, _root_.zero_le, ite_true] using H 0 (zero_le _)
  intro k hk
  -- Porting note: `apply` didn't work anymore, because of the implicit arguments
  refine Nat.decreasingInduction' ?_ hk ?_
  · intro n hn hk IH
    have hn' : n < (listTransvecCol M).length := by simpa [listTransvecCol] using hn
    let n' : Fin r := ⟨n, hn⟩
    rw [List.drop_eq_getElem_cons hn']
    have A :
      (listTransvecCol M)[n] =
        transvection (inl n') (inr unit) (-M (inl n') (inr unit) / M (inr unit) (inr unit)) := by
      simp [listTransvecCol]
    simp only [Matrix.mul_assoc, A, List.prod_cons]
    by_cases h : n' = i
    · have hni : n = i := by
        cases i
        simp only [n', Fin.mk_eq_mk] at h
        simp [h]
      simp only [h, transvection_mul_apply_same, IH, ← hni, add_le_iff_nonpos_right,
          listTransvecCol_mul_last_row_drop _ _ hn]
      field_simp [hM]
    · have hni : n ≠ i := by
        rintro rfl
        cases i
        simp at h
      simp only [ne_eq, inl.injEq, Ne.symm h, not_false_eq_true, transvection_mul_apply_of_ne]
      rw [IH]
      rcases le_or_lt (n + 1) i with (hi | hi)
      · simp only [hi, n.le_succ.trans hi, if_true]
      · rw [if_neg, if_neg]
        · simpa only [hni.symm, not_le, or_false_iff] using Nat.lt_succ_iff_lt_or_eq.1 hi
        · simpa only [not_le] using hi
  · simp only [listTransvecCol, List.length_ofFn, le_refl, List.drop_eq_nil_of_le, List.prod_nil,
      Matrix.one_mul]
    rw [if_neg]
    simpa only [not_le] using i.2
#align matrix.pivot.list_transvec_col_mul_last_col Matrix.Pivot.listTransvecCol_mul_last_col

/-- Multiplying by some of the matrices in `listTransvecRow M` does not change the last column. -/
theorem mul_listTransvecRow_last_col_take (i : Sum (Fin r) Unit) {k : ℕ} (hk : k ≤ r) :
    (M * ((listTransvecRow M).take k).prod) i (inr unit) = M i (inr unit) := by
  induction' k with k IH
  · simp only [Matrix.mul_one, List.take_zero, List.prod_nil, List.take, Matrix.mul_one]
  · have hkr : k < r := hk
    let k' : Fin r := ⟨k, hkr⟩
    have :
      (listTransvecRow M)[k]? =
        ↑(transvection (inr Unit.unit) (inl k')
            (-M (inr Unit.unit) (inl k') / M (inr Unit.unit) (inr Unit.unit))) := by
      simp only [listTransvecRow, List.ofFnNthVal, hkr, dif_pos, List.getElem?_ofFn]
    simp only [List.take_succ, ← Matrix.mul_assoc, this, List.prod_append, Matrix.mul_one,
      List.prod_cons, List.prod_nil, Option.toList_some]
    rw [mul_transvection_apply_of_ne, IH hkr.le]
    simp only [Ne, not_false_iff]
#align matrix.pivot.mul_list_transvec_row_last_col_take Matrix.Pivot.mul_listTransvecRow_last_col_take

/-- Multiplying by all the matrices in `listTransvecRow M` does not change the last column. -/
theorem mul_listTransvecRow_last_col (i : Sum (Fin r) Unit) :
    (M * (listTransvecRow M).prod) i (inr unit) = M i (inr unit) := by
  have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
  rw [← List.take_length (listTransvecRow M), A]
  simpa using mul_listTransvecRow_last_col_take M i le_rfl
#align matrix.pivot.mul_list_transvec_row_last_col Matrix.Pivot.mul_listTransvecRow_last_col

/-- Multiplying by all the matrices in `listTransvecRow M` kills all the coefficients in the
last row but the last one. -/
theorem mul_listTransvecRow_last_row (hM : M (inr unit) (inr unit) ≠ 0) (i : Fin r) :
    (M * (listTransvecRow M).prod) (inr unit) (inl i) = 0 := by
  suffices H :
    ∀ k : ℕ,
      k ≤ r →
        (M * ((listTransvecRow M).take k).prod) (inr unit) (inl i) =
          if k ≤ i then M (inr unit) (inl i) else 0 by
    have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
    rw [← List.take_length (listTransvecRow M), A]
    have : ¬r ≤ i := by simp
    simpa only [this, ite_eq_right_iff] using H r le_rfl
  intro k hk
  induction' k with n IH
  · simp only [if_true, Matrix.mul_one, List.take_zero, zero_le', List.prod_nil, Nat.zero_eq]
  · have hnr : n < r := hk
    let n' : Fin r := ⟨n, hnr⟩
    have A :
      (listTransvecRow M)[n]? =
        ↑(transvection (inr unit) (inl n')
        (-M (inr unit) (inl n') / M (inr unit) (inr unit))) := by
      simp only [listTransvecRow, List.ofFnNthVal, hnr, dif_pos, List.getElem?_ofFn]
    simp only [List.take_succ, A, ← Matrix.mul_assoc, List.prod_append, Matrix.mul_one,
      List.prod_cons, List.prod_nil, Option.toList_some]
    by_cases h : n' = i
    · have hni : n = i := by
        cases i
        simp only [n', Fin.mk_eq_mk] at h
        simp only [h]
      have : ¬n.succ ≤ i := by simp only [← hni, n.lt_succ_self, not_le]
      simp only [h, mul_transvection_apply_same, List.take, if_false,
        mul_listTransvecRow_last_col_take _ _ hnr.le, hni.le, this, if_true, IH hnr.le]
      field_simp [hM]
    · have hni : n ≠ i := by
        rintro rfl
        cases i
        tauto
      simp only [IH hnr.le, Ne, mul_transvection_apply_of_ne, Ne.symm h, inl.injEq,
        not_false_eq_true]
      rcases le_or_lt (n + 1) i with (hi | hi)
      · simp [hi, n.le_succ.trans hi, if_true]
      · rw [if_neg, if_neg]
        · simpa only [not_le] using hi
        · simpa only [hni.symm, not_le, or_false_iff] using Nat.lt_succ_iff_lt_or_eq.1 hi
#align matrix.pivot.mul_list_transvec_row_last_row Matrix.Pivot.mul_listTransvecRow_last_row

/-- Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecRow M` kills
all the coefficients in the last row but the last one. -/
theorem listTransvecCol_mul_mul_listTransvecRow_last_col (hM : M (inr unit) (inr unit) ≠ 0)
    (i : Fin r) :
    ((listTransvecCol M).prod * M * (listTransvecRow M).prod) (inr unit) (inl i) = 0 := by
  have : listTransvecRow M = listTransvecRow ((listTransvecCol M).prod * M) := by
    simp [listTransvecRow, listTransvecCol_mul_last_row]
  rw [this]
  apply mul_listTransvecRow_last_row
  simpa [listTransvecCol_mul_last_row] using hM
#align matrix.pivot.list_transvec_col_mul_mul_list_transvec_row_last_col Matrix.Pivot.listTransvecCol_mul_mul_listTransvecRow_last_col

/-- Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecRow M` kills
all the coefficients in the last column but the last one. -/
theorem listTransvecCol_mul_mul_listTransvecRow_last_row (hM : M (inr unit) (inr unit) ≠ 0)
    (i : Fin r) :
    ((listTransvecCol M).prod * M * (listTransvecRow M).prod) (inl i) (inr unit) = 0 := by
  have : listTransvecCol M = listTransvecCol (M * (listTransvecRow M).prod) := by
    simp [listTransvecCol, mul_listTransvecRow_last_col]
  rw [this, Matrix.mul_assoc]
  apply listTransvecCol_mul_last_col
  simpa [mul_listTransvecRow_last_col] using hM
#align matrix.pivot.list_transvec_col_mul_mul_list_transvec_row_last_row Matrix.Pivot.listTransvecCol_mul_mul_listTransvecRow_last_row

/-- Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecRow M` turns
the matrix in block-diagonal form. -/
theorem isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow
    (hM : M (inr unit) (inr unit) ≠ 0) :
    IsTwoBlockDiagonal ((listTransvecCol M).prod * M * (listTransvecRow M).prod) := by
  constructor
  · ext i j
    have : j = unit := by simp only [eq_iff_true_of_subsingleton]
    simp [toBlocks₁₂, this, listTransvecCol_mul_mul_listTransvecRow_last_row M hM]
  · ext i j
    have : i = unit := by simp only [eq_iff_true_of_subsingleton]
    simp [toBlocks₂₁, this, listTransvecCol_mul_mul_listTransvecRow_last_col M hM]
#align matrix.pivot.is_two_block_diagonal_list_transvec_col_mul_mul_list_transvec_row Matrix.Pivot.isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow

/-- There exist two lists of `TransvectionStruct` such that multiplying by them on the left and
on the right makes a matrix block-diagonal, when the last coefficient is nonzero. -/
theorem exists_isTwoBlockDiagonal_of_ne_zero (hM : M (inr unit) (inr unit) ≠ 0) :
    ∃ L L' : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod) := by
  let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inl i, inr unit, by simp, -M (inl i) (inr unit) / M (inr unit) (inr unit)⟩
  let L' : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inr unit, inl i, by simp, -M (inr unit) (inl i) / M (inr unit) (inr unit)⟩
  refine ⟨L, L', ?_⟩
  have A : L.map toMatrix = listTransvecCol M := by simp [L, listTransvecCol, (· ∘ ·)]
  have B : L'.map toMatrix = listTransvecRow M := by simp [L', listTransvecRow, (· ∘ ·)]
  rw [A, B]
  exact isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M hM
#align matrix.pivot.exists_is_two_block_diagonal_of_ne_zero Matrix.Pivot.exists_isTwoBlockDiagonal_of_ne_zero

/-- There exist two lists of `TransvectionStruct` such that multiplying by them on the left and
on the right makes a matrix block-diagonal. -/
theorem exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec
    (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃ L L' : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod) := by
  by_cases H : IsTwoBlockDiagonal M
  · refine ⟨List.nil, List.nil, by simpa using H⟩
  -- we have already proved this when the last coefficient is nonzero
  by_cases hM : M (inr unit) (inr unit) ≠ 0
  · exact exists_isTwoBlockDiagonal_of_ne_zero M hM
  -- when the last coefficient is zero but there is a nonzero coefficient on the last row or the
  -- last column, we will first put this nonzero coefficient in last position, and then argue as
  -- above.
  push_neg at hM
  simp only [not_and_or, IsTwoBlockDiagonal, toBlocks₁₂, toBlocks₂₁, ← Matrix.ext_iff] at H
  have : ∃ i : Fin r, M (inl i) (inr unit) ≠ 0 ∨ M (inr unit) (inl i) ≠ 0 := by
    cases' H with H H
    · contrapose! H
      rintro i ⟨⟩
      exact (H i).1
    · contrapose! H
      rintro ⟨⟩ j
      exact (H j).2
  rcases this with ⟨i, h | h⟩
  · let M' := transvection (inr Unit.unit) (inl i) 1 * M
    have hM' : M' (inr unit) (inr unit) ≠ 0 := by simpa [M', hM]
    rcases exists_isTwoBlockDiagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩
    rw [Matrix.mul_assoc] at hLL'
    refine ⟨L ++ [⟨inr unit, inl i, by simp, 1⟩], L', ?_⟩
    simp only [List.map_append, List.prod_append, Matrix.mul_one, toMatrix_mk, List.prod_cons,
      List.prod_nil, List.map, Matrix.mul_assoc (L.map toMatrix).prod]
    exact hLL'
  · let M' := M * transvection (inl i) (inr unit) 1
    have hM' : M' (inr unit) (inr unit) ≠ 0 := by simpa [M', hM]
    rcases exists_isTwoBlockDiagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩
    refine ⟨L, ⟨inl i, inr unit, by simp, 1⟩::L', ?_⟩
    simp only [← Matrix.mul_assoc, toMatrix_mk, List.prod_cons, List.map]
    rw [Matrix.mul_assoc (L.map toMatrix).prod]
    exact hLL'
#align matrix.pivot.exists_is_two_block_diagonal_list_transvec_mul_mul_list_transvec Matrix.Pivot.exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec

/-- Inductive step for the reduction: if one knows that any size `r` matrix can be reduced to
diagonal form by elementary operations, then one deduces it for matrices over `Fin r ⊕ Unit`. -/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction
    (IH :
      ∀ M : Matrix (Fin r) (Fin r) 𝕜,
        ∃ (L₀ L₀' : List (TransvectionStruct (Fin r) 𝕜)) (D₀ : Fin r → 𝕜),
          (L₀.map toMatrix).prod * M * (L₀'.map toMatrix).prod = diagonal D₀)
    (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃ (L L' : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜)) (D : Sum (Fin r) Unit → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  rcases exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec M with ⟨L₁, L₁', hM⟩
  let M' := (L₁.map toMatrix).prod * M * (L₁'.map toMatrix).prod
  let M'' := toBlocks₁₁ M'
  rcases IH M'' with ⟨L₀, L₀', D₀, h₀⟩
  set c := M' (inr unit) (inr unit)
  refine
    ⟨L₀.map (sumInl Unit) ++ L₁, L₁' ++ L₀'.map (sumInl Unit),
      Sum.elim D₀ fun _ => M' (inr unit) (inr unit), ?_⟩
  suffices (L₀.map (toMatrix ∘ sumInl Unit)).prod * M' * (L₀'.map (toMatrix ∘ sumInl Unit)).prod =
      diagonal (Sum.elim D₀ fun _ => c) by
    simpa [M', c, Matrix.mul_assoc]
  have : M' = fromBlocks M'' 0 0 (diagonal fun _ => c) := by
    -- Porting note: simplified proof, because `congr` didn't work anymore
    rw [← fromBlocks_toBlocks M', hM.1, hM.2]
    rfl
  rw [this]
  simp [h₀]
#align matrix.pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction

variable {n p} [Fintype n] [Fintype p]

/-- Reduction to diagonal form by elementary operations is invariant under reindexing. -/
theorem reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix p p 𝕜)
    (e : p ≃ n)
    (H :
      ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
        (L.map toMatrix).prod * Matrix.reindexAlgEquiv 𝕜 e M * (L'.map toMatrix).prod =
          diagonal D) :
    ∃ (L L' : List (TransvectionStruct p 𝕜)) (D : p → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  rcases H with ⟨L₀, L₀', D₀, h₀⟩
  refine ⟨L₀.map (reindexEquiv e.symm), L₀'.map (reindexEquiv e.symm), D₀ ∘ e, ?_⟩
  have : M = reindexAlgEquiv 𝕜 e.symm (reindexAlgEquiv 𝕜 e M) := by
    simp only [Equiv.symm_symm, submatrix_submatrix, reindex_apply, submatrix_id_id,
      Equiv.symm_comp_self, reindexAlgEquiv_apply]
  rw [this]
  simp only [toMatrix_reindexEquiv_prod, List.map_map, reindexAlgEquiv_apply]
  simp only [← reindexAlgEquiv_apply, ← reindexAlgEquiv_mul, h₀]
  simp only [Equiv.symm_symm, reindex_apply, submatrix_diagonal_equiv, reindexAlgEquiv_apply]
#align matrix.pivot.reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal Matrix.Pivot.reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal

/-- Any matrix can be reduced to diagonal form by elementary operations. Formulated here on `Type 0`
because we will make an induction using `Fin r`.
See `exists_list_transvec_mul_mul_list_transvec_eq_diagonal` for the general version (which follows
from this one and reindexing). -/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux (n : Type) [Fintype n]
    [DecidableEq n] (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  induction' hn : Fintype.card n with r IH generalizing n M
  · refine ⟨List.nil, List.nil, fun _ => 1, ?_⟩
    ext i j
    rw [Fintype.card_eq_zero_iff] at hn
    exact hn.elim' i
  · have e : n ≃ Sum (Fin r) Unit := by
      refine Fintype.equivOfCardEq ?_
      rw [hn]
      rw [@Fintype.card_sum (Fin r) Unit _ _]
      simp
    apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
    apply
      exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction fun N =>
        IH (Fin r) N (by simp)
#align matrix.pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux

/-- Any matrix can be reduced to diagonal form by elementary operations. -/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  have e : n ≃ Fin (Fintype.card n) := Fintype.equivOfCardEq (by simp)
  apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
  apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux
#align matrix.pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal

/-- Any matrix can be written as the product of transvections, a diagonal matrix, and
transvections. -/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      M = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod := by
  rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  refine ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, ?_⟩
  suffices
    M =
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod * M *
        ((L'.map toMatrix).prod * (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod)
    by simpa [← h, Matrix.mul_assoc]
  rw [reverse_inv_prod_mul_prod, prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one]
#align matrix.pivot.exists_list_transvec_mul_diagonal_mul_list_transvec Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec

end Pivot

open Pivot TransvectionStruct

variable {n} [Fintype n]

/-- Induction principle for matrices based on transvections: if a property is true for all diagonal
matrices, all transvections, and is stable under product, then it is true for all matrices. This is
the useful way to say that matrices are generated by diagonal matrices and transvections.

We state a slightly more general version: to prove a property for a matrix `M`, it suffices to
assume that the diagonal matrices we consider have the same determinant as `M`. This is useful to
obtain similar principles for `SLₙ` or `GLₙ`. -/
theorem diagonal_transvection_induction (P : Matrix n n 𝕜 → Prop) (M : Matrix n n 𝕜)
    (hdiag : ∀ D : n → 𝕜, det (diagonal D) = det M → P (diagonal D))
    (htransvec : ∀ t : TransvectionStruct n 𝕜, P t.toMatrix) (hmul : ∀ A B, P A → P B → P (A * B)) :
    P M := by
  rcases exists_list_transvec_mul_diagonal_mul_list_transvec M with ⟨L, L', D, h⟩
  have PD : P (diagonal D) := hdiag D (by simp [h])
  suffices H :
    ∀ (L₁ L₂ : List (TransvectionStruct n 𝕜)) (E : Matrix n n 𝕜),
      P E → P ((L₁.map toMatrix).prod * E * (L₂.map toMatrix).prod) by
    rw [h]
    apply H L L'
    exact PD
  intro L₁ L₂ E PE
  induction' L₁ with t L₁ IH
  · simp only [Matrix.one_mul, List.prod_nil, List.map]
    induction' L₂ with t L₂ IH generalizing E
    · simpa
    · simp only [← Matrix.mul_assoc, List.prod_cons, List.map]
      apply IH
      exact hmul _ _ PE (htransvec _)
  · simp only [Matrix.mul_assoc, List.prod_cons, List.map] at IH ⊢
    exact hmul _ _ (htransvec _) IH
#align matrix.diagonal_transvection_induction Matrix.diagonal_transvection_induction

/-- Induction principle for invertible matrices based on transvections: if a property is true for
all invertible diagonal matrices, all transvections, and is stable under product of invertible
matrices, then it is true for all invertible matrices. This is the useful way to say that
invertible matrices are generated by invertible diagonal matrices and transvections. -/
theorem diagonal_transvection_induction_of_det_ne_zero (P : Matrix n n 𝕜 → Prop) (M : Matrix n n 𝕜)
    (hMdet : det M ≠ 0) (hdiag : ∀ D : n → 𝕜, det (diagonal D) ≠ 0 → P (diagonal D))
    (htransvec : ∀ t : TransvectionStruct n 𝕜, P t.toMatrix)
    (hmul : ∀ A B, det A ≠ 0 → det B ≠ 0 → P A → P B → P (A * B)) : P M := by
  let Q : Matrix n n 𝕜 → Prop := fun N => det N ≠ 0 ∧ P N
  have : Q M := by
    apply diagonal_transvection_induction Q M
    · intro D hD
      have detD : det (diagonal D) ≠ 0 := by
        rw [hD]
        exact hMdet
      exact ⟨detD, hdiag _ detD⟩
    · intro t
      exact ⟨by simp, htransvec t⟩
    · intro A B QA QB
      exact ⟨by simp [QA.1, QB.1], hmul A B QA.1 QB.1 QA.2 QB.2⟩
  exact this.2
#align matrix.diagonal_transvection_induction_of_det_ne_zero Matrix.diagonal_transvection_induction_of_det_ne_zero

end Matrix
