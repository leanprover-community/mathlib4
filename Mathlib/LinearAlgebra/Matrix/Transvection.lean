/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.DMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FieldSimp

#align_import linear_algebra.matrix.transvection from "leanprover-community/mathlib"@"0e2aab2b0d521f060f62a14d2cf2e2c54e8491d6"

/-!
# Transvections

Transvections are matrices of the form `1 + StdBasisMatrix i j c`, where `StdBasisMatrix i j c`
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

* `Transvection i j c` is the matrix equal to `1 + StdBasisMatrix i j c`.
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

/-- The transvection matrix `Transvection i j c` is equal to the identity plus `c` at position
`(i, j)`. Multiplying by it on the left (as in `Transvection i j c * M`) corresponds to adding
`c` times the `j`-th line of `M` to its `i`-th line. Multiplying by it on the right corresponds
to adding `c` times the `i`-th column to the `j`-th column. -/
def transvection (c : R) : Matrix n n R :=
  1 + Matrix.stdBasisMatrix i j c
#align matrix.transvection Matrix.transvection

@[simp]
theorem transvection_zero : transvection i j (0 : R) = 1 := by simp [transvection]
                                                               -- 🎉 no goals
#align matrix.transvection_zero Matrix.transvection_zero

section

/-- A transvection matrix is obtained from the identity by adding `c` times the `j`-th row to
the `i`-th row. -/
theorem updateRow_eq_transvection [Finite n] (c : R) :
    updateRow (1 : Matrix n n R) i ((1 : Matrix n n R) i + c • (1 : Matrix n n R) j) =
      transvection i j c := by
  cases nonempty_fintype n
  -- ⊢ updateRow 1 i (OfNat.ofNat 1 i + c • OfNat.ofNat 1 j) = transvection i j c
  ext a b
  -- ⊢ updateRow 1 i (OfNat.ofNat 1 i + c • OfNat.ofNat 1 j) a b = transvection i j …
  by_cases ha : i = a; by_cases hb : j = b
  -- ⊢ updateRow 1 i (OfNat.ofNat 1 i + c • OfNat.ofNat 1 j) a b = transvection i j …
  · simp only [updateRow_self, transvection, ha, hb, Pi.add_apply, StdBasisMatrix.apply_same,
      one_apply_eq, Pi.smul_apply, mul_one, Algebra.id.smul_eq_mul, add_apply]
  · simp only [updateRow_self, transvection, ha, hb, StdBasisMatrix.apply_of_ne, Pi.add_apply,
      Ne.def, not_false_iff, Pi.smul_apply, and_false_iff, one_apply_ne, Algebra.id.smul_eq_mul,
      mul_zero, add_apply]
  · simp only [updateRow_ne, transvection, ha, Ne.symm ha, StdBasisMatrix.apply_of_ne, add_zero,
      Algebra.id.smul_eq_mul, Ne.def, not_false_iff, DMatrix.add_apply, Pi.smul_apply,
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
                                                           -- 🎉 no goals
#align matrix.transvection_mul_apply_same Matrix.transvection_mul_apply_same

@[simp]
theorem mul_transvection_apply_same (a : n) (c : R) (M : Matrix n n R) :
    (M * transvection i j c) a j = M a j + c * M a i := by
  simp [transvection, Matrix.mul_add, mul_comm]
  -- 🎉 no goals
#align matrix.mul_transvection_apply_same Matrix.mul_transvection_apply_same

@[simp]
theorem transvection_mul_apply_of_ne (a b : n) (ha : a ≠ i) (c : R) (M : Matrix n n R) :
    (transvection i j c * M) a b = M a b := by simp [transvection, Matrix.add_mul, ha]
                                               -- 🎉 no goals
#align matrix.transvection_mul_apply_of_ne Matrix.transvection_mul_apply_of_ne

@[simp]
theorem mul_transvection_apply_of_ne (a b : n) (hb : b ≠ j) (c : R) (M : Matrix n n R) :
    (M * transvection i j c) a b = M a b := by simp [transvection, Matrix.mul_add, hb]
                                               -- 🎉 no goals
#align matrix.mul_transvection_apply_of_ne Matrix.mul_transvection_apply_of_ne

@[simp]
theorem det_transvection_of_ne (h : i ≠ j) (c : R) : det (transvection i j c) = 1 := by
  rw [← updateRow_eq_transvection i j, det_updateRow_add_smul_self _ h, det_one]
  -- 🎉 no goals
#align matrix.det_transvection_of_ne Matrix.det_transvection_of_ne

end

variable (R n)

/-- A structure containing all the information from which one can build a nontrivial transvection.
This structure is easier to manipulate than transvections as one has a direct access to all the
relevant fields. -/
-- porting note: removed @[nolint has_nonempty_instance]
structure TransvectionStruct where
  (i j : n)
  hij : i ≠ j
  c : R
#align matrix.transvection_struct Matrix.TransvectionStruct

instance [Nontrivial n] : Nonempty (TransvectionStruct n R) := by
  choose x y hxy using exists_pair_ne n
  -- ⊢ Nonempty (TransvectionStruct n R)
  exact ⟨⟨x, y, hxy, 0⟩⟩
  -- 🎉 no goals

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
  -- ⊢ det (List.prod (List.map toMatrix [])) = 1
  · simp
    -- 🎉 no goals
  · simp [IH]
    -- 🎉 no goals
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
  -- ⊢ toMatrix (TransvectionStruct.inv { i := i✝, j := j✝, hij := t_hij, c := c✝ } …
  simp [toMatrix, transvection_mul_transvection_same, t_hij]
  -- 🎉 no goals
#align matrix.transvection_struct.inv_mul Matrix.TransvectionStruct.inv_mul

theorem mul_inv (t : TransvectionStruct n R) : t.toMatrix * t.inv.toMatrix = 1 := by
  rcases t with ⟨_, _, t_hij⟩
  -- ⊢ toMatrix { i := i✝, j := j✝, hij := t_hij, c := c✝ } * toMatrix (Transvectio …
  simp [toMatrix, transvection_mul_transvection_same, t_hij]
  -- 🎉 no goals
#align matrix.transvection_struct.mul_inv Matrix.TransvectionStruct.mul_inv

theorem reverse_inv_prod_mul_prod (L : List (TransvectionStruct n R)) :
    (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod = 1 := by
  induction' L with t L IH
  -- ⊢ List.prod (List.map (toMatrix ∘ TransvectionStruct.inv) (List.reverse [])) * …
  · simp
    -- 🎉 no goals
  · suffices
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (t.inv.toMatrix * t.toMatrix) *
          (L.map toMatrix).prod = 1
      by simpa [Matrix.mul_assoc]
    simpa [inv_mul] using IH
    -- 🎉 no goals
#align matrix.transvection_struct.reverse_inv_prod_mul_prod Matrix.TransvectionStruct.reverse_inv_prod_mul_prod

theorem prod_mul_reverse_inv_prod (L : List (TransvectionStruct n R)) :
    (L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod = 1 := by
  induction' L with t L IH
  -- ⊢ List.prod (List.map toMatrix []) * List.prod (List.map (toMatrix ∘ Transvect …
  · simp
    -- 🎉 no goals
  · suffices
      t.toMatrix *
            ((L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod) *
          t.inv.toMatrix = 1
      by simpa [Matrix.mul_assoc]
    simp_rw [IH, Matrix.mul_one, t.mul_inv]
    -- 🎉 no goals
#align matrix.transvection_struct.prod_mul_reverse_inv_prod Matrix.TransvectionStruct.prod_mul_reverse_inv_prod

end

open Sum

/-- Given a `TransvectionStruct` on `n`, define the corresponding `TransvectionStruct` on `n ⊕ p`
using the identity on `p`. -/
def sumInl (t : TransvectionStruct n R) : TransvectionStruct (Sum n p) R where
  i := inl t.i
  j := inl t.j
  hij := by simp [t.hij]
            -- 🎉 no goals
  c := t.c
#align matrix.transvection_struct.sum_inl Matrix.TransvectionStruct.sumInl

theorem toMatrix_sumInl (t : TransvectionStruct n R) :
    (t.sumInl p).toMatrix = fromBlocks t.toMatrix 0 0 1 := by
  cases t
  -- ⊢ toMatrix (sumInl p { i := i✝, j := j✝, hij := hij✝, c := c✝ }) = fromBlocks  …
  ext a b
  -- ⊢ toMatrix (sumInl p { i := i✝, j := j✝, hij := hij✝, c := c✝ }) a b = fromBlo …
  cases' a with a a <;> cases' b with b b
  -- ⊢ toMatrix (sumInl p { i := i✝, j := j✝, hij := hij✝, c := c✝ }) (inl a) b = f …
                        -- ⊢ toMatrix (sumInl p { i := i✝, j := j✝, hij := hij✝, c := c✝ }) (inl a) (inl  …
                        -- ⊢ toMatrix (sumInl p { i := i✝, j := j✝, hij := hij✝, c := c✝ }) (inr a) (inl  …
  · by_cases h : a = b <;> simp [TransvectionStruct.sumInl, transvection, h, stdBasisMatrix]
    -- ⊢ toMatrix (sumInl p { i := i✝, j := j✝, hij := hij✝, c := c✝ }) (inl a) (inl  …
                           -- 🎉 no goals
                           -- 🎉 no goals
  · simp [TransvectionStruct.sumInl, transvection]
    -- 🎉 no goals
  · simp [TransvectionStruct.sumInl, transvection]
    -- 🎉 no goals
  · by_cases h : a = b <;> simp [TransvectionStruct.sumInl, transvection, h]
    -- ⊢ toMatrix (sumInl p { i := i✝, j := j✝, hij := hij✝, c := c✝ }) (inr a) (inr  …
                           -- 🎉 no goals
                           -- 🎉 no goals
#align matrix.transvection_struct.to_matrix_sum_inl Matrix.TransvectionStruct.toMatrix_sumInl

@[simp]
theorem sumInl_toMatrix_prod_mul [Fintype n] [Fintype p] (M : Matrix n n R)
    (L : List (TransvectionStruct n R)) (N : Matrix p p R) :
    (L.map (toMatrix ∘ sumInl p)).prod * fromBlocks M 0 0 N =
      fromBlocks ((L.map toMatrix).prod * M) 0 0 N := by
  induction' L with t L IH
  -- ⊢ List.prod (List.map (toMatrix ∘ sumInl p) []) * fromBlocks M 0 0 N = fromBlo …
  · simp
    -- 🎉 no goals
  · simp [Matrix.mul_assoc, IH, toMatrix_sumInl, fromBlocks_multiply]
    -- 🎉 no goals
#align matrix.transvection_struct.sum_inl_to_matrix_prod_mul Matrix.TransvectionStruct.sumInl_toMatrix_prod_mul

@[simp]
theorem mul_sumInl_toMatrix_prod [Fintype n] [Fintype p] (M : Matrix n n R)
    (L : List (TransvectionStruct n R)) (N : Matrix p p R) :
    fromBlocks M 0 0 N * (L.map (toMatrix ∘ sumInl p)).prod =
      fromBlocks (M * (L.map toMatrix).prod) 0 0 N := by
  induction' L with t L IH generalizing M N
  -- ⊢ fromBlocks M 0 0 N * List.prod (List.map (toMatrix ∘ sumInl p) []) = fromBlo …
  · simp
    -- 🎉 no goals
  · simp [IH, toMatrix_sumInl, fromBlocks_multiply]
    -- 🎉 no goals
#align matrix.transvection_struct.mul_sum_inl_to_matrix_prod Matrix.TransvectionStruct.mul_sumInl_toMatrix_prod

variable {p}

/-- Given a `TransvectionStruct` on `n` and an equivalence between `n` and `p`, define the
corresponding `TransvectionStruct` on `p`. -/
def reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) : TransvectionStruct p R where
  i := e t.i
  j := e t.j
  hij := by simp [t.hij]
            -- 🎉 no goals
  c := t.c
#align matrix.transvection_struct.reindex_equiv Matrix.TransvectionStruct.reindexEquiv

variable [Fintype n] [Fintype p]

theorem toMatrix_reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) :
    (t.reindexEquiv e).toMatrix = reindexAlgEquiv R e t.toMatrix := by
  rcases t with ⟨t_i, t_j, _⟩
  -- ⊢ toMatrix (reindexEquiv e { i := t_i, j := t_j, hij := hij✝, c := c✝ }) = ↑(r …
  ext a b
  -- ⊢ toMatrix (reindexEquiv e { i := t_i, j := t_j, hij := hij✝, c := c✝ }) a b = …
  simp only [reindexEquiv, transvection, mul_boole, Algebra.id.smul_eq_mul, toMatrix_mk,
    submatrix_apply, reindex_apply, DMatrix.add_apply, Pi.smul_apply, reindexAlgEquiv_apply]
  by_cases ha : e t_i = a <;> by_cases hb : e t_j = b <;> by_cases hab : a = b <;>
  -- ⊢ (1 + stdBasisMatrix (↑e t_i) (↑e t_j) c✝) a b = (1 + stdBasisMatrix t_i t_j  …
                              -- ⊢ (1 + stdBasisMatrix (↑e t_i) (↑e t_j) c✝) a b = (1 + stdBasisMatrix t_i t_j  …
                              -- ⊢ (1 + stdBasisMatrix (↑e t_i) (↑e t_j) c✝) a b = (1 + stdBasisMatrix t_i t_j  …
                                                          -- ⊢ (1 + stdBasisMatrix (↑e t_i) (↑e t_j) c✝) a b = (1 + stdBasisMatrix t_i t_j  …
                                                          -- ⊢ (1 + stdBasisMatrix (↑e t_i) (↑e t_j) c✝) a b = (1 + stdBasisMatrix t_i t_j  …
                                                          -- ⊢ (1 + stdBasisMatrix (↑e t_i) (↑e t_j) c✝) a b = (1 + stdBasisMatrix t_i t_j  …
                                                          -- ⊢ (1 + stdBasisMatrix (↑e t_i) (↑e t_j) c✝) a b = (1 + stdBasisMatrix t_i t_j  …
    simp [ha, hb, hab, ← e.apply_eq_iff_eq_symm_apply, stdBasisMatrix]
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
#align matrix.transvection_struct.to_matrix_reindex_equiv Matrix.TransvectionStruct.toMatrix_reindexEquiv

theorem toMatrix_reindexEquiv_prod (e : n ≃ p) (L : List (TransvectionStruct n R)) :
    (L.map (toMatrix ∘ reindexEquiv e)).prod = reindexAlgEquiv R e (L.map toMatrix).prod := by
  induction' L with t L IH
  -- ⊢ List.prod (List.map (toMatrix ∘ reindexEquiv e) []) = ↑(reindexAlgEquiv R e) …
  · simp
    -- 🎉 no goals
  · simp only [toMatrix_reindexEquiv, IH, Function.comp_apply, List.prod_cons,
      reindexAlgEquiv_apply, List.map]
    exact (reindexAlgEquiv_mul _ _ _ _).symm
    -- 🎉 no goals
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
  -- porting note: `apply` didn't work anymore, because of the implicit arguments
  refine' Nat.decreasingInduction' _ hk _
  -- ⊢ ∀ (k_1 : ℕ), k_1 < r → k ≤ k_1 → (List.prod (List.drop (k_1 + 1) (listTransv …
  · intro n hn _ IH
    -- ⊢ (List.prod (List.drop n (listTransvecCol M)) * M) (inr ()) i = M (inr ()) i
    have hn' : n < (listTransvecCol M).length := by simpa [listTransvecCol] using hn
    -- ⊢ (List.prod (List.drop n (listTransvecCol M)) * M) (inr ()) i = M (inr ()) i
    -- porting note: after changing from `nthLe` to `get`, we need to provide all arguments
    rw [← @List.cons_get_drop_succ _ _ ⟨n, hn'⟩]
    -- ⊢ (List.prod (List.get (listTransvecCol M) { val := n, isLt := hn' } :: List.d …
    simpa [listTransvecCol, Matrix.mul_assoc]
    -- 🎉 no goals
  · simp only [listTransvecCol, List.length_ofFn, le_refl, List.drop_eq_nil_of_le, List.prod_nil,
      Matrix.one_mul]
#align matrix.pivot.list_transvec_col_mul_last_row_drop Matrix.Pivot.listTransvecCol_mul_last_row_drop

/-- Multiplying by all the matrices in `listTransvecCol M` does not change the last row. -/
theorem listTransvecCol_mul_last_row (i : Sum (Fin r) Unit) :
    ((listTransvecCol M).prod * M) (inr unit) i = M (inr unit) i := by
  simpa using listTransvecCol_mul_last_row_drop M i (zero_le _)
  -- 🎉 no goals
#align matrix.pivot.list_transvec_col_mul_last_row Matrix.Pivot.listTransvecCol_mul_last_row

/-- Multiplying by all the matrices in `listTransvecCol M` kills all the coefficients in the
last column but the last one. -/
theorem listTransvecCol_mul_last_col (hM : M (inr unit) (inr unit) ≠ 0) (i : Fin r) :
    ((listTransvecCol M).prod * M) (inl i) (inr unit) = 0 := by
  suffices H :
    ∀ k : ℕ,
      k ≤ r →
        (((listTransvecCol M).drop k).prod * M) (inl i) (inr unit) =
          if k ≤ i then 0 else M (inl i) (inr unit)
  · simpa only [List.drop, _root_.zero_le, ite_true] using H 0 (zero_le _)
    -- 🎉 no goals
  intro k hk
  -- ⊢ (List.prod (List.drop k (listTransvecCol M)) * M) (inl i) (inr ()) = if k ≤  …
  -- porting note: `apply` didn't work anymore, because of the implicit arguments
  refine' Nat.decreasingInduction' _ hk _
  -- ⊢ ∀ (k_1 : ℕ), k_1 < r → k ≤ k_1 → ((List.prod (List.drop (k_1 + 1) (listTrans …
  · intro n hn hk IH
    -- ⊢ (List.prod (List.drop n (listTransvecCol M)) * M) (inl i) (inr ()) = if n ≤  …
    have hn' : n < (listTransvecCol M).length := by simpa [listTransvecCol] using hn
    -- ⊢ (List.prod (List.drop n (listTransvecCol M)) * M) (inl i) (inr ()) = if n ≤  …
    let n' : Fin r := ⟨n, hn⟩
    -- ⊢ (List.prod (List.drop n (listTransvecCol M)) * M) (inl i) (inr ()) = if n ≤  …
    -- porting note: after changing from `nthLe` to `get`, we need to provide all arguments
    rw [← @List.cons_get_drop_succ _ _ ⟨n, hn'⟩]
    -- ⊢ (List.prod (List.get (listTransvecCol M) { val := n, isLt := hn' } :: List.d …
    have A :
      (listTransvecCol M).get ⟨n, hn'⟩ =
        transvection (inl n') (inr unit) (-M (inl n') (inr unit) / M (inr unit) (inr unit)) :=
      by simp [listTransvecCol]
    simp only [Matrix.mul_assoc, A, List.prod_cons]
    -- ⊢ (transvection (inl { val := n, isLt := hn }) (inr ()) (-M (inl { val := n, i …
    by_cases h : n' = i
    -- ⊢ (transvection (inl { val := n, isLt := hn }) (inr ()) (-M (inl { val := n, i …
    · have hni : n = i := by
        cases i
        simp only [Fin.mk_eq_mk] at h
        simp [h]
      simp only [h, transvection_mul_apply_same, IH, ← hni, add_le_iff_nonpos_right,
          listTransvecCol_mul_last_row_drop _ _ hn]
      field_simp [hM]
      -- 🎉 no goals
    · have hni : n ≠ i := by
        rintro rfl
        cases i
        simp at h
      simp only [ne_eq, inl.injEq, Ne.symm h, not_false_eq_true, transvection_mul_apply_of_ne]
      -- ⊢ (List.prod (List.drop (n + 1) (listTransvecCol M)) * M) (inl i) (inr ()) = i …
      rw [IH]
      -- ⊢ (if n + 1 ≤ ↑i then 0 else M (inl i) (inr ())) = if n ≤ ↑i then 0 else M (in …
      rcases le_or_lt (n + 1) i with (hi | hi)
      -- ⊢ (if n + 1 ≤ ↑i then 0 else M (inl i) (inr ())) = if n ≤ ↑i then 0 else M (in …
      · simp only [hi, n.le_succ.trans hi, if_true]
        -- 🎉 no goals
      · rw [if_neg, if_neg]
        -- ⊢ ¬n ≤ ↑i
        · simpa only [hni.symm, not_le, or_false_iff] using Nat.lt_succ_iff_lt_or_eq.1 hi
          -- 🎉 no goals
        · simpa only [not_le] using hi
          -- 🎉 no goals
  · simp only [listTransvecCol, List.length_ofFn, le_refl, List.drop_eq_nil_of_le, List.prod_nil,
      Matrix.one_mul]
    rw [if_neg]
    -- ⊢ ¬r ≤ ↑i
    simpa only [not_le] using i.2
    -- 🎉 no goals
#align matrix.pivot.list_transvec_col_mul_last_col Matrix.Pivot.listTransvecCol_mul_last_col

/-- Multiplying by some of the matrices in `listTransvecRow M` does not change the last column. -/
theorem mul_listTransvecRow_last_col_take (i : Sum (Fin r) Unit) {k : ℕ} (hk : k ≤ r) :
    (M * ((listTransvecRow M).take k).prod) i (inr unit) = M i (inr unit) := by
  induction' k with k IH
  -- ⊢ (M * List.prod (List.take Nat.zero (listTransvecRow M))) i (inr ()) = M i (i …
  · simp only [Matrix.mul_one, List.take_zero, List.prod_nil, List.take, Matrix.mul_one]
    -- 🎉 no goals
  · have hkr : k < r := hk
    -- ⊢ (M * List.prod (List.take (Nat.succ k) (listTransvecRow M))) i (inr ()) = M  …
    let k' : Fin r := ⟨k, hkr⟩
    -- ⊢ (M * List.prod (List.take (Nat.succ k) (listTransvecRow M))) i (inr ()) = M  …
    have :
      (listTransvecRow M).get? k =
        ↑(transvection (inr Unit.unit) (inl k')
            (-M (inr Unit.unit) (inl k') / M (inr Unit.unit) (inr Unit.unit))) := by
      simp only [listTransvecRow, List.ofFnNthVal, hkr, dif_pos, List.get?_ofFn]
    simp only [List.take_succ, ← Matrix.mul_assoc, this, List.prod_append, Matrix.mul_one,
      List.prod_cons, List.prod_nil, Option.to_list_some]
    rw [mul_transvection_apply_of_ne, IH hkr.le]
    -- ⊢ inr () ≠ inl { val := k, isLt := hkr }
    simp only [Ne.def, not_false_iff]
    -- 🎉 no goals
#align matrix.pivot.mul_list_transvec_row_last_col_take Matrix.Pivot.mul_listTransvecRow_last_col_take

/-- Multiplying by all the matrices in `listTransvecRow M` does not change the last column. -/
theorem mul_listTransvecRow_last_col (i : Sum (Fin r) Unit) :
    (M * (listTransvecRow M).prod) i (inr unit) = M i (inr unit) := by
  have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
  -- ⊢ (M * List.prod (listTransvecRow M)) i (inr ()) = M i (inr ())
  rw [← List.take_length (listTransvecRow M), A]
  -- ⊢ (M * List.prod (List.take r (listTransvecRow M))) i (inr ()) = M i (inr ())
  simpa using mul_listTransvecRow_last_col_take M i le_rfl
  -- 🎉 no goals
#align matrix.pivot.mul_list_transvec_row_last_col Matrix.Pivot.mul_listTransvecRow_last_col

/-- Multiplying by all the matrices in `listTransvecRow M` kills all the coefficients in the
last row but the last one. -/
theorem mul_listTransvecRow_last_row (hM : M (inr unit) (inr unit) ≠ 0) (i : Fin r) :
    (M * (listTransvecRow M).prod) (inr unit) (inl i) = 0 := by
  suffices H :
    ∀ k : ℕ,
      k ≤ r →
        (M * ((listTransvecRow M).take k).prod) (inr unit) (inl i) =
          if k ≤ i then M (inr unit) (inl i) else 0
  · have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
    -- ⊢ (M * List.prod (listTransvecRow M)) (inr ()) (inl i) = 0
    rw [← List.take_length (listTransvecRow M), A]
    -- ⊢ (M * List.prod (List.take r (listTransvecRow M))) (inr ()) (inl i) = 0
    have : ¬r ≤ i := by simp
    -- ⊢ (M * List.prod (List.take r (listTransvecRow M))) (inr ()) (inl i) = 0
    simpa only [this, ite_eq_right_iff] using H r le_rfl
    -- 🎉 no goals
  intro k hk
  -- ⊢ (M * List.prod (List.take k (listTransvecRow M))) (inr ()) (inl i) = if k ≤  …
  induction' k with n IH
  -- ⊢ (M * List.prod (List.take Nat.zero (listTransvecRow M))) (inr ()) (inl i) =  …
  · simp only [if_true, Matrix.mul_one, List.take_zero, zero_le', List.prod_nil, Nat.zero_eq]
    -- 🎉 no goals
  · have hnr : n < r := hk
    -- ⊢ (M * List.prod (List.take (Nat.succ n) (listTransvecRow M))) (inr ()) (inl i …
    let n' : Fin r := ⟨n, hnr⟩
    -- ⊢ (M * List.prod (List.take (Nat.succ n) (listTransvecRow M))) (inr ()) (inl i …
    have A :
      (listTransvecRow M).get? n =
        ↑(transvection (inr unit) (inl n')
        (-M (inr unit) (inl n') / M (inr unit) (inr unit))) := by
      simp only [listTransvecRow, List.ofFnNthVal, hnr, dif_pos, List.get?_ofFn]
    simp only [List.take_succ, A, ← Matrix.mul_assoc, List.prod_append, Matrix.mul_one,
      List.prod_cons, List.prod_nil, Option.to_list_some]
    by_cases h : n' = i
    -- ⊢ (M * List.prod (List.take n (listTransvecRow M)) * transvection (inr ()) (in …
    · have hni : n = i := by
        cases i
        simp only [Fin.mk_eq_mk] at h
        simp only [h]
      have : ¬n.succ ≤ i := by simp only [← hni, n.lt_succ_self, not_le]
      -- ⊢ (M * List.prod (List.take n (listTransvecRow M)) * transvection (inr ()) (in …
      simp only [h, mul_transvection_apply_same, List.take, if_false,
        mul_listTransvecRow_last_col_take _ _ hnr.le, hni.le, this, if_true, IH hnr.le]
      field_simp [hM]
      -- 🎉 no goals
    · have hni : n ≠ i := by
        rintro rfl
        cases i
        tauto
      simp only [IH hnr.le, Ne.def, mul_transvection_apply_of_ne, Ne.symm h, inl.injEq]
      -- ⊢ (if n ≤ ↑i then M (inr ()) (inl i) else 0) = if Nat.succ n ≤ ↑i then M (inr  …
      rcases le_or_lt (n + 1) i with (hi | hi)
      -- ⊢ (if n ≤ ↑i then M (inr ()) (inl i) else 0) = if Nat.succ n ≤ ↑i then M (inr  …
      · simp [hi, n.le_succ.trans hi, if_true]
        -- 🎉 no goals
      · rw [if_neg, if_neg]
        -- ⊢ ¬Nat.succ n ≤ ↑i
        · simpa only [not_le] using hi
          -- 🎉 no goals
        · simpa only [hni.symm, not_le, or_false_iff] using Nat.lt_succ_iff_lt_or_eq.1 hi
          -- 🎉 no goals
#align matrix.pivot.mul_list_transvec_row_last_row Matrix.Pivot.mul_listTransvecRow_last_row

/-- Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecRow M` kills
all the coefficients in the last row but the last one. -/
theorem listTransvecCol_mul_mul_listTransvecRow_last_col (hM : M (inr unit) (inr unit) ≠ 0)
    (i : Fin r) :
    ((listTransvecCol M).prod * M * (listTransvecRow M).prod) (inr unit) (inl i) = 0 := by
  have : listTransvecRow M = listTransvecRow ((listTransvecCol M).prod * M) := by
    simp [listTransvecRow, listTransvecCol_mul_last_row]
  rw [this]
  -- ⊢ (List.prod (listTransvecCol M) * M * List.prod (listTransvecRow (List.prod ( …
  apply mul_listTransvecRow_last_row
  -- ⊢ (List.prod (listTransvecCol M) * M) (inr ()) (inr ()) ≠ 0
  simpa [listTransvecCol_mul_last_row] using hM
  -- 🎉 no goals
#align matrix.pivot.list_transvec_col_mul_mul_list_transvec_row_last_col Matrix.Pivot.listTransvecCol_mul_mul_listTransvecRow_last_col

/-- Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecRow M` kills
all the coefficients in the last column but the last one. -/
theorem listTransvecCol_mul_mul_listTransvecRow_last_row (hM : M (inr unit) (inr unit) ≠ 0)
    (i : Fin r) :
    ((listTransvecCol M).prod * M * (listTransvecRow M).prod) (inl i) (inr unit) = 0 := by
  have : listTransvecCol M = listTransvecCol (M * (listTransvecRow M).prod) := by
    simp [listTransvecCol, mul_listTransvecRow_last_col]
  rw [this, Matrix.mul_assoc]
  -- ⊢ (List.prod (listTransvecCol (M * List.prod (listTransvecRow M))) * (M * List …
  apply listTransvecCol_mul_last_col
  -- ⊢ (M * List.prod (listTransvecRow M)) (inr ()) (inr ()) ≠ 0
  simpa [mul_listTransvecRow_last_col] using hM
  -- 🎉 no goals
#align matrix.pivot.list_transvec_col_mul_mul_list_transvec_row_last_row Matrix.Pivot.listTransvecCol_mul_mul_listTransvecRow_last_row

/-- Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecRow M` turns
the matrix in block-diagonal form. -/
theorem isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow
    (hM : M (inr unit) (inr unit) ≠ 0) :
    IsTwoBlockDiagonal ((listTransvecCol M).prod * M * (listTransvecRow M).prod) := by
  constructor
  -- ⊢ toBlocks₁₂ (List.prod (listTransvecCol M) * M * List.prod (listTransvecRow M …
  · ext i j
    -- ⊢ toBlocks₁₂ (List.prod (listTransvecCol M) * M * List.prod (listTransvecRow M …
    have : j = unit := by simp only [eq_iff_true_of_subsingleton]
    -- ⊢ toBlocks₁₂ (List.prod (listTransvecCol M) * M * List.prod (listTransvecRow M …
    simp [toBlocks₁₂, this, listTransvecCol_mul_mul_listTransvecRow_last_row M hM]
    -- 🎉 no goals
  · ext i j
    -- ⊢ toBlocks₂₁ (List.prod (listTransvecCol M) * M * List.prod (listTransvecRow M …
    have : i = unit := by simp only [eq_iff_true_of_subsingleton]
    -- ⊢ toBlocks₂₁ (List.prod (listTransvecCol M) * M * List.prod (listTransvecRow M …
    simp [toBlocks₂₁, this, listTransvecCol_mul_mul_listTransvecRow_last_col M hM]
    -- 🎉 no goals
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
  refine' ⟨L, L', _⟩
  -- ⊢ IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod (List.ma …
  have A : L.map toMatrix = listTransvecCol M := by simp [listTransvecCol, (· ∘ ·)]
  -- ⊢ IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod (List.ma …
  have B : L'.map toMatrix = listTransvecRow M := by simp [listTransvecRow, (· ∘ ·)]
  -- ⊢ IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod (List.ma …
  rw [A, B]
  -- ⊢ IsTwoBlockDiagonal (List.prod (listTransvecCol M) * M * List.prod (listTrans …
  exact isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M hM
  -- 🎉 no goals
#align matrix.pivot.exists_is_two_block_diagonal_of_ne_zero Matrix.Pivot.exists_isTwoBlockDiagonal_of_ne_zero

/-- There exist two lists of `TransvectionStruct` such that multiplying by them on the left and
on the right makes a matrix block-diagonal. -/
theorem exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec
    (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃ L L' : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod) := by
  by_cases H : IsTwoBlockDiagonal M
  -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
  · refine' ⟨List.nil, List.nil, by simpa using H⟩
    -- 🎉 no goals
  -- we have already proved this when the last coefficient is nonzero
  by_cases hM : M (inr unit) (inr unit) ≠ 0
  -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
  · exact exists_isTwoBlockDiagonal_of_ne_zero M hM
    -- 🎉 no goals
  -- when the last coefficient is zero but there is a nonzero coefficient on the last row or the
  -- last column, we will first put this nonzero coefficient in last position, and then argue as
  -- above.
  push_neg at hM
  -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
  simp only [not_and_or, IsTwoBlockDiagonal, toBlocks₁₂, toBlocks₂₁, ← Matrix.ext_iff] at H
  -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
  have : ∃ i : Fin r, M (inl i) (inr unit) ≠ 0 ∨ M (inr unit) (inl i) ≠ 0 := by
    cases' H with H H
    · contrapose! H
      rintro i ⟨⟩
      exact (H i).1
    · contrapose! H
      rintro ⟨⟩ j
      exact (H j).2
  rcases this with ⟨i, h | h⟩
  -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
  · let M' := transvection (inr Unit.unit) (inl i) 1 * M
    -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
    have hM' : M' (inr unit) (inr unit) ≠ 0 := by simpa [hM]
    -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
    rcases exists_isTwoBlockDiagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩
    -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
    rw [Matrix.mul_assoc] at hLL'
    -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
    refine' ⟨L ++ [⟨inr unit, inl i, by simp, 1⟩], L', _⟩
    -- ⊢ IsTwoBlockDiagonal (List.prod (List.map toMatrix (L ++ [{ i := inr (), j :=  …
    simp only [List.map_append, List.prod_append, Matrix.mul_one, toMatrix_mk, List.prod_cons,
      List.prod_nil, List.map, Matrix.mul_assoc (L.map toMatrix).prod]
    exact hLL'
    -- 🎉 no goals
  · let M' := M * transvection (inl i) (inr unit) 1
    -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
    have hM' : M' (inr unit) (inr unit) ≠ 0 := by simpa [hM]
    -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
    rcases exists_isTwoBlockDiagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩
    -- ⊢ ∃ L L', IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod  …
    refine' ⟨L, ⟨inl i, inr unit, by simp, 1⟩::L', _⟩
    -- ⊢ IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * List.prod (List.ma …
    simp only [← Matrix.mul_assoc, toMatrix_mk, List.prod_cons, List.map]
    -- ⊢ IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * M * transvection (inl  …
    rw [Matrix.mul_assoc (L.map toMatrix).prod]
    -- ⊢ IsTwoBlockDiagonal (List.prod (List.map toMatrix L) * (M * transvection (inl …
    exact hLL'
    -- 🎉 no goals
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
  -- ⊢ ∃ L L' D, List.prod (List.map toMatrix L) * M * List.prod (List.map toMatrix …
  let M' := (L₁.map toMatrix).prod * M * (L₁'.map toMatrix).prod
  -- ⊢ ∃ L L' D, List.prod (List.map toMatrix L) * M * List.prod (List.map toMatrix …
  let M'' := toBlocks₁₁ M'
  -- ⊢ ∃ L L' D, List.prod (List.map toMatrix L) * M * List.prod (List.map toMatrix …
  rcases IH M'' with ⟨L₀, L₀', D₀, h₀⟩
  -- ⊢ ∃ L L' D, List.prod (List.map toMatrix L) * M * List.prod (List.map toMatrix …
  set c := M' (inr unit) (inr unit)
  -- ⊢ ∃ L L' D, List.prod (List.map toMatrix L) * M * List.prod (List.map toMatrix …
  refine'
    ⟨L₀.map (sumInl Unit) ++ L₁, L₁' ++ L₀'.map (sumInl Unit),
      Sum.elim D₀ fun _ => M' (inr unit) (inr unit), _⟩
  suffices (L₀.map (toMatrix ∘ sumInl Unit)).prod * M' * (L₀'.map (toMatrix ∘ sumInl Unit)).prod =
      diagonal (Sum.elim D₀ fun _ => c) by
    simpa [Matrix.mul_assoc]
  have : M' = fromBlocks M'' 0 0 (diagonal fun _ => c) := by
    -- porting note: simplified proof, because `congr` didn't work anymore
    rw [← fromBlocks_toBlocks M', hM.1, hM.2]
    rfl
  rw [this]
  -- ⊢ List.prod (List.map (toMatrix ∘ sumInl Unit) L₀) * fromBlocks M'' 0 0 (diago …
  simp [h₀]
  -- 🎉 no goals
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
  -- ⊢ ∃ L L' D, List.prod (List.map toMatrix L) * M * List.prod (List.map toMatrix …
  refine' ⟨L₀.map (reindexEquiv e.symm), L₀'.map (reindexEquiv e.symm), D₀ ∘ e, _⟩
  -- ⊢ List.prod (List.map toMatrix (List.map (reindexEquiv e.symm) L₀)) * M * List …
  have : M = reindexAlgEquiv 𝕜 e.symm (reindexAlgEquiv 𝕜 e M) := by
    simp only [Equiv.symm_symm, submatrix_submatrix, reindex_apply, submatrix_id_id,
      Equiv.symm_comp_self, reindexAlgEquiv_apply]
  rw [this]
  -- ⊢ List.prod (List.map toMatrix (List.map (reindexEquiv e.symm) L₀)) * ↑(reinde …
  simp only [toMatrix_reindexEquiv_prod, List.map_map, reindexAlgEquiv_apply]
  -- ⊢ ↑(reindex e.symm e.symm) (List.prod (List.map toMatrix L₀)) * ↑(reindex e.sy …
  simp only [← reindexAlgEquiv_apply, ← reindexAlgEquiv_mul, h₀]
  -- ⊢ ↑(reindexAlgEquiv 𝕜 e.symm) (diagonal D₀) = diagonal (D₀ ∘ ↑e)
  simp only [Equiv.symm_symm, reindex_apply, submatrix_diagonal_equiv, reindexAlgEquiv_apply]
  -- 🎉 no goals
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
  -- ⊢ ∃ L L' D, List.prod (List.map toMatrix L) * M * List.prod (List.map toMatrix …
  · refine' ⟨List.nil, List.nil, fun _ => 1, _⟩
    -- ⊢ List.prod (List.map toMatrix []) * M * List.prod (List.map toMatrix []) = di …
    ext i j
    -- ⊢ (List.prod (List.map toMatrix []) * M * List.prod (List.map toMatrix [])) i  …
    rw [Fintype.card_eq_zero_iff] at hn
    -- ⊢ (List.prod (List.map toMatrix []) * M * List.prod (List.map toMatrix [])) i  …
    exact hn.elim' i
    -- 🎉 no goals
  · have e : n ≃ Sum (Fin r) Unit := by
      refine' Fintype.equivOfCardEq _
      rw [hn]
      rw [@Fintype.card_sum (Fin r) Unit _ _]
      simp
    apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
    -- ⊢ ∃ L L' D, List.prod (List.map toMatrix L) * ↑(reindexAlgEquiv 𝕜 e) M * List. …
    apply
      exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction fun N =>
        IH (Fin r) N (by simp)
#align matrix.pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux

/-- Any matrix can be reduced to diagonal form by elementary operations. -/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  have e : n ≃ Fin (Fintype.card n) := Fintype.equivOfCardEq (by simp)
  -- ⊢ ∃ L L' D, List.prod (List.map toMatrix L) * M * List.prod (List.map toMatrix …
  apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
  -- ⊢ ∃ L L' D, List.prod (List.map toMatrix L) * ↑(reindexAlgEquiv 𝕜 e) M * List. …
  apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux
  -- 🎉 no goals
#align matrix.pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal

/-- Any matrix can be written as the product of transvections, a diagonal matrix, and
transvections.-/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      M = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod := by
  rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  -- ⊢ ∃ L L' D, M = List.prod (List.map toMatrix L) * diagonal D * List.prod (List …
  refine' ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, _⟩
  -- ⊢ M = List.prod (List.map toMatrix (List.map TransvectionStruct.inv (List.reve …
  suffices
    M =
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod * M *
        ((L'.map toMatrix).prod * (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod)
    by simpa [← h, Matrix.mul_assoc]
  rw [reverse_inv_prod_mul_prod, prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one]
  -- 🎉 no goals
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
  -- ⊢ P M
  have PD : P (diagonal D) := hdiag D (by simp [h])
  -- ⊢ P M
  suffices H :
    ∀ (L₁ L₂ : List (TransvectionStruct n 𝕜)) (E : Matrix n n 𝕜),
      P E → P ((L₁.map toMatrix).prod * E * (L₂.map toMatrix).prod)
  · rw [h]
    -- ⊢ P (List.prod (List.map toMatrix L) * diagonal D * List.prod (List.map toMatr …
    apply H L L'
    -- ⊢ P (diagonal D)
    exact PD
    -- 🎉 no goals
  intro L₁ L₂ E PE
  -- ⊢ P (List.prod (List.map toMatrix L₁) * E * List.prod (List.map toMatrix L₂))
  induction' L₁ with t L₁ IH
  -- ⊢ P (List.prod (List.map toMatrix []) * E * List.prod (List.map toMatrix L₂))
  · simp only [Matrix.one_mul, List.prod_nil, List.map]
    -- ⊢ P (E * List.prod (List.map toMatrix L₂))
    induction' L₂ with t L₂ IH generalizing E
    -- ⊢ P (E * List.prod (List.map toMatrix []))
    · simpa
      -- 🎉 no goals
    · simp only [← Matrix.mul_assoc, List.prod_cons, List.map]
      -- ⊢ P (E * toMatrix t * List.prod (List.map toMatrix L₂))
      apply IH
      -- ⊢ P (E * toMatrix t)
      exact hmul _ _ PE (htransvec _)
      -- 🎉 no goals
  · simp only [Matrix.mul_assoc, List.prod_cons, List.map] at IH ⊢
    -- ⊢ P (toMatrix t * (List.prod (List.map toMatrix L₁) * (E * List.prod (List.map …
    exact hmul _ _ (htransvec _) IH
    -- 🎉 no goals
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
  -- ⊢ P M
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
  -- 🎉 no goals
#align matrix.diagonal_transvection_induction_of_det_ne_zero Matrix.diagonal_transvection_induction_of_det_ne_zero

end Matrix
