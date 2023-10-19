/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Wen Yang
-/
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases

#align_import linear_algebra.matrix.block from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!
# Block matrices and their determinant

This file defines a predicate `Matrix.BlockTriangular` saying a matrix
is block triangular, and proves the value of the determinant for various
matrices built out of blocks.

## Main definitions

 * `Matrix.BlockTriangular` expresses that an `o` by `o` matrix is block triangular,
   if the rows and columns are ordered according to some order `b : o → α`

## Main results
  * `Matrix.det_of_blockTriangular`: the determinant of a block triangular matrix
    is equal to the product of the determinants of all the blocks
  * `Matrix.det_of_upperTriangular` and `Matrix.det_of_lowerTriangular`: the determinant of
    a triangular matrix is the product of the entries along the diagonal

## Tags

matrix, diagonal, det, block triangular

-/


open Finset Function OrderDual

open BigOperators Matrix

universe v

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} [CommRing R] {M N : Matrix m m R} {b : m → α}

namespace Matrix

section LT

variable [LT α]

/-- Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then
`BlockTriangular M n b` says the matrix is block triangular. -/
def BlockTriangular (M : Matrix m m R) (b : m → α) : Prop :=
  ∀ ⦃i j⦄, b j < b i → M i j = 0
#align matrix.block_triangular Matrix.BlockTriangular

@[simp]
protected theorem BlockTriangular.submatrix {f : n → m} (h : M.BlockTriangular b) :
    (M.submatrix f f).BlockTriangular (b ∘ f) := fun _ _ hij => h hij
#align matrix.block_triangular.submatrix Matrix.BlockTriangular.submatrix

theorem blockTriangular_reindex_iff {b : n → α} {e : m ≃ n} :
    (reindex e e M).BlockTriangular b ↔ M.BlockTriangular (b ∘ e) := by
  refine' ⟨fun h => _, fun h => _⟩
  · convert h.submatrix
    simp only [reindex_apply, submatrix_submatrix, submatrix_id_id, Equiv.symm_comp_self]
  · convert h.submatrix
    simp only [comp.assoc b e e.symm, Equiv.self_comp_symm, comp.right_id]
#align matrix.block_triangular_reindex_iff Matrix.blockTriangular_reindex_iff

protected theorem BlockTriangular.transpose :
    M.BlockTriangular b → Mᵀ.BlockTriangular (toDual ∘ b) :=
  swap
#align matrix.block_triangular.transpose Matrix.BlockTriangular.transpose

@[simp]
protected theorem blockTriangular_transpose_iff {b : m → αᵒᵈ} :
    Mᵀ.BlockTriangular b ↔ M.BlockTriangular (ofDual ∘ b) :=
  forall_swap
#align matrix.block_triangular_transpose_iff Matrix.blockTriangular_transpose_iff

@[simp]
theorem blockTriangular_zero : BlockTriangular (0 : Matrix m m R) b := fun _ _ _ => rfl
#align matrix.block_triangular_zero Matrix.blockTriangular_zero

protected theorem BlockTriangular.neg (hM : BlockTriangular M b) : BlockTriangular (-M) b :=
  fun _ _ h => neg_eq_zero.2 <| hM h
#align matrix.block_triangular.neg Matrix.BlockTriangular.neg

theorem BlockTriangular.add (hM : BlockTriangular M b) (hN : BlockTriangular N b) :
    BlockTriangular (M + N) b := fun i j h => by simp_rw [Matrix.add_apply, hM h, hN h, zero_add]
#align matrix.block_triangular.add Matrix.BlockTriangular.add

theorem BlockTriangular.sub (hM : BlockTriangular M b) (hN : BlockTriangular N b) :
    BlockTriangular (M - N) b := fun i j h => by simp_rw [Matrix.sub_apply, hM h, hN h, sub_zero]
#align matrix.block_triangular.sub Matrix.BlockTriangular.sub

end LT

section Preorder

variable [Preorder α]

theorem blockTriangular_diagonal [DecidableEq m] (d : m → R) : BlockTriangular (diagonal d) b :=
  fun _ _ h => diagonal_apply_ne' d fun h' => ne_of_lt h (congr_arg _ h')
#align matrix.block_triangular_diagonal Matrix.blockTriangular_diagonal

theorem blockTriangular_blockDiagonal' [DecidableEq α] (d : ∀ i : α, Matrix (m' i) (m' i) R) :
    BlockTriangular (blockDiagonal' d) Sigma.fst := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  apply blockDiagonal'_apply_ne d i' j' fun h' => ne_of_lt h h'.symm
#align matrix.block_triangular_block_diagonal' Matrix.blockTriangular_blockDiagonal'

theorem blockTriangular_blockDiagonal [DecidableEq α] (d : α → Matrix m m R) :
    BlockTriangular (blockDiagonal d) Prod.snd := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  rw [blockDiagonal'_eq_blockDiagonal, blockTriangular_blockDiagonal']
  exact h
#align matrix.block_triangular_block_diagonal Matrix.blockTriangular_blockDiagonal

variable [DecidableEq m]

theorem blockTriangular_one : BlockTriangular (1 : Matrix m m R) b :=
  blockTriangular_diagonal _

theorem blockTriangular_stdBasisMatrix {i j : m} (hij : b i ≤ b j) (c : R) :
    BlockTriangular (stdBasisMatrix i j c) b := by
  intro r s hrs
  apply StdBasisMatrix.apply_of_ne
  rintro ⟨rfl, rfl⟩
  exact (hij.trans_lt hrs).false

theorem blockTriangular_stdBasisMatrix' {i j : m} (hij : b j ≤ b i) (c : R) :
    BlockTriangular (stdBasisMatrix i j c) (toDual ∘ b) :=
  blockTriangular_stdBasisMatrix (by exact toDual_le_toDual.mpr hij) _

theorem blockTriangular_transvection {i j : m} (hij : b i ≤ b j) (c : R) :
    BlockTriangular (transvection i j c) b :=
  blockTriangular_one.add (blockTriangular_stdBasisMatrix hij c)

theorem blockTriangular_transvection' {i j : m} (hij : b j ≤ b i) (c : R) :
    BlockTriangular (transvection i j c) (OrderDual.toDual ∘ b) :=
  blockTriangular_one.add (blockTriangular_stdBasisMatrix' hij c)

end Preorder

section LinearOrder

variable [LinearOrder α]

theorem BlockTriangular.mul [Fintype m] {M N : Matrix m m R} (hM : BlockTriangular M b)
    (hN : BlockTriangular N b) : BlockTriangular (M * N) b := by
  intro i j hij
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : b k < b i
  · simp_rw [hM hki, zero_mul]
  · simp_rw [hN (lt_of_lt_of_le hij (le_of_not_lt hki)), mul_zero]
#align matrix.block_triangular.mul Matrix.BlockTriangular.mul

end LinearOrder

theorem upper_two_blockTriangular [Preorder α] (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) {a b : α} (hab : a < b) :
    BlockTriangular (fromBlocks A B 0 D) (Sum.elim (fun _ => a) fun _ => b) := by
  rintro (c | c) (d | d) hcd <;> first | simp [hab.not_lt] at hcd ⊢
#align matrix.upper_two_block_triangular Matrix.upper_two_blockTriangular

/-! ### Determinant -/


variable [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem equiv_block_det (M : Matrix m m R) {p q : m → Prop} [DecidablePred p] [DecidablePred q]
    (e : ∀ x, q x ↔ p x) : (toSquareBlockProp M p).det = (toSquareBlockProp M q).det := by
  convert Matrix.det_reindex_self (Equiv.subtypeEquivRight e) (toSquareBlockProp M q)
#align matrix.equiv_block_det Matrix.equiv_block_det

@[simp]
theorem det_toSquareBlock_id (M : Matrix m m R) (i : m) : (M.toSquareBlock id i).det = M i i :=
  letI : Unique { a // id a = i } := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  (det_unique _).trans rfl
#align matrix.det_to_square_block_id Matrix.det_toSquareBlock_id

theorem det_toBlock (M : Matrix m m R) (p : m → Prop) [DecidablePred p] :
    M.det =
      (fromBlocks (toBlock M p p) (toBlock M p fun j => ¬p j) (toBlock M (fun j => ¬p j) p) <|
          toBlock M (fun j => ¬p j) fun j => ¬p j).det := by
  rw [← Matrix.det_reindex_self (Equiv.sumCompl p).symm M]
  rw [det_apply', det_apply']
  congr; ext σ; congr; ext x
  generalize hy : σ x = y
  cases x <;> cases y <;>
    simp only [Matrix.reindex_apply, toBlock_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inr,
      Equiv.sumCompl_apply_inl, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.submatrix_apply]
#align matrix.det_to_block Matrix.det_toBlock

theorem twoBlockTriangular_det (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
    (h : ∀ i, ¬p i → ∀ j, p j → M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [det_toBlock M p]
  convert det_fromBlocks_zero₂₁ (toBlock M p p) (toBlock M p fun j => ¬p j)
      (toBlock M (fun j => ¬p j) fun j => ¬p j)
  ext i j
  exact h (↑i) i.2 (↑j) j.2
#align matrix.two_block_triangular_det Matrix.twoBlockTriangular_det

theorem twoBlockTriangular_det' (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
    (h : ∀ i, p i → ∀ j, ¬p j → M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [M.twoBlockTriangular_det fun i => ¬p i, mul_comm]
  congr 1
  exact equiv_block_det _ fun _ => not_not.symm
  simpa only [Classical.not_not] using h
#align matrix.two_block_triangular_det' Matrix.twoBlockTriangular_det'

protected theorem BlockTriangular.det [DecidableEq α] [LinearOrder α] (hM : BlockTriangular M b) :
    M.det = ∏ a in univ.image b, (M.toSquareBlock b a).det := by
  clear N
  induction' hs : univ.image b using Finset.strongInduction with s ih generalizing m
  subst hs
  cases isEmpty_or_nonempty m
  · simp
  let k := (univ.image b).max' (univ_nonempty.image _)
  rw [twoBlockTriangular_det' M fun i => b i = k]
  · have : univ.image b = insert k ((univ.image b).erase k) := by
      rw [insert_erase]
      apply max'_mem
    rw [this, prod_insert (not_mem_erase _ _)]
    refine' congr_arg _ _
    let b' := fun i : { a // b a ≠ k } => b ↑i
    have h' : BlockTriangular (M.toSquareBlockProp fun i => b i ≠ k) b' := hM.submatrix
    have hb' : image b' univ = (image b univ).erase k := by
      convert image_subtype_ne_univ_eq_image_erase k b
    rw [ih _ (erase_ssubset <| max'_mem _ _) h' hb']
    refine' Finset.prod_congr rfl fun l hl => _
    let he : { a // b' a = l } ≃ { a // b a = l } :=
      haveI hc : ∀ i, b i = l → b i ≠ k := fun i hi => ne_of_eq_of_ne hi (ne_of_mem_erase hl)
      Equiv.subtypeSubtypeEquivSubtype @(hc)
    simp only [toSquareBlock_def]
    erw [← Matrix.det_reindex_self he.symm fun i j : { a // b a = l } => M ↑i ↑j]
    rfl
  · intro i hi j hj
    apply hM
    rw [hi]
    apply lt_of_le_of_ne _ hj
    exact Finset.le_max' (univ.image b) _ (mem_image_of_mem _ (mem_univ _))
#align matrix.block_triangular.det Matrix.BlockTriangular.det

theorem BlockTriangular.det_fintype [DecidableEq α] [Fintype α] [LinearOrder α]
    (h : BlockTriangular M b) : M.det = ∏ k : α, (M.toSquareBlock b k).det := by
  refine' h.det.trans (prod_subset (subset_univ _) fun a _ ha => _)
  have : IsEmpty { i // b i = a } := ⟨fun i => ha <| mem_image.2 ⟨i, mem_univ _, i.2⟩⟩
  exact det_isEmpty
#align matrix.block_triangular.det_fintype Matrix.BlockTriangular.det_fintype

theorem det_of_upperTriangular [LinearOrder m] (h : M.BlockTriangular id) :
    M.det = ∏ i : m, M i i := by
  haveI : DecidableEq R := Classical.decEq _
  simp_rw [h.det, image_id, det_toSquareBlock_id]
#align matrix.det_of_upper_triangular Matrix.det_of_upperTriangular

theorem det_of_lowerTriangular [LinearOrder m] (M : Matrix m m R) (h : M.BlockTriangular toDual) :
    M.det = ∏ i : m, M i i := by
  rw [← det_transpose]
  exact det_of_upperTriangular h.transpose
#align matrix.det_of_lower_triangular Matrix.det_of_lowerTriangular

/-! ### Invertible -/


theorem BlockTriangular.toBlock_inverse_mul_toBlock_eq_one [LinearOrder α] [Invertible M]
    (hM : BlockTriangular M b) (k : α) :
    ((M⁻¹.toBlock (fun i => b i < k) fun i => b i < k) *
        M.toBlock (fun i => b i < k) fun i => b i < k) =
      1 := by
  let p i := b i < k
  have h_sum :
    M⁻¹.toBlock p p * M.toBlock p p +
        (M⁻¹.toBlock p fun i => ¬p i) * M.toBlock (fun i => ¬p i) p =
      1 :=
    by rw [← toBlock_mul_eq_add, inv_mul_of_invertible M, toBlock_one_self]
  have h_zero : M.toBlock (fun i => ¬p i) p = 0 := by
    ext i j
    simpa using hM (lt_of_lt_of_le j.2 (le_of_not_lt i.2))
  simpa [h_zero] using h_sum
#align matrix.block_triangular.to_block_inverse_mul_to_block_eq_one Matrix.BlockTriangular.toBlock_inverse_mul_toBlock_eq_one

/-- The inverse of an upper-left subblock of a block-triangular matrix `M` is the upper-left
subblock of `M⁻¹`. -/
theorem BlockTriangular.inv_toBlock [LinearOrder α] [Invertible M] (hM : BlockTriangular M b)
    (k : α) :
    (M.toBlock (fun i => b i < k) fun i => b i < k)⁻¹ =
      M⁻¹.toBlock (fun i => b i < k) fun i => b i < k :=
  inv_eq_left_inv <| hM.toBlock_inverse_mul_toBlock_eq_one k
#align matrix.block_triangular.inv_to_block Matrix.BlockTriangular.inv_toBlock

/-- An upper-left subblock of an invertible block-triangular matrix is invertible. -/
def BlockTriangular.invertibleToBlock [LinearOrder α] [Invertible M] (hM : BlockTriangular M b)
    (k : α) : Invertible (M.toBlock (fun i => b i < k) fun i => b i < k) :=
  invertibleOfLeftInverse _ ((⅟ M).toBlock (fun i => b i < k) fun i => b i < k) <| by
    simpa only [invOf_eq_nonsing_inv] using hM.toBlock_inverse_mul_toBlock_eq_one k
#align matrix.block_triangular.invertible_to_block Matrix.BlockTriangular.invertibleToBlock

/-- A lower-left subblock of the inverse of a block-triangular matrix is zero. This is a first step
towards `BlockTriangular.inv_toBlock` below. -/
theorem toBlock_inverse_eq_zero [LinearOrder α] [Invertible M] (hM : BlockTriangular M b) (k : α) :
    (M⁻¹.toBlock (fun i => k ≤ b i) fun i => b i < k) = 0 := by
  let p i := b i < k
  let q i := ¬b i < k
  have h_sum : M⁻¹.toBlock q p * M.toBlock p p + M⁻¹.toBlock q q * M.toBlock q p = 0 := by
    rw [← toBlock_mul_eq_add, inv_mul_of_invertible M, toBlock_one_disjoint]
    rw [disjoint_iff_inf_le]
    exact fun i h => h.1 h.2
  have h_zero : M.toBlock q p = 0 := by
    ext i j
    simpa using hM (lt_of_lt_of_le j.2 <| le_of_not_lt i.2)
  have h_mul_eq_zero : M⁻¹.toBlock q p * M.toBlock p p = 0 := by simpa [h_zero] using h_sum
  haveI : Invertible (M.toBlock p p) := hM.invertibleToBlock k
  have : (fun i => k ≤ b i) = q := by
    ext
    exact not_lt.symm
  rw [this, ← Matrix.zero_mul (M.toBlock p p)⁻¹, ← h_mul_eq_zero,
    mul_inv_cancel_right_of_invertible]
#align matrix.to_block_inverse_eq_zero Matrix.toBlock_inverse_eq_zero

/-- The inverse of a block-triangular matrix is block-triangular. -/
theorem blockTriangular_inv_of_blockTriangular [LinearOrder α] [Invertible M]
    (hM : BlockTriangular M b) : BlockTriangular M⁻¹ b := by
  clear N
  induction' hs : univ.image b using Finset.strongInduction with s ih generalizing m
  subst hs
  intro i j hij
  haveI : Inhabited m := ⟨i⟩
  let k := (univ.image b).max' (univ_nonempty.image _)
  let b' := fun i : { a // b a < k } => b ↑i
  let A := M.toBlock (fun i => b i < k) fun j => b j < k
  obtain hbi | hi : b i = k ∨ _ := (le_max' _ (b i) <| mem_image_of_mem _ <| mem_univ _).eq_or_lt
  · have : M⁻¹.toBlock (fun i => k ≤ b i) (fun i => b i < k) ⟨i, hbi.ge⟩ ⟨j, hbi ▸ hij⟩ = 0 := by
      simp only [toBlock_inverse_eq_zero hM k, Matrix.zero_apply]
    simp [this.symm]
  haveI : Invertible A := hM.invertibleToBlock _
  have hA : A.BlockTriangular b' := hM.submatrix
  have hb' : image b' univ ⊂ image b univ := by
    convert image_subtype_univ_ssubset_image_univ k b _ (fun a => a < k) (lt_irrefl _)
    convert max'_mem (α := α) _ _
  have hij' : b' ⟨j, hij.trans hi⟩ < b' ⟨i, hi⟩ := by simp_rw [hij]
  simp [hM.inv_toBlock k, (ih (image b' univ) hb' hA rfl hij').symm]
#align matrix.block_triangular_inv_of_block_triangular Matrix.blockTriangular_inv_of_blockTriangular

end Matrix
