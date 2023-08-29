/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.LinearAlgebra.Matrix.Determinant
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
  * `Matrix.det_of_upperTriangular` and `matrix.det_of_lowerTriangular`: the determinant of
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
  -- ⊢ BlockTriangular M (b ∘ ↑e)
  · convert h.submatrix
    -- ⊢ M = submatrix (↑(reindex e e) M) ↑e ↑e
    simp only [reindex_apply, submatrix_submatrix, submatrix_id_id, Equiv.symm_comp_self]
    -- 🎉 no goals
  · convert h.submatrix
    -- ⊢ b = (b ∘ ↑e) ∘ fun i => ↑e.symm i
    simp only [comp.assoc b e e.symm, Equiv.self_comp_symm, comp.right_id]
    -- 🎉 no goals
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
                                                 -- 🎉 no goals
#align matrix.block_triangular.add Matrix.BlockTriangular.add

theorem BlockTriangular.sub (hM : BlockTriangular M b) (hN : BlockTriangular N b) :
    BlockTriangular (M - N) b := fun i j h => by simp_rw [Matrix.sub_apply, hM h, hN h, sub_zero]
                                                 -- 🎉 no goals
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
  -- ⊢ blockDiagonal' d { fst := i, snd := i' } { fst := j, snd := j' } = 0
  apply blockDiagonal'_apply_ne d i' j' fun h' => ne_of_lt h h'.symm
  -- 🎉 no goals
#align matrix.block_triangular_block_diagonal' Matrix.blockTriangular_blockDiagonal'

theorem blockTriangular_blockDiagonal [DecidableEq α] (d : α → Matrix m m R) :
    BlockTriangular (blockDiagonal d) Prod.snd := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  -- ⊢ blockDiagonal d (i, i') (j, j') = 0
  rw [blockDiagonal'_eq_blockDiagonal, blockTriangular_blockDiagonal']
  -- ⊢ { fst := j', snd := j }.fst < { fst := i', snd := i }.fst
  exact h
  -- 🎉 no goals
#align matrix.block_triangular_block_diagonal Matrix.blockTriangular_blockDiagonal

end Preorder

section LinearOrder

variable [LinearOrder α]

theorem BlockTriangular.mul [Fintype m] {M N : Matrix m m R} (hM : BlockTriangular M b)
    (hN : BlockTriangular N b) : BlockTriangular (M * N) b := by
  intro i j hij
  -- ⊢ (M * N) i j = 0
  apply Finset.sum_eq_zero
  -- ⊢ ∀ (x : m), x ∈ univ → (fun j => M i j) x * (fun j_1 => N j_1 j) x = 0
  intro k _
  -- ⊢ (fun j => M i j) k * (fun j_1 => N j_1 j) k = 0
  by_cases hki : b k < b i
  -- ⊢ (fun j => M i j) k * (fun j_1 => N j_1 j) k = 0
  · simp_rw [hM hki, zero_mul]
    -- 🎉 no goals
  · simp_rw [hN (lt_of_lt_of_le hij (le_of_not_lt hki)), mul_zero]
    -- 🎉 no goals
#align matrix.block_triangular.mul Matrix.BlockTriangular.mul

end LinearOrder

theorem upper_two_blockTriangular [Preorder α] (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) {a b : α} (hab : a < b) :
    BlockTriangular (fromBlocks A B 0 D) (Sum.elim (fun _ => a) fun _ => b) := by
  rintro (c | c) (d | d) hcd <;> first | simp [hab.not_lt] at hcd ⊢
                                 -- 🎉 no goals
                                 -- 🎉 no goals
                                 -- 🎉 no goals
                                 -- 🎉 no goals
#align matrix.upper_two_block_triangular Matrix.upper_two_blockTriangular

/-! ### Determinant -/


variable [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem equiv_block_det (M : Matrix m m R) {p q : m → Prop} [DecidablePred p] [DecidablePred q]
    (e : ∀ x, q x ↔ p x) : (toSquareBlockProp M p).det = (toSquareBlockProp M q).det := by
  convert Matrix.det_reindex_self (Equiv.subtypeEquivRight e) (toSquareBlockProp M q)
  -- 🎉 no goals
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
  -- ⊢ det (↑(reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm) M) = det (fr …
  rw [det_apply', det_apply']
  -- ⊢ ∑ σ : Equiv.Perm ({ a // p a } ⊕ { a // ¬p a }), ↑↑(↑Equiv.Perm.sign σ) * ∏  …
  congr; ext σ; congr; ext x
  -- ⊢ (fun σ => ↑↑(↑Equiv.Perm.sign σ) * ∏ i : { a // p a } ⊕ { a // ¬p a }, ↑(rei …
         -- ⊢ ↑↑(↑Equiv.Perm.sign σ) * ∏ i : { a // p a } ⊕ { a // ¬p a }, ↑(reindex (Equi …
                -- ⊢ (fun i => ↑(reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm) M (↑σ i …
                       -- ⊢ ↑(reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm) M (↑σ x) x = from …
  generalize hy : σ x = y
  -- ⊢ ↑(reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm) M y x = fromBlock …
  cases x <;> cases y <;>
  -- ⊢ ↑(reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm) M y (Sum.inl val✝ …
              -- ⊢ ↑(reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm) M (Sum.inl val✝)  …
              -- ⊢ ↑(reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm) M (Sum.inl val✝)  …
    simp only [Matrix.reindex_apply, toBlock_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inr,
      Equiv.sumCompl_apply_inl, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.submatrix_apply]
#align matrix.det_to_block Matrix.det_toBlock

theorem twoBlockTriangular_det (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
    (h : ∀ i, ¬p i → ∀ j, p j → M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [det_toBlock M p]
  -- ⊢ det (fromBlocks (toBlock M p p) (toBlock M p fun j => ¬p j) (toBlock M (fun  …
  convert det_fromBlocks_zero₂₁ (toBlock M p p) (toBlock M p fun j => ¬p j)
      (toBlock M (fun j => ¬p j) fun j => ¬p j)
  ext i j
  -- ⊢ toBlock M (fun j => ¬p j) p i j = OfNat.ofNat 0 i j
  exact h (↑i) i.2 (↑j) j.2
  -- 🎉 no goals
#align matrix.two_block_triangular_det Matrix.twoBlockTriangular_det

theorem twoBlockTriangular_det' (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
    (h : ∀ i, p i → ∀ j, ¬p j → M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [M.twoBlockTriangular_det fun i => ¬p i, mul_comm]
  -- ⊢ det (toSquareBlockProp M fun i => ¬¬p i) * det (toSquareBlockProp M fun i => …
  congr 1
  -- ⊢ det (toSquareBlockProp M fun i => ¬¬p i) = det (toSquareBlockProp M p)
  exact equiv_block_det _ fun _ => not_not.symm
  -- ⊢ ∀ (i : m), ¬¬p i → ∀ (j : m), ¬p j → M i j = 0
  simpa only [Classical.not_not] using h
  -- 🎉 no goals
#align matrix.two_block_triangular_det' Matrix.twoBlockTriangular_det'

protected theorem BlockTriangular.det [DecidableEq α] [LinearOrder α] (hM : BlockTriangular M b) :
    M.det = ∏ a in univ.image b, (M.toSquareBlock b a).det := by
  clear N
  -- ⊢ det M = ∏ a in image b univ, det (toSquareBlock M b a)
  induction' hs : univ.image b using Finset.strongInduction with s ih generalizing m
  -- ⊢ det M = ∏ a in s, det (toSquareBlock M b a)
  subst hs
  -- ⊢ det M = ∏ a in image b univ, det (toSquareBlock M b a)
  cases isEmpty_or_nonempty m
  -- ⊢ det M = ∏ a in image b univ, det (toSquareBlock M b a)
  · simp
    -- 🎉 no goals
  let k := (univ.image b).max' (univ_nonempty.image _)
  -- ⊢ det M = ∏ a in image b univ, det (toSquareBlock M b a)
  rw [twoBlockTriangular_det' M fun i => b i = k]
  -- ⊢ det (toSquareBlockProp M fun i => b i = k) * det (toSquareBlockProp M fun i  …
  · have : univ.image b = insert k ((univ.image b).erase k) := by
      rw [insert_erase]
      apply max'_mem
    rw [this, prod_insert (not_mem_erase _ _)]
    -- ⊢ det (toSquareBlockProp M fun i => b i = k) * det (toSquareBlockProp M fun i  …
    refine' congr_arg _ _
    -- ⊢ det (toSquareBlockProp M fun i => ¬b i = k) = ∏ x in erase (image b univ) k, …
    let b' := fun i : { a // b a ≠ k } => b ↑i
    -- ⊢ det (toSquareBlockProp M fun i => ¬b i = k) = ∏ x in erase (image b univ) k, …
    have h' : BlockTriangular (M.toSquareBlockProp fun i => b i ≠ k) b' := hM.submatrix
    -- ⊢ det (toSquareBlockProp M fun i => ¬b i = k) = ∏ x in erase (image b univ) k, …
    have hb' : image b' univ = (image b univ).erase k := by
      convert image_subtype_ne_univ_eq_image_erase k b
    rw [ih _ (erase_ssubset <| max'_mem _ _) h' hb']
    -- ⊢ ∏ a in erase (image b univ) (max' (image b univ) (_ : Finset.Nonempty (image …
    refine' Finset.prod_congr rfl fun l hl => _
    -- ⊢ det (toSquareBlock (toSquareBlockProp M fun i => b i ≠ k) b' l) = det (toSqu …
    let he : { a // b' a = l } ≃ { a // b a = l } :=
      haveI hc : ∀ i, b i = l → b i ≠ k := fun i hi => ne_of_eq_of_ne hi (ne_of_mem_erase hl)
      Equiv.subtypeSubtypeEquivSubtype @(hc)
    simp only [toSquareBlock_def]
    -- ⊢ det (↑of fun i j => toSquareBlockProp M (fun i => b i ≠ max' (image b univ)  …
    erw [← Matrix.det_reindex_self he.symm fun i j : { a // b a = l } => M ↑i ↑j]
    -- ⊢ det (↑of fun i j => toSquareBlockProp M (fun i => b i ≠ max' (image b univ)  …
    rfl
    -- 🎉 no goals
  · intro i hi j hj
    -- ⊢ M i j = 0
    apply hM
    -- ⊢ b j < b i
    rw [hi]
    -- ⊢ b j < k
    apply lt_of_le_of_ne _ hj
    -- ⊢ b j ≤ k
    exact Finset.le_max' (univ.image b) _ (mem_image_of_mem _ (mem_univ _))
    -- 🎉 no goals
#align matrix.block_triangular.det Matrix.BlockTriangular.det

theorem BlockTriangular.det_fintype [DecidableEq α] [Fintype α] [LinearOrder α]
    (h : BlockTriangular M b) : M.det = ∏ k : α, (M.toSquareBlock b k).det := by
  refine' h.det.trans (prod_subset (subset_univ _) fun a _ ha => _)
  -- ⊢ det (toSquareBlock M b a) = 1
  have : IsEmpty { i // b i = a } := ⟨fun i => ha <| mem_image.2 ⟨i, mem_univ _, i.2⟩⟩
  -- ⊢ det (toSquareBlock M b a) = 1
  exact det_isEmpty
  -- 🎉 no goals
#align matrix.block_triangular.det_fintype Matrix.BlockTriangular.det_fintype

theorem det_of_upperTriangular [LinearOrder m] (h : M.BlockTriangular id) :
    M.det = ∏ i : m, M i i := by
  haveI : DecidableEq R := Classical.decEq _
  -- ⊢ det M = ∏ i : m, M i i
  simp_rw [h.det, image_id, det_toSquareBlock_id]
  -- 🎉 no goals
#align matrix.det_of_upper_triangular Matrix.det_of_upperTriangular

theorem det_of_lowerTriangular [LinearOrder m] (M : Matrix m m R) (h : M.BlockTriangular toDual) :
    M.det = ∏ i : m, M i i := by
  rw [← det_transpose]
  -- ⊢ det Mᵀ = ∏ i : m, M i i
  exact det_of_upperTriangular h.transpose
  -- 🎉 no goals
#align matrix.det_of_lower_triangular Matrix.det_of_lowerTriangular

/-! ### Invertible -/


theorem BlockTriangular.toBlock_inverse_mul_toBlock_eq_one [LinearOrder α] [Invertible M]
    (hM : BlockTriangular M b) (k : α) :
    ((M⁻¹.toBlock (fun i => b i < k) fun i => b i < k) *
        M.toBlock (fun i => b i < k) fun i => b i < k) =
      1 := by
  let p i := b i < k
  -- ⊢ ((toBlock M⁻¹ (fun i => b i < k) fun i => b i < k) * toBlock M (fun i => b i …
  have h_sum :
    M⁻¹.toBlock p p * M.toBlock p p +
        (M⁻¹.toBlock p fun i => ¬p i) * M.toBlock (fun i => ¬p i) p =
      1 :=
    by rw [← toBlock_mul_eq_add, inv_mul_of_invertible M, toBlock_one_self]
  have h_zero : M.toBlock (fun i => ¬p i) p = 0 := by
    ext i j
    simpa using hM (lt_of_lt_of_le j.2 (le_of_not_lt i.2))
  simpa [h_zero] using h_sum
  -- 🎉 no goals
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
    -- 🎉 no goals
#align matrix.block_triangular.invertible_to_block Matrix.BlockTriangular.invertibleToBlock

/-- A lower-left subblock of the inverse of a block-triangular matrix is zero. This is a first step
towards `BlockTriangular.inv_toBlock` below. -/
theorem toBlock_inverse_eq_zero [LinearOrder α] [Invertible M] (hM : BlockTriangular M b) (k : α) :
    (M⁻¹.toBlock (fun i => k ≤ b i) fun i => b i < k) = 0 := by
  let p i := b i < k
  -- ⊢ (toBlock M⁻¹ (fun i => k ≤ b i) fun i => b i < k) = 0
  let q i := ¬b i < k
  -- ⊢ (toBlock M⁻¹ (fun i => k ≤ b i) fun i => b i < k) = 0
  have h_sum : M⁻¹.toBlock q p * M.toBlock p p + M⁻¹.toBlock q q * M.toBlock q p = 0 := by
    rw [← toBlock_mul_eq_add, inv_mul_of_invertible M, toBlock_one_disjoint]
    rw [disjoint_iff_inf_le]
    exact fun i h => h.1 h.2
  have h_zero : M.toBlock q p = 0 := by
    ext i j
    simpa using hM (lt_of_lt_of_le j.2 <| le_of_not_lt i.2)
  have h_mul_eq_zero : M⁻¹.toBlock q p * M.toBlock p p = 0 := by simpa [h_zero] using h_sum
  -- ⊢ (toBlock M⁻¹ (fun i => k ≤ b i) fun i => b i < k) = 0
  haveI : Invertible (M.toBlock p p) := hM.invertibleToBlock k
  -- ⊢ (toBlock M⁻¹ (fun i => k ≤ b i) fun i => b i < k) = 0
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
  -- ⊢ BlockTriangular M⁻¹ b
  induction' hs : univ.image b using Finset.strongInduction with s ih generalizing m
  -- ⊢ BlockTriangular M⁻¹ b
  subst hs
  -- ⊢ BlockTriangular M⁻¹ b
  intro i j hij
  -- ⊢ M⁻¹ i j = 0
  haveI : Inhabited m := ⟨i⟩
  -- ⊢ M⁻¹ i j = 0
  let k := (univ.image b).max' (univ_nonempty.image _)
  -- ⊢ M⁻¹ i j = 0
  let b' := fun i : { a // b a < k } => b ↑i
  -- ⊢ M⁻¹ i j = 0
  let A := M.toBlock (fun i => b i < k) fun j => b j < k
  -- ⊢ M⁻¹ i j = 0
  obtain hbi | hi : b i = k ∨ _ := (le_max' _ (b i) <| mem_image_of_mem _ <| mem_univ _).eq_or_lt
  -- ⊢ M⁻¹ i j = 0
  · have : M⁻¹.toBlock (fun i => k ≤ b i) (fun i => b i < k) ⟨i, hbi.ge⟩ ⟨j, hbi ▸ hij⟩ = 0 := by
      simp only [toBlock_inverse_eq_zero hM k, Matrix.zero_apply]
    simp [this.symm]
    -- 🎉 no goals
  haveI : Invertible A := hM.invertibleToBlock _
  -- ⊢ M⁻¹ i j = 0
  have hA : A.BlockTriangular b' := hM.submatrix
  -- ⊢ M⁻¹ i j = 0
  have hb' : image b' univ ⊂ image b univ := by
    convert image_subtype_univ_ssubset_image_univ k b _ (fun a => a < k) (lt_irrefl _)
    convert max'_mem (α := α) _ _
  have hij' : b' ⟨j, hij.trans hi⟩ < b' ⟨i, hi⟩ := by simp_rw [hij]
  -- ⊢ M⁻¹ i j = 0
  simp [hM.inv_toBlock k, (ih (image b' univ) hb' hA rfl hij').symm]
  -- 🎉 no goals
#align matrix.block_triangular_inv_of_block_triangular Matrix.blockTriangular_inv_of_blockTriangular

end Matrix
