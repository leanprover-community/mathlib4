/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin
-/
import Mathlib.Data.Matrix.Basic

#align_import data.matrix.block from "leanprover-community/mathlib"@"c060baa79af5ca092c54b8bf04f0f10592f59489"

/-!
# Block Matrices

## Main definitions

* `Matrix.fromBlocks`: build a block matrix out of 4 blocks
* `Matrix.toBlocks₁₁`, `Matrix.toBlocks₁₂`, `Matrix.toBlocks₂₁`, `Matrix.toBlocks₂₂`:
  extract each of the four blocks from `Matrix.fromBlocks`.
* `Matrix.blockDiagonal`: block diagonal of equally sized blocks. On square blocks, this is a
  ring homomorphisms, `Matrix.blockDiagonalRingHom`.
* `Matrix.blockDiag`: extract the blocks from the diagonal of a block diagonal matrix.
* `Matrix.blockDiagonal'`: block diagonal of unequally sized blocks. On square blocks, this is a
  ring homomorphisms, `Matrix.blockDiagonal'RingHom`.
* `Matrix.blockDiag'`: extract the blocks from the diagonal of a block diagonal matrix.
-/


variable {l m n o p q : Type*} {m' n' p' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type*} {β : Type*}

open BigOperators Matrix

namespace Matrix

theorem dotProduct_block [Fintype m] [Fintype n] [Mul α] [AddCommMonoid α] (v w : Sum m n → α) :
    v ⬝ᵥ w = v ∘ Sum.inl ⬝ᵥ w ∘ Sum.inl + v ∘ Sum.inr ⬝ᵥ w ∘ Sum.inr :=
  Fintype.sum_sum_type _
#align matrix.dot_product_block Matrix.dotProduct_block

section BlockMatrices

/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
-- @[pp_nodot] -- Porting note: removed
def fromBlocks (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    Matrix (Sum n o) (Sum l m) α :=
  of <| Sum.elim (fun i => Sum.elim (A i) (B i)) fun i => Sum.elim (C i) (D i)
#align matrix.from_blocks Matrix.fromBlocks

@[simp]
theorem fromBlocks_apply₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : l) : fromBlocks A B C D (Sum.inl i) (Sum.inl j) = A i j :=
  rfl
#align matrix.from_blocks_apply₁₁ Matrix.fromBlocks_apply₁₁

@[simp]
theorem fromBlocks_apply₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : m) : fromBlocks A B C D (Sum.inl i) (Sum.inr j) = B i j :=
  rfl
#align matrix.from_blocks_apply₁₂ Matrix.fromBlocks_apply₁₂

@[simp]
theorem fromBlocks_apply₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : l) : fromBlocks A B C D (Sum.inr i) (Sum.inl j) = C i j :=
  rfl
#align matrix.from_blocks_apply₂₁ Matrix.fromBlocks_apply₂₁

@[simp]
theorem fromBlocks_apply₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : m) : fromBlocks A B C D (Sum.inr i) (Sum.inr j) = D i j :=
  rfl
#align matrix.from_blocks_apply₂₂ Matrix.fromBlocks_apply₂₂

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top left" submatrix. -/
def toBlocks₁₁ (M : Matrix (Sum n o) (Sum l m) α) : Matrix n l α :=
  of fun i j => M (Sum.inl i) (Sum.inl j)
#align matrix.to_blocks₁₁ Matrix.toBlocks₁₁

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top right" submatrix. -/
def toBlocks₁₂ (M : Matrix (Sum n o) (Sum l m) α) : Matrix n m α :=
  of fun i j => M (Sum.inl i) (Sum.inr j)
#align matrix.to_blocks₁₂ Matrix.toBlocks₁₂

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom left" submatrix. -/
def toBlocks₂₁ (M : Matrix (Sum n o) (Sum l m) α) : Matrix o l α :=
  of fun i j => M (Sum.inr i) (Sum.inl j)
#align matrix.to_blocks₂₁ Matrix.toBlocks₂₁

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom right" submatrix. -/
def toBlocks₂₂ (M : Matrix (Sum n o) (Sum l m) α) : Matrix o m α :=
  of fun i j => M (Sum.inr i) (Sum.inr j)
#align matrix.to_blocks₂₂ Matrix.toBlocks₂₂

theorem fromBlocks_toBlocks (M : Matrix (Sum n o) (Sum l m) α) :
    fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M := by
  ext i j
  -- ⊢ fromBlocks (toBlocks₁₁ M) (toBlocks₁₂ M) (toBlocks₂₁ M) (toBlocks₂₂ M) i j = …
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
  -- ⊢ fromBlocks (toBlocks₁₁ M) (toBlocks₁₂ M) (toBlocks₂₁ M) (toBlocks₂₂ M) (Sum. …
                       -- ⊢ fromBlocks (toBlocks₁₁ M) (toBlocks₁₂ M) (toBlocks₂₁ M) (toBlocks₂₂ M) (Sum. …
                       -- ⊢ fromBlocks (toBlocks₁₁ M) (toBlocks₁₂ M) (toBlocks₂₁ M) (toBlocks₂₂ M) (Sum. …
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align matrix.from_blocks_to_blocks Matrix.fromBlocks_toBlocks

@[simp]
theorem toBlocks_fromBlocks₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₁ = A :=
  rfl
#align matrix.to_blocks_from_blocks₁₁ Matrix.toBlocks_fromBlocks₁₁

@[simp]
theorem toBlocks_fromBlocks₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₂ = B :=
  rfl
#align matrix.to_blocks_from_blocks₁₂ Matrix.toBlocks_fromBlocks₁₂

@[simp]
theorem toBlocks_fromBlocks₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₁ = C :=
  rfl
#align matrix.to_blocks_from_blocks₂₁ Matrix.toBlocks_fromBlocks₂₁

@[simp]
theorem toBlocks_fromBlocks₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₂ = D :=
  rfl
#align matrix.to_blocks_from_blocks₂₂ Matrix.toBlocks_fromBlocks₂₂

/-- Two block matrices are equal if their blocks are equal. -/
theorem ext_iff_blocks {A B : Matrix (Sum n o) (Sum l m) α} :
    A = B ↔
      A.toBlocks₁₁ = B.toBlocks₁₁ ∧
        A.toBlocks₁₂ = B.toBlocks₁₂ ∧ A.toBlocks₂₁ = B.toBlocks₂₁ ∧ A.toBlocks₂₂ = B.toBlocks₂₂ :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩, fun ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ => by
    rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, h₁₁, h₁₂, h₂₁, h₂₂]⟩
    -- 🎉 no goals
#align matrix.ext_iff_blocks Matrix.ext_iff_blocks

@[simp]
theorem fromBlocks_inj {A : Matrix n l α} {B : Matrix n m α} {C : Matrix o l α} {D : Matrix o m α}
    {A' : Matrix n l α} {B' : Matrix n m α} {C' : Matrix o l α} {D' : Matrix o m α} :
    fromBlocks A B C D = fromBlocks A' B' C' D' ↔ A = A' ∧ B = B' ∧ C = C' ∧ D = D' :=
  ext_iff_blocks
#align matrix.from_blocks_inj Matrix.fromBlocks_inj

theorem fromBlocks_map (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
    (f : α → β) : (fromBlocks A B C D).map f = fromBlocks (A.map f) (B.map f) (C.map f) (D.map f) :=
  by ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]
     -- ⊢ map (fromBlocks A B C D) f i j = fromBlocks (map A f) (map B f) (map C f) (m …
              -- ⊢ map (fromBlocks A B C D) f (Sum.inl val✝) j = fromBlocks (map A f) (map B f) …
                                   -- ⊢ map (fromBlocks A B C D) f (Sum.inl val✝¹) (Sum.inl val✝) = fromBlocks (map  …
                                   -- ⊢ map (fromBlocks A B C D) f (Sum.inr val✝¹) (Sum.inl val✝) = fromBlocks (map  …
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
#align matrix.from_blocks_map Matrix.fromBlocks_map

theorem fromBlocks_transpose (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ := by
  ext i j
  -- ⊢ (fromBlocks A B C D)ᵀ i j = fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]
  -- ⊢ (fromBlocks A B C D)ᵀ (Sum.inl val✝) j = fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ (Sum.inl val …
                       -- ⊢ (fromBlocks A B C D)ᵀ (Sum.inl val✝¹) (Sum.inl val✝) = fromBlocks Aᵀ Cᵀ Bᵀ D …
                       -- ⊢ (fromBlocks A B C D)ᵀ (Sum.inr val✝¹) (Sum.inl val✝) = fromBlocks Aᵀ Cᵀ Bᵀ D …
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align matrix.from_blocks_transpose Matrix.fromBlocks_transpose

theorem fromBlocks_conjTranspose [Star α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D)ᴴ = fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ := by
  simp only [conjTranspose, fromBlocks_transpose, fromBlocks_map]
  -- 🎉 no goals
#align matrix.from_blocks_conj_transpose Matrix.fromBlocks_conjTranspose

@[simp]
theorem fromBlocks_submatrix_sum_swap_left (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (f : p → Sum l m) :
    (fromBlocks A B C D).submatrix Sum.swap f = (fromBlocks C D A B).submatrix id f := by
  ext i j
  -- ⊢ submatrix (fromBlocks A B C D) Sum.swap f i j = submatrix (fromBlocks C D A  …
  cases i <;> dsimp <;> cases f j <;> rfl
  -- ⊢ submatrix (fromBlocks A B C D) Sum.swap f (Sum.inl val✝) j = submatrix (from …
              -- ⊢ fromBlocks A B C D (Sum.inr val✝) (f j) = fromBlocks C D A B (Sum.inl val✝)  …
              -- ⊢ fromBlocks A B C D (Sum.inl val✝) (f j) = fromBlocks C D A B (Sum.inr val✝)  …
                        -- ⊢ fromBlocks A B C D (Sum.inr val✝¹) (Sum.inl val✝) = fromBlocks C D A B (Sum. …
                        -- ⊢ fromBlocks A B C D (Sum.inl val✝¹) (Sum.inl val✝) = fromBlocks C D A B (Sum. …
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
#align matrix.from_blocks_submatrix_sum_swap_left Matrix.fromBlocks_submatrix_sum_swap_left

@[simp]
theorem fromBlocks_submatrix_sum_swap_right (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (f : p → Sum n o) :
    (fromBlocks A B C D).submatrix f Sum.swap = (fromBlocks B A D C).submatrix f id := by
  ext i j
  -- ⊢ submatrix (fromBlocks A B C D) f Sum.swap i j = submatrix (fromBlocks B A D  …
  cases j <;> dsimp <;> cases f i <;> rfl
  -- ⊢ submatrix (fromBlocks A B C D) f Sum.swap i (Sum.inl val✝) = submatrix (from …
              -- ⊢ fromBlocks A B C D (f i) (Sum.inr val✝) = fromBlocks B A D C (f i) (Sum.inl  …
              -- ⊢ fromBlocks A B C D (f i) (Sum.inl val✝) = fromBlocks B A D C (f i) (Sum.inr  …
                        -- ⊢ fromBlocks A B C D (Sum.inl val✝) (Sum.inr val✝¹) = fromBlocks B A D C (Sum. …
                        -- ⊢ fromBlocks A B C D (Sum.inl val✝) (Sum.inl val✝¹) = fromBlocks B A D C (Sum. …
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
#align matrix.from_blocks_submatrix_sum_swap_right Matrix.fromBlocks_submatrix_sum_swap_right

theorem fromBlocks_submatrix_sum_swap_sum_swap {l m n o α : Type*} (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    (fromBlocks A B C D).submatrix Sum.swap Sum.swap = fromBlocks D C B A := by simp
                                                                                -- 🎉 no goals
#align matrix.from_blocks_submatrix_sum_swap_sum_swap Matrix.fromBlocks_submatrix_sum_swap_sum_swap

/-- A 2x2 block matrix is block diagonal if the blocks outside of the diagonal vanish -/
def IsTwoBlockDiagonal [Zero α] (A : Matrix (Sum n o) (Sum l m) α) : Prop :=
  toBlocks₁₂ A = 0 ∧ toBlocks₂₁ A = 0
#align matrix.is_two_block_diagonal Matrix.IsTwoBlockDiagonal

/-- Let `p` pick out certain rows and `q` pick out certain columns of a matrix `M`. Then
  `toBlock M p q` is the corresponding block matrix. -/
def toBlock (M : Matrix m n α) (p : m → Prop) (q : n → Prop) : Matrix { a // p a } { a // q a } α :=
  M.submatrix (↑) (↑)
#align matrix.to_block Matrix.toBlock

@[simp]
theorem toBlock_apply (M : Matrix m n α) (p : m → Prop) (q : n → Prop) (i : { a // p a })
    (j : { a // q a }) : toBlock M p q i j = M ↑i ↑j :=
  rfl
#align matrix.to_block_apply Matrix.toBlock_apply

/-- Let `p` pick out certain rows and columns of a square matrix `M`. Then
  `toSquareBlockProp M p` is the corresponding block matrix. -/
def toSquareBlockProp (M : Matrix m m α) (p : m → Prop) : Matrix { a // p a } { a // p a } α :=
  toBlock M _ _
#align matrix.to_square_block_prop Matrix.toSquareBlockProp

theorem toSquareBlockProp_def (M : Matrix m m α) (p : m → Prop) :
    -- porting note: added missing `of`
    toSquareBlockProp M p = of (fun i j : { a // p a } => M ↑i ↑j) :=
  rfl
#align matrix.to_square_block_prop_def Matrix.toSquareBlockProp_def

/-- Let `b` map rows and columns of a square matrix `M` to blocks. Then
  `toSquareBlock M b k` is the block `k` matrix. -/
def toSquareBlock (M : Matrix m m α) (b : m → β) (k : β) :
    Matrix { a // b a = k } { a // b a = k } α :=
  toSquareBlockProp M _
#align matrix.to_square_block Matrix.toSquareBlock

theorem toSquareBlock_def (M : Matrix m m α) (b : m → β) (k : β) :
    -- porting note: added missing `of`
    toSquareBlock M b k = of (fun i j : { a // b a = k } => M ↑i ↑j) :=
  rfl
#align matrix.to_square_block_def Matrix.toSquareBlock_def

theorem fromBlocks_smul [SMul R α] (x : R) (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : x • fromBlocks A B C D = fromBlocks (x • A) (x • B) (x • C) (x • D) := by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [fromBlocks]
  -- ⊢ (x • fromBlocks A B C D) i j = fromBlocks (x • A) (x • B) (x • C) (x • D) i j
           -- ⊢ (x • fromBlocks A B C D) (Sum.inl val✝) j = fromBlocks (x • A) (x • B) (x •  …
                                -- ⊢ (x • fromBlocks A B C D) (Sum.inl val✝¹) (Sum.inl val✝) = fromBlocks (x • A) …
                                -- ⊢ (x • fromBlocks A B C D) (Sum.inr val✝¹) (Sum.inl val✝) = fromBlocks (x • A) …
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
#align matrix.from_blocks_smul Matrix.fromBlocks_smul

theorem fromBlocks_neg [Neg R] (A : Matrix n l R) (B : Matrix n m R) (C : Matrix o l R)
    (D : Matrix o m R) : -fromBlocks A B C D = fromBlocks (-A) (-B) (-C) (-D) := by
  ext i j
  -- ⊢ (-fromBlocks A B C D) i j = fromBlocks (-A) (-B) (-C) (-D) i j
  cases i <;> cases j <;> simp [fromBlocks]
  -- ⊢ (-fromBlocks A B C D) (Sum.inl val✝) j = fromBlocks (-A) (-B) (-C) (-D) (Sum …
              -- ⊢ (-fromBlocks A B C D) (Sum.inl val✝¹) (Sum.inl val✝) = fromBlocks (-A) (-B)  …
              -- ⊢ (-fromBlocks A B C D) (Sum.inr val✝¹) (Sum.inl val✝) = fromBlocks (-A) (-B)  …
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
#align matrix.from_blocks_neg Matrix.fromBlocks_neg

@[simp]
theorem fromBlocks_zero [Zero α] : fromBlocks (0 : Matrix n l α) 0 0 (0 : Matrix o m α) = 0 := by
  ext i j
  -- ⊢ fromBlocks 0 0 0 0 i j = OfNat.ofNat 0 i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
  -- ⊢ fromBlocks 0 0 0 0 (Sum.inl val✝) j = OfNat.ofNat 0 (Sum.inl val✝) j
                       -- ⊢ fromBlocks 0 0 0 0 (Sum.inl val✝¹) (Sum.inl val✝) = OfNat.ofNat 0 (Sum.inl v …
                       -- ⊢ fromBlocks 0 0 0 0 (Sum.inr val✝¹) (Sum.inl val✝) = OfNat.ofNat 0 (Sum.inr v …
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align matrix.from_blocks_zero Matrix.fromBlocks_zero

theorem fromBlocks_add [Add α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (A' : Matrix n l α) (B' : Matrix n m α) (C' : Matrix o l α)
    (D' : Matrix o m α) :
    fromBlocks A B C D + fromBlocks A' B' C' D' = fromBlocks (A + A') (B + B') (C + C') (D + D') :=
  by ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl
     -- ⊢ (fromBlocks A B C D + fromBlocks A' B' C' D') i j = fromBlocks (A + A') (B + …
              -- ⊢ (fromBlocks A B C D + fromBlocks A' B' C' D') (Sum.inl val✝) j = fromBlocks  …
                                   -- ⊢ (fromBlocks A B C D + fromBlocks A' B' C' D') (Sum.inl val✝¹) (Sum.inl val✝) …
                                   -- ⊢ (fromBlocks A B C D + fromBlocks A' B' C' D') (Sum.inr val✝¹) (Sum.inl val✝) …
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
#align matrix.from_blocks_add Matrix.fromBlocks_add

theorem fromBlocks_multiply [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (A' : Matrix l p α) (B' : Matrix l q α)
    (C' : Matrix m p α) (D' : Matrix m q α) :
    fromBlocks A B C D * fromBlocks A' B' C' D' =
      fromBlocks (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  ext i j
  -- ⊢ (fromBlocks A B C D * fromBlocks A' B' C' D') i j = fromBlocks (A * A' + B * …
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp only [fromBlocks, mul_apply, of_apply,
  -- ⊢ (fromBlocks A B C D * fromBlocks A' B' C' D') (Sum.inl val✝) j = fromBlocks  …
                       -- ⊢ (fromBlocks A B C D * fromBlocks A' B' C' D') (Sum.inl val✝¹) (Sum.inl val✝) …
                       -- ⊢ (fromBlocks A B C D * fromBlocks A' B' C' D') (Sum.inr val✝¹) (Sum.inl val✝) …
      Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl, add_apply]
#align matrix.from_blocks_multiply Matrix.fromBlocks_multiply

theorem fromBlocks_mulVec [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : Sum l m → α) :
    mulVec (fromBlocks A B C D) x =
      Sum.elim (mulVec A (x ∘ Sum.inl) + mulVec B (x ∘ Sum.inr))
        (mulVec C (x ∘ Sum.inl) + mulVec D (x ∘ Sum.inr)) := by
  ext i
  -- ⊢ mulVec (fromBlocks A B C D) x i = Sum.elim (mulVec A (x ∘ Sum.inl) + mulVec  …
  cases i <;> simp [mulVec, dotProduct]
  -- ⊢ mulVec (fromBlocks A B C D) x (Sum.inl val✝) = Sum.elim (mulVec A (x ∘ Sum.i …
              -- 🎉 no goals
              -- 🎉 no goals
#align matrix.from_blocks_mul_vec Matrix.fromBlocks_mulVec

theorem vecMul_fromBlocks [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α] (A : Matrix n l α)
    (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (x : Sum n o → α) :
    vecMul x (fromBlocks A B C D) =
      Sum.elim (vecMul (x ∘ Sum.inl) A + vecMul (x ∘ Sum.inr) C)
        (vecMul (x ∘ Sum.inl) B + vecMul (x ∘ Sum.inr) D) := by
  ext i
  -- ⊢ vecMul x (fromBlocks A B C D) i = Sum.elim (vecMul (x ∘ Sum.inl) A + vecMul  …
  cases i <;> simp [vecMul, dotProduct]
  -- ⊢ vecMul x (fromBlocks A B C D) (Sum.inl val✝) = Sum.elim (vecMul (x ∘ Sum.inl …
              -- 🎉 no goals
              -- 🎉 no goals
#align matrix.vec_mul_from_blocks Matrix.vecMul_fromBlocks

variable [DecidableEq l] [DecidableEq m]

section Zero

variable [Zero α]

theorem toBlock_diagonal_self (d : m → α) (p : m → Prop) :
    Matrix.toBlock (diagonal d) p p = diagonal fun i : Subtype p => d ↑i := by
  ext i j
  -- ⊢ toBlock (diagonal d) p p i j = diagonal (fun i => d ↑i) i j
  by_cases i = j
  -- ⊢ toBlock (diagonal d) p p i j = diagonal (fun i => d ↑i) i j
  -- ⊢ toBlock (diagonal d) p p i j = diagonal (fun i => d ↑i) i j
  · simp [h]
    -- 🎉 no goals
  · simp [One.one, h, Subtype.val_injective.ne h]
    -- 🎉 no goals
#align matrix.to_block_diagonal_self Matrix.toBlock_diagonal_self

theorem toBlock_diagonal_disjoint (d : m → α) {p q : m → Prop} (hpq : Disjoint p q) :
    Matrix.toBlock (diagonal d) p q = 0 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  -- ⊢ toBlock (diagonal d) p q { val := i, property := hi } { val := j, property : …
  have : i ≠ j := fun heq => hpq.le_bot i ⟨hi, heq.symm ▸ hj⟩
  -- ⊢ toBlock (diagonal d) p q { val := i, property := hi } { val := j, property : …
  simp [diagonal_apply_ne d this]
  -- 🎉 no goals
#align matrix.to_block_diagonal_disjoint Matrix.toBlock_diagonal_disjoint

@[simp]
theorem fromBlocks_diagonal (d₁ : l → α) (d₂ : m → α) :
    fromBlocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (Sum.elim d₁ d₂) := by
  ext i j
  -- ⊢ fromBlocks (diagonal d₁) 0 0 (diagonal d₂) i j = diagonal (Sum.elim d₁ d₂) i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [diagonal]
  -- ⊢ fromBlocks (diagonal d₁) 0 0 (diagonal d₂) (Sum.inl val✝) j = diagonal (Sum. …
                       -- ⊢ fromBlocks (diagonal d₁) 0 0 (diagonal d₂) (Sum.inl val✝¹) (Sum.inl val✝) =  …
                       -- ⊢ fromBlocks (diagonal d₁) 0 0 (diagonal d₂) (Sum.inr val✝¹) (Sum.inl val✝) =  …
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align matrix.from_blocks_diagonal Matrix.fromBlocks_diagonal

end Zero

section HasZeroHasOne

variable [Zero α] [One α]

@[simp]
theorem fromBlocks_one : fromBlocks (1 : Matrix l l α) 0 0 (1 : Matrix m m α) = 1 := by
  ext i j
  -- ⊢ fromBlocks 1 0 0 1 i j = OfNat.ofNat 1 i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> simp [one_apply]
  -- ⊢ fromBlocks 1 0 0 1 (Sum.inl val✝) j = OfNat.ofNat 1 (Sum.inl val✝) j
                       -- ⊢ fromBlocks 1 0 0 1 (Sum.inl val✝¹) (Sum.inl val✝) = OfNat.ofNat 1 (Sum.inl v …
                       -- ⊢ fromBlocks 1 0 0 1 (Sum.inr val✝¹) (Sum.inl val✝) = OfNat.ofNat 1 (Sum.inr v …
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align matrix.from_blocks_one Matrix.fromBlocks_one

@[simp]
theorem toBlock_one_self (p : m → Prop) : Matrix.toBlock (1 : Matrix m m α) p p = 1 :=
  toBlock_diagonal_self _ p
#align matrix.to_block_one_self Matrix.toBlock_one_self

theorem toBlock_one_disjoint {p q : m → Prop} (hpq : Disjoint p q) :
    Matrix.toBlock (1 : Matrix m m α) p q = 0 :=
  toBlock_diagonal_disjoint _ hpq
#align matrix.to_block_one_disjoint Matrix.toBlock_one_disjoint

end HasZeroHasOne

end BlockMatrices

section BlockDiagonal

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/-- `Matrix.blockDiagonal M` turns a homogenously-indexed collection of matrices
`M : o → Matrix m n α'` into an `m × o`-by-`n × o` block matrix which has the entries of `M` along
the diagonal and zero elsewhere.

See also `Matrix.blockDiagonal'` if the matrices may not have the same size everywhere.
-/
def blockDiagonal (M : o → Matrix m n α) : Matrix (m × o) (n × o) α :=
  of <| (fun ⟨i, k⟩ ⟨j, k'⟩ => if k = k' then M k i j else 0 : m × o → n × o → α)
#align matrix.block_diagonal Matrix.blockDiagonal

-- TODO: set as an equation lemma for `blockDiagonal`, see mathlib4#3024
theorem blockDiagonal_apply' (M : o → Matrix m n α) (i k j k') :
    blockDiagonal M ⟨i, k⟩ ⟨j, k'⟩ = if k = k' then M k i j else 0 :=
  rfl
#align matrix.block_diagonal_apply' Matrix.blockDiagonal_apply'

theorem blockDiagonal_apply (M : o → Matrix m n α) (ik jk) :
    blockDiagonal M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0 := by
  cases ik
  -- ⊢ blockDiagonal M (fst✝, snd✝) jk = if (fst✝, snd✝).snd = jk.snd then M (fst✝, …
  cases jk
  -- ⊢ blockDiagonal M (fst✝¹, snd✝¹) (fst✝, snd✝) = if (fst✝¹, snd✝¹).snd = (fst✝, …
  rfl
  -- 🎉 no goals
#align matrix.block_diagonal_apply Matrix.blockDiagonal_apply

@[simp]
theorem blockDiagonal_apply_eq (M : o → Matrix m n α) (i j k) :
    blockDiagonal M (i, k) (j, k) = M k i j :=
  if_pos rfl
#align matrix.block_diagonal_apply_eq Matrix.blockDiagonal_apply_eq

theorem blockDiagonal_apply_ne (M : o → Matrix m n α) (i j) {k k'} (h : k ≠ k') :
    blockDiagonal M (i, k) (j, k') = 0 :=
  if_neg h
#align matrix.block_diagonal_apply_ne Matrix.blockDiagonal_apply_ne

theorem blockDiagonal_map (M : o → Matrix m n α) (f : α → β) (hf : f 0 = 0) :
    (blockDiagonal M).map f = blockDiagonal fun k => (M k).map f := by
  ext
  -- ⊢ map (blockDiagonal M) f i✝ x✝ = blockDiagonal (fun k => map (M k) f) i✝ x✝
  simp only [map_apply, blockDiagonal_apply, eq_comm]
  -- ⊢ f (if i✝.snd = x✝.snd then M i✝.snd i✝.fst x✝.fst else 0) = if i✝.snd = x✝.s …
  rw [apply_ite f, hf]
  -- 🎉 no goals
#align matrix.block_diagonal_map Matrix.blockDiagonal_map

@[simp]
theorem blockDiagonal_transpose (M : o → Matrix m n α) :
    (blockDiagonal M)ᵀ = blockDiagonal fun k => (M k)ᵀ := by
  ext
  -- ⊢ (blockDiagonal M)ᵀ i✝ x✝ = blockDiagonal (fun k => (M k)ᵀ) i✝ x✝
  simp only [transpose_apply, blockDiagonal_apply, eq_comm]
  -- ⊢ (if i✝.snd = x✝.snd then M i✝.snd x✝.fst i✝.fst else 0) = if i✝.snd = x✝.snd …
  split_ifs with h
  -- ⊢ M i✝.snd x✝.fst i✝.fst = M x✝.snd x✝.fst i✝.fst
  · rw [h]
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align matrix.block_diagonal_transpose Matrix.blockDiagonal_transpose

@[simp]
theorem blockDiagonal_conjTranspose {α : Type*} [AddMonoid α] [StarAddMonoid α]
    (M : o → Matrix m n α) : (blockDiagonal M)ᴴ = blockDiagonal fun k => (M k)ᴴ := by
  simp only [conjTranspose, blockDiagonal_transpose]
  -- ⊢ map (blockDiagonal fun k => (M k)ᵀ) star = blockDiagonal fun k => map (M k)ᵀ …
  rw [blockDiagonal_map _ star (star_zero α)]
  -- 🎉 no goals
#align matrix.block_diagonal_conj_transpose Matrix.blockDiagonal_conjTranspose

@[simp]
theorem blockDiagonal_zero : blockDiagonal (0 : o → Matrix m n α) = 0 := by
  ext
  -- ⊢ blockDiagonal 0 i✝ x✝ = OfNat.ofNat 0 i✝ x✝
  simp [blockDiagonal_apply]
  -- 🎉 no goals
#align matrix.block_diagonal_zero Matrix.blockDiagonal_zero

@[simp]
theorem blockDiagonal_diagonal [DecidableEq m] (d : o → m → α) :
    (blockDiagonal fun k => diagonal (d k)) = diagonal fun ik => d ik.2 ik.1 := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  -- ⊢ blockDiagonal (fun k => diagonal (d k)) (i, k) (j, k') = diagonal (fun ik => …
  simp only [blockDiagonal_apply, diagonal_apply, Prod.mk.inj_iff, ← ite_and]
  -- ⊢ (if k = k' ∧ i = j then d k i else 0) = if i = j ∧ k = k' then d k i else 0
  congr 1
  -- ⊢ (k = k' ∧ i = j) = (i = j ∧ k = k')
  rw [and_comm]
  -- 🎉 no goals
#align matrix.block_diagonal_diagonal Matrix.blockDiagonal_diagonal

@[simp]
theorem blockDiagonal_one [DecidableEq m] [One α] : blockDiagonal (1 : o → Matrix m m α) = 1 :=
  show (blockDiagonal fun _ : o => diagonal fun _ : m => (1 : α)) = diagonal fun _ => 1 by
    rw [blockDiagonal_diagonal]
    -- 🎉 no goals
#align matrix.block_diagonal_one Matrix.blockDiagonal_one

end Zero

@[simp]
theorem blockDiagonal_add [AddZeroClass α] (M N : o → Matrix m n α) :
    blockDiagonal (M + N) = blockDiagonal M + blockDiagonal N := by
  ext
  -- ⊢ blockDiagonal (M + N) i✝ x✝ = (blockDiagonal M + blockDiagonal N) i✝ x✝
  simp only [blockDiagonal_apply, Pi.add_apply, add_apply]
  -- ⊢ (if i✝.snd = x✝.snd then M i✝.snd i✝.fst x✝.fst + N i✝.snd i✝.fst x✝.fst els …
  split_ifs <;> simp
  -- ⊢ M i✝.snd i✝.fst x✝.fst + N i✝.snd i✝.fst x✝.fst = M i✝.snd i✝.fst x✝.fst + N …
                -- 🎉 no goals
                -- 🎉 no goals
#align matrix.block_diagonal_add Matrix.blockDiagonal_add

section

variable (o m n α)

/-- `Matrix.blockDiagonal` as an `AddMonoidHom`. -/
@[simps]
def blockDiagonalAddMonoidHom [AddZeroClass α] : (o → Matrix m n α) →+ Matrix (m × o) (n × o) α
    where
  toFun := blockDiagonal
  map_zero' := blockDiagonal_zero
  map_add' := blockDiagonal_add
#align matrix.block_diagonal_add_monoid_hom Matrix.blockDiagonalAddMonoidHom

end

@[simp]
theorem blockDiagonal_neg [AddGroup α] (M : o → Matrix m n α) :
    blockDiagonal (-M) = -blockDiagonal M :=
  map_neg (blockDiagonalAddMonoidHom m n o α) M
#align matrix.block_diagonal_neg Matrix.blockDiagonal_neg

@[simp]
theorem blockDiagonal_sub [AddGroup α] (M N : o → Matrix m n α) :
    blockDiagonal (M - N) = blockDiagonal M - blockDiagonal N :=
  map_sub (blockDiagonalAddMonoidHom m n o α) M N
#align matrix.block_diagonal_sub Matrix.blockDiagonal_sub

@[simp]
theorem blockDiagonal_mul [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
    (M : o → Matrix m n α) (N : o → Matrix n p α) :
    (blockDiagonal fun k => M k * N k) = blockDiagonal M * blockDiagonal N := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  -- ⊢ blockDiagonal (fun k => M k * N k) (i, k) (j, k') = (blockDiagonal M * block …
  simp only [blockDiagonal_apply, mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  -- ⊢ (if k = k' then ∑ j_1 : n, M k i j_1 * N k j_1 j else 0) = ∑ x : n, ∑ x_1 :  …
  split_ifs with h <;> simp [h]
  -- ⊢ ∑ j_1 : n, M k i j_1 * N k j_1 j = ∑ x : n, ∑ x_1 : o, (if k = x_1 then M k  …
                       -- 🎉 no goals
                       -- 🎉 no goals
#align matrix.block_diagonal_mul Matrix.blockDiagonal_mul

section

variable (α m o)

/-- `Matrix.blockDiagonal` as a `RingHom`. -/
@[simps]
def blockDiagonalRingHom [DecidableEq m] [Fintype o] [Fintype m] [NonAssocSemiring α] :
    (o → Matrix m m α) →+* Matrix (m × o) (m × o) α :=
  { blockDiagonalAddMonoidHom m m o α with
    toFun := blockDiagonal
    map_one' := blockDiagonal_one
    map_mul' := blockDiagonal_mul }
#align matrix.block_diagonal_ring_hom Matrix.blockDiagonalRingHom

end

@[simp]
theorem blockDiagonal_pow [DecidableEq m] [Fintype o] [Fintype m] [Semiring α]
    (M : o → Matrix m m α) (n : ℕ) : blockDiagonal (M ^ n) = blockDiagonal M ^ n :=
  map_pow (blockDiagonalRingHom m o α) M n
#align matrix.block_diagonal_pow Matrix.blockDiagonal_pow

@[simp]
theorem blockDiagonal_smul {R : Type*} [Monoid R] [AddMonoid α] [DistribMulAction R α] (x : R)
    (M : o → Matrix m n α) : blockDiagonal (x • M) = x • blockDiagonal M := by
  ext
  -- ⊢ blockDiagonal (x • M) i✝ x✝ = (x • blockDiagonal M) i✝ x✝
  simp only [blockDiagonal_apply, Pi.smul_apply, smul_apply]
  -- ⊢ (if i✝.snd = x✝.snd then x • M i✝.snd i✝.fst x✝.fst else 0) = x • if i✝.snd  …
  split_ifs <;> simp
  -- ⊢ x • M i✝.snd i✝.fst x✝.fst = x • M i✝.snd i✝.fst x✝.fst
                -- 🎉 no goals
                -- 🎉 no goals
#align matrix.block_diagonal_smul Matrix.blockDiagonal_smul

end BlockDiagonal

section BlockDiag

/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `Matrix.diag`, and the left-inverse of `Matrix.blockDiagonal`. -/
def blockDiag (M : Matrix (m × o) (n × o) α) (k : o) : Matrix m n α :=
  of fun i j => M (i, k) (j, k)
#align matrix.block_diag Matrix.blockDiag

-- TODO: set as an equation lemma for `blockDiag`, see mathlib4#3024
theorem blockDiag_apply (M : Matrix (m × o) (n × o) α) (k : o) (i j) :
    blockDiag M k i j = M (i, k) (j, k) :=
  rfl
#align matrix.block_diag_apply Matrix.blockDiag_apply

theorem blockDiag_map (M : Matrix (m × o) (n × o) α) (f : α → β) :
    blockDiag (M.map f) = fun k => (blockDiag M k).map f :=
  rfl
#align matrix.block_diag_map Matrix.blockDiag_map

@[simp]
theorem blockDiag_transpose (M : Matrix (m × o) (n × o) α) (k : o) :
    blockDiag Mᵀ k = (blockDiag M k)ᵀ :=
  ext fun _ _ => rfl
#align matrix.block_diag_transpose Matrix.blockDiag_transpose

@[simp]
theorem blockDiag_conjTranspose {α : Type*} [AddMonoid α] [StarAddMonoid α]
    (M : Matrix (m × o) (n × o) α) (k : o) : blockDiag Mᴴ k = (blockDiag M k)ᴴ :=
  ext fun _ _ => rfl
#align matrix.block_diag_conj_transpose Matrix.blockDiag_conjTranspose

section Zero

variable [Zero α] [Zero β]

@[simp]
theorem blockDiag_zero : blockDiag (0 : Matrix (m × o) (n × o) α) = 0 :=
  rfl
#align matrix.block_diag_zero Matrix.blockDiag_zero

@[simp]
theorem blockDiag_diagonal [DecidableEq o] [DecidableEq m] (d : m × o → α) (k : o) :
    blockDiag (diagonal d) k = diagonal fun i => d (i, k) :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    -- ⊢ blockDiag (diagonal d) k i i = diagonal (fun i => d (i, k)) i i
    · rw [blockDiag_apply, diagonal_apply_eq, diagonal_apply_eq]
      -- 🎉 no goals
    · rw [blockDiag_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt _ hij)]
      -- ⊢ (i, k) = (j, k) → i = j
      exact Prod.fst_eq_iff.mpr
      -- 🎉 no goals
#align matrix.block_diag_diagonal Matrix.blockDiag_diagonal

@[simp]
theorem blockDiag_blockDiagonal [DecidableEq o] (M : o → Matrix m n α) :
    blockDiag (blockDiagonal M) = M :=
  funext fun _ => ext fun i j => blockDiagonal_apply_eq M i j _
#align matrix.block_diag_block_diagonal Matrix.blockDiag_blockDiagonal

theorem blockDiagonal_injective [DecidableEq o] :
    Function.Injective (blockDiagonal : (o → Matrix m n α) → Matrix _ _ α) :=
  Function.LeftInverse.injective blockDiag_blockDiagonal
#align matrix.block_diagonal_injective Matrix.blockDiagonal_injective

@[simp]
theorem blockDiagonal_inj [DecidableEq o] {M N : o → Matrix m n α} :
    blockDiagonal M = blockDiagonal N ↔ M = N :=
  blockDiagonal_injective.eq_iff
#align matrix.block_diagonal_inj Matrix.blockDiagonal_inj

@[simp]
theorem blockDiag_one [DecidableEq o] [DecidableEq m] [One α] :
    blockDiag (1 : Matrix (m × o) (m × o) α) = 1 :=
  funext <| blockDiag_diagonal _
#align matrix.block_diag_one Matrix.blockDiag_one

end Zero

@[simp]
theorem blockDiag_add [AddZeroClass α] (M N : Matrix (m × o) (n × o) α) :
    blockDiag (M + N) = blockDiag M + blockDiag N :=
  rfl
#align matrix.block_diag_add Matrix.blockDiag_add

section

variable (o m n α)

/-- `Matrix.blockDiag` as an `AddMonoidHom`. -/
@[simps]
def blockDiagAddMonoidHom [AddZeroClass α] : Matrix (m × o) (n × o) α →+ o → Matrix m n α where
  toFun := blockDiag
  map_zero' := blockDiag_zero
  map_add' := blockDiag_add
#align matrix.block_diag_add_monoid_hom Matrix.blockDiagAddMonoidHom

end

@[simp]
theorem blockDiag_neg [AddGroup α] (M : Matrix (m × o) (n × o) α) : blockDiag (-M) = -blockDiag M :=
  map_neg (blockDiagAddMonoidHom m n o α) M
#align matrix.block_diag_neg Matrix.blockDiag_neg

@[simp]
theorem blockDiag_sub [AddGroup α] (M N : Matrix (m × o) (n × o) α) :
    blockDiag (M - N) = blockDiag M - blockDiag N :=
  map_sub (blockDiagAddMonoidHom m n o α) M N
#align matrix.block_diag_sub Matrix.blockDiag_sub

@[simp]
theorem blockDiag_smul {R : Type*} [Monoid R] [AddMonoid α] [DistribMulAction R α] (x : R)
    (M : Matrix (m × o) (n × o) α) : blockDiag (x • M) = x • blockDiag M :=
  rfl
#align matrix.block_diag_smul Matrix.blockDiag_smul

end BlockDiag

section BlockDiagonal'

variable [DecidableEq o]

section Zero

variable [Zero α] [Zero β]

/-- `Matrix.blockDiagonal' M` turns `M : Π i, Matrix (m i) (n i) α` into a
`Σ i, m i`-by-`Σ i, n i` block matrix which has the entries of `M` along the diagonal
and zero elsewhere.

This is the dependently-typed version of `Matrix.blockDiagonal`. -/
def blockDiagonal' (M : ∀ i, Matrix (m' i) (n' i) α) : Matrix (Σi, m' i) (Σi, n' i) α :=
  of <|
    (fun ⟨k, i⟩ ⟨k', j⟩ => if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0 :
      (Σi, m' i) → (Σi, n' i) → α)
#align matrix.block_diagonal' Matrix.blockDiagonal'

-- TODO: set as an equation lemma for `blockDiagonal'`, see mathlib4#3024
theorem blockDiagonal'_apply' (M : ∀ i, Matrix (m' i) (n' i) α) (k i k' j) :
    blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ =
      if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0 :=
  rfl
#align matrix.block_diagonal'_apply' Matrix.blockDiagonal'_apply'

theorem blockDiagonal'_eq_blockDiagonal (M : o → Matrix m n α) {k k'} (i j) :
    blockDiagonal M (i, k) (j, k') = blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ :=
  rfl
#align matrix.block_diagonal'_eq_block_diagonal Matrix.blockDiagonal'_eq_blockDiagonal

theorem blockDiagonal'_submatrix_eq_blockDiagonal (M : o → Matrix m n α) :
    (blockDiagonal' M).submatrix (Prod.toSigma ∘ Prod.swap) (Prod.toSigma ∘ Prod.swap) =
      blockDiagonal M :=
  Matrix.ext fun ⟨_, _⟩ ⟨_, _⟩ => rfl
#align matrix.block_diagonal'_submatrix_eq_block_diagonal Matrix.blockDiagonal'_submatrix_eq_blockDiagonal

theorem blockDiagonal'_apply (M : ∀ i, Matrix (m' i) (n' i) α) (ik jk) :
    blockDiagonal' M ik jk =
      if h : ik.1 = jk.1 then M ik.1 ik.2 (cast (congr_arg n' h.symm) jk.2) else 0 := by
  cases ik
  -- ⊢ blockDiagonal' M { fst := fst✝, snd := snd✝ } jk = if h : { fst := fst✝, snd …
  cases jk
  -- ⊢ blockDiagonal' M { fst := fst✝¹, snd := snd✝¹ } { fst := fst✝, snd := snd✝ } …
  rfl
  -- 🎉 no goals
#align matrix.block_diagonal'_apply Matrix.blockDiagonal'_apply

@[simp]
theorem blockDiagonal'_apply_eq (M : ∀ i, Matrix (m' i) (n' i) α) (k i j) :
    blockDiagonal' M ⟨k, i⟩ ⟨k, j⟩ = M k i j :=
  dif_pos rfl
#align matrix.block_diagonal'_apply_eq Matrix.blockDiagonal'_apply_eq

theorem blockDiagonal'_apply_ne (M : ∀ i, Matrix (m' i) (n' i) α) {k k'} (i j) (h : k ≠ k') :
    blockDiagonal' M ⟨k, i⟩ ⟨k', j⟩ = 0 :=
  dif_neg h
#align matrix.block_diagonal'_apply_ne Matrix.blockDiagonal'_apply_ne

theorem blockDiagonal'_map (M : ∀ i, Matrix (m' i) (n' i) α) (f : α → β) (hf : f 0 = 0) :
    (blockDiagonal' M).map f = blockDiagonal' fun k => (M k).map f := by
  ext
  -- ⊢ map (blockDiagonal' M) f i✝ x✝ = blockDiagonal' (fun k => map (M k) f) i✝ x✝
  simp only [map_apply, blockDiagonal'_apply, eq_comm]
  -- ⊢ f (if h : i✝.fst = x✝.fst then M i✝.fst i✝.snd (cast (_ : n' x✝.fst = n' i✝. …
  rw [apply_dite f, hf]
  -- 🎉 no goals
#align matrix.block_diagonal'_map Matrix.blockDiagonal'_map

@[simp]
theorem blockDiagonal'_transpose (M : ∀ i, Matrix (m' i) (n' i) α) :
    (blockDiagonal' M)ᵀ = blockDiagonal' fun k => (M k)ᵀ := by
  ext ⟨ii, ix⟩ ⟨ji, jx⟩
  -- ⊢ (blockDiagonal' M)ᵀ { fst := ii, snd := ix } { fst := ji, snd := jx } = bloc …
  simp only [transpose_apply, blockDiagonal'_apply]
  -- ⊢ (if h : ji = ii then M ji jx (cast (_ : n' { fst := ii, snd := ix }.fst = n' …
  split_ifs with h -- Porting note: was split_ifs <;> cc
  · subst h; rfl
    -- ⊢ M ji jx (cast (_ : n' { fst := ji, snd := ix }.fst = n' { fst := ji, snd :=  …
             -- 🎉 no goals
  · simp_all only [not_true]
    -- 🎉 no goals
  · simp_all only [not_true]
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align matrix.block_diagonal'_transpose Matrix.blockDiagonal'_transpose

@[simp]
theorem blockDiagonal'_conjTranspose {α} [AddMonoid α] [StarAddMonoid α]
    (M : ∀ i, Matrix (m' i) (n' i) α) : (blockDiagonal' M)ᴴ = blockDiagonal' fun k => (M k)ᴴ := by
  simp only [conjTranspose, blockDiagonal'_transpose]
  -- ⊢ map (blockDiagonal' fun k => (M k)ᵀ) star = blockDiagonal' fun k => map (M k …
  exact blockDiagonal'_map _ star (star_zero α)
  -- 🎉 no goals
#align matrix.block_diagonal'_conj_transpose Matrix.blockDiagonal'_conjTranspose

@[simp]
theorem blockDiagonal'_zero : blockDiagonal' (0 : ∀ i, Matrix (m' i) (n' i) α) = 0 := by
  ext
  -- ⊢ blockDiagonal' 0 i✝ x✝ = OfNat.ofNat 0 i✝ x✝
  simp [blockDiagonal'_apply]
  -- 🎉 no goals
#align matrix.block_diagonal'_zero Matrix.blockDiagonal'_zero

@[simp]
theorem blockDiagonal'_diagonal [∀ i, DecidableEq (m' i)] (d : ∀ i, m' i → α) :
    (blockDiagonal' fun k => diagonal (d k)) = diagonal fun ik => d ik.1 ik.2 := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  -- ⊢ blockDiagonal' (fun k => diagonal (d k)) { fst := i, snd := k } { fst := j,  …
  simp only [blockDiagonal'_apply, diagonal]
  -- ⊢ (if h : i = j then ↑of (fun i_1 j => if i_1 = j then d i i_1 else 0) k (cast …
  obtain rfl | hij := Decidable.eq_or_ne i j
  -- ⊢ (if h : i = i then ↑of (fun i_1 j => if i_1 = j then d i i_1 else 0) k (cast …
  · simp
    -- 🎉 no goals
  · simp [hij]
    -- 🎉 no goals
#align matrix.block_diagonal'_diagonal Matrix.blockDiagonal'_diagonal

@[simp]
theorem blockDiagonal'_one [∀ i, DecidableEq (m' i)] [One α] :
    blockDiagonal' (1 : ∀ i, Matrix (m' i) (m' i) α) = 1 :=
  show (blockDiagonal' fun i : o => diagonal fun _ : m' i => (1 : α)) = diagonal fun _ => 1 by
    rw [blockDiagonal'_diagonal]
    -- 🎉 no goals
#align matrix.block_diagonal'_one Matrix.blockDiagonal'_one

end Zero

@[simp]
theorem blockDiagonal'_add [AddZeroClass α] (M N : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (M + N) = blockDiagonal' M + blockDiagonal' N := by
  ext
  -- ⊢ blockDiagonal' (M + N) i✝ x✝ = (blockDiagonal' M + blockDiagonal' N) i✝ x✝
  simp only [blockDiagonal'_apply, Pi.add_apply, add_apply]
  -- ⊢ (if h : i✝.fst = x✝.fst then M i✝.fst i✝.snd (cast (_ : n' x✝.fst = n' i✝.fs …
  split_ifs <;> simp
  -- ⊢ M i✝.fst i✝.snd (cast (_ : n' x✝.fst = n' i✝.fst) x✝.snd) + N i✝.fst i✝.snd  …
                -- 🎉 no goals
                -- 🎉 no goals
#align matrix.block_diagonal'_add Matrix.blockDiagonal'_add

section

variable (m' n' α)

/-- `Matrix.blockDiagonal'` as an `AddMonoidHom`. -/
@[simps]
def blockDiagonal'AddMonoidHom [AddZeroClass α] :
    (∀ i, Matrix (m' i) (n' i) α) →+ Matrix (Σi, m' i) (Σi, n' i) α where
  toFun := blockDiagonal'
  map_zero' := blockDiagonal'_zero
  map_add' := blockDiagonal'_add
#align matrix.block_diagonal'_add_monoid_hom Matrix.blockDiagonal'AddMonoidHom

end

@[simp]
theorem blockDiagonal'_neg [AddGroup α] (M : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (-M) = -blockDiagonal' M :=
  map_neg (blockDiagonal'AddMonoidHom m' n' α) M
#align matrix.block_diagonal'_neg Matrix.blockDiagonal'_neg

@[simp]
theorem blockDiagonal'_sub [AddGroup α] (M N : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiagonal' (M - N) = blockDiagonal' M - blockDiagonal' N :=
  map_sub (blockDiagonal'AddMonoidHom m' n' α) M N
#align matrix.block_diagonal'_sub Matrix.blockDiagonal'_sub

@[simp]
theorem blockDiagonal'_mul [NonUnitalNonAssocSemiring α] [∀ i, Fintype (n' i)] [Fintype o]
    (M : ∀ i, Matrix (m' i) (n' i) α) (N : ∀ i, Matrix (n' i) (p' i) α) :
    (blockDiagonal' fun k => M k * N k) = blockDiagonal' M * blockDiagonal' N := by
  ext ⟨k, i⟩ ⟨k', j⟩
  -- ⊢ blockDiagonal' (fun k => M k * N k) { fst := k, snd := i } { fst := k', snd  …
  simp only [blockDiagonal'_apply, mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  -- ⊢ (if h : k = k' then ∑ j_1 : n' k, M k i j_1 * N k j_1 (cast (_ : p' { fst := …
  rw [Fintype.sum_eq_single k]
  -- ⊢ (if h : k = k' then ∑ j_1 : n' k, M k i j_1 * N k j_1 (cast (_ : p' { fst := …
  · simp only [if_pos, dif_pos] -- porting note: added
    -- ⊢ (if h : k = k' then ∑ j_1 : n' k, M k i j_1 * N k j_1 (cast (_ : p' { fst := …
    split_ifs <;> simp
    -- ⊢ ∑ j_1 : n' k, M k i j_1 * N k j_1 (cast (_ : p' { fst := k', snd := j }.fst  …
                  -- 🎉 no goals
                  -- 🎉 no goals
  · intro j' hj'
    -- ⊢ (∑ x : n' j', (if h : k = j' then M k i (cast (_ : n' { fst := j', snd := x  …
    exact Finset.sum_eq_zero fun _ _ => by rw [dif_neg hj'.symm, zero_mul]
    -- 🎉 no goals
#align matrix.block_diagonal'_mul Matrix.blockDiagonal'_mul

section

variable (α m')

/-- `Matrix.blockDiagonal'` as a `RingHom`. -/
@[simps]
def blockDiagonal'RingHom [∀ i, DecidableEq (m' i)] [Fintype o] [∀ i, Fintype (m' i)]
    [NonAssocSemiring α] : (∀ i, Matrix (m' i) (m' i) α) →+* Matrix (Σi, m' i) (Σi, m' i) α :=
  { blockDiagonal'AddMonoidHom m' m' α with
    toFun := blockDiagonal'
    map_one' := blockDiagonal'_one
    map_mul' := blockDiagonal'_mul }
#align matrix.block_diagonal'_ring_hom Matrix.blockDiagonal'RingHom

end

@[simp]
theorem blockDiagonal'_pow [∀ i, DecidableEq (m' i)] [Fintype o] [∀ i, Fintype (m' i)] [Semiring α]
    (M : ∀ i, Matrix (m' i) (m' i) α) (n : ℕ) : blockDiagonal' (M ^ n) = blockDiagonal' M ^ n :=
  map_pow (blockDiagonal'RingHom m' α) M n
#align matrix.block_diagonal'_pow Matrix.blockDiagonal'_pow

@[simp]
theorem blockDiagonal'_smul {R : Type*} [Semiring R] [AddCommMonoid α] [Module R α] (x : R)
    (M : ∀ i, Matrix (m' i) (n' i) α) : blockDiagonal' (x • M) = x • blockDiagonal' M := by
  ext
  -- ⊢ blockDiagonal' (x • M) i✝ x✝ = (x • blockDiagonal' M) i✝ x✝
  simp only [blockDiagonal'_apply, Pi.smul_apply, smul_apply]
  -- ⊢ (if h : i✝.fst = x✝.fst then x • M i✝.fst i✝.snd (cast (_ : n' x✝.fst = n' i …
  split_ifs <;> simp
  -- ⊢ x • M i✝.fst i✝.snd (cast (_ : n' x✝.fst = n' i✝.fst) x✝.snd) = x • M i✝.fst …
                -- 🎉 no goals
                -- 🎉 no goals
#align matrix.block_diagonal'_smul Matrix.blockDiagonal'_smul

end BlockDiagonal'

section BlockDiag'

/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `Matrix.diag`, and the left-inverse of `Matrix.blockDiagonal'`. -/
def blockDiag' (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) : Matrix (m' k) (n' k) α :=
  of fun i j => M ⟨k, i⟩ ⟨k, j⟩
#align matrix.block_diag' Matrix.blockDiag'

-- TODO: set as an equation lemma for `blockDiag'`, see mathlib4#3024
theorem blockDiag'_apply (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) (i j) :
    blockDiag' M k i j = M ⟨k, i⟩ ⟨k, j⟩ :=
  rfl
#align matrix.block_diag'_apply Matrix.blockDiag'_apply

theorem blockDiag'_map (M : Matrix (Σi, m' i) (Σi, n' i) α) (f : α → β) :
    blockDiag' (M.map f) = fun k => (blockDiag' M k).map f :=
  rfl
#align matrix.block_diag'_map Matrix.blockDiag'_map

@[simp]
theorem blockDiag'_transpose (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) :
    blockDiag' Mᵀ k = (blockDiag' M k)ᵀ :=
  ext fun _ _ => rfl
#align matrix.block_diag'_transpose Matrix.blockDiag'_transpose

@[simp]
theorem blockDiag'_conjTranspose {α : Type*} [AddMonoid α] [StarAddMonoid α]
    (M : Matrix (Σi, m' i) (Σi, n' i) α) (k : o) : blockDiag' Mᴴ k = (blockDiag' M k)ᴴ :=
  ext fun _ _ => rfl
#align matrix.block_diag'_conj_transpose Matrix.blockDiag'_conjTranspose

section Zero

variable [Zero α] [Zero β]

@[simp]
theorem blockDiag'_zero : blockDiag' (0 : Matrix (Σi, m' i) (Σi, n' i) α) = 0 :=
  rfl
#align matrix.block_diag'_zero Matrix.blockDiag'_zero

@[simp]
theorem blockDiag'_diagonal [DecidableEq o] [∀ i, DecidableEq (m' i)] (d : (Σi, m' i) → α) (k : o) :
    blockDiag' (diagonal d) k = diagonal fun i => d ⟨k, i⟩ :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    -- ⊢ blockDiag' (diagonal d) k i i = diagonal (fun i => d { fst := k, snd := i }) …
    · rw [blockDiag'_apply, diagonal_apply_eq, diagonal_apply_eq]
      -- 🎉 no goals
    · rw [blockDiag'_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt (fun h => ?_) hij)]
      -- ⊢ i = j
      cases h
      -- ⊢ i = i
      rfl
      -- 🎉 no goals
#align matrix.block_diag'_diagonal Matrix.blockDiag'_diagonal

@[simp]
theorem blockDiag'_blockDiagonal' [DecidableEq o] (M : ∀ i, Matrix (m' i) (n' i) α) :
    blockDiag' (blockDiagonal' M) = M :=
  funext fun _ => ext fun _ _ => blockDiagonal'_apply_eq M _ _ _
#align matrix.block_diag'_block_diagonal' Matrix.blockDiag'_blockDiagonal'

theorem blockDiagonal'_injective [DecidableEq o] :
    Function.Injective (blockDiagonal' : (∀ i, Matrix (m' i) (n' i) α) → Matrix _ _ α) :=
  Function.LeftInverse.injective blockDiag'_blockDiagonal'
#align matrix.block_diagonal'_injective Matrix.blockDiagonal'_injective

@[simp]
theorem blockDiagonal'_inj [DecidableEq o] {M N : ∀ i, Matrix (m' i) (n' i) α} :
    blockDiagonal' M = blockDiagonal' N ↔ M = N :=
  blockDiagonal'_injective.eq_iff
#align matrix.block_diagonal'_inj Matrix.blockDiagonal'_inj

@[simp]
theorem blockDiag'_one [DecidableEq o] [∀ i, DecidableEq (m' i)] [One α] :
    blockDiag' (1 : Matrix (Σi, m' i) (Σi, m' i) α) = 1 :=
  funext <| blockDiag'_diagonal _
#align matrix.block_diag'_one Matrix.blockDiag'_one

end Zero

@[simp]
theorem blockDiag'_add [AddZeroClass α] (M N : Matrix (Σi, m' i) (Σi, n' i) α) :
    blockDiag' (M + N) = blockDiag' M + blockDiag' N :=
  rfl
#align matrix.block_diag'_add Matrix.blockDiag'_add

section

variable (m' n' α)

/-- `Matrix.blockDiag'` as an `AddMonoidHom`. -/
@[simps]
def blockDiag'AddMonoidHom [AddZeroClass α] :
    Matrix (Σi, m' i) (Σi, n' i) α →+ ∀ i, Matrix (m' i) (n' i) α where
  toFun := blockDiag'
  map_zero' := blockDiag'_zero
  map_add' := blockDiag'_add
#align matrix.block_diag'_add_monoid_hom Matrix.blockDiag'AddMonoidHom

end

@[simp]
theorem blockDiag'_neg [AddGroup α] (M : Matrix (Σi, m' i) (Σi, n' i) α) :
    blockDiag' (-M) = -blockDiag' M :=
  map_neg (blockDiag'AddMonoidHom m' n' α) M
#align matrix.block_diag'_neg Matrix.blockDiag'_neg

@[simp]
theorem blockDiag'_sub [AddGroup α] (M N : Matrix (Σi, m' i) (Σi, n' i) α) :
    blockDiag' (M - N) = blockDiag' M - blockDiag' N :=
  map_sub (blockDiag'AddMonoidHom m' n' α) M N
#align matrix.block_diag'_sub Matrix.blockDiag'_sub

@[simp]
theorem blockDiag'_smul {R : Type*} [Monoid R] [AddMonoid α] [DistribMulAction R α] (x : R)
    (M : Matrix (Σi, m' i) (Σi, n' i) α) : blockDiag' (x • M) = x • blockDiag' M :=
  rfl
#align matrix.block_diag'_smul Matrix.blockDiag'_smul

end BlockDiag'

section

variable [CommRing R]

theorem toBlock_mul_eq_mul {m n k : Type*} [Fintype n] (p : m → Prop) (q : k → Prop)
    (A : Matrix m n R) (B : Matrix n k R) :
    (A * B).toBlock p q = A.toBlock p ⊤ * B.toBlock ⊤ q := by
  ext i k
  -- ⊢ toBlock (A * B) p q i k = (toBlock A p ⊤ * toBlock B ⊤ q) i k
  simp only [toBlock_apply, mul_apply]
  -- ⊢ ∑ j : n, A (↑i) j * B j ↑k = ∑ x : { a // ⊤ a }, A ↑i ↑x * B ↑x ↑k
  rw [Finset.sum_subtype]
  -- ⊢ ∀ (x : n), x ∈ Finset.univ ↔ ⊤ x
  simp [Pi.top_apply, Prop.top_eq_true]
  -- 🎉 no goals
#align matrix.to_block_mul_eq_mul Matrix.toBlock_mul_eq_mul

theorem toBlock_mul_eq_add {m n k : Type*} [Fintype n] (p : m → Prop) (q : n → Prop)
    [DecidablePred q] (r : k → Prop) (A : Matrix m n R) (B : Matrix n k R) : (A * B).toBlock p r =
    A.toBlock p q * B.toBlock q r + (A.toBlock p fun i => ¬q i) * B.toBlock (fun i => ¬q i) r := by
  classical
    ext i k
    simp only [toBlock_apply, mul_apply, Pi.add_apply]
    exact (Fintype.sum_subtype_add_sum_subtype q fun x => A (↑i) x * B x ↑k).symm
#align matrix.to_block_mul_eq_add Matrix.toBlock_mul_eq_add

end

end Matrix
