/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser
-/
import Mathlib.Data.Matrix.ConjTranspose

/-!
# Row and column matrices

This file provides results about row and column matrices.

## Main definitions

* `Matrix.replicateRow ι r : Matrix ι n α`: the matrix where every row is the vector `r : n → α`
* `Matrix.replicateCol ι c : Matrix m ι α`: the matrix where every column is the vector `c : m → α`
* `Matrix.updateRow M i r`: update the `i`th row of `M` to `r`
* `Matrix.updateCol M j c`: update the `j`th column of `M` to `c`

-/

variable {l m n o : Type*}

universe u v w
variable {R : Type*} {α : Type v} {β : Type w}

namespace Matrix

/--
`Matrix.replicateCol ι u` is the matrix with all columns equal to the vector `u`.

To get a column matrix with exactly one column,
`Matrix.replicateCol (Fin 1) u` is the canonical choice.
-/
def replicateCol (ι : Type*) (w : m → α) : Matrix m ι α :=
  of fun x _ => w x

-- TODO: set as an equation lemma for `replicateCol`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem replicateCol_apply {ι : Type*} (w : m → α) (i) (j : ι) : replicateCol ι w i j = w i :=
  rfl

/--
`Matrix.replicateRow ι u` is the matrix with all rows equal to the vector `u`.

To get a row matrix with exactly one row, `Matrix.replicateRow (Fin 1) u` is the canonical choice.
-/
def replicateRow (ι : Type*) (v : n → α) : Matrix ι n α :=
  of fun _ y => v y

variable {ι : Type*}

-- TODO: set as an equation lemma for `replicateRow`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem replicateRow_apply (v : n → α) (i : ι) (j) : replicateRow ι v i j = v j :=
  rfl

theorem replicateCol_injective [Nonempty ι] :
    Function.Injective (replicateCol ι : (m → α) → Matrix m ι α) := by
  inhabit ι
  exact fun _x _y h => funext fun i => congr_fun₂ h i default

@[deprecated (since := "2025-03-20")] alias col_injective := replicateCol_injective

@[simp] theorem replicateCol_inj [Nonempty ι] {v w : m → α} :
    replicateCol ι v = replicateCol ι w ↔ v = w :=
  replicateCol_injective.eq_iff

@[deprecated (since := "2025-03-20")] alias col_inj := replicateCol_inj

@[simp] theorem replicateCol_zero [Zero α] : replicateCol ι (0 : m → α) = 0 := rfl

@[deprecated (since := "2025-03-20")] alias col_zero := replicateCol_zero

@[simp] theorem replicateCol_eq_zero [Zero α] [Nonempty ι] (v : m → α) :
    replicateCol ι v = 0 ↔ v = 0 :=
  replicateCol_inj

@[deprecated (since := "2025-03-20")] alias col_eq_zero := replicateCol_eq_zero

@[simp]
theorem replicateCol_add [Add α] (v w : m → α) :
    replicateCol ι (v + w) = replicateCol ι v + replicateCol ι w := by
  ext
  rfl

@[deprecated (since := "2025-03-20")] alias col_add := replicateCol_add

@[simp]
theorem replicateCol_smul [SMul R α] (x : R) (v : m → α) :
    replicateCol ι (x • v) = x • replicateCol ι v := by
  ext
  rfl

@[deprecated (since := "2025-03-20")] alias col_smul := replicateCol_smul

theorem replicateRow_injective [Nonempty ι] :
    Function.Injective (replicateRow ι : (n → α) → Matrix ι n α) := by
  inhabit ι
  exact fun _x _y h => funext fun j => congr_fun₂ h default j

@[deprecated (since := "2025-03-20")] alias row_injective := replicateRow_injective

@[simp] theorem replicateRow_inj [Nonempty ι] {v w : n → α} :
    replicateRow ι v = replicateRow ι w ↔ v = w :=
  replicateRow_injective.eq_iff

@[simp] theorem replicateRow_zero [Zero α] : replicateRow ι (0 : n → α) = 0 := rfl

@[deprecated (since := "2025-03-20")] alias row_zero := replicateRow_zero

@[simp] theorem replicateRow_eq_zero [Zero α] [Nonempty ι] (v : n → α) :
    replicateRow ι v = 0 ↔ v = 0 :=
  replicateRow_inj

@[deprecated (since := "2025-03-20")] alias row_eq_zero := replicateRow_eq_zero

@[simp]
theorem replicateRow_add [Add α] (v w : m → α) :
    replicateRow ι (v + w) = replicateRow ι v + replicateRow ι w := by
  ext
  rfl

@[deprecated (since := "2025-03-20")] alias row_add := replicateRow_add

@[simp]
theorem replicateRow_smul [SMul R α] (x : R) (v : m → α) :
    replicateRow ι (x • v) = x • replicateRow ι v := by
  ext
  rfl

@[deprecated (since := "2025-03-20")] alias row_smul := replicateRow_smul

@[simp]
theorem transpose_replicateCol (v : m → α) : (replicateCol ι v)ᵀ = replicateRow ι v := by
  ext
  rfl

@[simp]
theorem transpose_replicateRow (v : m → α) : (replicateRow ι v)ᵀ = replicateCol ι v := by
  ext
  rfl

@[simp]
theorem conjTranspose_replicateCol [Star α] (v : m → α) :
    (replicateCol ι v)ᴴ = replicateRow ι (star v) := by
  ext
  rfl

@[deprecated (since := "2025-03-20")] alias conjTranspose_col := conjTranspose_replicateCol

@[simp]
theorem conjTranspose_replicateRow [Star α] (v : m → α) :
    (replicateRow ι v)ᴴ = replicateCol ι (star v) := by
  ext
  rfl

@[deprecated (since := "2025-03-20")] alias conjTranspose_row := conjTranspose_replicateRow

theorem replicateRow_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : m → α) : replicateRow ι (v ᵥ* M) = replicateRow ι v * M := by
  ext
  rfl

@[deprecated (since := "2025-03-20")] alias row_vecMul := replicateRow_vecMul

theorem replicateCol_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : m → α) : replicateCol ι (v ᵥ* M) = (replicateRow ι v * M)ᵀ := by
  ext
  rfl

@[deprecated (since := "2025-03-20")] alias col_vecMul := replicateCol_vecMul

theorem replicateCol_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : n → α) : replicateCol ι (M *ᵥ v) = M * replicateCol ι v := by
  ext
  rfl

@[deprecated (since := "2025-03-20")] alias col_mulVec := replicateCol_mulVec

theorem replicateRow_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α)
    (v : n → α) : replicateRow ι (M *ᵥ v) = (M * replicateCol ι v)ᵀ := by
  ext
  rfl

@[deprecated (since := "2025-03-20")] alias row_mulVec := replicateRow_mulVec

theorem replicateRow_mulVec_eq_const [Fintype m] [NonUnitalNonAssocSemiring α] (v w : m → α) :
    replicateRow ι v *ᵥ w = Function.const _ (v ⬝ᵥ w) := rfl

@[deprecated (since := "2025-03-20")] alias row_mulVec_eq_const := replicateRow_mulVec_eq_const

theorem mulVec_replicateCol_eq_const [Fintype m] [NonUnitalNonAssocSemiring α] (v w : m → α) :
    v ᵥ* replicateCol ι w = Function.const _ (v ⬝ᵥ w) := rfl

@[deprecated (since := "2025-03-20")] alias mulVec_col_eq_const := mulVec_replicateCol_eq_const

theorem replicateRow_mul_replicateCol [Fintype m] [Mul α] [AddCommMonoid α] (v w : m → α) :
    replicateRow ι v * replicateCol ι w = of fun _ _ => v ⬝ᵥ w :=
  rfl

@[deprecated (since := "2025-03-20")] alias row_mul_col := replicateRow_mul_replicateCol

@[simp]
theorem replicateRow_mul_replicateCol_apply [Fintype m] [Mul α] [AddCommMonoid α] (v w : m → α)
    (i j) : (replicateRow ι v * replicateCol ι w) i j = v ⬝ᵥ w :=
  rfl

@[deprecated (since := "2025-03-20")] alias row_mul_col_apply := replicateRow_mul_replicateCol_apply

@[simp]
theorem diag_replicateCol_mul_replicateRow [Mul α] [AddCommMonoid α] [Unique ι] (a b : n → α) :
    diag (replicateCol ι a * replicateRow ι b) = a * b := by
  ext
  simp [Matrix.mul_apply, replicateCol, replicateRow]

@[deprecated (since := "2025-03-20")] alias diag_col_mul_row := diag_replicateCol_mul_replicateRow

variable (ι)

theorem vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (w : m → α) (v : n → α) :
    vecMulVec w v = replicateCol ι w * replicateRow ι v := by
  ext
  simp [vecMulVec, mul_apply]

/-! ### Updating rows and columns -/

/-- Update, i.e. replace the `i`th row of matrix `A` with the values in `b`. -/
def updateRow [DecidableEq m] (M : Matrix m n α) (i : m) (b : n → α) : Matrix m n α :=
  of <| Function.update M i b

/-- Update, i.e. replace the `j`th column of matrix `A` with the values in `b`. -/
def updateCol [DecidableEq n] (M : Matrix m n α) (j : n) (b : m → α) : Matrix m n α :=
  of fun i => Function.update (M i) j (b i)

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

@[simp]
theorem updateRow_self [DecidableEq m] : updateRow M i b i = b :=
  Function.update_self (β := fun _ => (n → α)) i b M

@[simp]
theorem updateCol_self [DecidableEq n] : updateCol M j c i j = c i :=
  Function.update_self (β := fun _ => α) j (c i) (M i)

@[simp]
theorem updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' ≠ i) : updateRow M i b i' = M i' :=
  Function.update_of_ne (β := fun _ => (n → α)) i_ne b M

@[simp]
theorem updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' ≠ j) :
    updateCol M j c i j' = M i j' :=
  Function.update_of_ne (β := fun _ => α) j_ne (c i) (M i)

theorem updateRow_apply [DecidableEq m] {i' : m} :
    updateRow M i b i' j = if i' = i then b j else M i' j := by
  by_cases h : i' = i
  · rw [h, updateRow_self, if_pos rfl]
  · rw [updateRow_ne h, if_neg h]

theorem updateCol_apply [DecidableEq n] {j' : n} :
    updateCol M j c i j' = if j' = j then c i else M i j' := by
  by_cases h : j' = j
  · rw [h, updateCol_self, if_pos rfl]
  · rw [updateCol_ne h, if_neg h]

@[simp]
theorem updateCol_subsingleton [Subsingleton n] (A : Matrix m n R) (i : n) (b : m → R) :
    A.updateCol i b = (replicateCol (Fin 1) b).submatrix id (Function.const n 0) := by
  ext x y
  simp [Subsingleton.elim i y]

@[simp]
theorem updateRow_subsingleton [Subsingleton m] (A : Matrix m n R) (i : m) (b : n → R) :
    A.updateRow i b = (replicateRow (Fin 1) b).submatrix (Function.const m 0) id := by
  ext x y
  simp [Subsingleton.elim i x]

theorem map_updateRow [DecidableEq m] (f : α → β) :
    map (updateRow M i b) f = updateRow (M.map f) i (f ∘ b) := by
  ext
  rw [updateRow_apply, map_apply, map_apply, updateRow_apply]
  exact apply_ite f _ _ _

theorem map_updateCol [DecidableEq n] (f : α → β) :
    map (updateCol M j c) f = updateCol (M.map f) j (f ∘ c) := by
  ext
  rw [updateCol_apply, map_apply, map_apply, updateCol_apply]
  exact apply_ite f _ _ _

theorem updateRow_transpose [DecidableEq n] : updateRow Mᵀ j c = (updateCol M j c)ᵀ := by
  ext
  rw [transpose_apply, updateRow_apply, updateCol_apply]
  rfl

theorem updateCol_transpose [DecidableEq m] : updateCol Mᵀ i b = (updateRow M i b)ᵀ := by
  ext
  rw [transpose_apply, updateRow_apply, updateCol_apply]
  rfl

theorem updateRow_conjTranspose [DecidableEq n] [Star α] :
    updateRow Mᴴ j (star c) = (updateCol M j c)ᴴ := by
  rw [conjTranspose, conjTranspose, transpose_map, transpose_map, updateRow_transpose,
    map_updateCol]
  rfl

theorem updateCol_conjTranspose [DecidableEq m] [Star α] :
    updateCol Mᴴ i (star b) = (updateRow M i b)ᴴ := by
  rw [conjTranspose, conjTranspose, transpose_map, transpose_map, updateCol_transpose,
    map_updateRow]
  rfl

@[simp]
theorem updateRow_eq_self [DecidableEq m] (A : Matrix m n α) (i : m) : A.updateRow i (A i) = A :=
  Function.update_eq_self i A

@[simp]
theorem updateCol_eq_self [DecidableEq n] (A : Matrix m n α) (i : n) :
    (A.updateCol i fun j => A j i) = A :=
  funext fun j => Function.update_eq_self i (A j)

@[simp]
theorem updateRow_zero_zero [DecidableEq m] [Zero α] (i : m) :
    (0 : Matrix m n α).updateRow i 0 = 0 :=
  updateRow_eq_self _ i

@[simp]
theorem updateCol_zero_zero [DecidableEq n] [Zero α] (i : n) :
    (0 : Matrix m n α).updateCol i 0 = 0 :=
  updateCol_eq_self _ i

theorem diagonal_updateCol_single [DecidableEq n] [Zero α] (v : n → α) (i : n) (x : α) :
    (diagonal v).updateCol i (Pi.single i x) = diagonal (Function.update v i x) := by
  ext j k
  obtain rfl | hjk := eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hji := eq_or_ne j i
    · rw [updateCol_self, Pi.single_eq_same, Function.update_self]
    · rw [updateCol_ne hji, diagonal_apply_eq, Function.update_of_ne hji]
  · rw [diagonal_apply_ne _ hjk]
    obtain rfl | hki := eq_or_ne k i
    · rw [updateCol_self, Pi.single_eq_of_ne hjk]
    · rw [updateCol_ne hki, diagonal_apply_ne _ hjk]

theorem diagonal_updateRow_single [DecidableEq n] [Zero α] (v : n → α) (i : n) (x : α) :
    (diagonal v).updateRow i (Pi.single i x) = diagonal (Function.update v i x) := by
  rw [← diagonal_transpose, updateRow_transpose, diagonal_updateCol_single, diagonal_transpose]

/-! Updating rows and columns commutes in the obvious way with reindexing the matrix. -/


theorem updateRow_submatrix_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l)
    (r : o → α) (e : l ≃ m) (f : o ≃ n) :
    updateRow (A.submatrix e f) i r = (A.updateRow (e i) fun j => r (f.symm j)).submatrix e f := by
  ext i' j
  simp only [submatrix_apply, updateRow_apply, Equiv.apply_eq_iff_eq, Equiv.symm_apply_apply]

theorem submatrix_updateRow_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m)
    (r : n → α) (e : l ≃ m) (f : o ≃ n) :
    (A.updateRow i r).submatrix e f = updateRow (A.submatrix e f) (e.symm i) fun i => r (f i) :=
  Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateRow_submatrix_equiv A _ _ e f).symm

theorem updateCol_submatrix_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o)
    (c : l → α) (e : l ≃ m) (f : o ≃ n) : updateCol (A.submatrix e f) j c =
    (A.updateCol (f j) fun i => c (e.symm i)).submatrix e f := by
  simpa only [← transpose_submatrix, updateRow_transpose] using
    congr_arg transpose (updateRow_submatrix_equiv Aᵀ j c f e)

theorem submatrix_updateCol_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n)
    (c : m → α) (e : l ≃ m) (f : o ≃ n) : (A.updateCol j c).submatrix e f =
    updateCol (A.submatrix e f) (f.symm j) fun i => c (e i) :=
  Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateCol_submatrix_equiv A _ _ e f).symm

/-! `reindex` versions of the above `submatrix` lemmas for convenience. -/


theorem updateRow_reindex [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l) (r : o → α)
    (e : m ≃ l) (f : n ≃ o) :
    updateRow (reindex e f A) i r = reindex e f (A.updateRow (e.symm i) fun j => r (f j)) :=
  updateRow_submatrix_equiv _ _ _ _ _

theorem reindex_updateRow [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m) (r : n → α)
    (e : m ≃ l) (f : n ≃ o) :
    reindex e f (A.updateRow i r) = updateRow (reindex e f A) (e i) fun i => r (f.symm i) :=
  submatrix_updateRow_equiv _ _ _ _ _

theorem updateCol_reindex [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o) (c : l → α)
    (e : m ≃ l) (f : n ≃ o) :
    updateCol (reindex e f A) j c = reindex e f (A.updateCol (f.symm j) fun i => c (e i)) :=
  updateCol_submatrix_equiv _ _ _ _ _

theorem reindex_updateCol [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n) (c : m → α)
    (e : m ≃ l) (f : n ≃ o) :
    reindex e f (A.updateCol j c) = updateCol (reindex e f A) (f j) fun i => c (e.symm i) :=
  submatrix_updateCol_equiv _ _ _ _ _

theorem single_eq_updateRow_zero [DecidableEq m] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α) :
    single i j r = updateRow 0 i (Pi.single j r) :=
  single_eq_of_single_single _ _ _

theorem single_eq_updateCol_zero [DecidableEq m] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α) :
    single i j r = updateCol 0 j (Pi.single i r) := by
  simpa [← updateCol_transpose] using congr($(single_eq_updateRow_zero j i r)ᵀ)

section mul

theorem updateRow_mulVec [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : l) (c : m → α) (v : m → α) :
    A.updateRow i c *ᵥ v = Function.update (A *ᵥ v) i (c ⬝ᵥ v) := by
  ext i'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mulVec]
  · simp [mulVec, hi]

theorem vecMul_updateCol [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (v : m → α) (B : Matrix m n α) (j : n) (r : m → α) :
    v ᵥ* B.updateCol j r = Function.update (v ᵥ* B) j (v ⬝ᵥ r) := by
  ext j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [vecMul]
  · simp [vecMul, hj]

theorem updateRow_mul [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : l) (r : m → α) (B : Matrix m n α) :
    A.updateRow i r * B = (A * B).updateRow i (r ᵥ* B) := by
  ext i' j'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mul_apply, vecMul, dotProduct]
  · simp [mul_apply, hi]

theorem mul_updateCol [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (B : Matrix m n α) (j : n) (c : m → α) :
    A * B.updateCol j c = (A * B).updateCol j (A *ᵥ c) := by
  ext i' j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [mul_apply, mulVec, dotProduct]
  · simp [mul_apply, hj]

open RightActions in
theorem mul_single_eq_updateCol_zero
    [DecidableEq m] [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : m) (j : n) (r : α) :
    A * single i j r = updateCol 0 j (A.col i <• r) := by
  rw [single_eq_updateCol_zero, mul_updateCol, Matrix.mul_zero, mulVec_single]

theorem single_mul_eq_updateRow_zero
    [DecidableEq l] [DecidableEq m] [Fintype m] [NonUnitalNonAssocSemiring α]
    (i : l) (j : m) (r : α) (B : Matrix m n α) :
    single i j r * B = updateRow 0 i (r • B.row j) := by
  rw [single_eq_updateRow_zero, updateRow_mul, Matrix.zero_mul, single_vecMul]

@[simp]
theorem updateRow_zero_mul_updateCol_zero
    [DecidableEq l] [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (i : l) (r : m → α) (j : n) (c : m → α) :
    (0 : Matrix l m α).updateRow i r * (0 : Matrix m n α).updateCol j c = single i j (r ⬝ᵥ c) := by
  rw [updateRow_mul, vecMul_updateCol, mul_updateCol, single_eq_of_single_single, Matrix.zero_mul,
    vecMul_zero, zero_mulVec, updateCol_zero_zero, updateRow, ← Pi.single, ← Pi.single]

end mul

end Matrix
