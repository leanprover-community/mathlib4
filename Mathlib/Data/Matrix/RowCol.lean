/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser
-/
import Mathlib.Data.Matrix.ConjTranspose

/-!
# Row and column matrices

This file provides results about row and column matrices

## Main definitions

* `Matrix.row r : Matrix Unit n α`: a matrix with a single row
* `Matrix.col c : Matrix m Unit α`: a matrix with a single column
* `Matrix.updateRow M i r`: update the `i`th row of `M` to `r`
* `Matrix.updateCol M j c`: update the `j`th column of `M` to `c`

-/

variable {l m n o : Type*}

universe u v w
variable {R : Type*} {α : Type v} {β : Type w}

namespace Matrix

/--
`Matrix.col ι u` the matrix with all columns equal to the vector `u`.

To get a column matrix with exactly one column, `Matrix.col (Fin 1) u` is the canonical choice.
-/
def col (ι : Type*) (w : m → α) : Matrix m ι α :=
  of fun x _ => w x

-- TODO: set as an equation lemma for `col`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem col_apply {ι : Type*} (w : m → α) (i) (j : ι) : col ι w i j = w i :=
  rfl

/--
`Matrix.row ι u` the matrix with all rows equal to the vector `u`.

To get a row matrix with exactly one row, `Matrix.row (Fin 1) u` is the canonical choice.
-/
def row (ι : Type*) (v : n → α) : Matrix ι n α :=
  of fun _ y => v y

variable {ι : Type*}

-- TODO: set as an equation lemma for `row`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem row_apply (v : n → α) (i : ι) (j) : row ι v i j = v j :=
  rfl

theorem col_injective [Nonempty ι] : Function.Injective (col ι : (m → α) → Matrix m ι α) := by
  inhabit ι
  exact fun _x _y h => funext fun i => congr_fun₂ h i default

@[simp] theorem col_inj [Nonempty ι] {v w : m → α} : col ι v = col ι w ↔ v = w :=
  col_injective.eq_iff

@[simp] theorem col_zero [Zero α] : col ι (0 : m → α) = 0 := rfl

@[simp] theorem col_eq_zero [Zero α] [Nonempty ι] (v : m → α) : col ι v = 0 ↔ v = 0 := col_inj

@[simp]
theorem col_add [Add α] (v w : m → α) : col ι (v + w) = col ι v + col ι w := by
  ext
  rfl

@[simp]
theorem col_smul [SMul R α] (x : R) (v : m → α) : col ι (x • v) = x • col ι v := by
  ext
  rfl

theorem row_injective [Nonempty ι] : Function.Injective (row ι : (n → α) → Matrix ι n α) := by
  inhabit ι
  exact fun _x _y h => funext fun j => congr_fun₂ h default j

@[simp] theorem row_inj [Nonempty ι] {v w : n → α} : row ι v = row ι w ↔ v = w :=
  row_injective.eq_iff

@[simp] theorem row_zero [Zero α] : row ι (0 : n → α) = 0 := rfl

@[simp] theorem row_eq_zero [Zero α] [Nonempty ι] (v : n → α) : row ι v = 0 ↔ v = 0 := row_inj

@[simp]
theorem row_add [Add α] (v w : m → α) : row ι (v + w) = row ι v + row ι w := by
  ext
  rfl

@[simp]
theorem row_smul [SMul R α] (x : R) (v : m → α) : row ι (x • v) = x • row ι v := by
  ext
  rfl

@[simp]
theorem transpose_col (v : m → α) : (Matrix.col ι v)ᵀ = Matrix.row ι v := by
  ext
  rfl

@[simp]
theorem transpose_row (v : m → α) : (Matrix.row ι v)ᵀ = Matrix.col ι v := by
  ext
  rfl

@[simp]
theorem conjTranspose_col [Star α] (v : m → α) : (col ι v)ᴴ = row ι (star v) := by
  ext
  rfl

@[simp]
theorem conjTranspose_row [Star α] (v : m → α) : (row ι v)ᴴ = col ι (star v) := by
  ext
  rfl

theorem row_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : m → α) :
    Matrix.row ι (v ᵥ* M) = Matrix.row ι v * M := by
  ext
  rfl

theorem col_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : m → α) :
    Matrix.col ι (v ᵥ* M) = (Matrix.row ι v * M)ᵀ := by
  ext
  rfl

theorem col_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : n → α) :
    Matrix.col ι (M *ᵥ v) = M * Matrix.col ι v := by
  ext
  rfl

theorem row_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : n → α) :
    Matrix.row ι (M *ᵥ v) = (M * Matrix.col ι v)ᵀ := by
  ext
  rfl

theorem row_mulVec_eq_const [Fintype m] [NonUnitalNonAssocSemiring α] (v w : m → α) :
    Matrix.row ι v *ᵥ w = Function.const _ (v ⬝ᵥ w) := rfl

theorem mulVec_col_eq_const [Fintype m] [NonUnitalNonAssocSemiring α] (v w : m → α) :
    v ᵥ* Matrix.col ι w = Function.const _ (v ⬝ᵥ w) := rfl

theorem row_mul_col [Fintype m] [Mul α] [AddCommMonoid α] (v w : m → α) :
    row ι v * col ι w = of fun _ _ => v ⬝ᵥ w :=
  rfl

@[simp]
theorem row_mul_col_apply [Fintype m] [Mul α] [AddCommMonoid α] (v w : m → α) (i j) :
    (row ι v * col ι w) i j = v ⬝ᵥ w :=
  rfl

@[simp]
theorem diag_col_mul_row [Mul α] [AddCommMonoid α] [Unique ι] (a b : n → α) :
    diag (col ι a * row ι b) = a * b := by
  ext
  simp [Matrix.mul_apply, col, row]

variable (ι)

theorem vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (w : m → α) (v : n → α) :
    vecMulVec w v = col ι w * row ι v := by
  ext
  simp [vecMulVec, mul_apply]

/-! ### Updating rows and columns -/

/-- Update, i.e. replace the `i`th row of matrix `A` with the values in `b`. -/
def updateRow [DecidableEq m] (M : Matrix m n α) (i : m) (b : n → α) : Matrix m n α :=
  of <| Function.update M i b

/-- Update, i.e. replace the `j`th column of matrix `A` with the values in `b`. -/
def updateCol [DecidableEq n] (M : Matrix m n α) (j : n) (b : m → α) : Matrix m n α :=
  of fun i => Function.update (M i) j (b i)

@[deprecated (since := "2024-12-11")] alias updateColumn := updateCol

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

@[simp]
theorem updateRow_self [DecidableEq m] : updateRow M i b i = b :=
  Function.update_self (β := fun _ => (n → α)) i b M

@[simp]
theorem updateCol_self [DecidableEq n] : updateCol M j c i j = c i :=
  Function.update_self (β := fun _ => α) j (c i) (M i)

@[deprecated (since := "2024-12-11")] alias updateColumn_self := updateCol_self

@[simp]
theorem updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' ≠ i) : updateRow M i b i' = M i' :=
  Function.update_of_ne (β := fun _ => (n → α)) i_ne b M

@[simp]
theorem updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' ≠ j) :
    updateCol M j c i j' = M i j' :=
  Function.update_of_ne (β := fun _ => α) j_ne (c i) (M i)

@[deprecated (since := "2024-12-11")] alias updateColumn_ne := updateCol_ne

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

@[deprecated (since := "2024-12-11")] alias updateColumn_apply := updateCol_apply

@[simp]
theorem updateCol_subsingleton [Subsingleton n] (A : Matrix m n R) (i : n) (b : m → R) :
    A.updateCol i b = (col (Fin 1) b).submatrix id (Function.const n 0) := by
  ext x y
  simp [updateCol_apply, Subsingleton.elim i y]

@[deprecated (since := "2024-12-11")] alias updateColumn_subsingleton := updateCol_subsingleton

@[simp]
theorem updateRow_subsingleton [Subsingleton m] (A : Matrix m n R) (i : m) (b : n → R) :
    A.updateRow i b = (row (Fin 1) b).submatrix (Function.const m 0) id := by
  ext x y
  simp [updateCol_apply, Subsingleton.elim i x]

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

@[deprecated (since := "2024-12-11")] alias map_updateColumn := map_updateCol

theorem updateRow_transpose [DecidableEq n] : updateRow Mᵀ j c = (updateCol M j c)ᵀ := by
  ext
  rw [transpose_apply, updateRow_apply, updateCol_apply]
  rfl

theorem updateCol_transpose [DecidableEq m] : updateCol Mᵀ i b = (updateRow M i b)ᵀ := by
  ext
  rw [transpose_apply, updateRow_apply, updateCol_apply]
  rfl

@[deprecated (since := "2024-12-11")] alias updateColumn_transpose := updateCol_transpose

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

@[deprecated (since := "2024-12-11")] alias updateColumn_conjTranspose := updateCol_conjTranspose

@[simp]
theorem updateRow_eq_self [DecidableEq m] (A : Matrix m n α) (i : m) : A.updateRow i (A i) = A :=
  Function.update_eq_self i A

@[simp]
theorem updateCol_eq_self [DecidableEq n] (A : Matrix m n α) (i : n) :
    (A.updateCol i fun j => A j i) = A :=
  funext fun j => Function.update_eq_self i (A j)

@[deprecated (since := "2024-12-11")] alias updateColumn_eq_self := updateCol_eq_self

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

@[deprecated (since := "2024-12-11")]
alias diagonal_updateColumn_single := diagonal_updateCol_single

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

@[deprecated (since := "2024-12-11")]
alias updateColumn_submatrix_equiv := updateCol_submatrix_equiv

theorem submatrix_updateCol_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n)
    (c : m → α) (e : l ≃ m) (f : o ≃ n) : (A.updateCol j c).submatrix e f =
    updateCol (A.submatrix e f) (f.symm j) fun i => c (e i) :=
  Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateCol_submatrix_equiv A _ _ e f).symm

@[deprecated (since := "2024-12-11")]
alias submatrix_updateColumn_equiv := submatrix_updateCol_equiv

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

@[deprecated (since := "2024-12-11")] alias updateColumn_reindex := updateCol_reindex

theorem reindex_updateCol [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n) (c : m → α)
    (e : m ≃ l) (f : n ≃ o) :
    reindex e f (A.updateCol j c) = updateCol (reindex e f A) (f j) fun i => c (e.symm i) :=
  submatrix_updateCol_equiv _ _ _ _ _

@[deprecated (since := "2024-12-11")] alias reindex_updateColumn := reindex_updateCol

end Matrix
