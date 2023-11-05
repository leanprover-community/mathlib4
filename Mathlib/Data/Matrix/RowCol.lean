/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser
-/
import Mathlib.Data.Matrix.Basic

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

/-- `Matrix.col u` is the column matrix whose entries are given by `u`. -/
def col (w : m → α) : Matrix m Unit α :=
  of fun x _ => w x

-- TODO: set as an equation lemma for `col`, see mathlib4#3024
@[simp]
theorem col_apply (w : m → α) (i j) : col w i j = w i :=
  rfl

/-- `Matrix.row u` is the row matrix whose entries are given by `u`. -/
def row (v : n → α) : Matrix Unit n α :=
  of fun _ y => v y

-- TODO: set as an equation lemma for `row`, see mathlib4#3024
@[simp]
theorem row_apply (v : n → α) (i j) : row v i j = v j :=
  rfl

theorem col_injective : Function.Injective (col : (m → α) → _) :=
  fun _x _y h => funext fun i => congr_fun₂ h i ()

@[simp] theorem col_inj {v w : m → α} : col v = col w ↔ v = w := col_injective.eq_iff

@[simp] theorem col_zero [Zero α] : col (0 : m → α) = 0 := rfl

@[simp] theorem col_eq_zero [Zero α] (v : m → α) : col v = 0 ↔ v = 0 := col_inj

@[simp]
theorem col_add [Add α] (v w : m → α) : col (v + w) = col v + col w := by
  ext
  rfl

@[simp]
theorem col_smul [SMul R α] (x : R) (v : m → α) : col (x • v) = x • col v := by
  ext
  rfl

theorem row_injective : Function.Injective (row : (n → α) → _) :=
  fun _x _y h => funext fun j => congr_fun₂ h () j

@[simp] theorem row_inj {v w : n → α} : row v = row w ↔ v = w := row_injective.eq_iff

@[simp] theorem row_zero [Zero α] : row (0 : n → α) = 0 := rfl

@[simp] theorem row_eq_zero [Zero α] (v : n → α) : row v = 0 ↔ v = 0 := row_inj

@[simp]
theorem row_add [Add α] (v w : m → α) : row (v + w) = row v + row w := by
  ext
  rfl

@[simp]
theorem row_smul [SMul R α] (x : R) (v : m → α) : row (x • v) = x • row v := by
  ext
  rfl

@[simp]
theorem transpose_col (v : m → α) : (Matrix.col v)ᵀ = Matrix.row v := by
  ext
  rfl

@[simp]
theorem transpose_row (v : m → α) : (Matrix.row v)ᵀ = Matrix.col v := by
  ext
  rfl

@[simp]
theorem conjTranspose_col [Star α] (v : m → α) : (col v)ᴴ = row (star v) := by
  ext
  rfl

@[simp]
theorem conjTranspose_row [Star α] (v : m → α) : (row v)ᴴ = col (star v) := by
  ext
  rfl

theorem row_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : m → α) :
    Matrix.row (Matrix.vecMul v M) = Matrix.row v * M := by
  ext
  rfl

theorem col_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : m → α) :
    Matrix.col (Matrix.vecMul v M) = (Matrix.row v * M)ᵀ := by
  ext
  rfl

theorem col_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : n → α) :
    Matrix.col (Matrix.mulVec M v) = M * Matrix.col v := by
  ext
  rfl

theorem row_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : n → α) :
    Matrix.row (Matrix.mulVec M v) = (M * Matrix.col v)ᵀ := by
  ext
  rfl

@[simp]
theorem row_mul_col_apply [Fintype m] [Mul α] [AddCommMonoid α] (v w : m → α) (i j) :
    (row v * col w) i j = v ⬝ᵥ w :=
  rfl

@[simp]
theorem diag_col_mul_row [Mul α] [AddCommMonoid α] (a b : n → α) :
    diag (col a * row b) = a * b := by
  ext
  simp [Matrix.mul_apply, col, row]

theorem vecMulVec_eq [Mul α] [AddCommMonoid α] (w : m → α) (v : n → α) :
    vecMulVec w v = col w * row v := by
  ext
  simp only [vecMulVec, mul_apply, Fintype.univ_punit, Finset.sum_singleton]
  rfl

/-! ### Updating rows and columns -/

/-- Update, i.e. replace the `i`th row of matrix `A` with the values in `b`. -/
def updateRow [DecidableEq m] (M : Matrix m n α) (i : m) (b : n → α) : Matrix m n α :=
  of <| Function.update M i b

/-- Update, i.e. replace the `j`th column of matrix `A` with the values in `b`. -/
def updateColumn [DecidableEq n] (M : Matrix m n α) (j : n) (b : m → α) : Matrix m n α :=
  of fun i => Function.update (M i) j (b i)

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

@[simp]
theorem updateRow_self [DecidableEq m] : updateRow M i b i = b :=
  -- Porting note: (implicit arg) added `(β := _)`
  Function.update_same (β := fun _ => (n → α)) i b M

@[simp]
theorem updateColumn_self [DecidableEq n] : updateColumn M j c i j = c i :=
  -- Porting note: (implicit arg) added `(β := _)`
  Function.update_same (β := fun _ => α) j (c i) (M i)

@[simp]
theorem updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' ≠ i) : updateRow M i b i' = M i' :=
  -- Porting note: (implicit arg) added `(β := _)`
  Function.update_noteq (β := fun _ => (n → α)) i_ne b M

@[simp]
theorem updateColumn_ne [DecidableEq n] {j' : n} (j_ne : j' ≠ j) :
    updateColumn M j c i j' = M i j' :=
  -- Porting note: (implicit arg) added `(β := _)`
  Function.update_noteq (β := fun _ => α) j_ne (c i) (M i)

theorem updateRow_apply [DecidableEq m] {i' : m} :
    updateRow M i b i' j = if i' = i then b j else M i' j := by
  by_cases i' = i
  · rw [h, updateRow_self, if_pos rfl]
  · rw [updateRow_ne h, if_neg h]

theorem updateColumn_apply [DecidableEq n] {j' : n} :
    updateColumn M j c i j' = if j' = j then c i else M i j' := by
  by_cases j' = j
  · rw [h, updateColumn_self, if_pos rfl]
  · rw [updateColumn_ne h, if_neg h]

@[simp]
theorem updateColumn_subsingleton [Subsingleton n] (A : Matrix m n R) (i : n) (b : m → R) :
    A.updateColumn i b = (col b).submatrix id (Function.const n ()) := by
  ext x y
  simp [updateColumn_apply, Subsingleton.elim i y]

@[simp]
theorem updateRow_subsingleton [Subsingleton m] (A : Matrix m n R) (i : m) (b : n → R) :
    A.updateRow i b = (row b).submatrix (Function.const m ()) id := by
  ext x y
  simp [updateColumn_apply, Subsingleton.elim i x]

theorem map_updateRow [DecidableEq m] (f : α → β) :
    map (updateRow M i b) f = updateRow (M.map f) i (f ∘ b) := by
  ext
  rw [updateRow_apply, map_apply, map_apply, updateRow_apply]
  exact apply_ite f _ _ _

theorem map_updateColumn [DecidableEq n] (f : α → β) :
    map (updateColumn M j c) f = updateColumn (M.map f) j (f ∘ c) := by
  ext
  rw [updateColumn_apply, map_apply, map_apply, updateColumn_apply]
  exact apply_ite f _ _ _

theorem updateRow_transpose [DecidableEq n] : updateRow Mᵀ j c = (updateColumn M j c)ᵀ := by
  ext
  rw [transpose_apply, updateRow_apply, updateColumn_apply]
  rfl

theorem updateColumn_transpose [DecidableEq m] : updateColumn Mᵀ i b = (updateRow M i b)ᵀ := by
  ext
  rw [transpose_apply, updateRow_apply, updateColumn_apply]
  rfl

theorem updateRow_conjTranspose [DecidableEq n] [Star α] :
    updateRow Mᴴ j (star c) = (updateColumn M j c)ᴴ := by
  rw [conjTranspose, conjTranspose, transpose_map, transpose_map, updateRow_transpose,
    map_updateColumn]
  rfl

theorem updateColumn_conjTranspose [DecidableEq m] [Star α] :
    updateColumn Mᴴ i (star b) = (updateRow M i b)ᴴ := by
  rw [conjTranspose, conjTranspose, transpose_map, transpose_map, updateColumn_transpose,
    map_updateRow]
  rfl

@[simp]
theorem updateRow_eq_self [DecidableEq m] (A : Matrix m n α) (i : m) : A.updateRow i (A i) = A :=
  Function.update_eq_self i A

@[simp]
theorem updateColumn_eq_self [DecidableEq n] (A : Matrix m n α) (i : n) :
    (A.updateColumn i fun j => A j i) = A :=
  funext fun j => Function.update_eq_self i (A j)

theorem diagonal_updateColumn_single [DecidableEq n] [Zero α] (v : n → α) (i : n) (x : α) :
    (diagonal v).updateColumn i (Pi.single i x) = diagonal (Function.update v i x) := by
  ext j k
  obtain rfl | hjk := eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hji := eq_or_ne j i
    · rw [updateColumn_self, Pi.single_eq_same, Function.update_same]
    · rw [updateColumn_ne hji, diagonal_apply_eq, Function.update_noteq hji]
  · rw [diagonal_apply_ne _ hjk]
    obtain rfl | hki := eq_or_ne k i
    · rw [updateColumn_self, Pi.single_eq_of_ne hjk]
    · rw [updateColumn_ne hki, diagonal_apply_ne _ hjk]

theorem diagonal_updateRow_single [DecidableEq n] [Zero α] (v : n → α) (i : n) (x : α) :
    (diagonal v).updateRow i (Pi.single i x) = diagonal (Function.update v i x) := by
  rw [← diagonal_transpose, updateRow_transpose, diagonal_updateColumn_single, diagonal_transpose]

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

theorem updateColumn_submatrix_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o)
    (c : l → α) (e : l ≃ m) (f : o ≃ n) : updateColumn (A.submatrix e f) j c =
    (A.updateColumn (f j) fun i => c (e.symm i)).submatrix e f := by
  simpa only [← transpose_submatrix, updateRow_transpose] using
    congr_arg transpose (updateRow_submatrix_equiv Aᵀ j c f e)

theorem submatrix_updateColumn_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n)
    (c : m → α) (e : l ≃ m) (f : o ≃ n) : (A.updateColumn j c).submatrix e f =
    updateColumn (A.submatrix e f) (f.symm j) fun i => c (e i) :=
  Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (updateColumn_submatrix_equiv A _ _ e f).symm

/-! `reindex` versions of the above `submatrix` lemmas for convenience. -/


theorem updateRow_reindex [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l) (r : o → α)
    (e : m ≃ l) (f : n ≃ o) :
    updateRow (reindex e f A) i r = reindex e f (A.updateRow (e.symm i) fun j => r (f j)) :=
  updateRow_submatrix_equiv _ _ _ _ _

theorem reindex_updateRow [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m) (r : n → α)
    (e : m ≃ l) (f : n ≃ o) :
    reindex e f (A.updateRow i r) = updateRow (reindex e f A) (e i) fun i => r (f.symm i) :=
  submatrix_updateRow_equiv _ _ _ _ _

theorem updateColumn_reindex [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : o) (c : l → α)
    (e : m ≃ l) (f : n ≃ o) :
    updateColumn (reindex e f A) j c = reindex e f (A.updateColumn (f.symm j) fun i => c (e i)) :=
  updateColumn_submatrix_equiv _ _ _ _ _

theorem reindex_updateColumn [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n) (c : m → α)
    (e : m ≃ l) (f : n ≃ o) :
    reindex e f (A.updateColumn j c) = updateColumn (reindex e f A) (f j) fun i => c (e.symm i) :=
  submatrix_updateColumn_equiv _ _ _ _ _
