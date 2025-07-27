/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Pi
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Nat.Cast.Basic

/-!
# Diagonal matrices

This file defines diagonal matrices and the `AddCommMonoidWithOne` structure on matrices.

## Main definitions

* `Matrix.diagonal d`: matrix with the vector `d` along the diagonal
* `Matrix.diag M`: the diagonal of a square matrix
* `Matrix.instAddCommMonoidWithOne`: matrices are an additive commutative monoid with one
-/

assert_not_exists Algebra Star

universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix

section Diagonal

variable [DecidableEq n]

/-- `diagonal d` is the square matrix such that `(diagonal d) i i = d i` and `(diagonal d) i j = 0`
if `i ≠ j`.

Note that bundled versions exist as:
* `Matrix.diagonalAddMonoidHom`
* `Matrix.diagonalLinearMap`
* `Matrix.diagonalRingHom`
* `Matrix.diagonalAlgHom`
-/
def diagonal [Zero α] (d : n → α) : Matrix n n α :=
  of fun i j => if i = j then d i else 0

-- TODO: set as an equation lemma for `diagonal`, see https://github.com/leanprover-community/mathlib4/pull/3024
theorem diagonal_apply [Zero α] (d : n → α) (i j) : diagonal d i j = if i = j then d i else 0 :=
  rfl

@[simp]
theorem diagonal_apply_eq [Zero α] (d : n → α) (i : n) : (diagonal d) i i = d i := by
  simp [diagonal]

@[simp]
theorem diagonal_apply_ne [Zero α] (d : n → α) {i j : n} (h : i ≠ j) : (diagonal d) i j = 0 := by
  simp [diagonal, h]

theorem diagonal_apply_ne' [Zero α] (d : n → α) {i j : n} (h : j ≠ i) : (diagonal d) i j = 0 :=
  diagonal_apply_ne d h.symm

@[simp]
theorem diagonal_eq_diagonal_iff [Zero α] {d₁ d₂ : n → α} :
    diagonal d₁ = diagonal d₂ ↔ ∀ i, d₁ i = d₂ i :=
  ⟨fun h i => by simpa using congr_arg (fun m : Matrix n n α => m i i) h, fun h => by
    rw [show d₁ = d₂ from funext h]⟩

theorem diagonal_injective [Zero α] : Function.Injective (diagonal : (n → α) → Matrix n n α) :=
  fun d₁ d₂ h => funext fun i => by simpa using Matrix.ext_iff.mpr h i i

@[simp]
theorem diagonal_zero [Zero α] : (diagonal fun _ => 0 : Matrix n n α) = 0 := by
  ext
  simp [diagonal]

@[simp]
theorem diagonal_transpose [Zero α] (v : n → α) : (diagonal v)ᵀ = diagonal v := by
  ext i j
  by_cases h : i = j
  · simp [h, transpose]
  · simp [h, transpose, diagonal_apply_ne' _ h]

@[simp]
theorem diagonal_add [AddZeroClass α] (d₁ d₂ : n → α) :
    diagonal d₁ + diagonal d₂ = diagonal fun i => d₁ i + d₂ i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]
theorem diagonal_smul [Zero α] [SMulZeroClass R α] (r : R) (d : n → α) :
    diagonal (r • d) = r • diagonal d := by
  ext i j
  by_cases h : i = j <;> simp [h]

@[simp]
theorem diagonal_neg [NegZeroClass α] (d : n → α) :
    -diagonal d = diagonal fun i => -d i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]
theorem diagonal_sub [SubNegZeroMonoid α] (d₁ d₂ : n → α) :
    diagonal d₁ - diagonal d₂ = diagonal fun i => d₁ i - d₂ i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

theorem diagonal_mem_matrix_iff [Zero α] {S : Set α} (hS : 0 ∈ S) {d : n → α} :
    Matrix.diagonal d ∈ S.matrix ↔ ∀ i, d i ∈ S := by
  simp only [Set.mem_matrix, diagonal, of_apply]
  conv_lhs => intro _ _; rw[ite_mem]
  simp [hS]

instance [Zero α] [NatCast α] : NatCast (Matrix n n α) where
  natCast m := diagonal fun _ => m

@[norm_cast]
theorem diagonal_natCast [Zero α] [NatCast α] (m : ℕ) : diagonal (fun _ : n => (m : α)) = m := rfl

@[norm_cast]
theorem diagonal_natCast' [Zero α] [NatCast α] (m : ℕ) : diagonal ((m : n → α)) = m := rfl

theorem diagonal_ofNat [Zero α] [NatCast α] (m : ℕ) [m.AtLeastTwo] :
    diagonal (fun _ : n => (ofNat(m) : α)) = OfNat.ofNat m := rfl

theorem diagonal_ofNat' [Zero α] [NatCast α] (m : ℕ) [m.AtLeastTwo] :
    diagonal (ofNat(m) : n → α) = OfNat.ofNat m := rfl

instance [Zero α] [IntCast α] : IntCast (Matrix n n α) where
  intCast m := diagonal fun _ => m

@[norm_cast]
theorem diagonal_intCast [Zero α] [IntCast α] (m : ℤ) : diagonal (fun _ : n => (m : α)) = m := rfl

@[norm_cast]
theorem diagonal_intCast' [Zero α] [IntCast α] (m : ℤ) : diagonal ((m : n → α)) = m := rfl

@[simp]
theorem diagonal_map [Zero α] [Zero β] {f : α → β} (h : f 0 = 0) {d : n → α} :
    (diagonal d).map f = diagonal fun m => f (d m) := by
  ext
  simp only [diagonal_apply, map_apply]
  split_ifs <;> simp [h]

protected theorem map_natCast [AddMonoidWithOne α] [Zero β]
    {f : α → β} (h : f 0 = 0) (d : ℕ) :
    (d : Matrix n n α).map f = diagonal (fun _ => f d) :=
  diagonal_map h

protected theorem map_ofNat [AddMonoidWithOne α] [Zero β]
    {f : α → β} (h : f 0 = 0) (d : ℕ) [d.AtLeastTwo] :
    (ofNat(d) : Matrix n n α).map f = diagonal (fun _ => f (OfNat.ofNat d)) :=
  diagonal_map h

theorem natCast_apply [AddMonoidWithOne α] {i j} {d : ℕ} :
    (d : Matrix n n α) i j = if i = j then d else 0 := by
  rw [Nat.cast_ite, Nat.cast_zero, ← diagonal_natCast, diagonal_apply]

theorem ofNat_apply [AddMonoidWithOne α] {i j} {d : ℕ} [d.AtLeastTwo] :
    (ofNat(d) : Matrix n n α) i j = if i = j then d else 0 :=
  natCast_apply

protected theorem map_intCast [AddGroupWithOne α] [Zero β]
    {f : α → β} (h : f 0 = 0) (d : ℤ) :
    (d : Matrix n n α).map f = diagonal (fun _ => f d) :=
  diagonal_map h

theorem diagonal_unique [Unique m] [DecidableEq m] [Zero α] (d : m → α) :
    diagonal d = of fun _ _ => d default := by
  ext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default, diagonal_apply_eq _ _, of_apply]

@[simp]
theorem col_diagonal [Zero α] (d : n → α) (i) : (diagonal d).col i = Pi.single i (d i) := by
  ext
  simp +contextual [diagonal, Pi.single_apply]

@[simp]
theorem row_diagonal [Zero α] (d : n → α) (j) : (diagonal d).row j = Pi.single j (d j) := by
  ext
  simp +contextual [diagonal, eq_comm, Pi.single_apply]

section One

variable [Zero α] [One α]

instance one : One (Matrix n n α) :=
  ⟨diagonal fun _ => 1⟩

@[simp]
theorem diagonal_one : (diagonal fun _ => 1 : Matrix n n α) = 1 :=
  rfl

theorem one_apply {i j} : (1 : Matrix n n α) i j = if i = j then 1 else 0 :=
  rfl

@[simp]
theorem one_apply_eq (i) : (1 : Matrix n n α) i i = 1 :=
  diagonal_apply_eq _ i

@[simp]
theorem one_apply_ne {i j} : i ≠ j → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne _

theorem one_apply_ne' {i j} : j ≠ i → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne' _

@[simp]
protected theorem map_one [Zero β] [One β] (f : α → β) (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
    (1 : Matrix n n α).map f = (1 : Matrix n n β) := by
  ext
  simp only [one_apply, map_apply]
  split_ifs <;> simp [h₀, h₁]

theorem one_eq_pi_single {i j} : (1 : Matrix n n α) i j = Pi.single (M := fun _ => α) i 1 j := by
  simp only [one_apply, Pi.single_apply, eq_comm]

end One

instance instAddMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (Matrix n n α) where
  natCast_zero := show diagonal _ = _ by
    rw [Nat.cast_zero, diagonal_zero]
  natCast_succ n := show diagonal _ = diagonal _ + _ by
    rw [Nat.cast_succ, ← diagonal_add, diagonal_one]

instance instAddGroupWithOne [AddGroupWithOne α] : AddGroupWithOne (Matrix n n α) where
  intCast_ofNat n := show diagonal _ = diagonal _ by
    rw [Int.cast_natCast]
  intCast_negSucc n := show diagonal _ = -(diagonal _) by
    rw [Int.cast_negSucc, diagonal_neg]
  __ := addGroup
  __ := instAddMonoidWithOne

instance instAddCommMonoidWithOne [AddCommMonoidWithOne α] :
    AddCommMonoidWithOne (Matrix n n α) where
  __ := addCommMonoid
  __ := instAddMonoidWithOne

instance instAddCommGroupWithOne [AddCommGroupWithOne α] :
    AddCommGroupWithOne (Matrix n n α) where
  __ := addCommGroup
  __ := instAddGroupWithOne

end Diagonal

section Diag

/-- The diagonal of a square matrix. -/
def diag (A : Matrix n n α) (i : n) : α :=
  A i i

@[simp]
theorem diag_apply (A : Matrix n n α) (i) : diag A i = A i i :=
  rfl

@[simp]
theorem diag_diagonal [DecidableEq n] [Zero α] (a : n → α) : diag (diagonal a) = a :=
  funext <| @diagonal_apply_eq _ _ _ _ a

@[simp]
theorem diag_transpose (A : Matrix n n α) : diag Aᵀ = diag A :=
  rfl

@[simp]
theorem diag_zero [Zero α] : diag (0 : Matrix n n α) = 0 :=
  rfl

@[simp]
theorem diag_add [Add α] (A B : Matrix n n α) : diag (A + B) = diag A + diag B :=
  rfl

@[simp]
theorem diag_sub [Sub α] (A B : Matrix n n α) : diag (A - B) = diag A - diag B :=
  rfl

@[simp]
theorem diag_neg [Neg α] (A : Matrix n n α) : diag (-A) = -diag A :=
  rfl

@[simp]
theorem diag_smul [SMul R α] (r : R) (A : Matrix n n α) : diag (r • A) = r • diag A :=
  rfl

@[simp]
theorem diag_one [DecidableEq n] [Zero α] [One α] : diag (1 : Matrix n n α) = 1 :=
  diag_diagonal _

theorem diag_map {f : α → β} {A : Matrix n n α} : diag (A.map f) = f ∘ diag A :=
  rfl

end Diag

end Matrix

open Matrix

namespace Matrix

section Transpose

@[simp]
theorem transpose_eq_diagonal [DecidableEq n] [Zero α] {M : Matrix n n α} {v : n → α} :
    Mᵀ = diagonal v ↔ M = diagonal v :=
  (Function.Involutive.eq_iff transpose_transpose).trans <|
    by rw [diagonal_transpose]

@[simp]
theorem transpose_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α)ᵀ = 1 :=
  diagonal_transpose _

@[simp]
theorem transpose_eq_one [DecidableEq n] [Zero α] [One α] {M : Matrix n n α} : Mᵀ = 1 ↔ M = 1 :=
  transpose_eq_diagonal

@[simp]
theorem transpose_natCast [DecidableEq n] [AddMonoidWithOne α] (d : ℕ) :
    (d : Matrix n n α)ᵀ = d :=
  diagonal_transpose _

@[simp]
theorem transpose_eq_natCast [DecidableEq n] [AddMonoidWithOne α] {M : Matrix n n α} {d : ℕ} :
    Mᵀ = d ↔ M = d :=
  transpose_eq_diagonal

@[simp]
theorem transpose_ofNat [DecidableEq n] [AddMonoidWithOne α] (d : ℕ) [d.AtLeastTwo] :
    (ofNat(d) : Matrix n n α)ᵀ = OfNat.ofNat d :=
  transpose_natCast _

@[simp]
theorem transpose_eq_ofNat [DecidableEq n] [AddMonoidWithOne α]
    {M : Matrix n n α} {d : ℕ} [d.AtLeastTwo] :
    Mᵀ = ofNat(d) ↔ M = OfNat.ofNat d :=
  transpose_eq_diagonal

@[simp]
theorem transpose_intCast [DecidableEq n] [AddGroupWithOne α] (d : ℤ) :
    (d : Matrix n n α)ᵀ = d :=
  diagonal_transpose _

@[simp]
theorem transpose_eq_intCast [DecidableEq n] [AddGroupWithOne α]
    {M : Matrix n n α} {d : ℤ} :
    Mᵀ = d ↔ M = d :=
  transpose_eq_diagonal

end Transpose

/-- Given a `(m × m)` diagonal matrix defined by a map `d : m → α`, if the reindexing map `e` is
  injective, then the resulting matrix is again diagonal. -/
theorem submatrix_diagonal [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l → m)
    (he : Function.Injective e) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  ext fun i j => by
    rw [submatrix_apply]
    by_cases h : i = j
    · rw [h, diagonal_apply_eq, diagonal_apply_eq, Function.comp_apply]
    · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (he.ne h)]

theorem submatrix_one [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l → m)
    (he : Function.Injective e) : (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_diagonal _ e he

theorem diag_submatrix (A : Matrix m m α) (e : l → m) : diag (A.submatrix e e) = A.diag ∘ e :=
  rfl

/-! `simp` lemmas for `Matrix.submatrix`s interaction with `Matrix.diagonal`, `1`, and `Matrix.mul`
for when the mappings are bundled. -/


@[simp]
theorem submatrix_diagonal_embedding [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α)
    (e : l ↪ m) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.injective

@[simp]
theorem submatrix_diagonal_equiv [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l ≃ m) :
    (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.injective

@[simp]
theorem submatrix_one_embedding [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ↪ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.injective

@[simp]
theorem submatrix_one_equiv [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ≃ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.injective

end Matrix
