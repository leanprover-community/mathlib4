/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Anne Baanen
-/
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.RowCol
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Alternating.Basic

#align_import linear_algebra.matrix.determinant from "leanprover-community/mathlib"@"c3019c79074b0619edb4b27553a91b2e82242395"

/-!
# Determinant of a matrix

This file defines the determinant of a matrix, `Matrix.det`, and its essential properties.

## Main definitions

 - `Matrix.det`: the determinant of a square matrix, as a sum over permutations
 - `Matrix.detRowAlternating`: the determinant, as an `AlternatingMap` in the rows of the matrix

## Main results

 - `det_mul`: the determinant of `A * B` is the product of determinants
 - `det_zero_of_row_eq`: the determinant is zero if there is a repeated row
 - `det_block_diagonal`: the determinant of a block diagonal matrix is a product
   of the blocks' determinants

## Implementation notes

It is possible to configure `simp` to compute determinants. See the file
`test/matrix.lean` for some examples.

-/


universe u v w z

open Equiv Equiv.Perm Finset Function

namespace Matrix

open Matrix

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
variable {R : Type v} [CommRing R]

local notation "ε " σ:arg => ((sign σ : ℤ) : R)

/-- `det` is an `AlternatingMap` in the rows of the matrix. -/
def detRowAlternating : (n → R) [⋀^n]→ₗ[R] R :=
  MultilinearMap.alternatization ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj)
#align matrix.det_row_alternating Matrix.detRowAlternating

/-- The determinant of a matrix given by the Leibniz formula. -/
abbrev det (M : Matrix n n R) : R :=
  detRowAlternating M
#align matrix.det Matrix.det

theorem det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i :=
  MultilinearMap.alternatization_apply _ M
#align matrix.det_apply Matrix.det_apply

-- This is what the old definition was. We use it to avoid having to change the old proofs below
theorem det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n, ε σ * ∏ i, M (σ i) i := by
  simp [det_apply, Units.smul_def]
#align matrix.det_apply' Matrix.det_apply'

@[simp]
theorem det_diagonal {d : n → R} : det (diagonal d) = ∏ i, d i := by
  rw [det_apply']
  refine (Finset.sum_eq_single 1 ?_ ?_).trans ?_
  · rintro σ - h2
    cases' not_forall.1 (mt Equiv.ext h2) with x h3
    convert mul_zero (ε σ)
    apply Finset.prod_eq_zero (mem_univ x)
    exact if_neg h3
  · simp
  · simp
#align matrix.det_diagonal Matrix.det_diagonal

-- @[simp] -- Porting note (#10618): simp can prove this
theorem det_zero (_ : Nonempty n) : det (0 : Matrix n n R) = 0 :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_zero
#align matrix.det_zero Matrix.det_zero

@[simp]
theorem det_one : det (1 : Matrix n n R) = 1 := by rw [← diagonal_one]; simp [-diagonal_one]
#align matrix.det_one Matrix.det_one

theorem det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A = 1 := by simp [det_apply]
#align matrix.det_is_empty Matrix.det_isEmpty

@[simp]
theorem coe_det_isEmpty [IsEmpty n] : (det : Matrix n n R → R) = Function.const _ 1 := by
  ext
  exact det_isEmpty
#align matrix.coe_det_is_empty Matrix.coe_det_isEmpty

theorem det_eq_one_of_card_eq_zero {A : Matrix n n R} (h : Fintype.card n = 0) : det A = 1 :=
  haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h
  det_isEmpty
#align matrix.det_eq_one_of_card_eq_zero Matrix.det_eq_one_of_card_eq_zero

/-- If `n` has only one element, the determinant of an `n` by `n` matrix is just that element.
Although `Unique` implies `DecidableEq` and `Fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
theorem det_unique {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) :
    det A = A default default := by simp [det_apply, univ_unique]
#align matrix.det_unique Matrix.det_unique

theorem det_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) :
    det A = A k k := by
  have := uniqueOfSubsingleton k
  convert det_unique A
#align matrix.det_eq_elem_of_subsingleton Matrix.det_eq_elem_of_subsingleton

theorem det_eq_elem_of_card_eq_one {A : Matrix n n R} (h : Fintype.card n = 1) (k : n) :
    det A = A k k :=
  haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  det_eq_elem_of_subsingleton _ _
#align matrix.det_eq_elem_of_card_eq_one Matrix.det_eq_elem_of_card_eq_one

theorem det_mul_aux {M N : Matrix n n R} {p : n → n} (H : ¬Bijective p) :
    (∑ σ : Perm n, ε σ * ∏ x, M (σ x) (p x) * N (p x) x) = 0 := by
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
    rw [← Finite.injective_iff_bijective, Injective] at H
    push_neg at H
    exact H
  exact
    sum_involution (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => by
        have : (∏ x, M (σ x) (p x)) = ∏ x, M ((σ * Equiv.swap i j) x) (p x) :=
          Fintype.prod_equiv (swap i j) _ _ (by simp [apply_swap_eq_self hpij])
        simp [this, sign_swap hij, -sign_swap', prod_mul_distrib])
      (fun σ _ _ => (not_congr mul_swap_eq_iff).mpr hij) (fun _ _ => mem_univ _) fun σ _ =>
      mul_swap_involutive i j σ
#align matrix.det_mul_aux Matrix.det_mul_aux

@[simp]
theorem det_mul (M N : Matrix n n R) : det (M * N) = det M * det N :=
  calc
    det (M * N) = ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ =
        ∑ p ∈ (@univ (n → n) _).filter Bijective,
          ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i :=
      (Eq.symm <|
        sum_subset (filter_subset _ _) fun f _ hbij =>
          det_mul_aux <| by simpa only [true_and_iff, mem_filter, mem_univ] using hbij)
    _ = ∑ τ : Perm n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i :=
      sum_bij (fun p h ↦ Equiv.ofBijective p (mem_filter.1 h).2) (fun _ _ ↦ mem_univ _)
        (fun _ _ _ _ h ↦ by injection h)
        (fun b _ ↦ ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, coe_fn_injective rfl⟩) fun _ _ ↦ rfl
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * ε τ * ∏ j, M (τ j) (σ j) := by
      simp only [mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i :=
      (sum_congr rfl fun σ _ =>
        Fintype.sum_equiv (Equiv.mulRight σ⁻¹) _ _ fun τ => by
          have : (∏ j, M (τ j) (σ j)) = ∏ j, M ((τ * σ⁻¹) j) j := by
            rw [← (σ⁻¹ : _ ≃ _).prod_comp]
            simp only [Equiv.Perm.coe_mul, apply_inv_self, Function.comp_apply]
          have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
            calc
              ε σ * ε (τ * σ⁻¹) = ε (τ * σ⁻¹ * σ) := by
                rw [mul_comm, sign_mul (τ * σ⁻¹)]
                simp only [Int.cast_mul, Units.val_mul]
              _ = ε τ := by simp only [inv_mul_cancel_right]

          simp_rw [Equiv.coe_mulRight, h]
          simp only [this])
    _ = det M * det N := by
      simp only [det_apply', Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
#align matrix.det_mul Matrix.det_mul

/-- The determinant of a matrix, as a monoid homomorphism. -/
def detMonoidHom : Matrix n n R →* R where
  toFun := det
  map_one' := det_one
  map_mul' := det_mul
#align matrix.det_monoid_hom Matrix.detMonoidHom

@[simp]
theorem coe_detMonoidHom : (detMonoidHom : Matrix n n R → R) = det :=
  rfl
#align matrix.coe_det_monoid_hom Matrix.coe_detMonoidHom

/-- On square matrices, `mul_comm` applies under `det`. -/
theorem det_mul_comm (M N : Matrix m m R) : det (M * N) = det (N * M) := by
  rw [det_mul, det_mul, mul_comm]
#align matrix.det_mul_comm Matrix.det_mul_comm

/-- On square matrices, `mul_left_comm` applies under `det`. -/
theorem det_mul_left_comm (M N P : Matrix m m R) : det (M * (N * P)) = det (N * (M * P)) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, det_mul, det_mul_comm M N, ← det_mul]
#align matrix.det_mul_left_comm Matrix.det_mul_left_comm

/-- On square matrices, `mul_right_comm` applies under `det`. -/
theorem det_mul_right_comm (M N P : Matrix m m R) : det (M * N * P) = det (M * P * N) := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, det_mul, det_mul_comm N P, ← det_mul]
#align matrix.det_mul_right_comm Matrix.det_mul_right_comm

-- TODO(mathlib4#6607): fix elaboration so that the ascription isn't needed
theorem det_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    det ((M : Matrix _ _ _) * N * (↑M⁻¹ : Matrix _ _ _)) = det N := by
  rw [det_mul_right_comm, Units.mul_inv, one_mul]
#align matrix.det_units_conj Matrix.det_units_conj

-- TODO(mathlib4#6607): fix elaboration so that the ascription isn't needed
theorem det_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    det ((↑M⁻¹ : Matrix _ _ _) * N * (↑M : Matrix _ _ _)) = det N :=
  det_units_conj M⁻¹ N
#align matrix.det_units_conj' Matrix.det_units_conj'

/-- Transposing a matrix preserves the determinant. -/
@[simp]
theorem det_transpose (M : Matrix n n R) : Mᵀ.det = M.det := by
  rw [det_apply', det_apply']
  refine Fintype.sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  rw [sign_inv]
  congr 1
  apply Fintype.prod_equiv σ
  intros
  simp
#align matrix.det_transpose Matrix.det_transpose

/-- Permuting the columns changes the sign of the determinant. -/
theorem det_permute (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix σ id).det = Perm.sign σ * M.det :=
  ((detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_perm M σ).trans (by simp [Units.smul_def])
#align matrix.det_permute Matrix.det_permute

/-- Permuting the rows changes the sign of the determinant. -/
theorem det_permute' (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix id σ).det = Perm.sign σ * M.det := by
  rw [← det_transpose, transpose_submatrix, det_permute, det_transpose]

/-- Permuting rows and columns with the same equivalence has no effect. -/
@[simp]
theorem det_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m R) :
    det (A.submatrix e e) = det A := by
  rw [det_apply', det_apply']
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  rw [Equiv.Perm.sign_permCongr e σ]
  congr 1
  apply Fintype.prod_equiv e
  intro i
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, submatrix_apply]
#align matrix.det_submatrix_equiv_self Matrix.det_submatrix_equiv_self

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`; this one is unsuitable because
`Matrix.reindex_apply` unfolds `reindex` first.
-/
theorem det_reindex_self (e : m ≃ n) (A : Matrix m m R) : det (reindex e e A) = det A :=
  det_submatrix_equiv_self e.symm A
#align matrix.det_reindex_self Matrix.det_reindex_self

theorem det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^ Fintype.card n * det A :=
  calc
    det (c • A) = det ((diagonal fun _ => c) * A) := by rw [smul_eq_diagonal_mul]
    _ = det (diagonal fun _ => c) * det A := det_mul _ _
    _ = c ^ Fintype.card n * det A := by simp [card_univ]
#align matrix.det_smul Matrix.det_smul

@[simp]
theorem det_smul_of_tower {α} [Monoid α] [DistribMulAction α R] [IsScalarTower α R R]
    [SMulCommClass α R R] (c : α) (A : Matrix n n R) :
    det (c • A) = c ^ Fintype.card n • det A := by
  rw [← smul_one_smul R c A, det_smul, smul_pow, one_pow, smul_mul_assoc, one_mul]
#align matrix.det_smul_of_tower Matrix.det_smul_of_tower

theorem det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.card n * det A := by
  rw [← det_smul, neg_one_smul]
#align matrix.det_neg Matrix.det_neg

/-- A variant of `Matrix.det_neg` with scalar multiplication by `Units ℤ` instead of multiplication
by `R`. -/
theorem det_neg_eq_smul (A : Matrix n n R) :
    det (-A) = (-1 : Units ℤ) ^ Fintype.card n • det A := by
  rw [← det_smul_of_tower, Units.neg_smul, one_smul]
#align matrix.det_neg_eq_smul Matrix.det_neg_eq_smul

/-- Multiplying each row by a fixed `v i` multiplies the determinant by
the product of the `v`s. -/
theorem det_mul_row (v : n → R) (A : Matrix n n R) :
    det (of fun i j => v j * A i j) = (∏ i, v i) * det A :=
  calc
    det (of fun i j => v j * A i j) = det (A * diagonal v) :=
      congr_arg det <| by
        ext
        simp [mul_comm]
    _ = (∏ i, v i) * det A := by rw [det_mul, det_diagonal, mul_comm]
#align matrix.det_mul_row Matrix.det_mul_row

/-- Multiplying each column by a fixed `v j` multiplies the determinant by
the product of the `v`s. -/
theorem det_mul_column (v : n → R) (A : Matrix n n R) :
    det (of fun i j => v i * A i j) = (∏ i, v i) * det A :=
  MultilinearMap.map_smul_univ _ v A
#align matrix.det_mul_column Matrix.det_mul_column

@[simp]
theorem det_pow (M : Matrix m m R) (n : ℕ) : det (M ^ n) = det M ^ n :=
  (detMonoidHom : Matrix m m R →* R).map_pow M n
#align matrix.det_pow Matrix.det_pow

section HomMap

variable {S : Type w} [CommRing S]

theorem _root_.RingHom.map_det (f : R →+* S) (M : Matrix n n R) :
    f M.det = Matrix.det (f.mapMatrix M) := by
  simp [Matrix.det_apply', map_sum f, map_prod f]
#align ring_hom.map_det RingHom.map_det

theorem _root_.RingEquiv.map_det (f : R ≃+* S) (M : Matrix n n R) :
    f M.det = Matrix.det (f.mapMatrix M) :=
  f.toRingHom.map_det _
#align ring_equiv.map_det RingEquiv.map_det

theorem _root_.AlgHom.map_det [Algebra R S] {T : Type z} [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
    (M : Matrix n n S) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toRingHom.map_det _
#align alg_hom.map_det AlgHom.map_det

theorem _root_.AlgEquiv.map_det [Algebra R S] {T : Type z} [CommRing T] [Algebra R T]
    (f : S ≃ₐ[R] T) (M : Matrix n n S) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toAlgHom.map_det _
#align alg_equiv.map_det AlgEquiv.map_det

end HomMap

@[simp]
theorem det_conjTranspose [StarRing R] (M : Matrix m m R) : det Mᴴ = star (det M) :=
  ((starRingEnd R).map_det _).symm.trans <| congr_arg star M.det_transpose
#align matrix.det_conj_transpose Matrix.det_conjTranspose

section DetZero

/-!
### `det_zero` section

Prove that a matrix with a repeated column has determinant equal to zero.
-/


theorem det_eq_zero_of_row_eq_zero {A : Matrix n n R} (i : n) (h : ∀ j, A i j = 0) : det A = 0 :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_coord_zero i (funext h)
#align matrix.det_eq_zero_of_row_eq_zero Matrix.det_eq_zero_of_row_eq_zero

theorem det_eq_zero_of_column_eq_zero {A : Matrix n n R} (j : n) (h : ∀ i, A i j = 0) :
    det A = 0 := by
  rw [← det_transpose]
  exact det_eq_zero_of_row_eq_zero j h
#align matrix.det_eq_zero_of_column_eq_zero Matrix.det_eq_zero_of_column_eq_zero

variable {M : Matrix n n R} {i j : n}

/-- If a matrix has a repeated row, the determinant will be zero. -/
theorem det_zero_of_row_eq (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_eq_zero_of_eq M hij i_ne_j
#align matrix.det_zero_of_row_eq Matrix.det_zero_of_row_eq

/-- If a matrix has a repeated column, the determinant will be zero. -/
theorem det_zero_of_column_eq (i_ne_j : i ≠ j) (hij : ∀ k, M k i = M k j) : M.det = 0 := by
  rw [← det_transpose, det_zero_of_row_eq i_ne_j]
  exact funext hij
#align matrix.det_zero_of_column_eq Matrix.det_zero_of_column_eq

/-- If we repeat a row of a matrix, we get a matrix of determinant zero. -/
theorem det_updateRow_eq_zero (h : i ≠ j) :
    (M.updateRow j (M i)).det = 0 := det_zero_of_row_eq h (by simp [h])

/-- If we repeat a column of a matrix, we get a matrix of determinant zero. -/
theorem det_updateColumn_eq_zero (h : i ≠ j) :
    (M.updateColumn j (fun k ↦ M k i)).det = 0 := det_zero_of_column_eq h (by simp [h])

end DetZero

theorem det_updateRow_add (M : Matrix n n R) (j : n) (u v : n → R) :
    det (updateRow M j <| u + v) = det (updateRow M j u) + det (updateRow M j v) :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_add M j u v
#align matrix.det_update_row_add Matrix.det_updateRow_add

theorem det_updateColumn_add (M : Matrix n n R) (j : n) (u v : n → R) :
    det (updateColumn M j <| u + v) = det (updateColumn M j u) + det (updateColumn M j v) := by
  rw [← det_transpose, ← updateRow_transpose, det_updateRow_add]
  simp [updateRow_transpose, det_transpose]
#align matrix.det_update_column_add Matrix.det_updateColumn_add

theorem det_updateRow_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateRow M j <| s • u) = s * det (updateRow M j u) :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_smul M j s u
#align matrix.det_update_row_smul Matrix.det_updateRow_smul

theorem det_updateColumn_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateColumn M j <| s • u) = s * det (updateColumn M j u) := by
  rw [← det_transpose, ← updateRow_transpose, det_updateRow_smul]
  simp [updateRow_transpose, det_transpose]
#align matrix.det_update_column_smul Matrix.det_updateColumn_smul

theorem det_updateRow_smul' (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateRow (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateRow M j u) :=
  MultilinearMap.map_update_smul _ M j s u
#align matrix.det_update_row_smul' Matrix.det_updateRow_smul'

theorem det_updateColumn_smul' (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateColumn (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateColumn M j u) := by
  rw [← det_transpose, ← updateRow_transpose, transpose_smul, det_updateRow_smul']
  simp [updateRow_transpose, det_transpose]
#align matrix.det_update_column_smul' Matrix.det_updateColumn_smul'

theorem det_updateRow_sum_aux (M : Matrix n n R) {j : n} (s : Finset n) (hj : j ∉ s) (c : n → R)
    (a : R) :
    (M.updateRow j (a • M j + ∑ k ∈ s, (c k) • M k)).det = a • M.det := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, add_zero, smul_eq_mul, det_updateRow_smul, updateRow_eq_self]
  | @insert k _ hk h_ind =>
      have h : k ≠ j := fun h ↦ (h ▸ hj) (Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hk, add_comm ((c k) • M k), ← add_assoc, det_updateRow_add,
        det_updateRow_smul, det_updateRow_eq_zero h, mul_zero, add_zero, h_ind]
      exact fun h ↦ hj (Finset.mem_insert_of_mem h)

/-- If we replace a row of a matrix by a linear combination of its rows, then the determinant is
multiplied by the coefficient of that row. -/
theorem det_updateRow_sum (A : Matrix n n R) (j : n) (c : n → R) :
    (A.updateRow j (∑ k, (c k) • A k)).det = (c j) • A.det := by
  convert det_updateRow_sum_aux A (Finset.univ.erase j) (Finset.univ.not_mem_erase j) c (c j)
  rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ j)]

/-- If we replace a column of a matrix by a linear combination of its columns, then the determinant
is multiplied by the coefficient of that column. -/
theorem det_updateColumn_sum (A : Matrix n n R) (j : n) (c : n → R) :
    (A.updateColumn j (fun k ↦ ∑ i, (c i) • A k i)).det = (c j) • A.det := by
  rw [← det_transpose, ← updateRow_transpose, ← det_transpose A]
  convert det_updateRow_sum A.transpose j c
  simp only [smul_eq_mul, Finset.sum_apply, Pi.smul_apply, transpose_apply]

section DetEq

/-! ### `det_eq` section

Lemmas showing the determinant is invariant under a variety of operations.
-/


theorem det_eq_of_eq_mul_det_one {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1)
    (hA : A = B * C) : det A = det B :=
  calc
    det A = det (B * C) := congr_arg _ hA
    _ = det B * det C := det_mul _ _
    _ = det B := by rw [hC, mul_one]
#align matrix.det_eq_of_eq_mul_det_one Matrix.det_eq_of_eq_mul_det_one

theorem det_eq_of_eq_det_one_mul {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1)
    (hA : A = C * B) : det A = det B :=
  calc
    det A = det (C * B) := congr_arg _ hA
    _ = det C * det B := det_mul _ _
    _ = det B := by rw [hC, one_mul]
#align matrix.det_eq_of_eq_det_one_mul Matrix.det_eq_of_eq_det_one_mul

theorem det_updateRow_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    det (updateRow A i (A i + A j)) = det A := by
  simp [det_updateRow_add,
    det_zero_of_row_eq hij (updateRow_self.trans (updateRow_ne hij.symm).symm)]
#align matrix.det_update_row_add_self Matrix.det_updateRow_add_self

theorem det_updateColumn_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    det (updateColumn A i fun k => A k i + A k j) = det A := by
  rw [← det_transpose, ← updateRow_transpose, ← det_transpose A]
  exact det_updateRow_add_self Aᵀ hij
#align matrix.det_update_column_add_self Matrix.det_updateColumn_add_self

theorem det_updateRow_add_smul_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
    det (updateRow A i (A i + c • A j)) = det A := by
  simp [det_updateRow_add, det_updateRow_smul,
    det_zero_of_row_eq hij (updateRow_self.trans (updateRow_ne hij.symm).symm)]
#align matrix.det_update_row_add_smul_self Matrix.det_updateRow_add_smul_self

theorem det_updateColumn_add_smul_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
    det (updateColumn A i fun k => A k i + c • A k j) = det A := by
  rw [← det_transpose, ← updateRow_transpose, ← det_transpose A]
  exact det_updateRow_add_smul_self Aᵀ hij c
#align matrix.det_update_column_add_smul_self Matrix.det_updateColumn_add_smul_self

theorem det_eq_of_forall_row_eq_smul_add_const_aux {A B : Matrix n n R} {s : Finset n} :
    ∀ (c : n → R) (_ : ∀ i, i ∉ s → c i = 0) (k : n) (_ : k ∉ s)
      (_: ∀ i j, A i j = B i j + c i * B k j), det A = det B := by
  induction s using Finset.induction_on generalizing B with
  | empty =>
    rintro c hs k - A_eq
    have : ∀ i, c i = 0 := by
      intro i
      specialize hs i
      contrapose! hs
      simp [hs]
    congr
    ext i j
    rw [A_eq, this, zero_mul, add_zero]
  | @insert i s _hi ih =>
    intro c hs k hk A_eq
    have hAi : A i = B i + c i • B k := funext (A_eq i)
    rw [@ih (updateRow B i (A i)) (Function.update c i 0), hAi, det_updateRow_add_smul_self]
    · exact mt (fun h => show k ∈ insert i s from h ▸ Finset.mem_insert_self _ _) hk
    · intro i' hi'
      rw [Function.update_apply]
      split_ifs with hi'i
      · rfl
      · exact hs i' fun h => hi' ((Finset.mem_insert.mp h).resolve_left hi'i)
    · exact k
    · exact fun h => hk (Finset.mem_insert_of_mem h)
    · intro i' j'
      rw [updateRow_apply, Function.update_apply]
      split_ifs with hi'i
      · simp [hi'i]
      rw [A_eq, updateRow_ne fun h : k = i => hk <| h ▸ Finset.mem_insert_self k s]
#align matrix.det_eq_of_forall_row_eq_smul_add_const_aux Matrix.det_eq_of_forall_row_eq_smul_add_const_aux

/-- If you add multiples of row `B k` to other rows, the determinant doesn't change. -/
theorem det_eq_of_forall_row_eq_smul_add_const {A B : Matrix n n R} (c : n → R) (k : n)
    (hk : c k = 0) (A_eq : ∀ i j, A i j = B i j + c i * B k j) : det A = det B :=
  det_eq_of_forall_row_eq_smul_add_const_aux c
    (fun i =>
      not_imp_comm.mp fun hi =>
        Finset.mem_erase.mpr
          ⟨mt (fun h : i = k => show c i = 0 from h.symm ▸ hk) hi, Finset.mem_univ i⟩)
    k (Finset.not_mem_erase k Finset.univ) A_eq
#align matrix.det_eq_of_forall_row_eq_smul_add_const Matrix.det_eq_of_forall_row_eq_smul_add_const

theorem det_eq_of_forall_row_eq_smul_add_pred_aux {n : ℕ} (k : Fin (n + 1)) :
    ∀ (c : Fin n → R) (_hc : ∀ i : Fin n, k < i.succ → c i = 0)
      {M N : Matrix (Fin n.succ) (Fin n.succ) R} (_h0 : ∀ j, M 0 j = N 0 j)
      (_hsucc : ∀ (i : Fin n) (j), M i.succ j = N i.succ j + c i * M (Fin.castSucc i) j),
      det M = det N := by
  refine Fin.induction ?_ (fun k ih => ?_) k <;> intro c hc M N h0 hsucc
  · congr
    ext i j
    refine Fin.cases (h0 j) (fun i => ?_) i
    rw [hsucc, hc i (Fin.succ_pos _), zero_mul, add_zero]
  set M' := updateRow M k.succ (N k.succ) with hM'
  have hM : M = updateRow M' k.succ (M' k.succ + c k • M (Fin.castSucc k)) := by
    ext i j
    by_cases hi : i = k.succ
    · simp [hi, hM', hsucc, updateRow_self]
    rw [updateRow_ne hi, hM', updateRow_ne hi]
  have k_ne_succ : (Fin.castSucc k) ≠ k.succ := (Fin.castSucc_lt_succ k).ne
  have M_k : M (Fin.castSucc k) = M' (Fin.castSucc k) := (updateRow_ne k_ne_succ).symm
  rw [hM, M_k, det_updateRow_add_smul_self M' k_ne_succ.symm, ih (Function.update c k 0)]
  · intro i hi
    rw [Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ, Nat.lt_succ_iff] at hi
    rw [Function.update_apply]
    split_ifs with hik
    · rfl
    exact hc _ (Fin.succ_lt_succ_iff.mpr (lt_of_le_of_ne hi (Ne.symm hik)))
  · rwa [hM', updateRow_ne (Fin.succ_ne_zero _).symm]
  intro i j
  rw [Function.update_apply]
  split_ifs with hik
  · rw [zero_mul, add_zero, hM', hik, updateRow_self]
  rw [hM', updateRow_ne ((Fin.succ_injective _).ne hik), hsucc]
  by_cases hik2 : k < i
  · simp [hc i (Fin.succ_lt_succ_iff.mpr hik2)]
  rw [updateRow_ne]
  apply ne_of_lt
  rwa [Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ, Nat.lt_succ_iff, ← not_lt]
#align matrix.det_eq_of_forall_row_eq_smul_add_pred_aux Matrix.det_eq_of_forall_row_eq_smul_add_pred_aux

/-- If you add multiples of previous rows to the next row, the determinant doesn't change. -/
theorem det_eq_of_forall_row_eq_smul_add_pred {n : ℕ} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (c : Fin n → R) (A_zero : ∀ j, A 0 j = B 0 j)
    (A_succ : ∀ (i : Fin n) (j), A i.succ j = B i.succ j + c i * A (Fin.castSucc i) j) :
    det A = det B :=
  det_eq_of_forall_row_eq_smul_add_pred_aux (Fin.last _) c
    (fun _ hi => absurd hi (not_lt_of_ge (Fin.le_last _))) A_zero A_succ
#align matrix.det_eq_of_forall_row_eq_smul_add_pred Matrix.det_eq_of_forall_row_eq_smul_add_pred

/-- If you add multiples of previous columns to the next columns, the determinant doesn't change. -/
theorem det_eq_of_forall_col_eq_smul_add_pred {n : ℕ} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (c : Fin n → R) (A_zero : ∀ i, A i 0 = B i 0)
    (A_succ : ∀ (i) (j : Fin n), A i j.succ = B i j.succ + c j * A i (Fin.castSucc j)) :
    det A = det B := by
  rw [← det_transpose A, ← det_transpose B]
  exact det_eq_of_forall_row_eq_smul_add_pred c A_zero fun i j => A_succ j i
#align matrix.det_eq_of_forall_col_eq_smul_add_pred Matrix.det_eq_of_forall_col_eq_smul_add_pred

end DetEq

@[simp]
theorem det_blockDiagonal {o : Type*} [Fintype o] [DecidableEq o] (M : o → Matrix n n R) :
    (blockDiagonal M).det = ∏ k, (M k).det := by
  -- Rewrite the determinants as a sum over permutations.
  simp_rw [det_apply']
  -- The right hand side is a product of sums, rewrite it as a sum of products.
  rw [Finset.prod_sum]
  simp_rw [Finset.prod_attach_univ, Finset.univ_pi_univ]
  -- We claim that the only permutations contributing to the sum are those that
  -- preserve their second component.
  let preserving_snd : Finset (Equiv.Perm (n × o)) :=
    Finset.univ.filter fun σ => ∀ x, (σ x).snd = x.snd
  have mem_preserving_snd :
    ∀ {σ : Equiv.Perm (n × o)}, σ ∈ preserving_snd ↔ ∀ x, (σ x).snd = x.snd := fun {σ} =>
    Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  rw [← Finset.sum_subset (Finset.subset_univ preserving_snd) _]
  -- And that these are in bijection with `o → Equiv.Perm m`.
  · refine (Finset.sum_bij (fun σ _ => prodCongrLeft fun k ↦ σ k (mem_univ k)) ?_ ?_ ?_ ?_).symm
    · intro σ _
      rw [mem_preserving_snd]
      rintro ⟨-, x⟩
      simp only [prodCongrLeft_apply]
    · intro σ _ σ' _ eq
      ext x hx k
      simp only at eq
      have :
        ∀ k x,
          prodCongrLeft (fun k => σ k (Finset.mem_univ _)) (k, x) =
            prodCongrLeft (fun k => σ' k (Finset.mem_univ _)) (k, x) :=
        fun k x => by rw [eq]
      simp only [prodCongrLeft_apply, Prod.mk.inj_iff] at this
      exact (this k x).1
    · intro σ hσ
      rw [mem_preserving_snd] at hσ
      have hσ' : ∀ x, (σ⁻¹ x).snd = x.snd := by
        intro x
        conv_rhs => rw [← Perm.apply_inv_self σ x, hσ]
      have mk_apply_eq : ∀ k x, ((σ (x, k)).fst, k) = σ (x, k) := by
        intro k x
        ext
        · simp only
        · simp only [hσ]
      have mk_inv_apply_eq : ∀ k x, ((σ⁻¹ (x, k)).fst, k) = σ⁻¹ (x, k) := by
        intro k x
        conv_lhs => rw [← Perm.apply_inv_self σ (x, k)]
        ext
        · simp only [apply_inv_self]
        · simp only [hσ']
      refine ⟨fun k _ => ⟨fun x => (σ (x, k)).fst, fun x => (σ⁻¹ (x, k)).fst, ?_, ?_⟩, ?_, ?_⟩
      · intro x
        simp only [mk_apply_eq, inv_apply_self]
      · intro x
        simp only [mk_inv_apply_eq, apply_inv_self]
      · apply Finset.mem_univ
      · ext ⟨k, x⟩
        · simp only [coe_fn_mk, prodCongrLeft_apply]
        · simp only [prodCongrLeft_apply, hσ]
    · intro σ _
      rw [Finset.prod_mul_distrib, ← Finset.univ_product_univ, Finset.prod_product_right]
      simp only [sign_prodCongrLeft, Units.coe_prod, Int.cast_prod, blockDiagonal_apply_eq,
        prodCongrLeft_apply]
  · intro σ _ hσ
    rw [mem_preserving_snd] at hσ
    obtain ⟨⟨k, x⟩, hkx⟩ := not_forall.mp hσ
    rw [Finset.prod_eq_zero (Finset.mem_univ (k, x)), mul_zero]
    rw [blockDiagonal_apply_ne]
    exact hkx
#align matrix.det_block_diagonal Matrix.det_blockDiagonal

/-- The determinant of a 2×2 block matrix with the lower-left block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`Matrix.det_of_upper_triangular`. -/
@[simp]
theorem det_fromBlocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (Matrix.fromBlocks A B 0 D).det = A.det * D.det := by
  classical
    simp_rw [det_apply']
    convert Eq.symm <|
      sum_subset (β := R) (subset_univ ((sumCongrHom m n).range : Set (Perm (Sum m n))).toFinset) ?_
    · simp_rw [sum_mul_sum, ← sum_product', univ_product_univ]
      refine sum_nbij (fun σ ↦ σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
      · intro σ₁₂ _
        simp only
        erw [Set.mem_toFinset, MonoidHom.mem_range]
        use σ₁₂
        simp only [sumCongrHom_apply]
      · intro σ₁ _ σ₂ _
        dsimp only
        intro h
        have h2 : ∀ x, Perm.sumCongr σ₁.fst σ₁.snd x = Perm.sumCongr σ₂.fst σ₂.snd x :=
          DFunLike.congr_fun h
        simp only [Sum.map_inr, Sum.map_inl, Perm.sumCongr_apply, Sum.forall, Sum.inl.injEq,
          Sum.inr.injEq] at h2
        ext x
        · exact h2.left x
        · exact h2.right x
      · intro σ hσ
        erw [Set.mem_toFinset, MonoidHom.mem_range] at hσ
        obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
        use σ₁₂
        rw [← hσ₁₂]
        simp
      · simp only [forall_prop_of_true, Prod.forall, mem_univ]
        intro σ₁ σ₂
        rw [Fintype.prod_sum_type]
        simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, fromBlocks_apply₁₁,
          fromBlocks_apply₂₂]
        rw [mul_mul_mul_comm]
        congr
        rw [sign_sumCongr, Units.val_mul, Int.cast_mul]
    · rintro σ - hσn
      have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
        rw [Set.mem_toFinset] at hσn
        -- Porting note: golfed
        simpa only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using
          mt mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
      obtain ⟨a, ha⟩ := not_forall.mp h1
      cases' hx : σ (Sum.inl a) with a2 b
      · have hn := (not_exists.mp ha) a2
        exact absurd hx.symm hn
      · rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a)), mul_zero]
        rw [hx, fromBlocks_apply₂₁, zero_apply]
#align matrix.det_from_blocks_zero₂₁ Matrix.det_fromBlocks_zero₂₁

/-- The determinant of a 2×2 block matrix with the upper-right block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`Matrix.det_of_lower_triangular`. -/
@[simp]
theorem det_fromBlocks_zero₁₂ (A : Matrix m m R) (C : Matrix n m R) (D : Matrix n n R) :
    (Matrix.fromBlocks A 0 C D).det = A.det * D.det := by
  rw [← det_transpose, fromBlocks_transpose, transpose_zero, det_fromBlocks_zero₂₁, det_transpose,
    det_transpose]
#align matrix.det_from_blocks_zero₁₂ Matrix.det_fromBlocks_zero₁₂

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column 0. -/
theorem det_succ_column_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    det A = ∑ i : Fin n.succ, (-1) ^ (i : ℕ) * A i 0 * det (A.submatrix i.succAbove Fin.succ) := by
  rw [Matrix.det_apply, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.prod_univ_succ, Matrix.det_apply, Finset.mul_sum,
      Equiv.Perm.decomposeFin_symm_apply_zero, Fin.val_zero, one_mul,
      Equiv.Perm.decomposeFin.symm_sign, Equiv.swap_self, if_true, id, eq_self_iff_true,
      Equiv.Perm.decomposeFin_symm_apply_succ, Fin.succAbove_zero, Equiv.coe_refl, pow_zero,
      mul_smul_comm, of_apply]
  -- `univ_perm_fin_succ` gives a different embedding of `Perm (Fin n)` into
  -- `Perm (Fin n.succ)` than the determinant of the submatrix we want,
  -- permute `A` so that we get the correct one.
  have : (-1 : R) ^ (i : ℕ) = (Perm.sign i.cycleRange) := by simp [Fin.sign_cycleRange]
  rw [Fin.val_succ, pow_succ', this, mul_assoc, mul_assoc, mul_left_comm (ε _),
    ← det_permute, Matrix.det_apply, Finset.mul_sum, Finset.mul_sum]
  -- now we just need to move the corresponding parts to the same place
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Equiv.Perm.decomposeFin.symm_sign, if_neg (Fin.succ_ne_zero i)]
  calc
    ((-1 * Perm.sign σ : ℤ) • ∏ i', A (Perm.decomposeFin.symm (Fin.succ i, σ) i') i') =
        (-1 * Perm.sign σ : ℤ) • (A (Fin.succ i) 0 *
          ∏ i', A ((Fin.succ i).succAbove (Fin.cycleRange i (σ i'))) i'.succ) := by
      simp only [Fin.prod_univ_succ, Fin.succAbove_cycleRange,
        Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
    _ = -1 * (A (Fin.succ i) 0 * (Perm.sign σ : ℤ) •
        ∏ i', A ((Fin.succ i).succAbove (Fin.cycleRange i (σ i'))) i'.succ) := by
      simp [mul_assoc, mul_comm, _root_.neg_mul, one_mul, zsmul_eq_mul, neg_inj, neg_smul,
        Fin.succAbove_cycleRange, mul_left_comm]
#align matrix.det_succ_column_zero Matrix.det_succ_column_zero

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row 0. -/
theorem det_succ_row_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    det A = ∑ j : Fin n.succ, (-1) ^ (j : ℕ) * A 0 j * det (A.submatrix Fin.succ j.succAbove) := by
  rw [← det_transpose A, det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← det_transpose]
  simp only [transpose_apply, transpose_submatrix, transpose_transpose]
#align matrix.det_succ_row_zero Matrix.det_succ_row_zero

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row `i`. -/
theorem det_succ_row {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n.succ) :
    det A =
      ∑ j : Fin n.succ, (-1) ^ (i + j : ℕ) * A i j * det (A.submatrix i.succAbove j.succAbove) := by
  simp_rw [pow_add, mul_assoc, ← mul_sum]
  have : det A = (-1 : R) ^ (i : ℕ) * (Perm.sign i.cycleRange⁻¹) * det A := by
    calc
      det A = ↑((-1 : ℤˣ) ^ (i : ℕ) * (-1 : ℤˣ) ^ (i : ℕ) : ℤˣ) * det A := by simp
      _ = (-1 : R) ^ (i : ℕ) * (Perm.sign i.cycleRange⁻¹) * det A := by simp [-Int.units_mul_self]
  rw [this, mul_assoc]
  congr
  rw [← det_permute, det_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, Matrix.submatrix_apply, submatrix_submatrix, id_comp, Function.comp_def, id]
  congr
  · rw [Equiv.Perm.inv_def, Fin.cycleRange_symm_zero]
  · ext i' j'
    rw [Equiv.Perm.inv_def, Matrix.submatrix_apply, Matrix.submatrix_apply,
      Fin.cycleRange_symm_succ]
#align matrix.det_succ_row Matrix.det_succ_row

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column `j`. -/
theorem det_succ_column {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) (j : Fin n.succ) :
    det A =
      ∑ i : Fin n.succ, (-1) ^ (i + j : ℕ) * A i j * det (A.submatrix i.succAbove j.succAbove) := by
  rw [← det_transpose, det_succ_row _ j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm, ← det_transpose, transpose_apply, transpose_submatrix, transpose_transpose]
#align matrix.det_succ_column Matrix.det_succ_column

/-- Determinant of 0x0 matrix -/
@[simp]
theorem det_fin_zero {A : Matrix (Fin 0) (Fin 0) R} : det A = 1 :=
  det_isEmpty
#align matrix.det_fin_zero Matrix.det_fin_zero

/-- Determinant of 1x1 matrix -/
theorem det_fin_one (A : Matrix (Fin 1) (Fin 1) R) : det A = A 0 0 :=
  det_unique A
#align matrix.det_fin_one Matrix.det_fin_one

theorem det_fin_one_of (a : R) : det !![a] = a :=
  det_fin_one _
#align matrix.det_fin_one_of Matrix.det_fin_one_of

/-- Determinant of 2x2 matrix -/
theorem det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  simp only [det_succ_row_zero, det_unique, Fin.default_eq_zero, submatrix_apply,
    Fin.succ_zero_eq_one, Fin.sum_univ_succ, Fin.val_zero, Fin.zero_succAbove, univ_unique,
    Fin.val_succ, Fin.coe_fin_one, Fin.succ_succAbove_zero, sum_singleton]
  ring
#align matrix.det_fin_two Matrix.det_fin_two

@[simp]
theorem det_fin_two_of (a b c d : R) : Matrix.det !![a, b; c, d] = a * d - b * c :=
  det_fin_two _
#align matrix.det_fin_two_of Matrix.det_fin_two_of

/-- Determinant of 3x3 matrix -/
theorem det_fin_three (A : Matrix (Fin 3) (Fin 3) R) :
    det A =
      A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
      - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
      + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 := by
  simp only [det_succ_row_zero, Nat.odd_iff_not_even, submatrix_apply, Fin.succ_zero_eq_one,
    submatrix_submatrix, det_unique, Fin.default_eq_zero, comp_apply, Fin.succ_one_eq_two,
    Fin.sum_univ_succ, Fin.val_zero, Fin.zero_succAbove, univ_unique, Fin.val_succ,
    Fin.coe_fin_one, Fin.succ_succAbove_zero, sum_singleton, Fin.succ_succAbove_one, even_add_self]
  ring
#align matrix.det_fin_three Matrix.det_fin_three

end Matrix
