/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Regular.Basic
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Polynomial.Basic

#align_import linear_algebra.matrix.adjugate from "leanprover-community/mathlib"@"a99f85220eaf38f14f94e04699943e185a5e1d1a"

/-!
# Cramer's rule and adjugate matrices

The adjugate matrix is the transpose of the cofactor matrix.
It is calculated with Cramer's rule, which we introduce first.
The vectors returned by Cramer's rule are given by the linear map `cramer`,
which sends a matrix `A` and vector `b` to the vector consisting of the
determinant of replacing the `i`th column of `A` with `b` at index `i`
(written as `(A.update_column i b).det`).
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`.
The entries of the adjugate are the minors of `A`.
Instead of defining a minor by deleting row `i` and column `j` of `A`, we
replace the `i`th row of `A` with the `j`th basis vector; the resulting matrix
has the same determinant but more importantly equals Cramer's rule applied
to `A` and the `j`th basis vector, simplifying the subsequent proofs.
We prove the adjugate behaves like `det A • A⁻¹`.

## Main definitions

 * `Matrix.cramer A b`: the vector output by Cramer's rule on `A` and `b`.
 * `Matrix.adjugate A`: the adjugate (or classical adjoint) of the matrix `A`.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

cramer, cramer's rule, adjugate
-/


namespace Matrix

universe u v w

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

open Matrix BigOperators Polynomial Equiv Equiv.Perm Finset

section Cramer

/-!
  ### `cramer` section

  Introduce the linear map `cramer` with values defined by `cramerMap`.
  After defining `cramerMap` and showing it is linear,
  we will restrict our proofs to using `cramer`.
-/


variable (A : Matrix n n α) (b : n → α)

/-- `cramerMap A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramerMap A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A * x = b` has a unique solution in `x`, `cramerMap A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramerMap` is well-defined but not necessarily useful.
-/
def cramerMap (i : n) : α :=
  (A.updateColumn i b).det
#align matrix.cramer_map Matrix.cramerMap

theorem cramerMap_is_linear (i : n) : IsLinearMap α fun b => cramerMap A b i :=
  { map_add := det_updateColumn_add _ _
    map_smul := det_updateColumn_smul _ _ }
#align matrix.cramer_map_is_linear Matrix.cramerMap_is_linear

theorem cramer_is_linear : IsLinearMap α (cramerMap A) := by
  constructor <;> intros <;> ext i
  -- ⊢ ∀ (x y : n → α), cramerMap A (x + y) = cramerMap A x + cramerMap A y
                  -- ⊢ cramerMap A (x✝ + y✝) = cramerMap A x✝ + cramerMap A y✝
                  -- ⊢ cramerMap A (c✝ • x✝) = c✝ • cramerMap A x✝
                             -- ⊢ cramerMap A (x✝ + y✝) i = (cramerMap A x✝ + cramerMap A y✝) i
                             -- ⊢ cramerMap A (c✝ • x✝) i = (c✝ • cramerMap A x✝) i
  · apply (cramerMap_is_linear A i).1
    -- 🎉 no goals
  · apply (cramerMap_is_linear A i).2
    -- 🎉 no goals
#align matrix.cramer_is_linear Matrix.cramer_is_linear

/-- `cramer A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A * x = b` has a unique solution in `x`, `cramer A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer` is well-defined but not necessarily useful.
 -/
def cramer (A : Matrix n n α) : (n → α) →ₗ[α] (n → α) :=
  IsLinearMap.mk' (cramerMap A) (cramer_is_linear A)
#align matrix.cramer Matrix.cramer

theorem cramer_apply (i : n) : cramer A b i = (A.updateColumn i b).det :=
  rfl
#align matrix.cramer_apply Matrix.cramer_apply

theorem cramer_transpose_apply (i : n) : cramer Aᵀ b i = (A.updateRow i b).det := by
  rw [cramer_apply, updateColumn_transpose, det_transpose]
  -- 🎉 no goals
#align matrix.cramer_transpose_apply Matrix.cramer_transpose_apply

theorem cramer_transpose_row_self (i : n) : Aᵀ.cramer (A i) = Pi.single i A.det := by
  ext j
  -- ⊢ ↑(cramer Aᵀ) (A i) j = Pi.single i (det A) j
  rw [cramer_apply, Pi.single_apply]
  -- ⊢ det (updateColumn Aᵀ j (A i)) = if j = i then det A else 0
  split_ifs with h
  -- ⊢ det (updateColumn Aᵀ j (A i)) = det A
  · -- i = j: this entry should be `A.det`
    subst h
    -- ⊢ det (updateColumn Aᵀ j (A j)) = det A
    simp only [updateColumn_transpose, det_transpose, updateRow_eq_self]
    -- 🎉 no goals
  · -- i ≠ j: this entry should be 0
    rw [updateColumn_transpose, det_transpose]
    -- ⊢ det (updateRow A j (A i)) = 0
    apply det_zero_of_row_eq h
    -- ⊢ updateRow A j (A i) j = updateRow A j (A i) i
    rw [updateRow_self, updateRow_ne (Ne.symm h)]
    -- 🎉 no goals
#align matrix.cramer_transpose_row_self Matrix.cramer_transpose_row_self

theorem cramer_row_self (i : n) (h : ∀ j, b j = A j i) : A.cramer b = Pi.single i A.det := by
  rw [← transpose_transpose A, det_transpose]
  -- ⊢ ↑(cramer Aᵀᵀ) b = Pi.single i (det Aᵀ)
  convert cramer_transpose_row_self Aᵀ i
  -- ⊢ b = Aᵀ i
  exact funext h
  -- 🎉 no goals
#align matrix.cramer_row_self Matrix.cramer_row_self

@[simp]
theorem cramer_one : cramer (1 : Matrix n n α) = 1 := by
  -- Porting note: was `ext i j`
  refine LinearMap.pi_ext' (fun (i : n) => LinearMap.ext_ring (funext (fun (j : n) => ?_)))
  -- ⊢ ↑(LinearMap.comp (cramer 1) (LinearMap.single i)) 1 j = ↑(LinearMap.comp 1 ( …
  convert congr_fun (cramer_row_self (1 : Matrix n n α) (Pi.single i 1) i _) j
  -- ⊢ 1 = det 1
  · simp
    -- 🎉 no goals
  · intro j
    -- ⊢ Pi.single i 1 j = OfNat.ofNat 1 j i
    rw [Matrix.one_eq_pi_single, Pi.single_comm]
    -- 🎉 no goals
#align matrix.cramer_one Matrix.cramer_one

theorem cramer_smul (r : α) (A : Matrix n n α) :
    cramer (r • A) = r ^ (Fintype.card n - 1) • cramer A :=
  LinearMap.ext fun _ => funext fun _ => det_updateColumn_smul' _ _ _ _
#align matrix.cramer_smul Matrix.cramer_smul

@[simp]
theorem cramer_subsingleton_apply [Subsingleton n] (A : Matrix n n α) (b : n → α) (i : n) :
    cramer A b i = b i := by rw [cramer_apply, det_eq_elem_of_subsingleton _ i, updateColumn_self]
                             -- 🎉 no goals
#align matrix.cramer_subsingleton_apply Matrix.cramer_subsingleton_apply

theorem cramer_zero [Nontrivial n] : cramer (0 : Matrix n n α) = 0 := by
  ext i j
  -- ⊢ ↑(LinearMap.comp (cramer 0) (LinearMap.single i)) 1 j = ↑(LinearMap.comp 0 ( …
  obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j
  -- ⊢ ↑(LinearMap.comp (cramer 0) (LinearMap.single i)) 1 j = ↑(LinearMap.comp 0 ( …
  apply det_eq_zero_of_column_eq_zero j'
  -- ⊢ ∀ (i_1 : n), updateColumn 0 j (↑(LinearMap.single i) 1) i_1 j' = 0
  intro j''
  -- ⊢ updateColumn 0 j (↑(LinearMap.single i) 1) j'' j' = 0
  simp [updateColumn_ne hj']
  -- 🎉 no goals
#align matrix.cramer_zero Matrix.cramer_zero

/-- Use linearity of `cramer` to take it out of a summation. -/
theorem sum_cramer {β} (s : Finset β) (f : β → n → α) :
    (∑ x in s, cramer A (f x)) = cramer A (∑ x in s, f x) :=
  (LinearMap.map_sum (cramer A)).symm
#align matrix.sum_cramer Matrix.sum_cramer

/-- Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a summation. -/
theorem sum_cramer_apply {β} (s : Finset β) (f : n → β → α) (i : n) :
    (∑ x in s, cramer A (fun j => f j x) i) = cramer A (fun j : n => ∑ x in s, f j x) i :=
  calc
    (∑ x in s, cramer A (fun j => f j x) i) = (∑ x in s, cramer A fun j => f j x) i :=
      (Finset.sum_apply i s _).symm
    _ = cramer A (fun j : n => ∑ x in s, f j x) i := by
      rw [sum_cramer, cramer_apply, cramer_apply]
      -- ⊢ det (updateColumn A i (∑ x in s, fun j => f j x)) = det (updateColumn A i fu …
      simp only [updateColumn]
      -- ⊢ det (↑of fun i_1 => Function.update (A i_1) i (Finset.sum s (fun x j => f j  …
      congr with j
      -- ⊢ Function.update (A j) i (Finset.sum s (fun x j => f j x) j) x✝ = Function.up …
      congr
      -- ⊢ Finset.sum s (fun x j => f j x) j = ∑ x in s, f j x
      apply Finset.sum_apply
      -- 🎉 no goals
#align matrix.sum_cramer_apply Matrix.sum_cramer_apply

theorem cramer_submatrix_equiv (A : Matrix m m α) (e : n ≃ m) (b : n → α) :
    cramer (A.submatrix e e) b = cramer A (b ∘ e.symm) ∘ e := by
  ext i
  -- ⊢ ↑(cramer (submatrix A ↑e ↑e)) b i = (↑(cramer A) (b ∘ ↑e.symm) ∘ ↑e) i
  simp_rw [Function.comp_apply, cramer_apply, updateColumn_submatrix_equiv,
    det_submatrix_equiv_self e, Function.comp]
#align matrix.cramer_submatrix_equiv Matrix.cramer_submatrix_equiv

theorem cramer_reindex (e : m ≃ n) (A : Matrix m m α) (b : n → α) :
    cramer (reindex e e A) b = cramer A (b ∘ e) ∘ e.symm :=
  cramer_submatrix_equiv _ _ _
#align matrix.cramer_reindex Matrix.cramer_reindex

end Cramer

section Adjugate

/-!
### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring.
-/


/-- The adjugate matrix is the transpose of the cofactor matrix.

  Typically, the cofactor matrix is defined by taking minors,
  i.e. the determinant of the matrix with a row and column removed.
  However, the proof of `mul_adjugate` becomes a lot easier if we use the
  matrix replacing a column with a basis vector, since it allows us to use
  facts about the `cramer` map.
-/
def adjugate (A : Matrix n n α) : Matrix n n α :=
  of fun i => cramer Aᵀ (Pi.single i 1)
#align matrix.adjugate Matrix.adjugate

theorem adjugate_def (A : Matrix n n α) : adjugate A = of fun i => cramer Aᵀ (Pi.single i 1) :=
  rfl
#align matrix.adjugate_def Matrix.adjugate_def

theorem adjugate_apply (A : Matrix n n α) (i j : n) :
    adjugate A i j = (A.updateRow j (Pi.single i 1)).det := by
  rw [adjugate_def, of_apply, cramer_apply, updateColumn_transpose, det_transpose]
  -- 🎉 no goals
#align matrix.adjugate_apply Matrix.adjugate_apply

theorem adjugate_transpose (A : Matrix n n α) : (adjugate A)ᵀ = adjugate Aᵀ := by
  ext i j
  -- ⊢ (adjugate A)ᵀ i j = adjugate Aᵀ i j
  rw [transpose_apply, adjugate_apply, adjugate_apply, updateRow_transpose, det_transpose]
  -- ⊢ det (updateRow A i (Pi.single j 1)) = det (updateColumn A j (Pi.single i 1))
  rw [det_apply', det_apply']
  -- ⊢ ∑ σ : Perm n, ↑↑(↑sign σ) * ∏ i_1 : n, updateRow A i (Pi.single j 1) (↑σ i_1 …
  apply Finset.sum_congr rfl
  -- ⊢ ∀ (x : Perm n), x ∈ univ → ↑↑(↑sign x) * ∏ i_1 : n, updateRow A i (Pi.single …
  intro σ _
  -- ⊢ ↑↑(↑sign σ) * ∏ i_1 : n, updateRow A i (Pi.single j 1) (↑σ i_1) i_1 = ↑↑(↑si …
  congr 1
  -- ⊢ ∏ i_1 : n, updateRow A i (Pi.single j 1) (↑σ i_1) i_1 = ∏ i_1 : n, updateCol …
  by_cases i = σ j
  -- ⊢ ∏ i_1 : n, updateRow A i (Pi.single j 1) (↑σ i_1) i_1 = ∏ i_1 : n, updateCol …
  -- ⊢ ∏ i_1 : n, updateRow A i (Pi.single j 1) (↑σ i_1) i_1 = ∏ i_1 : n, updateCol …
  · -- Everything except `(i , j)` (= `(σ j , j)`) is given by A, and the rest is a single `1`.
    congr
    -- ⊢ (fun i_1 => updateRow A i (Pi.single j 1) (↑σ i_1) i_1) = fun i_1 => updateC …
    ext j'
    -- ⊢ updateRow A i (Pi.single j 1) (↑σ j') j' = updateColumn A j (Pi.single i 1)  …
    subst h
    -- ⊢ updateRow A (↑σ j) (Pi.single j 1) (↑σ j') j' = updateColumn A j (Pi.single  …
    have : σ j' = σ j ↔ j' = j := σ.injective.eq_iff
    -- ⊢ updateRow A (↑σ j) (Pi.single j 1) (↑σ j') j' = updateColumn A j (Pi.single  …
    rw [updateRow_apply, updateColumn_apply]
    -- ⊢ (if ↑σ j' = ↑σ j then Pi.single j 1 j' else A (↑σ j') j') = if j' = j then P …
    simp_rw [this]
    -- ⊢ (if j' = j then Pi.single j 1 j' else A (↑σ j') j') = if j' = j then Pi.sing …
    rw [← dite_eq_ite, ← dite_eq_ite]
    -- ⊢ (if x : j' = j then Pi.single j 1 j' else A (↑σ j') j') = if x : j' = j then …
    congr 1 with rfl
    -- ⊢ Pi.single j' 1 j' = Pi.single (↑σ j') 1 (↑σ j')
    rw [Pi.single_eq_same, Pi.single_eq_same]
    -- 🎉 no goals
  · -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have : (∏ j' : n, updateColumn A j (Pi.single i 1) (σ j') j') = 0 := by
      apply prod_eq_zero (mem_univ j)
      rw [updateColumn_self, Pi.single_eq_of_ne' h]
    rw [this]
    -- ⊢ ∏ i_1 : n, updateRow A i (Pi.single j 1) (↑σ i_1) i_1 = 0
    apply prod_eq_zero (mem_univ (σ⁻¹ i))
    -- ⊢ updateRow A i (Pi.single j 1) (↑σ (↑σ⁻¹ i)) (↑σ⁻¹ i) = 0
    erw [apply_symm_apply σ i, updateRow_self]
    -- ⊢ Pi.single j 1 (↑σ⁻¹ i) = 0
    apply Pi.single_eq_of_ne
    -- ⊢ ↑σ⁻¹ i ≠ j
    intro h'
    -- ⊢ False
    exact h ((symm_apply_eq σ).mp h')
    -- 🎉 no goals
#align matrix.adjugate_transpose Matrix.adjugate_transpose

@[simp]
theorem adjugate_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m α) :
    adjugate (A.submatrix e e) = (adjugate A).submatrix e e := by
  ext i j
  -- ⊢ adjugate (submatrix A ↑e ↑e) i j = submatrix (adjugate A) (↑e) (↑e) i j
  rw [adjugate_apply, submatrix_apply, adjugate_apply, ← det_submatrix_equiv_self e,
    updateRow_submatrix_equiv]
  -- Porting note: added
  suffices (fun j => Pi.single i 1 (e.symm j)) = Pi.single (e i) 1 by
    erw [this]
  exact Function.update_comp_equiv _ e.symm _ _
  -- 🎉 no goals
#align matrix.adjugate_submatrix_equiv_self Matrix.adjugate_submatrix_equiv_self

theorem adjugate_reindex (e : m ≃ n) (A : Matrix m m α) :
    adjugate (reindex e e A) = reindex e e (adjugate A) :=
  adjugate_submatrix_equiv_self _ _
#align matrix.adjugate_reindex Matrix.adjugate_reindex

/-- Since the map `b ↦ cramer A b` is linear in `b`, it must be multiplication by some matrix. This
matrix is `A.adjugate`. -/
theorem cramer_eq_adjugate_mulVec (A : Matrix n n α) (b : n → α) :
    cramer A b = A.adjugate.mulVec b := by
  nth_rw 2 [← A.transpose_transpose]
  -- ⊢ ↑(cramer A) b = mulVec (adjugate Aᵀᵀ) b
  rw [← adjugate_transpose, adjugate_def]
  -- ⊢ ↑(cramer A) b = mulVec (↑of fun i => ↑(cramer Aᵀᵀ) (Pi.single i 1))ᵀ b
  have : b = ∑ i, b i • Pi.single i 1 := by
    refine' (pi_eq_sum_univ b).trans _
    congr with j
    -- Porting note: needed to help `Pi.smul_apply`
    simp [Pi.single_apply, eq_comm, Pi.smul_apply (b j)]
  conv_lhs =>
    rw [this]
  ext k
  -- ⊢ ↑(cramer A) (∑ i : n, b i • Pi.single i 1) k = mulVec (↑of fun i => ↑(cramer …
  simp [mulVec, dotProduct, mul_comm]
  -- 🎉 no goals
#align matrix.cramer_eq_adjugate_mul_vec Matrix.cramer_eq_adjugate_mulVec

theorem mul_adjugate_apply (A : Matrix n n α) (i j k) :
    A i k * adjugate A k j = cramer Aᵀ (Pi.single k (A i k)) j := by
  erw [← smul_eq_mul, adjugate, of_apply, ← Pi.smul_apply, ← LinearMap.map_smul, ← Pi.single_smul',
    smul_eq_mul, mul_one]
#align matrix.mul_adjugate_apply Matrix.mul_adjugate_apply

theorem mul_adjugate (A : Matrix n n α) : A * adjugate A = A.det • (1 : Matrix n n α) := by
  ext i j
  -- ⊢ (A * adjugate A) i j = (det A • 1) i j
  rw [mul_apply, Pi.smul_apply, Pi.smul_apply, one_apply, smul_eq_mul, mul_boole]
  -- ⊢ ∑ j_1 : n, A i j_1 * adjugate A j_1 j = if i = j then det A else 0
  simp [mul_adjugate_apply, sum_cramer_apply, cramer_transpose_row_self, Pi.single_apply, eq_comm]
  -- 🎉 no goals
#align matrix.mul_adjugate Matrix.mul_adjugate

theorem adjugate_mul (A : Matrix n n α) : adjugate A * A = A.det • (1 : Matrix n n α) :=
  calc
    adjugate A * A = (Aᵀ * adjugate Aᵀ)ᵀ := by
      rw [← adjugate_transpose, ← transpose_mul, transpose_transpose]
      -- 🎉 no goals
    _ = _ := by rw [mul_adjugate Aᵀ, det_transpose, transpose_smul, transpose_one]
                -- 🎉 no goals
#align matrix.adjugate_mul Matrix.adjugate_mul

theorem adjugate_smul (r : α) (A : Matrix n n α) :
    adjugate (r • A) = r ^ (Fintype.card n - 1) • adjugate A := by
  rw [adjugate, adjugate, transpose_smul, cramer_smul]
  -- ⊢ (↑of fun i => ↑(r ^ (Fintype.card n - 1) • cramer Aᵀ) (Pi.single i 1)) = r ^ …
  rfl
  -- 🎉 no goals
#align matrix.adjugate_smul Matrix.adjugate_smul

/-- A stronger form of **Cramer's rule** that allows us to solve some instances of `A * x = b` even
if the determinant is not a unit. A sufficient (but still not necessary) condition is that `A.det`
divides `b`. -/
@[simp]
theorem mulVec_cramer (A : Matrix n n α) (b : n → α) : A.mulVec (cramer A b) = A.det • b := by
  rw [cramer_eq_adjugate_mulVec, mulVec_mulVec, mul_adjugate, smul_mulVec_assoc, one_mulVec]
  -- 🎉 no goals
#align matrix.mul_vec_cramer Matrix.mulVec_cramer

theorem adjugate_subsingleton [Subsingleton n] (A : Matrix n n α) : adjugate A = 1 := by
  ext i j
  -- ⊢ adjugate A i j = OfNat.ofNat 1 i j
  simp [Subsingleton.elim i j, adjugate_apply, det_eq_elem_of_subsingleton _ i]
  -- 🎉 no goals
#align matrix.adjugate_subsingleton Matrix.adjugate_subsingleton

theorem adjugate_eq_one_of_card_eq_one {A : Matrix n n α} (h : Fintype.card n = 1) :
    adjugate A = 1 :=
  haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  adjugate_subsingleton _
#align matrix.adjugate_eq_one_of_card_eq_one Matrix.adjugate_eq_one_of_card_eq_one

@[simp]
theorem adjugate_zero [Nontrivial n] : adjugate (0 : Matrix n n α) = 0 := by
  ext i j
  -- ⊢ adjugate 0 i j = OfNat.ofNat 0 i j
  obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j
  -- ⊢ adjugate 0 i j = OfNat.ofNat 0 i j
  apply det_eq_zero_of_column_eq_zero j'
  -- ⊢ ∀ (i_1 : n), updateColumn 0ᵀ j (Pi.single i 1) i_1 j' = 0
  intro j''
  -- ⊢ updateColumn 0ᵀ j (Pi.single i 1) j'' j' = 0
  simp [updateColumn_ne hj']
  -- 🎉 no goals
#align matrix.adjugate_zero Matrix.adjugate_zero

@[simp]
theorem adjugate_one : adjugate (1 : Matrix n n α) = 1 := by
  ext
  -- ⊢ adjugate 1 i✝ x✝ = OfNat.ofNat 1 i✝ x✝
  simp [adjugate_def, Matrix.one_apply, Pi.single_apply, eq_comm]
  -- 🎉 no goals
#align matrix.adjugate_one Matrix.adjugate_one

@[simp]
theorem adjugate_diagonal (v : n → α) :
    adjugate (diagonal v) = diagonal fun i => ∏ j in Finset.univ.erase i, v j := by
  ext i j
  -- ⊢ adjugate (diagonal v) i j = diagonal (fun i => ∏ j in Finset.erase univ i, v …
  simp only [adjugate_def, cramer_apply, diagonal_transpose, of_apply]
  -- ⊢ det (updateColumn (diagonal v) j (Pi.single i 1)) = diagonal (fun i => ∏ j i …
  obtain rfl | hij := eq_or_ne i j
  -- ⊢ det (updateColumn (diagonal v) i (Pi.single i 1)) = diagonal (fun i => ∏ j i …
  · rw [diagonal_apply_eq, diagonal_updateColumn_single, det_diagonal,
      prod_update_of_mem (Finset.mem_univ _), sdiff_singleton_eq_erase, one_mul]
  · rw [diagonal_apply_ne _ hij]
    -- ⊢ det (updateColumn (diagonal v) j (Pi.single i 1)) = 0
    refine' det_eq_zero_of_row_eq_zero j fun k => _
    -- ⊢ updateColumn (diagonal v) j (Pi.single i 1) j k = 0
    obtain rfl | hjk := eq_or_ne k j
    -- ⊢ updateColumn (diagonal v) k (Pi.single i 1) k k = 0
    · rw [updateColumn_self, Pi.single_eq_of_ne' hij]
      -- 🎉 no goals
    · rw [updateColumn_ne hjk, diagonal_apply_ne' _ hjk]
      -- 🎉 no goals
#align matrix.adjugate_diagonal Matrix.adjugate_diagonal

theorem _root_.RingHom.map_adjugate {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix n n R) : f.mapMatrix M.adjugate = Matrix.adjugate (f.mapMatrix M) := by
  ext i k
  -- ⊢ ↑(RingHom.mapMatrix f) (adjugate M) i k = adjugate (↑(RingHom.mapMatrix f) M …
  have : Pi.single i (1 : S) = f ∘ Pi.single i 1 := by
    rw [← f.map_one]
    exact Pi.single_op (fun _ => f) (fun _ => f.map_zero) i (1 : R)
  rw [adjugate_apply, RingHom.mapMatrix_apply, map_apply, RingHom.mapMatrix_apply, this, ←
    map_updateRow, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← adjugate_apply]
#align ring_hom.map_adjugate RingHom.map_adjugate

theorem _root_.AlgHom.map_adjugate {R A B : Type*} [CommSemiring R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (M : Matrix n n A) :
    f.mapMatrix M.adjugate = Matrix.adjugate (f.mapMatrix M) :=
  f.toRingHom.map_adjugate _
#align alg_hom.map_adjugate AlgHom.map_adjugate

theorem det_adjugate (A : Matrix n n α) : (adjugate A).det = A.det ^ (Fintype.card n - 1) := by
  -- get rid of the `- 1`
  cases' (Fintype.card n).eq_zero_or_pos with h_card h_card
  -- ⊢ det (adjugate A) = det A ^ (Fintype.card n - 1)
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h_card
    -- ⊢ det (adjugate A) = det A ^ (Fintype.card n - 1)
    rw [h_card, Nat.zero_sub, pow_zero, adjugate_subsingleton, det_one]
    -- 🎉 no goals
  replace h_card := tsub_add_cancel_of_le h_card.nat_succ_le
  -- ⊢ det (adjugate A) = det A ^ (Fintype.card n - 1)
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n ℤ
  -- ⊢ det (adjugate A) = det A ^ (Fintype.card n - 1)
  suffices A'.adjugate.det = A'.det ^ (Fintype.card n - 1) by
    rw [← mvPolynomialX_mapMatrix_aeval ℤ A, ← AlgHom.map_adjugate, ← AlgHom.map_det, ←
      AlgHom.map_det, ← AlgHom.map_pow, this]
  apply mul_left_cancel₀ (show A'.det ≠ 0 from det_mvPolynomialX_ne_zero n ℤ)
  -- ⊢ det A' * det (adjugate A') = det A' * det A' ^ (Fintype.card n - 1)
  calc
    A'.det * A'.adjugate.det = (A' * adjugate A').det := (det_mul _ _).symm
    _ = A'.det ^ Fintype.card n := by rw [mul_adjugate, det_smul, det_one, mul_one]
    _ = A'.det * A'.det ^ (Fintype.card n - 1) := by rw [← pow_succ, h_card]
#align matrix.det_adjugate Matrix.det_adjugate

@[simp]
theorem adjugate_fin_zero (A : Matrix (Fin 0) (Fin 0) α) : adjugate A = 0 :=
  Subsingleton.elim _ _
#align matrix.adjugate_fin_zero Matrix.adjugate_fin_zero

@[simp]
theorem adjugate_fin_one (A : Matrix (Fin 1) (Fin 1) α) : adjugate A = 1 :=
  adjugate_subsingleton A
#align matrix.adjugate_fin_one Matrix.adjugate_fin_one

theorem adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) α) :
    adjugate A = !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
  ext i j
  -- ⊢ adjugate A i j = ↑of ![![A 1 1, -A 0 1], ![-A 1 0, A 0 0]] i j
  rw [adjugate_apply, det_fin_two]
  -- ⊢ updateRow A j (Pi.single i 1) 0 0 * updateRow A j (Pi.single i 1) 1 1 - upda …
  fin_cases i <;> fin_cases j <;>
  -- ⊢ updateRow A j (Pi.single { val := 0, isLt := (_ : 0 < 2) } 1) 0 0 * updateRo …
                  -- ⊢ updateRow A { val := 0, isLt := (_ : 0 < 2) } (Pi.single { val := 0, isLt := …
                  -- ⊢ updateRow A { val := 0, isLt := (_ : 0 < 2) } (Pi.single { val := 1, isLt := …
    simp [one_mul, Fin.one_eq_zero_iff, Pi.single_eq_same, mul_zero, sub_zero,
      Pi.single_eq_of_ne, Ne.def, not_false_iff, updateRow_self, updateRow_ne, cons_val_zero,
      of_apply, Nat.succ_succ_ne_one, Pi.single_eq_of_ne, updateRow_self, Pi.single_eq_of_ne,
      Ne.def, Fin.zero_eq_one_iff, Nat.succ_succ_ne_one, not_false_iff, updateRow_ne,
      Fin.one_eq_zero_iff, zero_mul, Pi.single_eq_same, one_mul, zero_sub, of_apply,
      cons_val', cons_val_fin_one, cons_val_one, head_fin_const, neg_inj, eq_self_iff_true,
      cons_val_zero, head_cons, mul_one]
#align matrix.adjugate_fin_two Matrix.adjugate_fin_two

@[simp]
theorem adjugate_fin_two_of (a b c d : α) : adjugate !![a, b; c, d] = !![d, -b; -c, a] :=
  adjugate_fin_two _
#align matrix.adjugate_fin_two_of Matrix.adjugate_fin_two_of

theorem adjugate_fin_succ_eq_det_submatrix {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) α) (i j) :
    adjugate A i j = (-1) ^ (j + i : ℕ) * det (A.submatrix j.succAbove i.succAbove) := by
  simp_rw [adjugate_apply, det_succ_row _ j, updateRow_self, submatrix_updateRow_succAbove]
  -- ⊢ ∑ x : Fin (Nat.succ n), (-1) ^ (↑j + ↑x) * Pi.single i 1 x * det (submatrix  …
  rw [Fintype.sum_eq_single i fun h hjk => ?_, Pi.single_eq_same, mul_one]
  -- ⊢ (-1) ^ (↑j + ↑h) * Pi.single i 1 h * det (submatrix A (Fin.succAbove j) (Fin …
  rw [Pi.single_eq_of_ne hjk, mul_zero, zero_mul]
  -- 🎉 no goals
#align matrix.adjugate_fin_succ_eq_det_submatrix Matrix.adjugate_fin_succ_eq_det_submatrix

theorem det_eq_sum_mul_adjugate_row (A : Matrix n n α) (i : n) :
    det A = ∑ j : n, A i j * adjugate A j i := by
  haveI : Nonempty n := ⟨i⟩
  -- ⊢ det A = ∑ j : n, A i j * adjugate A j i
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero : Fintype.card n ≠ 0)
  -- ⊢ det A = ∑ j : n, A i j * adjugate A j i
  obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hn'
  -- ⊢ det A = ∑ j : n, A i j * adjugate A j i
  let A' := reindex e e A
  -- ⊢ det A = ∑ j : n, A i j * adjugate A j i
  suffices det A' = ∑ j : Fin n'.succ, A' (e i) j * adjugate A' j (e i) by
    simp_rw [det_reindex_self, adjugate_reindex, reindex_apply, submatrix_apply, ← e.sum_comp,
      Equiv.symm_apply_apply] at this
    exact this
  rw [det_succ_row A' (e i)]
  -- ⊢ ∑ j : Fin (Nat.succ n'), (-1) ^ (↑(↑e i) + ↑j) * A' (↑e i) j * det (submatri …
  simp_rw [mul_assoc, mul_left_comm _ (A' _ _), ← adjugate_fin_succ_eq_det_submatrix]
  -- 🎉 no goals
#align matrix.det_eq_sum_mul_adjugate_row Matrix.det_eq_sum_mul_adjugate_row

theorem det_eq_sum_mul_adjugate_col (A : Matrix n n α) (j : n) :
    det A = ∑ i : n, A i j * adjugate A j i := by
  simpa only [det_transpose, ← adjugate_transpose] using det_eq_sum_mul_adjugate_row Aᵀ j
  -- 🎉 no goals
#align matrix.det_eq_sum_mul_adjugate_col Matrix.det_eq_sum_mul_adjugate_col

theorem adjugate_conjTranspose [StarRing α] (A : Matrix n n α) : A.adjugateᴴ = adjugate Aᴴ := by
  dsimp only [conjTranspose]
  -- ⊢ map (adjugate A)ᵀ star = adjugate (map Aᵀ star)
  have : Aᵀ.adjugate.map star = adjugate (Aᵀ.map star) := (starRingEnd α).map_adjugate Aᵀ
  -- ⊢ map (adjugate A)ᵀ star = adjugate (map Aᵀ star)
  rw [A.adjugate_transpose, this]
  -- 🎉 no goals
#align matrix.adjugate_conj_transpose Matrix.adjugate_conjTranspose

theorem isRegular_of_isLeftRegular_det {A : Matrix n n α} (hA : IsLeftRegular A.det) :
    IsRegular A := by
  constructor
  -- ⊢ IsLeftRegular A
  · intro B C h
    -- ⊢ B = C
    refine' hA.matrix _
    -- ⊢ (fun x => det A • x) B = (fun x => det A • x) C
    simp only at h ⊢
    -- ⊢ det A • B = det A • C
    rw [← Matrix.one_mul B, ← Matrix.one_mul C, ← Matrix.smul_mul, ← Matrix.smul_mul, ←
      adjugate_mul, Matrix.mul_assoc, Matrix.mul_assoc, h]
  · intro B C (h : B * A = C * A)
    -- ⊢ B = C
    refine' hA.matrix _
    -- ⊢ (fun x => det A • x) B = (fun x => det A • x) C
    simp only
    -- ⊢ det A • B = det A • C
    rw [← Matrix.mul_one B, ← Matrix.mul_one C, ← Matrix.mul_smul, ← Matrix.mul_smul, ←
      mul_adjugate, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h]
#align matrix.is_regular_of_is_left_regular_det Matrix.isRegular_of_isLeftRegular_det

theorem adjugate_mul_distrib_aux (A B : Matrix n n α) (hA : IsLeftRegular A.det)
    (hB : IsLeftRegular B.det) : adjugate (A * B) = adjugate B * adjugate A := by
  have hAB : IsLeftRegular (A * B).det := by
    rw [det_mul]
    exact hA.mul hB
  refine' (isRegular_of_isLeftRegular_det hAB).left _
  -- ⊢ (fun x => A * B * x) (adjugate (A * B)) = (fun x => A * B * x) (adjugate B * …
  simp only
  -- ⊢ A * B * adjugate (A * B) = A * B * (adjugate B * adjugate A)
  rw [mul_adjugate, Matrix.mul_assoc, ← Matrix.mul_assoc B, mul_adjugate,
    smul_mul, Matrix.one_mul, mul_smul, mul_adjugate, smul_smul, mul_comm, ← det_mul]
#align matrix.adjugate_mul_distrib_aux Matrix.adjugate_mul_distrib_aux

/-- Proof follows from "The trace Cayley-Hamilton theorem" by Darij Grinberg, Section 5.3
-/
theorem adjugate_mul_distrib (A B : Matrix n n α) : adjugate (A * B) = adjugate B * adjugate A := by
  let g : Matrix n n α → Matrix n n α[X] := fun M =>
    M.map Polynomial.C + (Polynomial.X : α[X]) • (1 : Matrix n n α[X])
  let f' : Matrix n n α[X] →+* Matrix n n α := (Polynomial.evalRingHom 0).mapMatrix
  -- ⊢ adjugate (A * B) = adjugate B * adjugate A
  have f'_inv : ∀ M, f' (g M) = M := by
    intro
    ext
    simp
  have f'_adj : ∀ M : Matrix n n α, f' (adjugate (g M)) = adjugate M := by
    intro
    rw [RingHom.map_adjugate, f'_inv]
  have f'_g_mul : ∀ M N : Matrix n n α, f' (g M * g N) = M * N := by
    intros M N
    rw [RingHom.map_mul, f'_inv, f'_inv]
  have hu : ∀ M : Matrix n n α, IsRegular (g M).det := by
    intro M
    refine' Polynomial.Monic.isRegular _
    simp only [Polynomial.Monic.def, ← Polynomial.leadingCoeff_det_X_one_add_C M, add_comm]
  rw [← f'_adj, ← f'_adj, ← f'_adj, ← f'.map_mul, ←
    adjugate_mul_distrib_aux _ _ (hu A).left (hu B).left, RingHom.map_adjugate,
    RingHom.map_adjugate, f'_inv, f'_g_mul]
#align matrix.adjugate_mul_distrib Matrix.adjugate_mul_distrib

@[simp]
theorem adjugate_pow (A : Matrix n n α) (k : ℕ) : adjugate (A ^ k) = adjugate A ^ k := by
  induction' k with k IH
  -- ⊢ adjugate (A ^ Nat.zero) = adjugate A ^ Nat.zero
  · simp
    -- 🎉 no goals
  · rw [pow_succ', adjugate_mul_distrib, IH, pow_succ]
    -- 🎉 no goals
#align matrix.adjugate_pow Matrix.adjugate_pow

theorem det_smul_adjugate_adjugate (A : Matrix n n α) :
    det A • adjugate (adjugate A) = det A ^ (Fintype.card n - 1) • A := by
  have : A * (A.adjugate * A.adjugate.adjugate) =
      A * (A.det ^ (Fintype.card n - 1) • (1 : Matrix n n α)) := by
    rw [← adjugate_mul_distrib, adjugate_mul, adjugate_smul, adjugate_one]
  rwa [← Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul] at this
#align matrix.det_smul_adjugate_adjugate Matrix.det_smul_adjugate_adjugate

/-- Note that this is not true for `Fintype.card n = 1` since `1 - 2 = 0` and not `-1`. -/
theorem adjugate_adjugate (A : Matrix n n α) (h : Fintype.card n ≠ 1) :
    adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A := by
  -- get rid of the `- 2`
  cases' h_card : Fintype.card n with n'
  -- ⊢ adjugate (adjugate A) = det A ^ (Nat.zero - 2) • A
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h_card
    -- ⊢ adjugate (adjugate A) = det A ^ (Nat.zero - 2) • A
    apply Subsingleton.elim
    -- 🎉 no goals
  cases n'
  -- ⊢ adjugate (adjugate A) = det A ^ (Nat.succ Nat.zero - 2) • A
  · exact (h h_card).elim
    -- 🎉 no goals
  rw [← h_card]
  -- ⊢ adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n ℤ
  -- ⊢ adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A
  suffices adjugate (adjugate A') = det A' ^ (Fintype.card n - 2) • A' by
    rw [← mvPolynomialX_mapMatrix_aeval ℤ A, ← AlgHom.map_adjugate, ← AlgHom.map_adjugate, this,
      ← AlgHom.map_det, ← AlgHom.map_pow, AlgHom.mapMatrix_apply, AlgHom.mapMatrix_apply,
      Matrix.map_smul' _ _ _ (_root_.map_mul _)]
  have h_card' : Fintype.card n - 2 + 1 = Fintype.card n - 1 := by simp [h_card]
  -- ⊢ adjugate (adjugate A') = det A' ^ (Fintype.card n - 2) • A'
  have is_reg : IsSMulRegular (MvPolynomial (n × n) ℤ) (det A') := fun x y =>
    mul_left_cancel₀ (det_mvPolynomialX_ne_zero n ℤ)
  apply is_reg.matrix
  -- ⊢ (fun x => det A' • x) (adjugate (adjugate A')) = (fun x => det A' • x) (det  …
  simp only
  -- ⊢ det (mvPolynomialX n n ℤ) • adjugate (adjugate (mvPolynomialX n n ℤ)) = det  …
  rw [smul_smul, ← pow_succ, h_card', det_smul_adjugate_adjugate]
  -- 🎉 no goals
#align matrix.adjugate_adjugate Matrix.adjugate_adjugate

/-- A weaker version of `Matrix.adjugate_adjugate` that uses `Nontrivial`. -/
theorem adjugate_adjugate' (A : Matrix n n α) [Nontrivial n] :
    adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A :=
  adjugate_adjugate _ <| Fintype.one_lt_card.ne'
#align matrix.adjugate_adjugate' Matrix.adjugate_adjugate'

end Adjugate

end Matrix
