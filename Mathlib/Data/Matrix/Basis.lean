/-
Copyright (c) 2020 Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Scott Morrison, Eric Wieser, Oliver Nash
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

#align_import data.matrix.basis from "leanprover-community/mathlib"@"320df450e9abeb5fc6417971e75acb6ae8bc3794"

/-!
# Matrices with a single non-zero element.

This file provides `matrix.stdBasisMatrix`. The matrix `matrix.stdBasisMatrix i j c` has `c`
at position `(i, j)`, and zeroes elsewhere.
-/


variable {l m n : Type*}

variable {R α : Type*}

namespace Matrix

open Matrix

open BigOperators

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [Semiring α]

/-- `stdBasisMatrix i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def stdBasisMatrix (i : m) (j : n) (a : α) : Matrix m n α := fun i' j' =>
  if i = i' ∧ j = j' then a else 0
#align matrix.std_basis_matrix Matrix.stdBasisMatrix

@[simp]
theorem smul_stdBasisMatrix (i : m) (j : n) (a b : α) :
    b • stdBasisMatrix i j a = stdBasisMatrix i j (b • a) := by
  unfold stdBasisMatrix
  -- ⊢ (b • fun i' j' => if i = i' ∧ j = j' then a else 0) = fun i' j' => if i = i' …
  ext
  -- ⊢ (b • fun i' j' => if i = i' ∧ j = j' then a else 0) i✝ x✝ = if i = i✝ ∧ j =  …
  simp
  -- 🎉 no goals
#align matrix.smul_std_basis_matrix Matrix.smul_stdBasisMatrix

@[simp]
theorem stdBasisMatrix_zero (i : m) (j : n) : stdBasisMatrix i j (0 : α) = 0 := by
  unfold stdBasisMatrix
  -- ⊢ (fun i' j' => if i = i' ∧ j = j' then 0 else 0) = 0
  ext
  -- ⊢ (if i = i✝ ∧ j = x✝ then 0 else 0) = OfNat.ofNat 0 i✝ x✝
  simp
  -- 🎉 no goals
#align matrix.std_basis_matrix_zero Matrix.stdBasisMatrix_zero

theorem stdBasisMatrix_add (i : m) (j : n) (a b : α) :
    stdBasisMatrix i j (a + b) = stdBasisMatrix i j a + stdBasisMatrix i j b := by
  unfold stdBasisMatrix; ext
  -- ⊢ (fun i' j' => if i = i' ∧ j = j' then a + b else 0) = (fun i' j' => if i = i …
                         -- ⊢ (if i = i✝ ∧ j = x✝ then a + b else 0) = ((fun i' j' => if i = i' ∧ j = j' t …
  split_ifs with h <;> simp [h]
  -- ⊢ a + b = ((fun i' j' => if i = i' ∧ j = j' then a else 0) + fun i' j' => if i …
                       -- 🎉 no goals
                       -- 🎉 no goals
#align matrix.std_basis_matrix_add Matrix.stdBasisMatrix_add

theorem matrix_eq_sum_std_basis [Fintype m] [Fintype n] (x : Matrix m n α) :
    x = ∑ i : m, ∑ j : n, stdBasisMatrix i j (x i j) := by
  ext i j; symm
  -- ⊢ x i j = Finset.sum Finset.univ (fun i => ∑ j : n, stdBasisMatrix i j (x i j) …
           -- ⊢ Finset.sum Finset.univ (fun i => ∑ j : n, stdBasisMatrix i j (x i j)) i j =  …
  iterate 2 rw [Finset.sum_apply]
  -- ⊢ ∑ c : m, Finset.sum Finset.univ (fun j => stdBasisMatrix c j (x c j)) i j =  …
  -- Porting note: was `convert`
  refine (Fintype.sum_eq_single i ?_).trans ?_; swap
  -- ⊢ ∀ (x_1 : m), x_1 ≠ i → Finset.sum Finset.univ (fun j => stdBasisMatrix x_1 j …
                                                -- ⊢ Finset.sum Finset.univ (fun j => stdBasisMatrix i j (x i j)) i j = x i j
  · -- Porting note: `simp` seems unwilling to apply `Fintype.sum_apply`
    simp only [stdBasisMatrix]
    -- ⊢ Finset.sum Finset.univ (fun x_1 i' j' => if i = i' ∧ x_1 = j' then x i x_1 e …
    rw [Fintype.sum_apply, Fintype.sum_apply]
    -- ⊢ (∑ c : n, if i = i ∧ c = j then x i c else 0) = x i j
    simp
    -- 🎉 no goals
  · intro j' hj'
    -- ⊢ Finset.sum Finset.univ (fun j => stdBasisMatrix j' j (x j' j)) i j = 0
    -- Porting note: `simp` seems unwilling to apply `Fintype.sum_apply`
    simp only [stdBasisMatrix]
    -- ⊢ Finset.sum Finset.univ (fun x_1 i' j'_1 => if j' = i' ∧ x_1 = j'_1 then x j' …
    rw [Fintype.sum_apply, Fintype.sum_apply]
    -- ⊢ (∑ c : n, if j' = i ∧ c = j then x j' c else 0) = 0
    simp [hj']
    -- 🎉 no goals
#align matrix.matrix_eq_sum_std_basis Matrix.matrix_eq_sum_std_basis

-- TODO: tie this up with the `Basis` machinery of linear algebra
-- this is not completely trivial because we are indexing by two types, instead of one
-- TODO: add `std_basis_vec`
theorem std_basis_eq_basis_mul_basis (i : m) (j : n) :
    stdBasisMatrix i j 1 = vecMulVec (fun i' => ite (i = i') 1 0) fun j' => ite (j = j') 1 0 := by
  ext i' j'
  -- ⊢ stdBasisMatrix i j 1 i' j' = vecMulVec (fun i' => if i = i' then 1 else 0) ( …
  -- Porting note: was `norm_num [std_basis_matrix, vec_mul_vec]` though there are no numerals
  -- involved.
  simp only [stdBasisMatrix, vecMulVec, mul_ite, mul_one, mul_zero, of_apply]
  -- ⊢ (if i = i' ∧ j = j' then 1 else 0) = if j = j' then if i = i' then 1 else 0  …
  -- Porting note: added next line
  simp_rw [@and_comm (i = i')]
  -- ⊢ (if j = j' ∧ i = i' then 1 else 0) = if j = j' then if i = i' then 1 else 0  …
  exact ite_and _ _ _ _
  -- 🎉 no goals
#align matrix.std_basis_eq_basis_mul_basis Matrix.std_basis_eq_basis_mul_basis

-- todo: the old proof used fintypes, I don't know `Finsupp` but this feels generalizable
@[elab_as_elim]
protected theorem induction_on' [Fintype m] [Fintype n] {P : Matrix m n α → Prop} (M : Matrix m n α)
    (h_zero : P 0) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ (i : m) (j : n) (x : α), P (stdBasisMatrix i j x)) : P M := by
  rw [matrix_eq_sum_std_basis M, ← Finset.sum_product']
  -- ⊢ P (∑ x in Finset.univ ×ˢ Finset.univ, stdBasisMatrix x.fst x.snd (M x.fst x. …
  apply Finset.sum_induction _ _ h_add h_zero
  -- ⊢ ∀ (x : m × n), x ∈ Finset.univ ×ˢ Finset.univ → P (stdBasisMatrix x.fst x.sn …
  · intros
    -- ⊢ P (stdBasisMatrix x✝.fst x✝.snd (M x✝.fst x✝.snd))
    apply h_std_basis
    -- 🎉 no goals
#align matrix.induction_on' Matrix.induction_on'

@[elab_as_elim]
protected theorem induction_on [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    {P : Matrix m n α → Prop} (M : Matrix m n α) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ i j x, P (stdBasisMatrix i j x)) : P M :=
  Matrix.induction_on' M
    (by
      inhabit m
      -- ⊢ P 0
      inhabit n
      -- ⊢ P 0
      simpa using h_std_basis default default 0)
      -- 🎉 no goals
    h_add h_std_basis
#align matrix.induction_on Matrix.induction_on

namespace StdBasisMatrix

section

variable (i : m) (j : n) (c : α) (i' : m) (j' : n)

@[simp]
theorem apply_same : stdBasisMatrix i j c i j = c :=
  if_pos (And.intro rfl rfl)
#align matrix.std_basis_matrix.apply_same Matrix.StdBasisMatrix.apply_same

@[simp]
theorem apply_of_ne (h : ¬(i = i' ∧ j = j')) : stdBasisMatrix i j c i' j' = 0 := by
  simp only [stdBasisMatrix, and_imp, ite_eq_right_iff]
  -- ⊢ i = i' → j = j' → c = 0
  tauto
  -- 🎉 no goals
#align matrix.std_basis_matrix.apply_of_ne Matrix.StdBasisMatrix.apply_of_ne

@[simp]
theorem apply_of_row_ne {i i' : m} (hi : i ≠ i') (j j' : n) (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hi]
                                         -- 🎉 no goals
#align matrix.std_basis_matrix.apply_of_row_ne Matrix.StdBasisMatrix.apply_of_row_ne

@[simp]
theorem apply_of_col_ne (i i' : m) {j j' : n} (hj : j ≠ j') (a : α) :
    stdBasisMatrix i j a i' j' = 0 := by simp [hj]
                                         -- 🎉 no goals
#align matrix.std_basis_matrix.apply_of_col_ne Matrix.StdBasisMatrix.apply_of_col_ne

end

section

variable (i j : n) (c : α) (i' j' : n)

@[simp]
theorem diag_zero (h : j ≠ i) : diag (stdBasisMatrix i j c) = 0 :=
  funext fun _ => if_neg fun ⟨e₁, e₂⟩ => h (e₂.trans e₁.symm)
#align matrix.std_basis_matrix.diag_zero Matrix.StdBasisMatrix.diag_zero

@[simp]
theorem diag_same : diag (stdBasisMatrix i i c) = Pi.single i c := by
  ext j
  -- ⊢ diag (stdBasisMatrix i i c) j = Pi.single i c j
  by_cases hij : i = j <;> (try rw [hij]) <;> simp [hij]
  -- ⊢ diag (stdBasisMatrix i i c) j = Pi.single i c j
                            -- ⊢ diag (stdBasisMatrix j j c) j = Pi.single j c j
                            -- ⊢ diag (stdBasisMatrix i i c) j = Pi.single i c j
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align matrix.std_basis_matrix.diag_same Matrix.StdBasisMatrix.diag_same

variable [Fintype n]

@[simp]
theorem trace_zero (h : j ≠ i) : trace (stdBasisMatrix i j c) = 0 := by
  -- Porting note: added `-diag_apply`
  simp [trace, -diag_apply, h]
  -- 🎉 no goals
#align matrix.std_basis_matrix.trace_zero Matrix.StdBasisMatrix.trace_zero

@[simp]
theorem trace_eq : trace (stdBasisMatrix i i c) = c := by
  -- Porting note: added `-diag_apply`
  simp [trace, -diag_apply]
  -- 🎉 no goals
#align matrix.std_basis_matrix.trace_eq Matrix.StdBasisMatrix.trace_eq

@[simp]
theorem mul_left_apply_same (b : n) (M : Matrix n n α) :
    (stdBasisMatrix i j c * M) i b = c * M j b := by simp [mul_apply, stdBasisMatrix]
                                                     -- 🎉 no goals
#align matrix.std_basis_matrix.mul_left_apply_same Matrix.StdBasisMatrix.mul_left_apply_same

@[simp]
theorem mul_right_apply_same (a : n) (M : Matrix n n α) :
    (M * stdBasisMatrix i j c) a j = M a i * c := by simp [mul_apply, stdBasisMatrix, mul_comm]
                                                     -- 🎉 no goals
#align matrix.std_basis_matrix.mul_right_apply_same Matrix.StdBasisMatrix.mul_right_apply_same

@[simp]
theorem mul_left_apply_of_ne (a b : n) (h : a ≠ i) (M : Matrix n n α) :
    (stdBasisMatrix i j c * M) a b = 0 := by simp [mul_apply, h.symm]
                                             -- 🎉 no goals
#align matrix.std_basis_matrix.mul_left_apply_of_ne Matrix.StdBasisMatrix.mul_left_apply_of_ne

@[simp]
theorem mul_right_apply_of_ne (a b : n) (hbj : b ≠ j) (M : Matrix n n α) :
    (M * stdBasisMatrix i j c) a b = 0 := by simp [mul_apply, hbj.symm]
                                             -- 🎉 no goals
#align matrix.std_basis_matrix.mul_right_apply_of_ne Matrix.StdBasisMatrix.mul_right_apply_of_ne

@[simp]
theorem mul_same (k : n) (d : α) :
    stdBasisMatrix i j c * stdBasisMatrix j k d = stdBasisMatrix i k (c * d) := by
  ext a b
  -- ⊢ (stdBasisMatrix i j c * stdBasisMatrix j k d) a b = stdBasisMatrix i k (c *  …
  simp only [mul_apply, stdBasisMatrix, boole_mul]
  -- ⊢ (∑ j_1 : n, (if i = a ∧ j = j_1 then c else 0) * if j = j_1 ∧ k = b then d e …
  by_cases h₁ : i = a <;> by_cases h₂ : k = b <;> simp [h₁, h₂]
  -- ⊢ (∑ j_1 : n, (if i = a ∧ j = j_1 then c else 0) * if j = j_1 ∧ k = b then d e …
                          -- ⊢ (∑ j_1 : n, (if i = a ∧ j = j_1 then c else 0) * if j = j_1 ∧ k = b then d e …
                          -- ⊢ (∑ j_1 : n, (if i = a ∧ j = j_1 then c else 0) * if j = j_1 ∧ k = b then d e …
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align matrix.std_basis_matrix.mul_same Matrix.StdBasisMatrix.mul_same

@[simp]
theorem mul_of_ne {k l : n} (h : j ≠ k) (d : α) :
    stdBasisMatrix i j c * stdBasisMatrix k l d = 0 := by
  ext a b
  -- ⊢ (stdBasisMatrix i j c * stdBasisMatrix k l d) a b = OfNat.ofNat 0 a b
  simp only [mul_apply, boole_mul, stdBasisMatrix]
  -- ⊢ (∑ j_1 : n, (if i = a ∧ j = j_1 then c else 0) * if k = j_1 ∧ l = b then d e …
  by_cases h₁ : i = a
  -- ⊢ (∑ j_1 : n, (if i = a ∧ j = j_1 then c else 0) * if k = j_1 ∧ l = b then d e …
  -- Porting note: was `simp [h₁, h, h.symm]`
  · simp only [h₁, true_and, mul_ite, ite_mul, zero_mul, mul_zero, ← ite_and, zero_apply]
    -- ⊢ (∑ x : n, if (k = x ∧ l = b) ∧ j = x then c * d else 0) = 0
    refine Finset.sum_eq_zero (fun x _ => ?_)
    -- ⊢ (if (k = x ∧ l = b) ∧ j = x then c * d else 0) = 0
    apply if_neg
    -- ⊢ ¬((k = x ∧ l = b) ∧ j = x)
    rintro ⟨⟨rfl, rfl⟩, h⟩
    -- ⊢ False
    contradiction
    -- 🎉 no goals
  · simp only [h₁, false_and, ite_false, mul_ite, zero_mul, mul_zero, ite_self,
      Finset.sum_const_zero, zero_apply]
#align matrix.std_basis_matrix.mul_of_ne Matrix.StdBasisMatrix.mul_of_ne

end

end StdBasisMatrix

end Matrix
