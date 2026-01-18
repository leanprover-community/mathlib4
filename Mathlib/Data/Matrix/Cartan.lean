/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Jonathan Reich
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Cartan matrices

This file defines Cartan matrices for simple Lie algebras, both the exceptional types
(E₆, E₇, E₈, F₄, G₂) and the classical infinite families (A, B, C, D).

## Main definitions

### Exceptional types
* `CartanMatrix.E₆` : The Cartan matrix of type E₆
* `CartanMatrix.E₇` : The Cartan matrix of type E₇
* `CartanMatrix.E₈` : The Cartan matrix of type E₈
* `CartanMatrix.F₄` : The Cartan matrix of type F₄
* `CartanMatrix.G₂` : The Cartan matrix of type G₂

### Classical types
* `CartanMatrix.A` : The Cartan matrix of type Aₙ₋₁ (corresponding to sl(n))
* `CartanMatrix.B` : The Cartan matrix of type Bₙ (corresponding to so(2n+1))
* `CartanMatrix.C` : The Cartan matrix of type Cₙ (corresponding to sp(2n))
* `CartanMatrix.D` : The Cartan matrix of type Dₙ (corresponding to so(2n))

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) plates I -- IX
* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*] Chapter 11

## Tags

cartan matrix, lie algebra, dynkin diagram
-/

@[expose] public section

namespace CartanMatrix

open Matrix

/-! ### Exceptional Cartan matrices -/

/-- The Cartan matrix of type E₆. See [bourbaki1968] plate V, page 277. -/
def E₆ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 2,  0, -1,  0,  0,  0;
      0,  2,  0, -1,  0,  0;
     -1,  0,  2, -1,  0,  0;
      0, -1, -1,  2, -1,  0;
      0,  0,  0, -1,  2, -1;
      0,  0,  0,  0, -1,  2]

/-- The Cartan matrix of type E₇. See [bourbaki1968] plate VI, page 281. -/
def E₇ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0;
      0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0, -1,  2]

/-- The Cartan matrix of type E₈. See [bourbaki1968] plate VII, page 285. -/
def E₈ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

/-- The Cartan matrix of type F₄. See [bourbaki1968] plate VIII, page 288. -/
def F₄ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 2, -1,  0,  0;
     -1,  2, -2,  0;
      0, -1,  2, -1;
      0,  0, -1,  2]

/-- The Cartan matrix of type G₂. See [bourbaki1968] plate IX, page 290.
We use the transpose of Bourbaki's matrix for consistency with F₄. -/
def G₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![ 2, -3;
     -1,  2]

/-! ### Classical Cartan matrices -/

/-- The Cartan matrix of type Aₙ₋₁ (rank n-1, corresponding to sl(n)). -/
def A (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1
    else 0

/-- The Cartan matrix of type Bₙ (rank n, corresponding to so(2n+1)). -/
def B (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then
      if j.val = n - 1 then -2 else -1
    else if j.val + 1 = i.val then -1
    else 0

/-- The Cartan matrix of type Cₙ (rank n, corresponding to sp(2n)). -/
def C (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then -1
    else if j.val + 1 = i.val then
      if i.val = n - 1 then -2 else -1
    else 0

/-- The Cartan matrix of type Dₙ (rank n, corresponding to so(2n)). -/
def D (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if n ≤ 2 then 0
    else if i.val + 1 = j.val ∧ j.val + 2 < n then -1
    else if j.val + 1 = i.val ∧ i.val + 2 < n then -1
    else if i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n) then -1
    else if j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n) then -1
    else 0

/-! ### Properties -/

section Properties

variable (n : ℕ)

@[simp] theorem A_diag : (A n).diag = 2 := by ext; simp [A]
@[simp] theorem B_diag (i : Fin n) : B n i i = 2 := by simp [B, Matrix.of_apply]
@[simp] theorem C_diag (i : Fin n) : C n i i = 2 := by simp [C, Matrix.of_apply]
@[simp] theorem D_diag (i : Fin n) : D n i i = 2 := by simp [D, Matrix.of_apply]

theorem A_apply_le_zero_of_ne (i j : Fin n) (h : i ≠ j) : A n i j ≤ 0 := by
  simp only [A, Matrix.of_apply]; split_ifs <;> omega

theorem B_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : B n i j ≤ 0 := by
  simp only [B, Matrix.of_apply]; split_ifs <;> omega

theorem C_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : C n i j ≤ 0 := by
  simp only [C, Matrix.of_apply]; split_ifs <;> omega

theorem D_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : D n i j ≤ 0 := by
  simp only [D, Matrix.of_apply]; split_ifs <;> omega

/-! ### Transpose properties -/

@[simp] theorem A_transpose : (A n).transpose = A n := by
  ext; simp only [A, transpose_apply, of_apply]; grind

@[simp] theorem B_transpose : (B n).transpose = C n := by
  ext; simp only [B, C, transpose_apply, of_apply]; grind

@[simp] theorem C_transpose : (C n).transpose = B n := by
  rw [← (B n).transpose_transpose, B_transpose]

@[simp] theorem D_transpose : (D n).transpose = D n := by
  ext; simp only [D, transpose_apply, of_apply]; grind

/-! ### Small cases -/

theorem A_one : A 1 = !![2] := by decide

theorem A_two : A 2 = !![ 2, -1;
                         -1,  2] := by decide

theorem A_three : A 3 = !![ 2, -1,  0;
                           -1,  2, -1;
                            0, -1,  2] := by decide

theorem B_one : B 1 = A 1 := by decide

theorem C_one : C 1 = A 1 := by decide

theorem D_one : D 1 = A 1 := by decide

theorem D_two : D 2 = !![2, 0;
                         0, 2] := by decide

theorem B_two : B 2 = !![ 2, -2;
                         -1,  2] := by decide

theorem C_two : C 2 = !![ 2, -1;
                         -2,  2] := by decide

theorem D_three : D 3 = !![ 2, -1, -1;
                           -1,  2,  0;
                           -1,  0,  2] := by decide

theorem D_three' : (D 3).reindex c[0, 1] c[0, 1] = A 3 := by decide

theorem D_four : D 4 = !![ 2, -1,  0,  0;
                          -1,  2, -1, -1;
                           0, -1,  2,  0;
                           0, -1,  0,  2] := by decide



/-! ### Exceptional matrix diagonal entries -/

@[simp] theorem E₆_diag (i : Fin 6) : E₆ i i = 2 := by fin_cases i <;> decide

@[simp] theorem E₇_diag (i : Fin 7) : E₇ i i = 2 := by fin_cases i <;> decide

@[simp] theorem E₈_diag (i : Fin 8) : E₈ i i = 2 := by fin_cases i <;> decide

@[simp] theorem F₄_diag (i : Fin 4) : F₄ i i = 2 := by fin_cases i <;> decide

@[simp] theorem G₂_diag (i : Fin 2) : G₂ i i = 2 := by fin_cases i <;> decide


/-! ### Exceptional matrix off-diagonal entries -/

theorem E₆_off_diag_nonpos (i j : Fin 6) (h : i ≠ j) : E₆ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [E₆]

theorem E₇_off_diag_nonpos (i j : Fin 7) (h : i ≠ j) : E₇ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [E₇]

theorem E₈_off_diag_nonpos (i j : Fin 8) (h : i ≠ j) : E₈ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [E₈]

theorem F₄_off_diag_nonpos (i j : Fin 4) (h : i ≠ j) : F₄ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [F₄]

theorem G₂_off_diag_nonpos (i j : Fin 2) (h : i ≠ j) : G₂ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [G₂]

/-! ### Exceptional matrix transpose properties -/

@[simp] theorem E₆_transpose : E₆.transpose = E₆ := by decide

@[simp] theorem E₇_transpose : E₇.transpose = E₇ := by decide

@[simp] theorem E₈_transpose : E₈.transpose = E₈ := by decide

/-! ### Exceptional matrix determinants -/

theorem G₂_det : G₂.det = 1 := by decide

theorem F₄_det : F₄.det = 1 := by decide

/-! The determinants of E₆, E₇, E₈ are 3, 2, 1 respectively.
`decide` fails for these larger matrices without increasing the max recursion depth.
We could write manual proofs (e.g., expanding via `det_succ_column_zero`),
but prefer to wait for a more principled determinant tactic. -/

proof_wanted E₆_det : E₆.det = 3

proof_wanted E₇_det : E₇.det = 2

proof_wanted E₈_det : E₈.det = 1

/-- A Cartan matrix is simply laced if its off-diagonal entries are all `0` or `-1`. -/
def _root_.Matrix.IsSimplyLaced {ι : Type*} (A : Matrix ι ι ℤ) : Prop :=
  Pairwise fun i j ↦ A i j = 0 ∨ A i j = -1

instance {ι : Type*} [Fintype ι] [DecidableEq ι] : DecidablePred (Matrix.IsSimplyLaced (ι := ι)) :=
  inferInstanceAs <|
    DecidablePred fun A : Matrix ι ι ℤ ↦ ∀ ⦃i j : ι⦄, i ≠ j → (fun i j ↦ A i j = 0 ∨ A i j = -1) i j

@[simp] theorem _root_.Matrix.isSimplyLaced_transpose {ι : Type*} (A : Matrix ι ι ℤ) :
    A.transpose.IsSimplyLaced ↔ A.IsSimplyLaced := by
  rw [IsSimplyLaced, IsSimplyLaced, Pairwise, Pairwise, forall_comm]
  aesop

theorem isSimplyLaced_A (n : ℕ) : IsSimplyLaced (A n) := by
  intro i j h
  simp only [A, of_apply]
  grind

theorem isSimplyLaced_D (n : ℕ) : IsSimplyLaced (D n) := by
  intro i j h
  simp only [D, of_apply]
  grind

theorem isSimplyLaced_E₆ : IsSimplyLaced E₆ :=
  fun i j h ↦ by fin_cases i <;> fin_cases j <;> simp [E₆] at h ⊢

theorem isSimplyLaced_E₇ : IsSimplyLaced E₇ :=
  fun i j h ↦ by fin_cases i <;> fin_cases j <;> simp [E₇] at h ⊢

theorem isSimplyLaced_E₈ : IsSimplyLaced E₈ :=
  fun i j h ↦ by fin_cases i <;> fin_cases j <;> simp [E₈] at h ⊢

/-! The Cartan matrices F₄ and G₂ are not simply laced because they contain
off-diagonal entries that are neither 0 nor -1. -/

theorem not_isSimplyLaced_F₄ : ¬ IsSimplyLaced F₄ := by decide

theorem not_isSimplyLaced_G₂ : ¬ IsSimplyLaced G₂ := by decide

end Properties

end CartanMatrix

end
