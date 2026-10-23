/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Jonathan Reich, Rida Hamadani
-/
module

public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Simproc.IsIndecomposable

/-!
# Cartan matrices

This file defines Cartan matrices for simple Lie algebras, both the exceptional types
(E₆, E₇, E₈, F₄, G₂) and the classical infinite families (A, B, C, D), as well as the
generalized Eₙ family obtained by continuing the E-type Dynkin diagram.

It also defines the predicate that a matrix is a finite-type Cartan matrix `Matrix.IsFiniteCartan`.

## Main definitions

### Exceptional types and the E family
* `CartanMatrix.E` : The Cartan matrix of type Eₙ
* `CartanMatrix.F₄` : The Cartan matrix of type F₄
* `CartanMatrix.G₂` : The Cartan matrix of type G₂

### Classical types
* `CartanMatrix.A` : The Cartan matrix of type Aₙ₋₁ (corresponding to sl(n))
* `CartanMatrix.B` : The Cartan matrix of type Bₙ (corresponding to so(2n+1))
* `CartanMatrix.C` : The Cartan matrix of type Cₙ (corresponding to sp(2n))
* `CartanMatrix.D` : The Cartan matrix of type Dₙ (corresponding to so(2n))

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*][bourbaki1968] plates I -- IX
* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972]
  Chapter 11

## Tags

cartan matrix, lie algebra, dynkin diagram
-/

@[expose] public section

open Matrix

namespace CartanMatrix

/-! ### Exceptional Cartan matrices -/

/-- The generalized Cartan matrix of type Eₙ, extending E₆, E₇, E₈ by the same Dynkin-diagram
pattern. -/
def E (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  .of fun i j =>
    if i = j then 2
    else if (i.val = 0 ∧ j.val = 2) ∨ (j.val = 0 ∧ i.val = 2) ∨
      (i.val = 1 ∧ j.val = 3) ∨ (j.val = 1 ∧ i.val = 3) ∨
      (2 ≤ i.val ∧ i.val + 1 = j.val) ∨ (2 ≤ j.val ∧ j.val + 1 = i.val)
    then -1 else 0

/-- `E 6` is the Cartan matrix of type E₆. See [bourbaki1968] plate V, page 277. -/
lemma E_six_eq :
    E 6 = !![ 2,  0, -1,  0,  0,  0;
              0,  2,  0, -1,  0,  0;
             -1,  0,  2, -1,  0,  0;
              0, -1, -1,  2, -1,  0;
              0,  0,  0, -1,  2, -1;
              0,  0,  0,  0, -1,  2] := by decide

/-- Deprecated alias for `E 6`. -/
@[deprecated "Use `E 6` instead" (since := "2026-07-29")]
abbrev E₆ : Matrix (Fin 6) (Fin 6) ℤ := E 6

/-- `E 7` is the Cartan matrix of type E₇. See [bourbaki1968] plate VI, page 281. -/
lemma E_seven_eq :
    E 7 = !![ 2,  0, -1,  0,  0,  0,  0;
              0,  2,  0, -1,  0,  0,  0;
             -1,  0,  2, -1,  0,  0,  0;
              0, -1, -1,  2, -1,  0,  0;
              0,  0,  0, -1,  2, -1,  0;
              0,  0,  0,  0, -1,  2, -1;
              0,  0,  0,  0,  0, -1,  2] := by decide

/-- Deprecated alias for `E 7`. -/
@[deprecated "Use `E 7` instead" (since := "2026-07-29")]
abbrev E₇ : Matrix (Fin 7) (Fin 7) ℤ := E 7

/-- `E 8` is the Cartan matrix of type E₈. See [bourbaki1968] plate VII, page 285. -/
lemma E_eight_eq :
    E 8 = !![ 2,  0, -1,  0,  0,  0,  0,  0;
              0,  2,  0, -1,  0,  0,  0,  0;
             -1,  0,  2, -1,  0,  0,  0,  0;
              0, -1, -1,  2, -1,  0,  0,  0;
              0,  0,  0, -1,  2, -1,  0,  0;
              0,  0,  0,  0, -1,  2, -1,  0;
              0,  0,  0,  0,  0, -1,  2, -1;
              0,  0,  0,  0,  0,  0, -1,  2] := by decide

/-- Deprecated alias for `E 8`. -/
@[deprecated "Use `E 8` instead" (since := "2026-07-29")]
abbrev E₈ : Matrix (Fin 8) (Fin 8) ℤ := E 8

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
  simp only [A, Matrix.of_apply]; split_ifs <;> lia

theorem B_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : B n i j ≤ 0 := by
  simp only [B, Matrix.of_apply]; split_ifs <;> lia

theorem C_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : C n i j ≤ 0 := by
  simp only [C, Matrix.of_apply]; split_ifs <;> lia

theorem D_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : D n i j ≤ 0 := by
  simp only [D, Matrix.of_apply]; split_ifs <;> lia

/-! ### Transpose properties -/

@[simp] theorem A_transpose : (A n).transpose = A n := by
  ext; simp only [A, transpose_apply, of_apply]; grind

theorem A_isSymm : (A n).IsSymm := A_transpose n

@[simp] theorem B_transpose : (B n).transpose = C n := by
  ext; simp only [B, C, transpose_apply, of_apply]; grind

@[simp] theorem C_transpose : (C n).transpose = B n := by
  rw [← (B n).transpose_transpose, B_transpose]

@[simp] theorem D_transpose : (D n).transpose = D n := by
  ext; simp only [D, transpose_apply, of_apply]; grind

theorem D_isSymm : (D n).IsSymm := D_transpose n

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

@[simp] theorem E_diag (n : ℕ) (i : Fin n) : E n i i = 2 := by
  simp [E]

@[deprecated "Use `E_diag` instead" (since := "2026-08-11")]
theorem E₆_diag (i : Fin 6) : E 6 i i = 2 := E_diag 6 i

@[deprecated "Use `E_diag` instead" (since := "2026-08-11")]
theorem E₇_diag (i : Fin 7) : E 7 i i = 2 := E_diag 7 i

@[deprecated "Use `E_diag` instead" (since := "2026-08-11")]
theorem E₈_diag (i : Fin 8) : E 8 i i = 2 := E_diag 8 i

@[simp] theorem F₄_diag (i : Fin 4) : F₄ i i = 2 := by fin_cases i <;> decide

@[simp] theorem G₂_diag (i : Fin 2) : G₂ i i = 2 := by fin_cases i <;> decide


/-! ### Exceptional matrix off-diagonal entries -/

theorem E_off_diag_nonpos (n : ℕ) (i j : Fin n) (h : i ≠ j) : E n i j ≤ 0 := by
  simp only [E, of_apply]
  split_ifs <;> lia

@[deprecated "Use `E_off_diag_nonpos` instead" (since := "2026-08-11")]
theorem E₆_off_diag_nonpos (i j : Fin 6) (h : i ≠ j) : E 6 i j ≤ 0 :=
  E_off_diag_nonpos 6 i j h

@[deprecated "Use `E_off_diag_nonpos` instead" (since := "2026-08-11")]
theorem E₇_off_diag_nonpos (i j : Fin 7) (h : i ≠ j) : E 7 i j ≤ 0 :=
  E_off_diag_nonpos 7 i j h

@[deprecated "Use `E_off_diag_nonpos` instead" (since := "2026-08-11")]
theorem E₈_off_diag_nonpos (i j : Fin 8) (h : i ≠ j) : E 8 i j ≤ 0 :=
  E_off_diag_nonpos 8 i j h

theorem F₄_off_diag_nonpos (i j : Fin 4) (h : i ≠ j) : F₄ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [F₄]

theorem G₂_off_diag_nonpos (i j : Fin 2) (h : i ≠ j) : G₂ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [G₂]

/-! ### Exceptional matrix transpose properties -/

@[simp] theorem E_transpose (n : ℕ) : (E n).transpose = E n := by
  ext i j
  simp only [E, transpose_apply, of_apply]
  grind

theorem E_isSymm (n : ℕ) : (E n).IsSymm := E_transpose n

@[deprecated "Use `E_transpose` instead" (since := "2026-08-11")]
theorem E₆_transpose : (E 6).transpose = E 6 := E_transpose 6

@[deprecated "Use `E_transpose` instead" (since := "2026-08-11")]
theorem E₇_transpose : (E 7).transpose = E 7 := E_transpose 7

@[deprecated "Use `E_transpose` instead" (since := "2026-08-11")]
theorem E₈_transpose : (E 8).transpose = E 8 := E_transpose 8

@[deprecated "Use `E_isSymm` instead" (since := "2026-08-11")]
theorem E₆_isSymm : (E 6).IsSymm := E_isSymm 6

@[deprecated "Use `E_isSymm` instead" (since := "2026-08-11")]
theorem E₇_isSymm : (E 7).IsSymm := E_isSymm 7

@[deprecated "Use `E_isSymm` instead" (since := "2026-08-11")]
theorem E₈_isSymm : (E 8).IsSymm := E_isSymm 8

/-! ### Exceptional matrix determinants -/

theorem G₂_det : G₂.det = 1 := by decide

theorem F₄_det : F₄.det = 1 := by decide

/-- Append a new node to the end of a path-like Dynkin diagram: `M` occupies the top-left block
and the new node (index `Fin.last`) is joined to the previous final node by a `-1` edge. -/
private def extendPath {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n.succ) (Fin n.succ) ℤ :=
  letI tailLink := fun i : Fin n ↦ if i.val + 1 = n then -1 else 0
  fun i j ↦
    Fin.lastCases (Fin.lastCases 2 tailLink j)
      (fun i ↦ Fin.lastCases (tailLink i) (fun j ↦ M i j) j) i

private theorem extendPath_tail {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    (extendPath M).submatrix Fin.castSucc Fin.castSucc = M := by
  ext i j
  simp [extendPath]

private theorem extendPath_minor {n : ℕ} (M : Matrix (Fin n.succ) (Fin n.succ) ℤ) :
    ((extendPath M).submatrix Fin.castSucc (Fin.succAbove (Fin.castSucc (Fin.last n)))).det =
      -(M.submatrix Fin.castSucc Fin.castSucc).det := by
  let B := (extendPath M).submatrix Fin.castSucc (Fin.succAbove (Fin.castSucc (Fin.last n)))
  have hlast : B (Fin.last n) (Fin.last n) = -1 := by simp [B, extendPath]
  have hzero (i : Fin n) : B i.castSucc (Fin.last n) = 0 := by simp [B, extendPath]; grind
  have hminor : B.submatrix Fin.castSucc Fin.castSucc = M.submatrix Fin.castSucc Fin.castSucc := by
    ext; simp [B, extendPath]
  change B.det = _
  simp [Matrix.det_succ_column B (Fin.last n), Fin.sum_univ_castSucc, hlast, hzero, hminor]

private theorem extendPath_det {n : ℕ} (M : Matrix (Fin n.succ) (Fin n.succ) ℤ) :
    (extendPath M).det = 2 * M.det - (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row (extendPath M) (Fin.last _), Fin.sum_univ_castSucc]
  simp only [extendPath, extendPath_tail, Fin.lastCases_last, Fin.lastCases_castSucc,
    Fin.val_last, Fin.val_castSucc, Fin.succAbove_last]
  rw [Finset.sum_eq_single_of_mem (Fin.last n) (Finset.mem_univ _)]
  · rw [ite_eq_left (by rfl), extendPath_minor, Fin.val_last, Odd.neg_one_pow ⟨n, by ring⟩,
      Even.neg_one_pow ⟨n + 1, rfl⟩]
    ring
  · intro b _ hb
    rw [ite_eq_right (fun h => hb (Fin.ext (by rw [Fin.val_last]; lia)))]
    ring

private theorem E_succ (n : ℕ) (hn : 4 ≤ n) :
    E (n + 1) = extendPath (E n) := by
  ext i j
  refine Fin.lastCases ?_ (fun i ↦ Fin.lastCases ?_ (fun j ↦ ?_) j) i
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simp [E, extendPath]
    · simp only [E, of_apply, extendPath, Fin.lastCases_last, Fin.lastCases_castSucc,
        Fin.val_last, Fin.val_castSucc]
      grind
  · simp only [E, of_apply, extendPath, Fin.lastCases_last, Fin.lastCases_castSucc,
      Fin.val_last, Fin.val_castSucc]
    grind
  · simp only [E, of_apply, extendPath, Fin.lastCases_castSucc, Fin.val_castSucc,
      Fin.castSucc_inj]

theorem det_E_add_two (n : ℕ) (hn : 4 ≤ n) :
    (E (n + 2)).det = 2 * (E (n + 1)).det - (E n).det := by
  have htail : (E (n + 1)).submatrix Fin.castSucc Fin.castSucc = E n := by
    rw [E_succ n hn, extendPath_tail]
  rw [E_succ (n + 1) (by lia), extendPath_det, htail]

/-- The determinant of `E n` is `9 - n` for `n ≥ 3`. -/
theorem E_det {n : ℕ} (hn : 3 ≤ n) : (E n).det = 9 - n := by
  rcases eq_or_ne n 3 with rfl | hn; · decide
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (show 4 ≤ n by lia)
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one =>
    have : E 5 =
      !![ 2,  0, -1,  0,  0;
          0,  2,  0, -1,  0;
         -1,  0,  2, -1,  0;
          0, -1, -1,  2, -1;
          0,  0,  0, -1,  2] := by decide
    simp [this, norm_det]
  | more n hn hn1 => rw [det_E_add_two (n + 4) (by lia)]; grind

/-! The determinants of E₆, E₇, E₈ are 3, 2, 1 respectively. -/

theorem E₆_det : (E 6).det = 3 := by
  simp only [E_six_eq, norm_det]

theorem E₇_det : (E 7).det = 2 := by
  simp only [E_seven_eq, norm_det]

theorem E₈_det : (E 8).det = 1 := by
  simp only [E_eight_eq, norm_det]

/-- A Cartan matrix is simply laced if its off-diagonal entries are all `0` or `-1`. -/
def _root_.Matrix.IsSimplyLaced {ι : Type*} (A : Matrix ι ι ℤ) : Prop :=
  Pairwise fun i j ↦ A i j = 0 ∨ A i j = -1

set_option backward.isDefEq.respectTransparency.types false in
instance {ι : Type*} [Fintype ι] [DecidableEq ι] : DecidablePred (Matrix.IsSimplyLaced (ι := ι)) :=
  inferInstanceAs <|
    DecidablePred fun A : Matrix ι ι ℤ ↦ ∀ ⦃i j : ι⦄, i ≠ j → (fun i j ↦ A i j = 0 ∨ A i j = -1) i j

lemma _root_.Matrix.isSimplyLaced_iff_of_linearOrder
    {ι : Type*} [LinearOrder ι] (A : Matrix ι ι ℤ) (hA : A.IsSymm) :
    A.IsSimplyLaced ↔ ∀ ⦃i j : ι⦄, j < i → (A i j = 0 ∨ A i j = -1) := by
  constructor
  · intro h i j hij
    exact h hij.ne'
  · intro h i j hij
    obtain hij | hij := hij.lt_or_gt
    · simpa only [hA.apply i j] using h hij
    · exact h hij

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

theorem isSimplyLaced_E (n : ℕ) : IsSimplyLaced (E n) := by
  intro i j h
  simp only [E, of_apply]
  split_ifs <;> simp_all

@[deprecated "Use `isSimplyLaced_E` instead" (since := "2026-08-11")]
theorem isSimplyLaced_E₆ : IsSimplyLaced (E 6) := isSimplyLaced_E 6

@[deprecated "Use `isSimplyLaced_E` instead" (since := "2026-08-11")]
theorem isSimplyLaced_E₇ : IsSimplyLaced (E 7) := isSimplyLaced_E 7

@[deprecated "Use `isSimplyLaced_E` instead" (since := "2026-08-11")]
theorem isSimplyLaced_E₈ : IsSimplyLaced (E 8) := isSimplyLaced_E 8

/-! The Cartan matrices F₄ and G₂ are not simply laced because they contain
off-diagonal entries that are neither 0 nor -1. -/

theorem not_isSimplyLaced_F₄ : ¬ IsSimplyLaced F₄ := by decide

theorem not_isSimplyLaced_G₂ : ¬ IsSimplyLaced G₂ := by decide

theorem isIndecomposable_E_six : (E 6).IsIndecomposable := by
  simp only [E_six_eq, reduceIsIndecomposable]

theorem isIndecomposable_E_seven : (E 7).IsIndecomposable := by
  simp only [E_seven_eq, reduceIsIndecomposable]

theorem isIndecomposable_E_eight : (E 8).IsIndecomposable := by
  simp only [E_eight_eq, reduceIsIndecomposable]

theorem isIndecomposable_F₄ : F₄.IsIndecomposable := by
  simp only [F₄, reduceIsIndecomposable]

theorem isIndecomposable_G₂ : G₂.IsIndecomposable := by
  simp only [G₂, reduceIsIndecomposable]

end Properties

end CartanMatrix

/-- The proposition that a matrix is a finite-type Cartan matrix. -/
structure Matrix.IsFiniteCartan {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) : Prop where
  diag : ∀ i, M i i = 2
  offDiag_nonpos : ∀ i j, i ≠ j → M i j ≤ 0
  zero_comm : ∀ i j, M i j = 0 ↔ M j i = 0
  exists_posDef : ∃ d : ι → ℤ, (∀ i, 0 < d i) ∧ (diagonal d * M).PosDef

namespace Matrix.IsFiniteCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℤ} (hM : M.IsFiniteCartan)
include hM

lemma det_pos :
    0 < M.det := by
  obtain ⟨d, hd, hd'⟩ := hM.exists_posDef
  replace hd : 0 < (diagonal d).det := by simpa using Finset.prod_pos fun i a ↦ hd i
  replace hd' : 0 < (diagonal d).det * M.det := by simpa only [← det_mul] using hd'.det_pos
  nlinarith

protected lemma isUnit_map (k : Type*) [Field k] [CharZero k] :
    IsUnit <| M.map (Int.cast : ℤ → k) := by
  suffices IsUnit <| (Int.castRingHom k).mapMatrix M by simpa
  rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det]
  simpa using hM.det_pos.ne'

protected lemma transpose :
    Mᵀ.IsFiniteCartan := by
  obtain ⟨d, hd_pos, hdM⟩ := hM.exists_posDef
  set d' : ι → ℤ := fun i ↦ ∏ j ∈ Finset.univ.erase i, d j with hd'
  have hd'_pos (i : ι) : 0 < d' i := Finset.prod_pos fun j _ ↦ hd_pos j
  suffices (diagonal d' * Mᵀ).PosDef from
    { diag i := by simpa using hM.diag i
      offDiag_nonpos i j hij := by simpa using hM.offDiag_nonpos j i hij.symm
      zero_comm i j := by simpa using hM.zero_comm j i
      exists_posDef := ⟨d', hd'_pos, this⟩ }
  set C : ℤ := ∏ j, d j with hC
  have hCd (i : ι) : d i * d' i = C := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  have hsymm (i j : ι) : d' i * M j i = d' j * M i j := by
    apply mul_left_cancel₀ (a := d i * d j) (by simp [(hd_pos _).ne'])
    have aux : d i * M i j = d j * M j i := by simpa using hdM.isHermitian.apply j i
    linear_combination (d j * M j i) * hCd i - (d i * M i j) * hCd j - C * aux
  suffices ∀ v : ι → ℤ, v ≠ 0 → 0 < star v ⬝ᵥ (diagonal d' * Mᵀ) *ᵥ v from
    posDef_iff_dotProduct_mulVec.mpr ⟨by ext i j; simpa using (hsymm i j).symm, this⟩
  intro v hv
  have key : (d' * v) ⬝ᵥ (diagonal d * M) *ᵥ (d' * v) = C * (v ⬝ᵥ (diagonal d' * Mᵀ) *ᵥ v) := by
    simp only [dotProduct, mulVec, diagonal_mul, transpose_apply, Finset.mul_sum, Pi.mul_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    linear_combination (M i j * d' j * v i * v j) * hCd i - (C * v i * v j) * hsymm i j
  have hpos := hdM.dotProduct_mulVec_pos (x := d' * v) <|
    fun h ↦ hv (funext fun i ↦ by simpa [(hd'_pos i).ne'] using congr_fun h i)
  rw [star_trivial, key] at hpos
  have hCpos : 0 < C := Finset.prod_pos fun j _ ↦ hd_pos j
  rwa [star_trivial, ← mul_pos_iff_of_pos_left hCpos]

omit hM in
@[simp] protected lemma transpose_iff :
    Mᵀ.IsFiniteCartan ↔ M.IsFiniteCartan :=
  ⟨fun h ↦ by simpa using h.transpose, IsFiniteCartan.transpose⟩

end Matrix.IsFiniteCartan

namespace CartanMatrix

theorem isFiniteCartan_a (n : ℕ) : (A n).IsFiniteCartan where
  diag := by simp [← diag_apply, A_diag]
  offDiag_nonpos := A_apply_le_zero_of_ne n
  zero_comm i j := by dsimp [A]; grind
  exists_posDef := by
    use 1
    simp only [Pi.one_apply, zero_lt_one, implies_true, diagonal_one', one_mul, true_and]
    let M : Matrix (Fin (n + 1)) (Fin n) ℤ := fun i j ↦
        (if i = j.castSucc then 1 else 0) + if i = j.succ then -1 else 0
    have hsum (a b : Fin (n + 1)) (hab : a ≠ b) (f : Fin (n + 1) → ℤ) :
        (∑ x, if x = a then f x else if x = b then -f x else 0) = f a - f b := calc
      _ = ∑ x, ((if x = a then f x else 0) + (if x = b then -f x else 0)) := by grind
      _ = _ := by simp [Finset.sum_add_distrib, Int.add_neg_eq_sub]
    have h : A n = Mᴴ * M := by
      ext i j
      rw [conjTranspose_eq_transpose_of_trivial, mul_apply]
      dsimp [A]
      grind [transpose_apply, hsum j.castSucc j.succ (by grind) (fun x ↦ if x = i.castSucc then 1
        else if x = i.succ then -1 else 0)]
    rw [h]
    apply PosDef.conjTranspose_mul_self
    intro x y hxy
    funext ⟨k, hk⟩
    induction k with
    | zero =>
      have hp (z : Fin n → ℤ) : (∑ j, (if 0 = j.castSucc then 1 else 0) * z j) = z ⟨0, hk⟩ := calc
        _ = ∑ j, (if j = ⟨0, hk⟩ then 1 else 0) * z j := by grind
        _ = z ⟨0, hk⟩ := by simp
      have hn (z : Fin n → ℤ) : (∑ j, (if 0 = j.succ then -1 else 0) * z j) = 0 := by
        grind [Finset.sum_eq_zero]
      have h (z : Fin n → ℤ) : (M.mulVec z) 0 = z ⟨0, hk⟩ := by
        simp_rw [mulVec_apply_eq_sum, M, add_mul, Finset.sum_add_distrib, hp z, hn z, add_zero]
      have heq := congrFun hxy 0
      rwa [h x, h y] at heq
    | succ k =>
      have hk' : k < n := Nat.lt_of_succ_lt hk
      have hp (z : Fin n → ℤ) : (∑ j, (if Fin.succ ⟨k, hk'⟩ = j.castSucc then 1 else 0) * z j)
          = z ⟨k + 1, hk⟩ := calc
        _ = ∑ j : Fin n, (if j = ⟨k + 1, hk⟩ then 1 else 0) * z j := by grind
        _ = _ := by simp
      have hn (z : Fin n → ℤ) : (∑ j, (if Fin.succ ⟨k, hk'⟩ = j.succ then -1 else 0) * z j)
          = -z ⟨k, hk'⟩ := calc
        _ = ∑ j, (if j = ⟨k, hk'⟩ then -1 else 0) * z j := by grind
        _ = _ := by simp
      have h (z : Fin n → ℤ) : (M.mulVec z) (Fin.succ ⟨k, hk'⟩) = z ⟨k + 1, hk⟩ - z ⟨k, hk'⟩ := by
        simp_rw [mulVec_apply_eq_sum, M, add_mul, Finset.sum_add_distrib, hp z, hn z,
          Int.add_neg_eq_sub]
      grind [congrFun hxy (Fin.succ ⟨k, hk'⟩)]

theorem isFiniteCartan_b (n : ℕ) : (B n).IsFiniteCartan where
  diag := B_diag n
  offDiag_nonpos := B_off_diag_nonpos n
  zero_comm i j := by
    dsimp [B]
    split_ifs <;> grind
  exists_posDef := by
    let d : Fin n → ℤ := fun i ↦ if i.val + 1 = n then 2 else 1
    use d
    refine ⟨fun i ↦ by grind, ?_⟩
    let M : Matrix (Fin (n + 1)) (Fin n) ℤ := fun i j ↦ (if i = j.castSucc then d j else 0) +
      (if i = j.succ then if j.val + 1 = n then 0 else -1 else 0)
    have h (a b : Fin (n + 1)) (hab : a ≠ b) (c₁ c₂ : ℤ) (f : Fin (n + 1) → ℤ) : (∑ x, if x = a
        then c₁ * f x else if x = b then c₂ * f x else 0) = c₁ * f a + c₂ * f b := calc
      _ = ∑ x, ((if x = a then c₁ * f x else 0) + if x = b then c₂ * f x else 0) := by grind
      _ = _ := by simp [Finset.sum_add_distrib]
    have h : diagonal d * B n = Mᴴ * M := by
      ext i j
      have : (∑ x, M x i * M x j)
          = d j * M (j.castSucc) i + (if j.val + 1 = n then 0 else -1) * M (j.succ) i := calc
        _ = _ := by grind
        _ = _ := h j.castSucc j.succ (by grind) (d j) (if j + 1 = n then 0 else -1) (fun x ↦ M x i)
      calc
        _ = d i * B n i j := by simp [diagonal, mul_apply]
        _ = ∑ x : Fin (n + 1), M x i * M x j := by dsimp [B, d, M]; grind
        _ = _ := by simp_rw [conjTranspose_eq_transpose_of_trivial, mul_apply, transpose_apply]
    rw [h]
    apply PosDef.conjTranspose_mul_self
    intro _ _ hxy
    funext ⟨k, hk⟩
    induction k with
    | zero =>
      have hp (z : Fin n → ℤ) : ∑ j, (if 0 = j.castSucc then d j else 0) * z j = d ⟨0, hk⟩
          * z ⟨0, hk⟩ := calc
        _ = ∑ j : Fin n, (if j = (⟨0, hk⟩ : Fin n) then d j else 0) * z j := by grind
        _ = _ := by simp
      have hn (z : Fin n → ℤ) : (∑ j, (if 0 = j.succ then (if j.val + 1 = n then 0 else -1) else 0)
          * z j) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp [show 0 ≠ j.succ by grind]
      have (z : Fin n → ℤ) : (M.mulVec z) 0 = d ⟨0, hk⟩ * z ⟨0, hk⟩ := by
        simp_rw [mulVec_apply_eq_sum, M, add_mul, Finset.sum_add_distrib, hp z, hn z, add_zero]
      grind [congrFun hxy 0]
    | succ k =>
      have hk' : k < n := Nat.lt_of_succ_lt hk
      have hp (z : Fin n → ℤ) : ∑ j, (if Fin.succ ⟨k, hk'⟩ = j.castSucc then d j else 0) * z j
          = d ⟨k + 1, hk⟩ * z ⟨k + 1, hk⟩ := calc
        _ = ∑ j, (if j = ⟨k + 1, hk⟩ then d j else 0) * z j := by grind
        _ = _ := by simp
      have hn (z : Fin n → ℤ) : ∑ j, (if Fin.succ ⟨k, hk'⟩ = j.succ then (if j.val + 1
          = n then 0 else -1) else 0) * z j = -z ⟨k, hk'⟩ := calc
        _ = ∑ j, (if j = ⟨k, hk'⟩ then -1 else 0) * z j := by grind
        _ = _ := by simp
      have h (z : Fin n → ℤ) : (M.mulVec z) (Fin.succ ⟨k, hk'⟩) = d ⟨k + 1, hk⟩ * z ⟨k + 1, hk⟩
          - z ⟨k, hk'⟩ := by
        simp_rw [mulVec_apply_eq_sum, M, add_mul, Finset.sum_add_distrib, hp z, hn z,
          Int.add_neg_eq_sub]
      grind [congrFun hxy (Fin.succ ⟨k, hk'⟩)]

theorem isFiniteCartan_c (n : ℕ) : (C n).IsFiniteCartan where
  diag := C_diag n
  offDiag_nonpos := C_off_diag_nonpos n
  zero_comm i j := by
    dsimp [C]
    split_ifs <;> grind
  exists_posDef := by
    let d : Fin n → ℤ := fun i ↦ if i.val + 1 = n then 2 else 4
    use d
    refine ⟨fun i ↦ by grind, ?_⟩
    let M : Matrix (Fin (n + 1)) (Fin n) ℤ := fun i j ↦ (if i = j.castSucc then 2 else 0)
      + (if i = j.succ then if j.val + 1 = n then 0 else -2 else 0)
    have h (a b : Fin (n + 1)) (hab : a ≠ b) (c₁ c₂ : ℤ) (f : Fin (n + 1) → ℤ) : (∑ x, if x = a
        then c₁ * f x else if x = b then c₂ * f x else 0) = c₁ * f a + c₂ * f b := calc
      _ = ∑ x, ((if x = a then c₁ * f x else 0) + if x = b then c₂ * f x else 0) := by grind
      _ = _ := by simp [Finset.sum_add_distrib]
    have h : diagonal d * C n = Mᴴ * M := by
      ext i j
      have : (∑ x, M x i * M x j)
          = 2 * M (j.castSucc) i + (if j.val + 1 = n then 0 else -2) * M (j.succ) i := calc
        _ = _ := by grind
        _ = _ := h j.castSucc j.succ (by grind) 2 (if j.val + 1 = n then 0 else -2) (fun x ↦ M x i)
      calc
        _ = d i * C n i j := by simp [mul_apply, diagonal]
        _ = ∑ x, M x i * M x j := by dsimp [C, d, M]; grind
        _ = _ := by
          simp_rw [conjTranspose_eq_transpose_of_trivial, mul_apply, transpose_apply]
    rw [h]
    apply PosDef.conjTranspose_mul_self
    intro _ _ hxy
    funext ⟨k, hk⟩
    induction k with
    | zero =>
      have hp (z : Fin n → ℤ) : ∑ j, (if 0 = j.castSucc then 2 else 0) * z j = 2 * z ⟨0, hk⟩ := calc
        _ = ∑ j : Fin n, (if j = ⟨0, hk⟩ then 2 else 0) * z j := by grind
        _ = _ := by simp
      have hn (z : Fin n → ℤ) : ∑ j, (if 0 = j.succ then (if j.val + 1 = n then 0 else -2) else 0)
          * z j = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp [show 0 ≠ j.succ by grind]
      have (z : Fin n → ℤ) : (M.mulVec z) 0 = 2 * z ⟨0, hk⟩ := by
        simp_rw [mulVec_apply_eq_sum, M, add_mul, Finset.sum_add_distrib, hp z, hn z, add_zero]
      grind [congrFun hxy 0]
    | succ k =>
      have hk' : k < n := Nat.lt_of_succ_lt hk
      have hp (z : Fin n → ℤ) : (∑ j, (if Fin.succ ⟨k, hk'⟩ = j.castSucc then 2 else 0) * z j) =
          2 * z ⟨k + 1, hk⟩ := calc
        _ = ∑ j, (if j = (⟨k + 1, hk⟩ : Fin n) then 2 else 0) * z j := by grind
        _ = _ := by simp
      have hn (z : Fin n → ℤ) : ∑ j, (if Fin.succ ⟨k, hk'⟩ = j.succ then (if j.val + 1 = n then 0
          else -2) else 0) * z j = -2 * z ⟨k, hk'⟩ := calc
        _ = ∑ j, (if j = (⟨k, hk'⟩ : Fin n) then -2 else 0) * z j := by grind
        _ = _ := by simp
      have (z : Fin n → ℤ) : (M.mulVec z) (Fin.succ ⟨k, hk'⟩) = 2 * z ⟨k + 1, hk⟩
          - 2 * z ⟨k, hk'⟩ := by
        simp_rw [mulVec_apply_eq_sum, M, add_mul, Finset.sum_add_distrib, hp z, hn z]
        ring
      grind [congrFun hxy (Fin.succ ⟨k, hk'⟩)]

theorem isFiniteCartan_e₆ : (E 6).IsFiniteCartan where
  diag := E_diag 6
  offDiag_nonpos := E_off_diag_nonpos 6
  zero_comm i j := by fin_cases i <;> fin_cases j <;> rfl
  exists_posDef := by
    use 1
    simp only [Pi.one_apply, zero_lt_one, implies_true, diagonal_one', E_six_eq, Int.reduceNeg,
      one_mul, true_and]
    apply PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    intro x hx
    simp only [star_trivial, Int.reduceNeg, cons_mulVec, cons_dotProduct, zero_mul,
      show vecHead x = x 0 by rfl, Fin.isValue, show vecHead (vecTail x) = x 1 by rfl,
      show vecHead (vecTail (vecTail x)) = x 2 by rfl, neg_mul, one_mul,
      show vecHead (vecTail (vecTail (vecTail x))) = x 3 by rfl,
      show vecHead (vecTail (vecTail (vecTail (vecTail x)))) = x 4 by rfl,
      show vecHead (vecTail (vecTail (vecTail (vecTail (vecTail x))))) = x 5 by rfl,
      dotProduct_of_isEmpty, add_zero, zero_add, empty_mulVec, dotProduct_cons]
    apply pos_of_mul_pos_right (a := 6) ?_ (by positivity)
    have : 6 * (x 0 * (2 * x 0 + -x 2) + (x 1 * (2 * x 1 + -x 3) + (x 2 * (-x 0 + (2 * x 2 + -x 3))
        + (x 3 * (-x 1 + (-x 2 + (2 * x 3 + -x 4))) + (x 4 * (-x 3 + (2 * x 4 + -x 5))
        + x 5 * (-x 4 + 2 * x 5)))))) = 3 * (2 * x 0 - x 2) ^ 2 + (3 * x 2 - 2 * x 3) ^ 2 +
        3 * (2 * x 1 - x 3) ^ 2 + (3 * x 4 - 2 * x 3) ^ 2 + 3 * (2 * x 5 - x 4) ^ 2 + x 3 ^ 2 := by
      ring
    rw [this]
    apply lt_of_le_of_ne
    · positivity
    · symm
      contrapose hx
      repeat rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)] at hx
      obtain ⟨⟨_, _⟩, _⟩ := hx
      ext i
      rw [Pi.zero_apply]
      fin_cases i <;> simp_all

theorem isFiniteCartan_e₇ : (E 7).IsFiniteCartan where
  diag := E_diag 7
  offDiag_nonpos := E_off_diag_nonpos 7
  zero_comm i j := by fin_cases i <;> fin_cases j <;> rfl
  exists_posDef := by
    use 1
    simp only [Pi.one_apply, zero_lt_one, implies_true, diagonal_one', E_seven_eq, Int.reduceNeg,
      one_mul, true_and]
    apply PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    intro x hx
    simp only [star_trivial, Int.reduceNeg, cons_mulVec, cons_dotProduct, zero_mul,
      show vecHead x = x 0 by rfl, Fin.isValue, show vecHead (vecTail x) = x 1 by rfl,
      show vecHead (vecTail (vecTail x)) = x 2 by rfl, neg_mul, one_mul,
      show vecHead (vecTail (vecTail (vecTail x))) = x 3 by rfl,
      show vecHead (vecTail (vecTail (vecTail (vecTail x)))) = x 4 by rfl,
      show vecHead (vecTail (vecTail (vecTail (vecTail (vecTail x))))) = x 5 by rfl,
      show vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail x)))))) = x 6 by rfl,
      dotProduct_of_isEmpty, add_zero, zero_add, empty_mulVec, dotProduct_cons]
    apply pos_of_mul_pos_right (a := 12) ?_ (by positivity)
    have : 12 * (x 0 * (2 * x 0 + -x 2) + (x 1 * (2 * x 1 + -x 3) + (x 2 * (-x 0 + (2 * x 2 + -x 3))
        + (x 3 * (-x 1 + (-x 2 + (2 * x 3 + -x 4))) + (x 4 * (-x 3 + (2 * x 4 + -x 5)) + (x 5 *
        (-x 4 + (2 * x 5 + -x 6)) + x 6 * (-x 5 + 2 * x 6))))))) = 6 * (2 * x 0 - x 2) ^ 2
        + 2 * (3 * x 2 - 2 * x 3) ^ 2 + 6 * (2 * x 1 - x 3) ^ 2 + (4 * x 4 - 3 * x 3) ^ 2
        + 2 * (3 * x 5 - 2 * x 4) ^ 2 + 6 * (2 * x 6 - x 5) ^ 2 + x 3 ^ 2 := by ring
    rw [this]
    apply lt_of_le_of_ne
    · positivity
    · symm
      contrapose hx
      repeat rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)] at hx
      obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := hx
      ext i
      rw [Pi.zero_apply]
      fin_cases i <;> simp_all

theorem isFiniteCartan_e₈ : (E 8).IsFiniteCartan where
  diag := E_diag 8
  offDiag_nonpos := E_off_diag_nonpos 8
  zero_comm i j := by fin_cases i <;> fin_cases j <;> rfl
  exists_posDef := by
    use 1
    simp only [Pi.one_apply, zero_lt_one, implies_true, diagonal_one', E_eight_eq, Int.reduceNeg,
      one_mul, true_and]
    apply PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    intro x hx
    simp only [star_trivial, Int.reduceNeg, cons_mulVec, cons_dotProduct, zero_mul,
      show vecHead x = x 0 by rfl, Fin.isValue, show vecHead (vecTail x) = x 1 by rfl,
      show vecHead (vecTail (vecTail x)) = x 2 by rfl, neg_mul, one_mul,
      show vecHead (vecTail (vecTail (vecTail x))) = x 3 by rfl,
      show vecHead (vecTail (vecTail (vecTail (vecTail x)))) = x 4 by rfl,
      show vecHead (vecTail (vecTail (vecTail (vecTail (vecTail x))))) = x 5 by rfl,
      show vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail x)))))) = x 6 by rfl,
      show vecHead (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail (vecTail x))))))) = x 7 by
      rfl, dotProduct_of_isEmpty, add_zero, zero_add, empty_mulVec, dotProduct_cons]
    apply pos_of_mul_pos_right (a := 60) ?_ (by positivity)
    have : 60 * (x 0 * (2 * x 0 + -x 2) + (x 1 * (2 * x 1 + -x 3) + (x 2 * (-x 0 + (2 * x 2 + -x 3))
        + (x 3 * (-x 1 + (-x 2 + (2 * x 3 + -x 4))) + (x 4 * (-x 3 + (2 * x 4 + -x 5)) + (x 5 * (-x
        4 + (2 * x 5 + -x 6)) + (x 6 * (-x 5 + (2 * x 6 + -x 7)) + x 7 * (-x 6 + 2 * x 7)))))))) =
        30 * (2 * x 0 - x 2) ^ 2 + 10 * (3 * x 2 - 2 * x 3) ^ 2 + 30 * (2 * x 1 - x 3) ^ 2
        + 3 * (5 * x 4 - 4 * x 3) ^ 2 + 5 * (4 * x 5 - 3 * x 4) ^ 2 + 10 * (3 * x 6 - 2 * x 5) ^ 2
        + 30 * (2 * x 7 - x 6) ^ 2 + 2 * x 3 ^ 2 := by
      ring
    rw [this]
    apply lt_of_le_of_ne
    · positivity
    · symm
      contrapose hx
      repeat rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)] at hx
      obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := hx
      ext i
      rw [Pi.zero_apply]
      fin_cases i <;> simp_all

theorem isFiniteCartan_f₄ : F₄.IsFiniteCartan where
  diag := F₄_diag
  offDiag_nonpos := F₄_off_diag_nonpos
  zero_comm i j := by fin_cases i <;> fin_cases j <;> simp [F₄]
  exists_posDef := by
    use ![1, 1, 2, 2]
    have h : diagonal ![1, 1, 2, 2] * F₄
        = !![2, -1, 0, 0; -1, 2, -2, 0; 0, -2, 4, -2; 0, 0, -2, 4] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [h]
    refine ⟨fun i ↦ by fin_cases i <;> simp, PosDef.of_dotProduct_mulVec_pos ?_ ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · intro x hx
      have h : star x ⬝ᵥ !![2, -1, 0, 0; -1, 2, -2, 0; 0, -2, 4, -2; 0, 0, -2, 4] *ᵥ x
          = 2 * x 0 ^ 2 + 2 * x 1 ^ 2 + 4 * x 2 ^ 2 + 4 * x 3 ^ 2
          - 2 * x 0 * x 1 - 4 * x 1 * x 2 - 4 * x 2 * x 3 := by
        simp [show vecHead x = x 0 by rfl, show vecHead (vecTail x) = x 1 by rfl,
          show vecHead (vecTail (vecTail x)) = x 2 by rfl,
          show vecHead (vecTail (vecTail (vecTail x))) = x 3 by rfl]
        ring
      rw [h]
      apply pos_of_mul_pos_right (a := 6) ?_ (by positivity)
      have h : 6 * (2 * x 0 ^ 2 + 2 * x 1 ^ 2 + 4 * x 2 ^ 2 + 4 * x 3 ^ 2
          - 2 * x 0 * x 1 - 4 * x 1 * x 2 - 4 * x 2 * x 3)
          = 3 * (2 * x 0 - x 1) ^ 2 + (3 * x 1 - 4 * x 2) ^ 2 + 2 * (2 * x 2 - 3 * x 3) ^ 2
          + 6 * x 3 ^ 2 := by ring
      rw [h]
      apply lt_of_le_of_ne
      · positivity
      · symm
        contrapose hx
        repeat rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)] at hx
        obtain ⟨⟨_, _⟩, _⟩ := hx
        ext i
        rw [Pi.zero_apply]
        fin_cases i <;> simp_all

theorem isFiniteCartan_g₂ : G₂.IsFiniteCartan where
  diag := G₂_diag
  offDiag_nonpos := G₂_off_diag_nonpos
  zero_comm := by simp [G₂]
  exists_posDef := by
    use ![1, 3]
    have h : diagonal ![1, 3] * G₂ = !![2, -3; -3, 6] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    simp only [h, Fin.forall_fin_two, cons_val_zero, zero_lt_one, true_and,
      cons_val_one, cons_val_fin_one, Nat.ofNat_pos, Int.reduceNeg]
    apply PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · intro x hx
      have h : star x ⬝ᵥ !![2, -3; -3, 6].mulVec x =
        2 * x 0 ^ 2 - 6 * x 0 * x 1 + 6 * x 1 ^ 2 := by
        simp [show vecHead x = x 0 by rfl, show vecHead (vecTail x) = x 1 by rfl]
        ring
      rw [h]
      by_cases h : x 1 = 0
      · have h₀ : x 0 ≠ 0 := by
          contrapose hx
          ext i
          fin_cases i <;> simp_all
        simp [h, sq_pos_iff.mpr h₀]
      · nlinarith [sq_pos_iff.mpr h, sq_nonneg (2 * x 0 - 3 * x 1)]

end CartanMatrix

end
