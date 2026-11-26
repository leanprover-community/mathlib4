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
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.NormDet

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

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) plates I -- IX
* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*] Chapter 11

## Tags

cartan matrix, lie algebra, dynkin diagram
-/

@[expose] public section

namespace CartanMatrix

open Matrix

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

end Properties

end CartanMatrix

/-- The proposition that a matrix is a finite-type Cartan matrix. -/
structure Matrix.IsFiniteCartan {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) : Prop where
  diag : ∀ i, M i i = 2
  offDiag_nonpos : ∀ i j, i ≠ j → M i j ≤ 0
  zero_comm : ∀ i j, M i j = 0 ↔ M j i = 0
  exists_posDef : ∃ d : ι → ℤ, (∀ i, 0 < d i) ∧ (diagonal d * M).PosDef

end
