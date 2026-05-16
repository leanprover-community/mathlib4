/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji, Joseph Qian, Veer Shukla, Dhruv Bhatia, Zheng Wu
-/
module

public import Mathlib.LinearAlgebra.Matrix.Swap
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Echelon and reduced echelon form

This file develops a theorem-oriented interface for row reduction.

## Main definitions

* `Matrix.rowScale i c`: the elementary matrix which scales row `i` by `c`
* `Matrix.RowEquivalent A B`: row-equivalence by left multiplication by an element of `GL`
* `Matrix.RowIsZero M i`: row `i` of `M` is zero
* `Matrix.IsPivot M i p`: row `i` has pivot column `p`
* `Matrix.IsEchelonForm M`: row echelon form
* `Matrix.IsReducedEchelonForm M`: reduced row echelon form
* `Matrix.IsEchelonFormOf A B`, `Matrix.IsReducedEchelonFormOf A B`: semantic representatives
-/

@[expose] public section

namespace Matrix

variable {R m n : Type*}

section RowScale

variable [CommRing R] [DecidableEq m]

/-- The elementary matrix scaling row `i` by `c`. -/
def rowScale (i : m) (c : R) : Matrix m m R :=
  Matrix.diagonal (Function.update (1 : m → R) i c)

@[simp]
lemma rowScale_apply_same (i : m) (c : R) :
    rowScale i c i i = c := by
  simp [rowScale]

@[simp]
lemma rowScale_apply_diag_of_ne {i a : m} (h : a ≠ i) (c : R) :
    rowScale i c a a = 1 := by
  simp [rowScale, h]

@[simp]
lemma rowScale_apply_ne {i a b : m} (hab : a ≠ b) (c : R) :
    rowScale i c a b = 0 := by
  simp [rowScale, hab]

section

variable [Fintype m]

@[simp]
lemma rowScale_mul_apply_same (i : m) (c : R) (M : Matrix m n R) (j : n) :
    (rowScale i c * M) i j = c * M i j := by
  rw [rowScale, Matrix.diagonal_mul, Function.update_self]

@[simp]
lemma rowScale_mul_apply_of_ne {i a : m} (ha : a ≠ i) (c : R) (M : Matrix m n R) (j : n) :
    (rowScale i c * M) a j = M a j := by
  rw [rowScale, Matrix.diagonal_mul, Function.update_of_ne ha]
  simp

@[simp]
lemma mul_rowScale_apply_same (i : m) (c : R) (M : Matrix n m R) (a : n) :
    (M * rowScale i c) a i = M a i * c := by
  rw [rowScale, Matrix.mul_diagonal, Function.update_self]

@[simp]
lemma mul_rowScale_apply_of_ne {i b : m} (hb : b ≠ i) (c : R) (M : Matrix n m R) (a : n) :
    (M * rowScale i c) a b = M a b := by
  rw [rowScale, Matrix.mul_diagonal, Function.update_of_ne hb]
  simp

@[simp]
lemma rowScale_mul_rowScale (i : m) (c d : R) :
    rowScale i c * rowScale i d = rowScale i (c * d) := by
  rw [rowScale, rowScale, Matrix.diagonal_mul_diagonal]
  congr
  ext a
  by_cases ha : a = i
  · subst ha
    simp
  · simp [ha]

omit [Fintype m] in
@[simp] lemma rowScale_one (i : m) :
    rowScale i (1 : R) = 1 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = i <;> simp [rowScale, ha]
  · simp [rowScale, hab]

end

namespace GeneralLinearGroup

variable [Fintype m]

/-- `Matrix.rowScale` as an element of `GL m R`. -/
@[simps]
def rowScale (i : m) (c : Rˣ) : GL m R where
  val := Matrix.rowScale i (c : R)
  inv := Matrix.rowScale i ↑c⁻¹
  val_inv := by
    rw [Matrix.rowScale_mul_rowScale]
    simp
  inv_val := by
    rw [Matrix.rowScale_mul_rowScale]
    simp [mul_comm]

variable {S : Type*} [CommRing S] (f : R →+* S)

@[simp]
lemma map_rowScale (i : m) (c : Rˣ) :
    (rowScale (R := R) i c).map f = rowScale (R := S) i (Units.map f c) := by
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = i
    · subst ha
      simp [rowScale, Matrix.rowScale]
    · simp [rowScale, Matrix.rowScale, ha]
  · simp [rowScale, Matrix.rowScale, hab]

end GeneralLinearGroup

end RowScale

section TransvectionGL

variable [CommRing R] [Fintype m] [DecidableEq m]

namespace GeneralLinearGroup

/-- `Matrix.transvection` as an element of `GL`. -/
@[simps]
def transvection (i j : m) (h : i ≠ j) (c : R) : GL m R where
  val := Matrix.transvection i j c
  inv := Matrix.transvection i j (-c)
  val_inv := by
    simpa using Matrix.transvection_mul_transvection_same (i := i) (j := j) h c (-c)
  inv_val := by
    simpa [add_comm] using Matrix.transvection_mul_transvection_same (i := i) (j := j) h (-c) c

end GeneralLinearGroup

end TransvectionGL

section RowEquivalent

variable [CommRing R] [Fintype m] [DecidableEq m]

/-- Row-equivalence via the left action of `GL m R` on `Matrix m n R`.

For square matrices this is analogous to `Associated` in the opposite monoid, but this
definition also applies to rectangular matrices, where `Associated` is not available. -/
def RowEquivalent (A B : Matrix m n R) : Prop :=
  ∃ g : GL m R, B = (g : Matrix m m R) * A

lemma RowEquivalent.refl (A : Matrix m n R) : RowEquivalent A A := by
  refine ⟨1, ?_⟩
  simp

lemma RowEquivalent.symm {A B : Matrix m n R} (h : RowEquivalent A B) : RowEquivalent B A := by
  rcases h with ⟨g, rfl⟩
  refine ⟨g⁻¹, ?_⟩
  simp

lemma RowEquivalent.trans {A B C : Matrix m n R}
    (hAB : RowEquivalent A B) (hBC : RowEquivalent B C) : RowEquivalent A C := by
  rcases hAB with ⟨g, rfl⟩
  rcases hBC with ⟨h, rfl⟩
  refine ⟨h * g, ?_⟩
  simp [Matrix.mul_assoc]

instance rowEquivalentSetoid : Setoid (Matrix m n R) where
  r := RowEquivalent
  iseqv := ⟨RowEquivalent.refl, RowEquivalent.symm, RowEquivalent.trans⟩

lemma rowEquivalent_swap (A : Matrix m n R) (i j : m) :
    RowEquivalent A (Matrix.swap R i j * A) := by
  exact ⟨Matrix.GeneralLinearGroup.swap R i j, rfl⟩

lemma rowEquivalent_rowScale (A : Matrix m n R) (i : m) (c : Rˣ) :
    RowEquivalent A (Matrix.rowScale i (c : R) * A) := by
  exact ⟨Matrix.GeneralLinearGroup.rowScale (R := R) i c, rfl⟩

lemma rowEquivalent_transvection (A : Matrix m n R) (i j : m) (h : i ≠ j) (c : R) :
    RowEquivalent A (Matrix.transvection i j c * A) := by
  exact ⟨Matrix.GeneralLinearGroup.transvection (R := R) i j h c, rfl⟩

end RowEquivalent

section Echelon

variable [Zero R]

/-- Row `i` of `M` is zero. -/
def RowIsZero (M : Matrix m n R) (i : m) : Prop :=
  ∀ j, M i j = 0

/-- Row `i` has pivot column `p`. -/
def IsPivot [LinearOrder n] (M : Matrix m n R) (i : m) (p : n) : Prop :=
  M i p ≠ 0 ∧ ∀ j < p, M i j = 0

lemma RowIsZero.not_isPivot [LinearOrder n] {M : Matrix m n R} {i : m} {p : n}
    (hzero : RowIsZero M i) : ¬ IsPivot M i p := by
  intro hp
  exact hp.1 (hzero p)

lemma IsPivot.eq [LinearOrder n] {M : Matrix m n R} {i : m} {p q : n}
    (hp : IsPivot M i p) (hq : IsPivot M i q) : p = q := by
  have hpq : ¬ p < q := fun hlt => hp.1 (hq.2 p hlt)
  have hqp : ¬ q < p := fun hlt => hq.1 (hp.2 q hlt)
  exact le_antisymm (le_of_not_gt hqp) (le_of_not_gt hpq)

/-- Row echelon form. -/
structure IsEchelonForm [LinearOrder m] [LinearOrder n] (M : Matrix m n R) : Prop where
  row_zero_or_pivot : ∀ i, RowIsZero M i ∨ ∃ p, IsPivot M i p
  zero_rows_bottom : ∀ i j, i < j → RowIsZero M i → RowIsZero M j
  pivots_strictly_increasing :
    ∀ i j p q, i < j → IsPivot M i p → IsPivot M j q → p < q

lemma IsEchelonForm.pivot_column_zero_below [LinearOrder m] [LinearOrder n]
    {M : Matrix m n R} (hM : IsEchelonForm M) :
    ∀ i r p, i < r → IsPivot M i p → M r p = 0 := by
  intro i r p hir hp
  rcases hM.row_zero_or_pivot r with hzero | ⟨q, hq⟩
  · exact hzero p
  · exact hq.2 p (hM.pivots_strictly_increasing i r p q hir hp hq)

variable [One R]

/-- Reduced row echelon form. -/
structure IsReducedEchelonForm [LinearOrder m] [LinearOrder n] (M : Matrix m n R) : Prop where
  echelon : IsEchelonForm M
  pivot_is_one : ∀ i p, IsPivot M i p → M i p = 1
  pivot_column_zero_above : ∀ i r p, r < i → IsPivot M i p → M r p = 0

lemma IsReducedEchelonForm.pivot_column_zero_ne [LinearOrder m] [LinearOrder n]
    {M : Matrix m n R} (hM : IsReducedEchelonForm M) :
    ∀ {i r p}, r ≠ i → IsPivot M i p → M r p = 0 := by
  intro i r p hri hp
  by_cases hr : r < i
  · exact hM.pivot_column_zero_above i r p hr hp
  · have hir : i < r := lt_of_le_of_ne (le_of_not_gt hr) hri.symm
    exact hM.echelon.pivot_column_zero_below i r p hir hp

lemma IsReducedEchelonForm.pivot_column_eq_ite [LinearOrder m] [LinearOrder n]
    {M : Matrix m n R} (hM : IsReducedEchelonForm M) {i : m} {p : n} (hp : IsPivot M i p) :
    ∀ r, M r p = if r = i then 1 else 0 := by
  intro r
  by_cases hri : r = i
  · subst hri
    simp [hM.pivot_is_one _ _ hp]
  · simp [hri, hM.pivot_column_zero_ne hri hp]

end Echelon

section Semantic

variable [CommRing R] [Fintype m] [DecidableEq m]

/-- `B` is an echelon-form representative of `A`. -/
def IsEchelonFormOf [LinearOrder m] [LinearOrder n] (A B : Matrix m n R) : Prop :=
  RowEquivalent A B ∧ IsEchelonForm B

lemma IsEchelonFormOf.rowEquivalent [LinearOrder m] [LinearOrder n] {A B : Matrix m n R}
    (h : IsEchelonFormOf A B) : RowEquivalent A B :=
  h.1

lemma IsEchelonFormOf.echelon [LinearOrder m] [LinearOrder n] {A B : Matrix m n R}
    (h : IsEchelonFormOf A B) : IsEchelonForm B :=
  h.2

/-- `B` is a reduced-echelon-form representative of `A`. -/
def IsReducedEchelonFormOf [LinearOrder m] [LinearOrder n] (A B : Matrix m n R) : Prop :=
  RowEquivalent A B ∧ IsReducedEchelonForm B

lemma IsReducedEchelonFormOf.rowEquivalent [LinearOrder m] [LinearOrder n] {A B : Matrix m n R}
    (h : IsReducedEchelonFormOf A B) : RowEquivalent A B :=
  h.1

lemma IsReducedEchelonFormOf.reduced [LinearOrder m] [LinearOrder n] {A B : Matrix m n R}
    (h : IsReducedEchelonFormOf A B) : IsReducedEchelonForm B :=
  h.2

lemma IsReducedEchelonFormOf.echelon [LinearOrder m] [LinearOrder n] {A B : Matrix m n R}
    (h : IsReducedEchelonFormOf A B) : IsEchelonForm B :=
  h.2.echelon

end Semantic

end Matrix
