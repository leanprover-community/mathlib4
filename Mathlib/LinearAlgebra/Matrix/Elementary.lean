/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji, Joseph Qian, Veer Shukla, Dhruv Bhatia, Zheng Wu
-/
module

public import Mathlib.LinearAlgebra.Matrix.Swap
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Elementary row operations

This file defines row-scaling matrices and row-equivalence.

## Main definitions

* `Matrix.rowScale i c`: the elementary matrix which scales row `i` by `c`
* `Matrix.RowEquivalent A B`: row-equivalence by left multiplication by an element of `GL`
-/

@[expose] public section

namespace Matrix

variable {R m n : Type*}

section RowScale

section

variable [Zero R] [One R] [DecidableEq m]

/-- The elementary matrix scaling row `i` by `c`. -/
def rowScale (i : m) (c : R) : Matrix m m R :=
  Matrix.diagonal (Pi.mulSingle i c)

@[simp]
lemma rowScale_one (i : m) :
    rowScale i (1 : R) = 1 := by
  simp [rowScale]

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

end

section

variable [CommRing R] [Fintype m] [DecidableEq m]

lemma rowScale_mul (i : m) (c : R) (M : Matrix m n R) :
    rowScale i c * M = M.updateRow i (c • M.row i) := by
  aesop (add simp [rowScale, updateRow_apply])

lemma mul_rowScale (i : m) (c : R) (M : Matrix n m R) :
    M * rowScale i c = M.updateCol i (c • M.col i) := by
  aesop (add simp [rowScale, updateCol_apply, mul_comm])

@[simp]
lemma rowScale_mul_rowScale (i : m) (c d : R) :
    rowScale i c * rowScale i d = rowScale i (c * d) := by
  rw [rowScale, rowScale, Matrix.diagonal_mul_diagonal]
  congr
  exact (Pi.mulSingle_mul (f := fun _ : m ↦ R) i c d).symm

end

namespace GeneralLinearGroup

variable [CommRing R] [Fintype m] [DecidableEq m]

/-- `Matrix.rowScale` as an element of `GL m R`. -/
@[simps val]
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
@[simps val]
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

lemma rowEquivalent_iff_associated_op_op {A B : Matrix m m R} :
    RowEquivalent A B ↔ Associated (MulOpposite.op A) (MulOpposite.op B) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨Units.opEquiv.symm (MulOpposite.op g), rfl⟩
  · rintro ⟨u, h⟩
    refine ⟨(Units.opEquiv u).unop, ?_⟩
    simpa using (congrArg MulOpposite.unop h).symm

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

namespace RowEquivalent

/-- The row-equivalence relation as a scoped setoid instance. -/
scoped instance setoid : Setoid (Matrix m n R) where
  r := Matrix.RowEquivalent
  iseqv := ⟨Matrix.RowEquivalent.refl, Matrix.RowEquivalent.symm, Matrix.RowEquivalent.trans⟩

end RowEquivalent

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

end Matrix
