/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Matrices with fixed determinant

This file defines the type of matrices with fixed determinant `m` and proves some basic results
about them.

Note: Some of this was done originally in Lean 3 in the
kbb (https://github.com/kim-em/kbb/tree/master) repository, so credit to those authors.
-/

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

/--The set of matrices with fixed determinant `m`. -/
def FixedDetMatrix (m : R) := { A : Matrix n n R // A.det = m }

namespace FixedDetMatrix

open ModularGroup Matrix SpecialLinearGroup MatrixGroups

/--Extensionality theorem for `FixedDetMatrix` with respect to the underlying matrix, not
entriwise. -/
lemma ext' {m : R} {A B : FixedDetMatrix n R m} (h : A.1 = B.1) : A = B := by
  cases A; cases B
  congr

@[ext]
lemma ext {m : R} {A B : FixedDetMatrix n R m} (h : ∀ i j , A.1 i j = B.1 i j) : A = B := by
  apply ext'
  ext i j
  apply h

instance (m : R) : SMul (SpecialLinearGroup n R) (FixedDetMatrix n R m) where
  smul g A := ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩

lemma smul_def (m : R) (g : SpecialLinearGroup n R) (A : (FixedDetMatrix n R m)) :
    g • A = ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩ :=
  rfl

instance (m : R) : MulAction (SpecialLinearGroup n R) (FixedDetMatrix n R m) where
  one_smul b := by rw [smul_def]; simp only [coe_one, one_mul, Subtype.coe_eta]
  mul_smul x y b := by simp_rw [smul_def, ← mul_assoc, coe_mul]

lemma smul_coe (m : R) (g : SpecialLinearGroup n R) (A : FixedDetMatrix n R m) :
    (g • A).1 = g * A.1 := by
  rw [smul_def]

end FixedDetMatrix
