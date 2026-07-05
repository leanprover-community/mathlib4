/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Totally nonnegative matrices

This file defines totally nonnegative matrices and provides basic API for them.

## Main definitions

- `Matrix.IsTotallyNonneg`: a matrix is totally nonnegative if all its finite minors have
  nonnegative determinant.

## Main results

- `Matrix.IsTotallyNonneg.submatrix`: any submatrix (with strictly monotonic row/column indices)
  of a totally nonnegative matrix is totally nonnegative.
- `Matrix.IsTotallyNonneg.nonneg`: any entry of a totally nonnegative matrix is nonnegative.
- `Matrix.IsTotallyNonneg.zero`: the zero matrix is totally nonnegative.
- `Matrix.IsTotallyNonneg.one`: the identity matrix is totally nonnegative.
- `Matrix.IsTotallyNonneg.smul`: a nonnegative scalar multiple of a totally nonnegative matrix
  is totally nonnegative.
-/
public section

namespace Matrix

variable {ι κ R : Type*} [PartialOrder ι] [PartialOrder κ] [CommRing R] [PartialOrder R]
  {M : Matrix ι ι R} {i j : ι} {f g : κ → ι}

/-- A matrix is totally nonnegative if all its finite minors have nonnegative determinant. -/
@[expose]
def IsTotallyNonneg (M : Matrix ι ι R) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃rows cols : Fin n → ι⦄, StrictMono rows → StrictMono cols →
    0 ≤ (M.submatrix rows cols).det

protected lemma IsTotallyNonneg.submatrix (hM : M.IsTotallyNonneg) (hf : StrictMono f)
    (hg : StrictMono g) : (M.submatrix f g).IsTotallyNonneg :=
  fun n rows cols hrows hcols ↦ by simpa using hM (hf.comp hrows) (hg.comp hcols)

lemma IsTotallyNonneg.nonneg (hM : M.IsTotallyNonneg) (i j : ι) : 0 ≤ M i j := by
  have hrows : StrictMono ![i] := fun _ _ _ ↦ by lia
  have hcols : StrictMono ![j] := fun _ _ _ ↦ by lia
  grind [det_unique, submatrix_apply, const_fin1_eq, hM hrows hcols]

variable [IsStrictOrderedRing R]

@[simp] protected lemma IsTotallyNonneg.zero : (0 : Matrix ι ι R).IsTotallyNonneg
  | 0 => by grind [det_fin_zero]
  | n + 1 => by simp

@[simp] protected lemma IsTotallyNonneg.one [DecidableEq ι] :
    (1 : Matrix ι ι R).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  by_cases h_range : Set.range rows = Set.range cols
  · simp [hrows.eq_of_range_eq hcols h_range, submatrix_one cols hcols.injective]
  · obtain ⟨i, hi⟩ : ∃ i : Fin n, rows i ∉ Set.range cols :=
      hrows.injective.exists_not_mem_range_of_range_ne hcols.injective h_range
    have : ∀ j, rows i ≠ cols j := by grind
    simp [det_eq_zero_of_row_eq_zero i, this]

lemma IsTotallyNonneg.smul {M : Matrix ι ι R}
    (hM : M.IsTotallyNonneg) {c : R} (hc : 0 ≤ c) :
    (c • M).IsTotallyNonneg := by
  intro _ rows cols hrows hcols
  change 0 ≤ (c • M.submatrix rows cols).det
  grind [det_smul, mul_nonneg, pow_nonneg, hM _]

end Matrix
