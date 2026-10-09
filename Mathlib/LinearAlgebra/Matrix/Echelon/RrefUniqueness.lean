/-
Copyright (c) 2026 Joseph Qian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Qian, Junye Ji, Dhruv Bhatia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic

/-!
# Reduced row-echelon form uniqueness

This file proves that two reduced row-echelon representatives of the same
matrix are equal.

## Main results

- `Matrix.reduced_unique_of_rowEquivalent` is a proof that if two matrices are row equivalent and
  are both in reduced row echelon form, then they are equal.
- `Matrix.IsReducedRowEchelonOf.unique` is a proof that if two matrices are both reduced row echelon
  representatives of the same matrix, then those two matrices are equal.
-/

universe v

namespace Matrix

variable {m n : Type*}
variable {R : Type v} {A : Matrix m n R}

variable [Field R]

/--
Kronecker-delta view of a pivot column.

For a pivot `(i,p)` in reduced form, column `p` equals `1` at row `i` and `0`
everywhere else.
-/
private lemma reduced_pivot_col_unit {m n : Nat}
    {M : Matrix (Fin m) (Fin n) R}
    (hRed : IsReducedRowEchelon M)
    {i r : Fin m} {p : Fin n}
    (hp : IsLeadingEntry M i p) :
    M r p = if r = i then 1 else 0 := by
  by_cases hri : r = i
  · subst hri
    simpa using hRed.eq_one hp
  · simp [hri, hRed.eq_zero_of_ne_of_isLeadingEntry hri hp]

/--
Coefficient extraction from a pivot column.

If `B = U * C` and column `q` of `C` is a pivot column with pivot row `k`,
then entry `B i q` is exactly the coefficient `U i k`.
-/
private lemma coeff_from_pivot_column {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hC : IsReducedRowEchelon C)
    (U : Matrix (Fin m) (Fin m) R)
    (hBC : B = U * C)
    {k i : Fin m} {q : Fin n}
    (hq : IsLeadingEntry C k q) :
    B i q = U i k := by
  have hEntry : B i q = (U * C) i q := by simp [hBC]
  rw [Matrix.mul_apply] at hEntry
  have hsum : (∑ t, U i t * C t q) = U i k := by
    calc
      (∑ t, U i t * C t q)
          = ∑ t, U i t * (if t = k then 1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro t _
              simp [reduced_pivot_col_unit hC hq]
      _ = U i k := by simp
  simpa [hsum] using hEntry

/--
Row-level matching relation used in the uniqueness proof.

At row `i`, either both matrices are zero rows, or they share the same pivot
column at that row.
-/
private def RowMatch {m n : Nat}
    (B C : Matrix (Fin m) (Fin n) R) (i : Fin m) : Prop :=
  (B i = 0 ∧ C i = 0) ∨ ∃ p : Fin n, IsLeadingEntry B i p ∧ IsLeadingEntry C i p

/--
Pivot-column transfer lemma (from left matrix to right matrix).

Given row-equivalence and reducedness of `C`, every pivot column appearing in
`B` must also appear as a pivot column in `C` (possibly at another row).
-/
private lemma pivot_exists_in_right {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hC : IsReducedRowEchelon C)
    {i : Fin m} {p : Fin n}
    (hpB : IsLeadingEntry B i p) :
    ∃ k : Fin m, IsLeadingEntry C k p := by
  rcases RowEquivalent.symm hBC with ⟨UUnit, hUAction⟩
  let U : Matrix (Fin m) (Fin m) R := (UUnit : Matrix (Fin m) (Fin m) R)
  have hU : B = U * C := by simpa [U] using hUAction.symm
  by_contra hnone
  have hsumZero : (∑ t, U i t * C t p) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t _
    have h_zero_or_leadingEntry (A : Matrix (Fin m) (Fin n) R) (i : Fin m) :
        A i = 0 ∨ ∃ c, A.IsLeadingEntry i c := by
      by_cases hZero : A i = 0
      · exact Or.inl hZero
      · exact Or.inr (row_ne_zero_iff_exists_isLeadingEntry.mp hZero)
    cases h_zero_or_leadingEntry C t with
    | inl hZero =>
        simp [hZero]
    | inr hPivot =>
        rcases hPivot with ⟨q, hq⟩
        by_cases hqp : q = p
        · exact (hnone ⟨t, by simpa [hqp] using hq⟩).elim
        · rcases lt_or_gt_of_ne hqp with hqLt | hpLt
          · have hUit : U i t = 0 := by
              have hCoeff : B i q = U i t :=
                coeff_from_pivot_column (hC := hC) (U := U) (hBC := hU)
                  (k := t) (i := i) (q := q) hq
              have hBiq : B i q = 0 := hpB.left q hqLt
              calc
                U i t = B i q := hCoeff.symm
                _ = 0 := hBiq
            simp [hUit]
          · have hCtp : C t p = 0 := hq.left p hpLt
            simp [hCtp]
  have hBpZero : B i p = 0 := by
    calc
      B i p = (U * C) i p := by simp [hU]
      _ = ∑ t, U i t * C t p := by simp [Matrix.mul_apply]
      _ = 0 := hsumZero
  exact hpB.right hBpZero

/--
Symmetric pivot-column transfer lemma (right matrix to left matrix).

This is `pivot_exists_in_right` applied to the symmetric row-equivalence.
-/
private lemma pivot_exists_in_left {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedRowEchelon B)
    {i : Fin m} {p : Fin n}
    (hpC : IsLeadingEntry C i p) :
    ∃ k : Fin m, IsLeadingEntry B k p := by
  simpa using
    (pivot_exists_in_right (hBC := RowEquivalent.symm hBC) (hC := hB) hpC)

/-- In row echelon form, if row `k < i` matches row `k` of another matrix,
    a pivot at row `k` in `B` contradicts a pivot at row `i` in `C`. -/
private lemma not_pivot_lt_of_rowMatch_left {m n : Nat} {B C : Matrix (Fin m) (Fin n) R}
    (hC : C.IsRowEchelon) {i k : Fin m} {q : Fin n} (hkLt : k < i)
    (hMatch : RowMatch B C k) (hkB : B.IsLeadingEntry k q) (hqC : C.IsLeadingEntry i q) :
    False := by
  cases hMatch with
  | inl hZero => exact not_isLeadingEntry_of_row_eq_zero hZero.1 hkB
  | inr hPivot =>
      rcases hPivot with ⟨qk, hkB', hkCk⟩
      have hqk : qk = q := IsLeadingEntry.unique hkB' hkB
      have hkCq : IsLeadingEntry C k q := hqk ▸ hkCk
      exact lt_irrefl q (hC.pivotCol_strictly_increasing hkLt hkCq hqC)

private lemma not_pivot_lt_of_rowMatch_right {m n : Nat} {B C : Matrix (Fin m) (Fin n) R}
    (hB : B.IsRowEchelon) {i k : Fin m} {p : Fin n} (hkLt : k < i)
    (hMatch : RowMatch B C k) (hkC : C.IsLeadingEntry k p) (hpB : B.IsLeadingEntry i p) :
    False := by
  cases hMatch with
  | inl hZero => exact not_isLeadingEntry_of_row_eq_zero hZero.2 hkC
  | inr hPivot =>
      rcases hPivot with ⟨pk, hkBk, hkCk⟩
      have hpk : pk = p := IsLeadingEntry.unique hkCk hkC
      have hkBp : IsLeadingEntry B k p := hpk ▸ hkBk
      exact lt_irrefl p (hB.pivotCol_strictly_increasing hkLt hkBp hpB)

/--
Key row-by-row alignment theorem under row-equivalence and reducedness.

For each row index `i`, matrices `B` and `C` either are both zero rows or
share the same pivot column at row `i`.
-/
private theorem reduced_rowMatch_of_rowEquivalent {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedRowEchelon B)
    (hC : IsReducedRowEchelon C) :
    ∀ i : Fin m, RowMatch (R := R) B C i := by
  have hMatchNat : ∀ iNat : Nat, ∀ hi : iNat < m, RowMatch (R := R) B C ⟨iNat, hi⟩ := by
    intro iNat
    refine Nat.strong_induction_on iNat ?_
    intro iNat ih hi
    let iFin : Fin m := ⟨iNat, hi⟩
    have h_zero_or_leadingEntry (A : Matrix (Fin m) (Fin n) R) (i : Fin m) :
        A i = 0 ∨ ∃ c, A.IsLeadingEntry i c := by
      by_cases hZero : A i = 0
      · exact Or.inl hZero
      · exact Or.inr (row_ne_zero_iff_exists_isLeadingEntry.mp hZero)
    cases h_zero_or_leadingEntry B iFin with
    | inl hBZero =>
        have hCZero : C iFin = 0 := by
          cases hCi : h_zero_or_leadingEntry C iFin with
          | inl hZero =>
              exact hZero
          | inr hPivot =>
              rcases hPivot with ⟨q, hqC⟩
              rcases pivot_exists_in_left (hBC := hBC) (hB := hB) hqC with ⟨k, hkB⟩
              rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
              · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
                have hkLt' : k < iFin := by simpa [Fin.lt_def, iFin] using hkLt
                exact (not_pivot_lt_of_rowMatch_left hC.isRowEchelon hkLt' hkMatch hkB hqC).elim
              · have hkEqFin : k = iFin := Fin.ext hkEq
                subst hkEqFin
                exact (not_isLeadingEntry_of_row_eq_zero hBZero hkB).elim
              · have hiLt' : iFin < k := by simpa [Fin.lt_def, iFin] using hiLt
                have hkZero : B k = 0 := hB.isRowEchelon.row_eq_zero_of_lt hiLt' hBZero
                exact (not_isLeadingEntry_of_row_eq_zero hkZero hkB).elim
        exact Or.inl ⟨hBZero, hCZero⟩
    | inr hPivotB =>
        rcases hPivotB with ⟨p, hpB⟩
        have hCNonzero : ¬ C iFin = 0 := by
          intro hCZero
          rcases pivot_exists_in_right (hBC := hBC) (hC := hC) hpB with ⟨k, hkC⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
            have hkLt' : k < iFin := by simpa [Fin.lt_def, iFin] using hkLt
            exact (not_pivot_lt_of_rowMatch_right hB.isRowEchelon hkLt' hkMatch hkC hpB).elim
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            exact (not_isLeadingEntry_of_row_eq_zero hCZero hkC).elim
          · have hiLt' : iFin < k := by simpa [Fin.lt_def, iFin] using hiLt
            have hkZero : C k = 0 := hC.isRowEchelon.row_eq_zero_of_lt hiLt' hCZero
            exact (not_isLeadingEntry_of_row_eq_zero hkZero hkC).elim
        -- Extract the pivot of row `i` in `C`.
        have hCPivot : ∃ q : Fin n, IsLeadingEntry C iFin q := by
          cases hCi : h_zero_or_leadingEntry C iFin with
          | inl hZero =>
              exact (hCNonzero hZero).elim
          | inr hPivot =>
              exact hPivot
        rcases hCPivot with ⟨q, hqC⟩
        have hpLeQ : p ≤ q := by
          by_contra hNotLe
          have hqLtP : q < p := lt_of_not_ge hNotLe
          rcases pivot_exists_in_left (hBC := hBC) (hB := hB) hqC with ⟨k, hkBq⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
            have hkLt' : k < iFin := by simpa [Fin.lt_def, iFin] using hkLt
            exact (not_pivot_lt_of_rowMatch_left hC.isRowEchelon hkLt' hkMatch hkBq hqC).elim
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            have hpEqQ : p = q := IsLeadingEntry.unique hpB hkBq
            exact (ne_of_lt hqLtP) hpEqQ.symm
          · have hiLt' : iFin < k := by simpa [Fin.lt_def, iFin] using hiLt
            have hpLtQ : p < q :=
              hB.isRowEchelon.pivotCol_strictly_increasing hiLt' hpB hkBq
            exact (lt_irrefl _ (hqLtP.trans hpLtQ)).elim
        have hqLeP : q ≤ p := by
          by_contra hNotLe
          have hpLtQ : p < q := lt_of_not_ge hNotLe
          rcases pivot_exists_in_right (hBC := hBC) (hC := hC) hpB with ⟨k, hkCp⟩
          rcases lt_trichotomy k.1 iNat with hkLt | hkEq | hiLt
          · have hkMatch : RowMatch (R := R) B C k := ih k.1 hkLt k.2
            have hkLt' : k < iFin := by simpa [Fin.lt_def, iFin] using hkLt
            exact (not_pivot_lt_of_rowMatch_right hB.isRowEchelon hkLt' hkMatch hkCp hpB).elim
          · have hkEqFin : k = iFin := Fin.ext hkEq
            subst hkEqFin
            have hqEqP : q = p := IsLeadingEntry.unique hqC hkCp
            exact (ne_of_lt hpLtQ) hqEqP.symm
          · have hiLt' : iFin < k := by simpa [Fin.lt_def, iFin] using hiLt
            have hqLtP : q < p :=
              hC.isRowEchelon.pivotCol_strictly_increasing hiLt' hqC hkCp
            exact (lt_irrefl _ (hpLtQ.trans hqLtP)).elim
        have hpq : p = q := le_antisymm hpLeQ hqLeP
        exact Or.inr ⟨p, hpB, by simpa [hpq] using hqC⟩
  intro i
  simpa using hMatchNat i.1 i.2

/--
Semantic uniqueness under row-equivalence.

If `B` and `C` are reduced and row-equivalent, then they are entrywise equal.
The proof rewrites `B = U * C`, then uses row matching plus pivot-column
Kronecker behavior to collapse coefficients to `(if i = t then 1 else 0)`.
-/
theorem reduced_unique_of_rowEquivalent {m n : Nat}
    {B C : Matrix (Fin m) (Fin n) R}
    (hBC : RowEquivalent B C)
    (hB : IsReducedRowEchelon B)
    (hC : IsReducedRowEchelon C) :
    B = C := by
  rcases RowEquivalent.symm hBC with ⟨UUnit, hUAction⟩
  let U : Matrix (Fin m) (Fin m) R := (UUnit : Matrix (Fin m) (Fin m) R)
  have hU : B = U * C := by simpa [U] using hUAction.symm
  have hMatch : ∀ i : Fin m, RowMatch (R := R) B C i :=
    reduced_rowMatch_of_rowEquivalent (hBC := hBC) (hB := hB) (hC := hC)
  ext i j
  calc
    B i j = ∑ t, U i t * C t j := by
      calc
        B i j = (U * C) i j := by simp [hU]
        _ = ∑ t, U i t * C t j := by simp [Matrix.mul_apply]
    _ = ∑ t, (if i = t then 1 else 0) * C t j := by
      refine Finset.sum_congr rfl ?_
      intro t _
      cases hMatch t with
      | inl hZeroPair =>
          simp [hZeroPair.2]
      | inr hPivotPair =>
          rcases hPivotPair with ⟨p, hpBt, hpCt⟩
          have hCoeff : U i t = B i p :=
            (coeff_from_pivot_column (hC := hC) (U := U) (hBC := hU)
              (k := t) (i := i) (q := p) hpCt).symm
          have hUnit : B i p = if i = t then 1 else 0 :=
            reduced_pivot_col_unit hB hpBt
          simp [hCoeff, hUnit]
    _ = C i j := by simp


/--
Core semantic uniqueness theorem.

Two matrices that are both reduced representatives of the same source `B`
must be equal.
-/
theorem IsReducedRowEchelonOf.unique {m n : Nat}
    {A A' B : Matrix (Fin m) (Fin n) R}
    (hA : IsReducedRowEchelonOf A B)
    (hA' : IsReducedRowEchelonOf A' B) :
    A = A' := by
  have hAA' : RowEquivalent A A' :=
    RowEquivalent.trans hA.rowEquivalent (RowEquivalent.symm hA'.rowEquivalent)
  exact reduced_unique_of_rowEquivalent (hBC := hAA') (hB := hA.isReducedRowEchelon)
    (hC := hA'.isReducedRowEchelon)

end Matrix
