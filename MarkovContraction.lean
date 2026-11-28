/-
Copyright (c) 2026 Radu Irbe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Radu Irbe
-/
module

public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Contraction and positivity lemmas for row-stochastic maps

This module establishes single-step `ℓ₁` nonexpansiveness, single-step Doeblin
contraction on mass-zero vectors, and strict positivity propagation for left
eigenvectors of minorized matrices over linearly ordered commutative rings.
-/

@[expose] public section

open scoped Matrix

section MarkovContraction
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]

/-- **Mass-free L1-nonexpansiveness** of the left action of a row-stochastic
matrix: on pairs of vectors, the map `v ↦ v ᵥ* M` does not increase the L1
distance. The statement is unconditionally mass-free: the triangle, Fubini, and
row-sum argument never uses the total masses. -/
theorem abs_vecMul_sub_le_of_rowStochastic (M : Matrix ι ι R)
    (hM : M ∈ Matrix.rowStochastic R ι) (c₁ c₂ : ι → R) :
    ∑ j, |(c₁ ᵥ* M - c₂ ᵥ* M) j| ≤ ∑ i, |c₁ i - c₂ i| := by
  have htri : ∀ j, |(c₁ ᵥ* M - c₂ ᵥ* M) j| ≤ ∑ i, |c₁ i - c₂ i| * M i j := by
    intro j
    rw [← Matrix.sub_vecMul]
    change |∑ i, (c₁ i - c₂ i) * M i j| ≤ _
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
    rw [abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hM)]
  calc ∑ j, |(c₁ ᵥ* M - c₂ ᵥ* M) j|
      ≤ ∑ j, ∑ i, |c₁ i - c₂ i| * M i j :=
        Finset.sum_le_sum fun j _ => htri j
    _ = ∑ i, |c₁ i - c₂ i| * ∑ j, M i j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ i, |c₁ i - c₂ i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.sum_row_of_mem_rowStochastic hM i, mul_one]

end MarkovContraction

section Doeblin
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]

/-- **Doeblin strict contraction**: with an entrywise minorant
`δ ≤ M i j`, the left action contracts the L¹ norm of a mass-zero
vector by the factor `1 - card • δ`. -/
theorem abs_vecMul_le_of_doeblin (M : Matrix ι ι R)
    (hM : M ∈ Matrix.rowStochastic R ι) {δ : R}
    (hd : ∀ i j, δ ≤ M i j)
    (d : ι → R) (hd0 : ∑ i, d i = 0) :
    ∑ j, |(d ᵥ* M) j| ≤ (1 - (Fintype.card ι : ℕ) • δ) * ∑ i, |d i| := by
  have hshift : ∀ j, (d ᵥ* M) j = ∑ i, d i * (M i j - δ) := by
    intro j
    change ∑ i, d i * M i j = _
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hd0, zero_mul, sub_zero]
  have hcol : ∀ j, |(d ᵥ* M) j| ≤ ∑ i, |d i| * (M i j - δ) := by
    intro j
    rw [hshift j]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hd i j))]
  calc ∑ j, |(d ᵥ* M) j|
      ≤ ∑ j, ∑ i, |d i| * (M i j - δ) :=
        Finset.sum_le_sum fun j _ => hcol j
    _ = ∑ i, |d i| * (1 - (Fintype.card ι : ℕ) • δ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, Finset.sum_sub_distrib,
          Matrix.sum_row_of_mem_rowStochastic hM i, Finset.sum_const, Finset.card_univ]
    _ = (1 - (Fintype.card ι : ℕ) • δ) * ∑ i, |d i| := by
        rw [← Finset.sum_mul, mul_comm]

omit [DecidableEq ι] in
/-- **Sign propagation** for the left eigenvector of a minorant kernel:
if the minimum of `v` is positive, every entry is positive. -/
theorem pos_of_vecMul_eq_of_min_pos [Nonempty ι] [NoZeroDivisors R]
    {δ : R} (M : Matrix ι ι R)
    (hMk : ∀ i j, δ ≤ M i j) (hδpos : 0 < δ)
    (v : ι → R) (hv : ∀ j, v j = ∑ i, v i * M i j)
    (n : R) (hn : ∀ i, n ≤ v i) (hnpos : 0 < n) (j : ι) :
    0 < v j := by
  have hMpos : ∀ i l, 0 ≤ M i l := fun i l => hδpos.le.trans (hMk i l)
  have hcol : (Fintype.card ι : ℕ) • δ ≤ ∑ i, M i j := by
    calc (Fintype.card ι : ℕ) • δ = ∑ _ : ι, δ := by simp [Finset.sum_const]
      _ ≤ ∑ i, M i j := Finset.sum_le_sum fun i _ => hMk i j
  have hcardpos : 0 < (Fintype.card ι : R) * δ := by
    rw [← nsmul_eq_mul]
    have hk : Fintype.card ι = (Fintype.card ι - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)).symm
    rw [hk, add_nsmul, one_nsmul]
    exact add_pos_of_nonneg_of_pos (nsmul_nonneg hδpos.le _) hδpos
  have hdecomp : v j = n * ∑ i, M i j + ∑ i, (v i - n) * M i j := by
    rw [hv j]
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hrem : 0 ≤ ∑ i, (v i - n) * M i j :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr (hn i)) (hMpos i j)
  have hbound : n * ((Fintype.card ι : R) * δ) ≤ v j := by
    calc n * ((Fintype.card ι : R) * δ)
        ≤ n * ∑ i, M i j := by
          rw [← nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_left hcol hnpos.le
      _ ≤ v j := by
          rw [hdecomp]
          exact le_add_of_nonneg_right hrem
  have hprod_ne : n * ((Fintype.card ι : R) * δ) ≠ 0 :=
    mul_ne_zero hnpos.ne' hcardpos.ne'
  exact lt_of_lt_of_le (lt_of_le_of_ne (mul_nonneg hnpos.le hcardpos.le) hprod_ne.symm) hbound

end Doeblin
