module

public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-! Draft port of the PR_04 contraction lemmas (test harness). -/

@[expose] public section

open scoped Matrix

section MarkovContraction
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]

/-- **Mass-free L1-nonexpansiveness** of the left action of a row-stochastic
matrix: on pairs of vectors with equal total mass, the map `v |-> v *ᵥ M`
does not increase the L1 distance.  The statement is unconditionally
mass-free: the triangle + Fubini + row-sum proof never uses the total
masses, so no equal-mass hypothesis is needed (a strictly stronger and
shorter statement than the one the application carried). -/
theorem abs_vecMul_sub_le_of_rowStochastic (M : Matrix ι ι R)
    (hM : M ∈ Matrix.rowStochastic R ι) (c₁ c₂ : ι → R) :
    ∑ j, |(c₁ ᵥ* M - c₂ ᵥ* M) j| ≤ ∑ i, |c₁ i - c₂ i| := by
  have hrow : ∀ i, ∑ j, M i j = 1 := fun i => Matrix.sum_row_of_mem_rowStochastic hM i
  have hpos : ∀ i j, 0 ≤ M i j := fun i j => Matrix.nonneg_of_mem_rowStochastic hM
  have hrewrite : ∀ j, (c₁ ᵥ* M - c₂ ᵥ* M) j = ∑ i, (c₁ i - c₂ i) * M i j := by
    intro j
    have h1 : ∀ c : ι → R, (c ᵥ* M) j = ∑ i, c i * M i j := fun c => by
      simp only [Matrix.vecMul_apply, dotProduct, Matrix.col_apply]
    rw [Pi.sub_apply, h1, h1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc ∑ j, |(c₁ ᵥ* M - c₂ ᵥ* M) j|
      = ∑ j, |∑ i, (c₁ i - c₂ i) * M i j| :=
        Finset.sum_congr rfl fun j _ => by rw [hrewrite j]
    _ ≤ ∑ j, ∑ i, |(c₁ i - c₂ i) * M i j| :=
        Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, ∑ i, |c₁ i - c₂ i| * M i j :=
        Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg (hpos i j)]
    _ = ∑ i, |c₁ i - c₂ i| * (∑ j, M i j) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ i, |c₁ i - c₂ i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hrow i, mul_one]

end MarkovContraction

section Doeblin
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]

/-- **Doeblin strict contraction**: with an entrywise minorant
`δ ≤ M i j`, the left action contracts the L¹ norm of a mass-zero
vector by the factor `1 - card • δ`. -/
theorem abs_vecMul_le_of_doeblin (M : Matrix ι ι R)
    (hM : M ∈ Matrix.rowStochastic R ι) {δ : R}
    (hd : ∀ i j, δ ≤ M i j) (_hδ : 0 ≤ δ)
    (_hδsmall : (Fintype.card ι : ℕ) • δ ≤ 1)
    (d : ι → R) (hd0 : ∑ i, d i = 0) :
    ∑ j, |(d ᵥ* M) j| ≤ (1 - (Fintype.card ι : ℕ) • δ) * ∑ i, |d i| := by
  have hpos : ∀ i j, 0 ≤ M i j := fun i j =>
    Matrix.nonneg_of_mem_rowStochastic hM
  have hr0 : ∀ i j, 0 ≤ M i j - δ := fun i j => sub_nonneg.mpr (hd i j)
  have hrrow : ∀ i, ∑ j, (M i j - δ) = 1 - (Fintype.card ι : ℕ) • δ := by
    intro i
    rw [Finset.sum_sub_distrib, Finset.sum_const,
      Matrix.sum_row_of_mem_rowStochastic hM i, ← Finset.card_univ]
  have hvec : ∀ c : ι → R, ∀ j, (c ᵥ* M) j = ∑ i, c i * M i j := fun c j => by
    simp only [Matrix.vecMul_apply, dotProduct, Matrix.col_apply]
  have hkey : ∀ j, (d ᵥ* M) j = ∑ i, d i * (M i j - δ) := by
    intro j
    rw [hvec d j]
    have hstep : ∀ i : ι, d i * (M i j - δ)
        = d i * M i j - d i * δ := fun i => by ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i),
      Finset.sum_sub_distrib, ← Finset.sum_mul, hd0, zero_mul, sub_zero]
  calc ∑ j, |(d ᵥ* M) j|
      = ∑ j, |∑ i, d i * (M i j - δ)| :=
        Finset.sum_congr rfl fun j _ => by rw [hkey j]
    _ ≤ ∑ j, ∑ i, |d i * (M i j - δ)| :=
        Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, ∑ i, |d i| * (M i j - δ) :=
        Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg (hr0 i j)]
    _ = ∑ i, |d i| * (∑ j, (M i j - δ)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ =>
          (Finset.mul_sum (Finset.univ : Finset ι)
            (fun j => M i j - δ) (|d i|)).symm
    _ = (1 - (Fintype.card ι : ℕ) • δ) * ∑ i, |d i| := by
        simp only [hrrow]
        rw [← Finset.sum_mul]
        exact mul_comm _ _

/-- **Sign propagation** for the left eigenvector of a minorant kernel:
if the minimum of `v` is positive, every entry is positive. -/
theorem pos_of_vecMul_eq_of_min_pos
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R] [NoZeroDivisors R]
    {δ : R} (M : Matrix ι ι R)
    (hMk : ∀ i j, δ ≤ M i j) (hδ : 0 ≤ δ) (hδpos : 0 < δ)
    (v : ι → R) (hv : ∀ j, v j = ∑ i, v i * M i j)
    (n : R) (hn : ∀ i, n ≤ v i) (hnpos : 0 < n) (j : ι) :
    0 < v j := by
  have hMpos : ∀ i j, 0 ≤ M i j := fun i j =>
    le_trans (le_of_lt hδpos) (hMk i j)
  have hcol : (Fintype.card ι : ℕ) • δ ≤ ∑ i, M i j := by
    have h1 : ∑ i : ι, δ ≤ ∑ i, M i j :=
      Finset.sum_le_sum fun i _ => hMk i j
    rwa [Finset.sum_const] at h1
  have hcardpos : (0:R) < (Fintype.card ι : ℕ) • δ := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Fintype.card ι = m + 1 :=
      ⟨Fintype.card ι - 1, by
        have hcp : (0:ℕ) < Fintype.card ι := Fintype.card_pos
        omega⟩
    rw [hm, add_nsmul]
    have h2 : (0:R) ≤ m • δ := nsmul_nonneg hδ m
    calc (0:R) < δ := hδpos
      _ ≤ m • δ + (1:ℕ) • δ := by
            rw [one_nsmul, add_comm]
            exact le_add_of_nonneg_right h2
  -- the key identity: v j - n * colsum = sum (v i - n) * M i j >= 0
  have hkey : v j - n * ∑ i, M i j
      = ∑ i, (v i - n) * M i j := by
    rw [hv j]
    have hsplit : ∑ i, (v i - n) * M i j
        = ∑ i, (v i * M i j - n * M i j) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hge : 0 ≤ ∑ i, (v i - n) * M i j :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (sub_nonneg.mpr (hn i)) (hMpos i j)
  have hbr : (Fintype.card ι : ℕ) • δ = (Fintype.card ι : R) * δ := by
    rw [nsmul_eq_mul]
  have hvjge : n * ((Fintype.card ι : R) * δ) ≤ v j := by
    have h1 : n * ((Fintype.card ι : R) * δ) ≤ n * ∑ i, M i j :=
      mul_le_mul_of_nonneg_left (by rw [← hbr]; exact hcol) (le_of_lt hnpos)
    have h2 : n * ∑ i, M i j ≤ v j := by
      have hk := hkey
      calc n * ∑ i, M i j = v j - ∑ i, (v i - n) * M i j := by
            have hkv : v j = n * ∑ i, M i j + ∑ i, (v i - n) * M i j := by
              rw [← hkey]
              ring
            rw [hkv]
            ring
        _ ≤ v j := by
            refine sub_le_self _ ?_
            exact Finset.sum_nonneg fun i _ =>
              mul_nonneg (sub_nonneg.mpr (hn i)) (hMpos i j)
    exact le_trans h1 h2

  have hnz : n ≠ 0 := by
    intro h
    rw [h] at hnpos
    simp at hnpos
  have hdz : (Fintype.card ι : R) * δ ≠ 0 := by
    rw [← hbr]
    exact ne_of_gt hcardpos
  have hprod : n * ((Fintype.card ι : R) * δ) ≠ 0 := mul_ne_zero hnz hdz
  calc (0:R) < n * ((Fintype.card ι : R) * δ) :=
        lt_of_le_of_ne
          (mul_nonneg (le_of_lt hnpos) (by rw [← hbr]; exact le_of_lt hcardpos))
          (Ne.symm hprod)
    _ ≤ v j := hvjge
end Doeblin
