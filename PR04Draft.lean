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
