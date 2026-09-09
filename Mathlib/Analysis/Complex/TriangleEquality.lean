/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Analysis.Complex.Arg
public import Mathlib.Analysis.Convex.TriangleEquality

/-!
# Triangle equality for sums of complex numbers

Over `ℂ`, lying on a common closed ray means sharing a phase. So the triangle inequality
`‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖` is an equality exactly when every nonzero summand has the same
phase as the sum, equivalently when every summand is a nonnegative real multiple of one complex
number of norm one. This is the finite-family form of `Complex.norm_add_eq_iff`; the statement in
a general strictly convex space is `norm_sum_eq_iff_pairwise_sameRay`.

## Main statements

* `Complex.normalize_eq_of_pairwise_sameRay`: if the summands pairwise lie on a common closed ray,
  then every nonzero summand has the same phase as the sum.
* `Complex.norm_sum_eq_iff_pairwise_normalize_eq`: for nonzero summands, triangle equality holds
  iff all the summands have the same phase.
* `Complex.norm_sum_eq_iff_exists_mul`: triangle equality holds iff every summand is a nonnegative
  real multiple of a single complex number.


## Tags

triangle inequality, triangle equality, same ray, phase, argument
-/

public section

namespace Complex

open Finset

variable {ι : Type*} {s : Finset ι} {i : ι} {v : ι → ℂ}

lemma normalize_eq_of_pairwise_sameRay (hp : ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (v i) (v j)) (hi : i ∈ s)
    (hvi : v i ≠ 0) :
    NormedSpace.normalize (v i) = NormedSpace.normalize (∑ j ∈ s, v j) :=
  (sameRay_sum fun j hj ↦ hp i hi j hj).normalize_eq hvi
    (sum_ne_zero_of_pairwise_sameRay hp hi hvi)

/-- **Triangle equality** for nonzero summands: the norm of the sum equals the sum of the norms
exactly when all the summands share a phase. -/
theorem norm_sum_eq_iff_pairwise_normalize_eq (hv : ∀ i ∈ s, v i ≠ 0) :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔
      ∀ i ∈ s, ∀ j ∈ s, NormedSpace.normalize (v i) = NormedSpace.normalize (v j) := by
  rw [norm_sum_eq_iff_pairwise_sameRay]
  exact forall_congr' fun i ↦ forall_congr' fun hi ↦ forall_congr' fun j ↦ forall_congr' fun hj ↦
    NormedSpace.sameRay_iff_normalize_eq (hv i hi) (hv j hj)

/-- **Triangle equality** over `ℂ`: the norm of a finite sum equals the sum of the norms exactly
when every summand is a nonnegative real multiple of a single complex number. -/
theorem norm_sum_eq_iff_exists_mul :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔ ∃ c : ℂ, ∀ i ∈ s, v i = (‖v i‖ : ℂ) * c := by
  refine ⟨fun h ↦ ⟨NormedSpace.normalize (∑ i ∈ s, v i), fun i hi ↦ ?_⟩, ?_⟩
  · rcases eq_or_ne (v i) 0 with hv | hv
    · simp [hv]
    · rw [← normalize_eq_of_pairwise_sameRay (norm_sum_eq_iff_pairwise_sameRay.1 h) hi hv,
        ← real_smul, NormedSpace.norm_smul_normalize]
  · rintro ⟨c, hvc⟩
    rw [norm_sum_eq_iff_pairwise_sameRay]
    intro i hi j hj
    rw [hvc i hi, hvc j hj, ← real_smul, ← real_smul]
    exact (SameRay.sameRay_nonneg_smul_left c (norm_nonneg _)).nonneg_smul_right (norm_nonneg _)


end Complex
