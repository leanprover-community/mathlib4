/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.LinearAlgebra.ConvexSpace
import Mathlib.LinearAlgebra.AffineSpace.Combination

/-!
# Affine spaces are convex spaces

This file shows that every affine space is a convex space.

## Main results

* `AddTorsor.instConvexSpace`: An affine space over a module is a convex space.
-/

noncomputable section

open scoped Affine

variable {R : Type*} {V : Type*} {P : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]

namespace StdSimplex

omit [IsStrictOrderedRing R] in
/-- The sum of weights over the support equals 1. -/
theorem support_sum (s : StdSimplex R P) : ∑ p ∈ s.weights.support, s.weights p = 1 :=
  s.total

end StdSimplex

namespace AddTorsor

/-- The convex combination of points in an affine space, given a probability distribution. -/
def convexCombination (s : StdSimplex R P) : P :=
  s.weights.support.affineCombination R id s.weights

theorem convexCombination_single (x : P) :
    convexCombination (StdSimplex.single x : StdSimplex R P) = x := by
  simp only [convexCombination, StdSimplex.single]
  rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  refine ({x} : Finset P).affineCombination_of_eq_one_of_eq_zero _ _
    (Finset.mem_singleton_self x) Finsupp.single_eq_same ?_
  intro j _ hne
  exact Finsupp.single_eq_of_ne hne

theorem convexCombination_assoc (f : StdSimplex R (StdSimplex R P)) :
    convexCombination (f.map convexCombination) = convexCombination f.join := by
  classical
  -- Choose a base point
  obtain ⟨b⟩ : Nonempty P := inferInstance
  -- Express both sides using weightedVSubOfPoint with base point b
  have hL := (f.map convexCombination).total
  have hR := f.join.total
  have eqL := @Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    R V P _ _ _ _ P (f.map convexCombination).weights.support
    (f.map convexCombination).weights id hL b
  rw [convexCombination, eqL]
  rw [convexCombination,
    f.join.weights.support.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ hR b]
  congr 1
  -- Now show the weighted vector sums are equal
  simp only [Finset.weightedVSubOfPoint_apply, StdSimplex.map, StdSimplex.join, id]
  -- Rewrite LHS using sum_mapDomain_index
  conv_lhs =>
    rw [show ∑ x ∈ (Finsupp.mapDomain convexCombination f.weights).support,
            (Finsupp.mapDomain convexCombination f.weights) x • (x -ᵥ b) =
          (Finsupp.mapDomain convexCombination f.weights).sum
            (fun x w => w • (x -ᵥ b)) from rfl]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
  -- LHS: f.weights.sum (fun d _ => f.weights d • (cc d -ᵥ b))
  simp only [Finsupp.sum, convexCombination]
  -- Expand cc d -ᵥ b
  conv_lhs =>
    congr; · skip
    ext d
    rw [d.weights.support.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
        _ _ d.total b, vadd_vsub, Finset.weightedVSubOfPoint_apply]
    simp only [id]
  simp_rw [Finset.smul_sum, smul_smul]
  -- LHS: ∑_{d ∈ f.support} ∑_{p ∈ d.support} (f.weights d * d.weights p) • (p -ᵥ b)
  -- RHS: ∑ x ∈ (∑ d ∈ f.support, f.weights d • d.weights).support, ... • (x -ᵥ b)
  -- First expand RHS using sum_finset_sum_index
  let h : P → R → V := fun x w => w • (x -ᵥ b)
  have h_rhs : (∑ d ∈ f.weights.support, f.weights d • d.weights).sum h
      = ∑ d ∈ f.weights.support, (f.weights d • d.weights).sum h :=
    (Finsupp.sum_finset_sum_index (h := h) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)).symm
  simp only [Finsupp.sum] at h_rhs ⊢
  rw [h_rhs]
  -- Now both sides are ∑_{d ∈ f.support} ∑_{p ∈ ...} ...
  congr 1
  ext d
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  -- Need to show the inner sums match
  -- LHS inner: ∑_{p ∈ d.support} (f.weights d * d.weights p) • (p -ᵥ b)
  -- RHS inner: ∑_{p ∈ (f.weights d • d.weights).support} (f.weights d * d.weights p) • (p -ᵥ b)
  -- The supports match when f.weights d ≠ 0 (which is the case in the outer sum)
  by_cases hd : f.weights d = 0
  · simp [hd]
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finsupp.mem_support_iff, ne_eq]
    constructor
    · intro hp
      -- Both f.weights d and d.weights p are non-negative and nonzero, hence positive
      have hd_pos := (f.nonneg d).lt_of_ne' hd
      have hp_pos := (d.nonneg p).lt_of_ne' hp
      exact (mul_pos hd_pos hp_pos).ne'
    · intro hp hp'
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hp', mul_zero,
        not_true_eq_false] at hp

instance instConvexSpace : ConvexSpace R P where
  convexCombination := convexCombination
  single := convexCombination_single
  assoc := convexCombination_assoc

end AddTorsor
