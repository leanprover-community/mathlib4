/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.LinearAlgebra.ConvexSpace
public import Mathlib.LinearAlgebra.AffineSpace.Combination
import Batteries.Tactic.Trans
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.SetLike

/-!
# Affine spaces are convex spaces

This file shows that every affine space is a convex space.

## Main results

* `AddTorsor.instConvexSpace`: An affine space over a module is a convex space.
* `AddTorsor.convexCombination_eq_affineCombination`: The convex combination equals the affine
  combination.
* `AddTorsor.convexComboPair_eq_lineMap`: Binary convex combinations are given by `lineMap`.
-/

noncomputable section

open scoped Affine

variable {R : Type*} {V : Type*} {P : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]

namespace AddTorsor

/-- The convex combination of points in an affine space, given a probability distribution. -/
public def convexCombination (s : StdSimplex R P) : P :=
  s.weights.support.affineCombination R id s.weights

public theorem convexCombination_single (x : P) :
    convexCombination (StdSimplex.single x : StdSimplex R P) = x := by
  simp only [convexCombination, StdSimplex.single]
  rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  exact ({x} : Finset P).affineCombination_of_eq_one_of_eq_zero _ _
    (Finset.mem_singleton_self x) Finsupp.single_eq_same fun j _ hne => Finsupp.single_eq_of_ne hne

public theorem convexCombination_assoc (f : StdSimplex R (StdSimplex R P)) :
    convexCombination (f.map convexCombination) = convexCombination f.join := by
  classical
  -- Choose a base point
  obtain ⟨b⟩ : Nonempty P := inferInstance
  -- Express both sides using weightedVSubOfPoint with base point b
  have hL := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (f.map convexCombination).weights.support (f.map convexCombination).weights id
    (f.map convexCombination).total b
  have hR := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    f.join.weights.support f.join.weights id f.join.total b
  simp only [convexCombination, hL, hR]
  congr 1
  -- Now show the weighted vector sums are equal
  simp only [Finset.weightedVSubOfPoint_apply, StdSimplex.map, StdSimplex.join, id]
  -- Rewrite LHS using sum_mapDomain_index
  change (Finsupp.mapDomain convexCombination f.weights).sum (fun x w => w • (x -ᵥ b)) = _
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
  simp only [Finsupp.sum, convexCombination]
  -- Expand convexCombination d using base point b
  conv_lhs =>
    congr; · skip
    ext d
    rw [d.weights.support.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
        _ _ d.total b, vadd_vsub, Finset.weightedVSubOfPoint_apply]
    simp only [id]
  simp_rw [Finset.smul_sum, smul_smul]
  -- Expand RHS using sum_finset_sum_index
  let h : P → R → V := fun x w => w • (x -ᵥ b)
  have h_rhs : (∑ d ∈ f.weights.support, f.weights d • d.weights).sum h
      = ∑ d ∈ f.weights.support, (f.weights d • d.weights).sum h :=
    (Finsupp.sum_finset_sum_index (h := h) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)).symm
  simp only [Finsupp.sum] at h_rhs ⊢
  rw [h_rhs]
  -- Both sides are now double sums; show the inner sums match
  congr 1
  ext d
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  -- Show that d.support = (f.weights d • d.weights).support
  by_cases hd : f.weights d = 0
  · simp [hd]
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finsupp.mem_support_iff, ne_eq]
    constructor
    · intro hp
      exact (mul_pos ((f.nonneg d).lt_of_ne' hd) ((d.nonneg p).lt_of_ne' hp)).ne'
    · intro hp hp'
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hp', mul_zero,
        not_true_eq_false] at hp

public instance instConvexSpace : ConvexSpace R P where
  convexCombination := convexCombination
  single := convexCombination_single
  assoc := convexCombination_assoc

/-- `ConvexSpace.convexCombination` in an affine space is the affine combination. -/
public theorem convexCombination_eq_affineCombination (s : StdSimplex R P) :
    letI : ConvexSpace R P := inferInstance
    ConvexSpace.convexCombination s = s.weights.support.affineCombination R id s.weights := by
  rfl

public lemma _root_.convexCombination_eq_sum (f : StdSimplex R V) :
    letI : ConvexSpace R V := inferInstance
    ConvexSpace.convexCombination f = f.sum fun i r ↦ r • i := by
  simp [AddTorsor.convexCombination_eq_affineCombination,
    Finset.affineCombination_eq_linear_combination _ _ _ f.total, Finsupp.sum]

/-- `convexComboPair` in an affine space is the affine line map. -/
public theorem convexComboPair_eq_lineMap (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : s + t = 1) (x y : P) :
    convexComboPair s t hs ht h x y = AffineMap.lineMap y x s := by
  simp only [convexComboPair, convexCombination_eq_affineCombination, StdSimplex.duple,
    AffineMap.lineMap_apply]
  classical
  -- Use weighted subtraction with base point y
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ id (b := y)]
  swap
  · -- Prove sum of weights equals 1
    trans (Finsupp.single x s + Finsupp.single y t).sum fun _ r => r
    · apply Finset.sum_congr rfl
      intro i _
      simp only [Finsupp.coe_add, Pi.add_apply]
    · rw [Finsupp.sum_add_index (by simp) (by simp), Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp), h]
  -- Now simplify the weighted subtraction
  congr 1
  rw [Finset.weightedVSubOfPoint_apply]
  simp only [id]
  -- Convert to Finsupp.sum
  change (Finsupp.single x s + Finsupp.single y t).sum (fun p w => w • (p -ᵥ y)) = _
  rw [Finsupp.sum_add_index (by simp) (fun _ a b => by simp [add_smul]),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  simp [vsub_self]

end AddTorsor
