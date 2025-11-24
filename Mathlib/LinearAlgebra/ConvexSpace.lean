/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound
public import Mathlib.Data.Finsupp.SMul

/-!
# Convex spaces

This file defines convex spaces as an algebraic structure supporting finite convex combinations.

## Main definitions

* `StdSimplex R M`: A finitely supported probability distribution over elements of `M` with
  coefficients in `R`. The weights are non-negative and sum to 1.
* `StdSimplex.map`: Map a function over the support of a standard simplex.
* `StdSimplex.join`: Monadic join operation for standard simplices.
* `ConvexSpace R M`: A typeclass for spaces `M` equipped with an operation
  `convexCombination : StdSimplex R M → M` satisfying monadic laws.
* `convexCombo₂`: Binary convex combinations of two points.

## Design

The design follows a monadic structure where `StdSimplex R` forms a monad and `convexCombination`
is a monadic algebra. This eliminates the need for explicit extensionality axioms and resolves
universe issues with indexed families.

## TODO

* Complete the proofs for `StdSimplex.map` and `StdSimplex.join`.
* Show that an `AffineSpace` is a `ConvexSpace`.
* Show that `lineMap` agrees with `convexCombo₂` where defined.
* Show the usual associativity law for binary convex combinations follows from the `assoc` axiom.
-/

@[expose] public section

universe u v w

noncomputable section

/--
A finitely supported probability distribution over elements of `M` with coefficients in `R`.
The weights are non-negative and sum to 1.
-/
structure StdSimplex (R : Type u) [LE R] [AddCommMonoid R] [One R] (M : Type v)
    extends weights : M →₀ R where
  /-- All weights are non-negative. -/
  nonneg : ∀ m, 0 ≤ weights m
  /-- The weights sum to 1. -/
  total : weights.sum (fun _ r => r) = 1

namespace StdSimplex

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  {M : Type v}

open Classical in
/-- The point mass distribution concentrated at `x`. -/
def single (x : M) : StdSimplex R M where
  weights := Finsupp.single x 1
  nonneg m := by
    rw [Finsupp.single_apply]
    split
    · exact zero_le_one' R
    · grind
  total := by simp

open Classical in
/-- A probability distribution with weight `s` on `x` and weight `t` on `y`. -/
def duple (x y : M) {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) : StdSimplex R M where
  weights := Finsupp.single x s + Finsupp.single y t
  nonneg m := by
    -- Proof by Claude, needs golfing:
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    split_ifs with hx hy
    · exact add_nonneg hs ht
    · simp; exact hs
    · simp; exact ht
    · simp
  total := by
    -- Proof by Claude, needs golfing:
    rw [Finsupp.sum_add_index]
    · simp only [Finsupp.sum_single_index, h]
    · intro; simp
    · intro; simp

/--
Map a function over the support of a standard simplex.
For each n : N, the weight is the sum of weights of all m : M with g m = n.
-/
def map {M : Type v} {N : Type w} (g : M → N) (f : StdSimplex R M) : StdSimplex R N where
  weights := f.weights.sum (fun m r => Finsupp.single (g m) r)
  nonneg n := by
    -- Proof by Claude, needs golfing:
    classical
    simp only [Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_nonneg fun m _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact f.nonneg m
    · rfl
  total := by
    -- Proof by Aristotle, needs golfing:
    simp [Finsupp.sum_sum_index]
    induction f
    grind

/--
Join operation for standard simplices (monadic join).
Given a distribution over distributions, flattens it to a single distribution.
-/
def join (f : StdSimplex R (StdSimplex R M)) : StdSimplex R M where
  weights := f.weights.sum (fun d r => r • d.weights)
  nonneg m := by
    -- Proof by Claude, needs golfing:
    simp only [Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_nonneg (fun d _ => ?_)
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    have := f.nonneg d
    have := d.nonneg m
    bound
  total := by
    -- Proof by Aristotle, needs golfing:
    have h_sum_d : ∀ d ∈ f.support, (d.weights.sum (fun _ r => r)) = 1 := by
      intros d hd
      apply d.total;
    simp_all only [Finsupp.mem_support_iff, ne_eq, implies_true, Finsupp.sum_sum_index]
    refine Eq.trans (b := f.support.sum fun d => f.weights d * 1) (Finset.sum_congr rfl ?_) ?_
    · have h_sum_mul : ∀ (a : StdSimplex R M) (b : R),
        (b • a.weights).sum (fun _ r => r) = b * a.weights.sum (fun _ r => r) := by
        intro a b
        have : ((b • a.weights).sum fun x r ↦ r) = b * a.sum fun x r ↦ r := by
          rw [Finsupp.sum_smul_index]
          · simp_all [Finsupp.sum, Finset.mul_sum]
          · simp
        bound
      aesop
    · simp_all [StdSimplex.total];
      exact f.total

end StdSimplex

/--
A set equipped with an operation of finite convex combinations,
where the coefficients must be non-negative and sum to 1.
-/
class ConvexSpace (R : Type u) (M : Type v)
    [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] where
  /-- Take a convex combination with the given probability distribution over points. -/
  convexCombination (f : StdSimplex R M) : M
  /-- Associativity of convex combination (monadic join law). -/
  assoc (f : StdSimplex R (StdSimplex R M)) :
    convexCombination (f.map convexCombination) = convexCombination f.join
  /-- A convex combination of a single point is that point. -/
  single (x : M) : convexCombination (.single x) = x

open ConvexSpace

variable {R M} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] [ConvexSpace R M]

/-- Take a convex combination of two points. -/
def convexCombo₂ (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M) : M :=
  convexCombination (.duple x y hs ht h)

/-- A binary convex combination with weight 0 on the first point returns the second point. -/
proof_wanted convexCombo₂_zero {x y : M} :
  convexCombo₂ (0 : R) 1 (by simp) (by simp) (by simp) x y = y

/-- A binary convex combination with weight 1 on the first point returns the first point. -/
proof_wanted convexCombo₂_one {x y : M} :
  convexCombo₂ (1 : R) 0 (by simp) (by simp) (by simp) x y = x

/-- A convex combination of a point with itself is that point. -/
proof_wanted convexCombo₂_same {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) {x : M} :
  convexCombo₂ s t hs ht h x x = x
