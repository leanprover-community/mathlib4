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
public import Mathlib.Tactic.Bound
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Order

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
* `convexComboPair`: Binary convex combinations of two points.

## Design

The design follows a monadic structure where `StdSimplex R` forms a monad and `convexCombination`
is a monadic algebra. This eliminates the need for explicit extensionality axioms and resolves
universe issues with indexed families.

## TODO

* Show that an `AffineSpace` is a `ConvexSpace`.
* Show that `lineMap` agrees with `convexComboPair` where defined.
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
  nonneg : 0 ≤ weights
  /-- The weights sum to 1. -/
  total : weights.sum (fun _ r => r) = 1

attribute [simp] StdSimplex.total
grind_pattern StdSimplex.nonneg => self.weights
grind_pattern StdSimplex.total => self.weights

namespace StdSimplex

variable {R : Type u} [PartialOrder R] [Semiring R]
  {M : Type v}

@[ext]
theorem ext {f g : StdSimplex R M} (h : f.weights = g.weights) : f = g := by
  cases f; cases g; simp_all

variable [IsStrictOrderedRing R]

/-- The point mass distribution concentrated at `x`. -/
def single (x : M) : StdSimplex R M where
  weights := Finsupp.single x 1
  nonneg := by simp
  total := by simp

@[simp]
theorem mk_single (x : M) {nonneg total} :
    (StdSimplex.mk (Finsupp.single x (1 : R)) nonneg total) = single x := rfl

/-- A probability distribution with weight `s` on `x` and weight `t` on `y`. -/
def duple (x y : M) {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) : StdSimplex R M where
  weights := Finsupp.single x s + Finsupp.single y t
  nonneg := add_nonneg (by simpa) (by simpa)
  total := by
    classical
    rw [Finsupp.sum_add_index] <;> simp [h]

/--
Map a function over the support of a standard simplex.
For each n : N, the weight is the sum of weights of all m : M with g m = n.
-/
def map {M : Type v} {N : Type w} (g : M → N) (f : StdSimplex R M) : StdSimplex R N where
  weights := f.weights.mapDomain g
  nonneg := f.mapDomain_nonneg f.nonneg
  total := by simp [Finsupp.sum_mapDomain_index]

/--
Join operation for standard simplices (monadic join).
Given a distribution over distributions, flattens it to a single distribution.
-/
def join (f : StdSimplex R (StdSimplex R M)) : StdSimplex R M where
  weights := f.weights.sum (fun d r => r • d.weights)
  nonneg := f.sum_nonneg fun d _ ↦ smul_nonneg (f.nonneg d) d.nonneg
  total := by
    rw [Finsupp.sum_sum_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
    convert f.total
    rw [Finsupp.sum_smul_index (fun _ ↦ rfl), ← Finsupp.mul_sum, StdSimplex.total, mul_one]

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

attribute [simp] ConvexSpace.single

open ConvexSpace

variable {R M} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] [ConvexSpace R M]

/-- Take a convex combination of two points. -/
def convexComboPair (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M) : M :=
  convexCombination (.duple x y hs ht h)

/-- A binary convex combination with weight 0 on the first point returns the second point. -/
theorem convexComboPair_zero {x y : M} :
    convexComboPair (0 : R) 1 (by simp) (by simp) (by simp) x y = y := by
  simp [convexComboPair, StdSimplex.duple]

/-- A binary convex combination with weight 1 on the first point returns the first point. -/
theorem convexComboPair_one {x y : M} :
    convexComboPair (1 : R) 0 (by simp) (by simp) (by simp) x y = x := by
  simp [convexComboPair, StdSimplex.duple]

/-- A convex combination of a point with itself is that point. -/
theorem convexComboPair_same {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) {x : M} :
    convexComboPair s t hs ht h x x = x := by
  unfold convexComboPair
  convert ConvexSpace.single x
  simp only [StdSimplex.duple, StdSimplex.single, ← Finsupp.single_add, h]
