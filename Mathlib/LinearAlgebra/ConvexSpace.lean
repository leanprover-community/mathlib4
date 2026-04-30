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

variable {R : Type u} [PartialOrder R] [Semiring R] {M N P : Type*}

lemma nonempty [Nontrivial R] (f : StdSimplex R M) : Nonempty M := by
  by_contra!
  simpa [Subsingleton.elim f.weights 0, -total] using f.total

@[ext]
theorem ext {f g : StdSimplex R M} (h : f.weights = g.weights) : f = g := by
  cases f; cases g; simp_all

instance instFunLike : FunLike (StdSimplex R M) M R := {
  coe s := s.weights.toFun
  coe_injective' := fun _ _ h ↦ ext (Finsupp.ext fun i ↦ congrFun h i)
}

variable [IsStrictOrderedRing R]

/-- The point mass distribution concentrated at `x`. -/
@[simps weights]
def single (x : M) : StdSimplex R M where
  weights := Finsupp.single x 1
  nonneg := by simp
  total := by simp

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

@[simp]
lemma map_const (f : StdSimplex R M) (x : N) : f.map (fun _ ↦ x) = .single x := by
  classical
  ext a
  suffices f.sum (fun a₁ b ↦ if x = a then b else 0) = if x = a then 1 else 0 by
    simpa [map, Finsupp.mapDomain, ← mk_single, Finsupp.single_apply]
  split_ifs <;> simp

@[simp]
lemma map_single (x : M) (f : M → N) : (single (R := R) x).map f = .single (f x) := by
  ext a
  simp [map, ← mk_single]

@[simp]
lemma map_duple {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M) (f : M → N) :
    (duple x y hs ht h).map f = duple (f x) (f y) hs ht h := by
  ext a
  simp [map, duple, Finsupp.mapDomain_add]

@[simp]
lemma map_id (f : StdSimplex R M) : f.map id = f := by
  ext; simp [map]

lemma map_comp (f : StdSimplex R M) (g₁ : M → N) (g₂ : N → P) :
    f.map (g₂ ∘ g₁) = (f.map g₁).map g₂ := by
  ext; simp [map, Finsupp.mapDomain_comp]

lemma map_map (f : StdSimplex R M) (g₁ : M → N) (g₂ : N → P) :
    (f.map g₁).map g₂ = f.map (fun x ↦ g₂ (g₁ x)) :=
  (map_comp ..).symm

lemma sum_map {s : StdSimplex R M} {f : M → N} {g : N → R → R}
    (hadd : ∀ (a : N) (b₁ b₂ : R), g a (b₁ + b₂) = g a b₁ + g a b₂) :
    (map f s).sum g = s.sum (fun m r ↦ g (f m) r) := by
  have hzero (n : N) : g n 0 = 0 := by simpa using hadd n 0 0
  simp only [map, Finsupp.mapDomain, Finsupp.sum_sum_index hzero hadd]
  congr
  ext m r
  rw [Finsupp.sum_single_index (hzero (f m))]

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

/--
Monadic bind operation for standard simplices. Given weights `f : StdSimplex R M` and
a family of weights `g : M → StdSimplex R N'`, `StdSimplex.bind f g` is the convex
combination of the `g m`, weighted by `f`.
-/
def bind (f : StdSimplex R M) (g : M → StdSimplex R N) : StdSimplex R N := (f.map g).join

@[simp]
lemma bind_single (m : M) (g : M → StdSimplex R N) : bind (single m) g = g m := by
  simp [bind, join]

@[simp]
lemma bind_const (f : StdSimplex R M) (g : StdSimplex R N) : bind f (fun _ ↦ g) = g := by
  simp [bind, join]

lemma bind_weights (f : StdSimplex R M) (g : M → StdSimplex R N) :
  (bind f g).weights = fun n ↦ ∑ k ∈ f.support, f.weights k * (g k).weights n := by
  ext n
  simp only [bind, join, map, Finsupp.sum_apply]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  simp [Finsupp.sum]

lemma support_subset_bind_support {f : StdSimplex R M} (g : M → StdSimplex R N) {m : M}
    (hm : m ∈ f.support) : (g m).support ⊆ (bind f g).support := by
  intro n hn
  rw [Finsupp.mem_support_iff, bind_weights]
  refine ne_of_gt ?_
  have hpos : 0 < f.weights m * (g m).weights n :=
    mul_pos ((f.nonneg m).lt_of_ne' (by grind)) (((g m).nonneg n).lt_of_ne' (by grind))
  have hnonneg (k : M) (hk : k ∈ f.support) : 0 ≤ f.weights k * (g k).weights n := by
    exact mul_nonneg (f.nonneg k) ((g k).nonneg n)
  exact lt_of_lt_of_le hpos (Finset.single_le_sum hnonneg hm)

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
@[simp]
theorem convexComboPair_zero {x y : M} :
    convexComboPair (0 : R) 1 (by simp) (by simp) (by simp) x y = y := by
  simp [convexComboPair, StdSimplex.duple, StdSimplex.mk_single]

/-- A binary convex combination with weight 1 on the first point returns the first point. -/
@[simp]
theorem convexComboPair_one {x y : M} :
    convexComboPair (1 : R) 0 (by simp) (by simp) (by simp) x y = x := by
  simp [convexComboPair, StdSimplex.duple, StdSimplex.mk_single]

/-- A convex combination of a point with itself is that point. -/
@[simp]
theorem convexComboPair_same {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) {x : M} :
    convexComboPair s t hs ht h x x = x := by
  unfold convexComboPair
  convert ConvexSpace.single x
  simp only [StdSimplex.duple, StdSimplex.single, ← Finsupp.single_add, h]

theorem convexComboPair_symm {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) {x y : M} :
    convexComboPair s t hs ht h x y = convexComboPair t s ht hs ((add_comm _ _).trans h) y x := by
  unfold convexComboPair
  congr 1
  ext1
  simp [StdSimplex.duple, add_comm]
