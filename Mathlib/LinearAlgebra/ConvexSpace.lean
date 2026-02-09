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
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LSum

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

/-- The support of a duple has at most 2 elements. -/
theorem duple_support_card_le_two (x y : M)
    {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) :
    (duple x y hs ht h).weights.support.card ≤ 2 := by
  classical
  simp only [duple]
  calc (Finsupp.single x s + Finsupp.single y t).support.card
      _ ≤ ((Finsupp.single x s).support ∪ (Finsupp.single y t).support).card :=
          Finset.card_le_card Finsupp.support_add
      _ ≤ (Finsupp.single x s).support.card + (Finsupp.single y t).support.card :=
          Finset.card_union_le _ _
      _ ≤ ({x} : Finset M).card + ({y} : Finset M).card := by
          apply Nat.add_le_add
          · exact Finset.card_le_card Finsupp.support_single_subset
          · exact Finset.card_le_card Finsupp.support_single_subset
      _ = 2 := by simp [Finset.card_singleton]

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

@[simp]
theorem single_weights (x : M) : (single x : StdSimplex R M).weights = Finsupp.single x 1 := rfl

theorem single_weights_support (x : M) : (single x : StdSimplex R M).weights.support = {x} :=
  Finsupp.support_single_ne_zero x one_ne_zero

/-- The support of a single-element simplex has cardinality 1. -/
theorem single_support_card (x : M) : (single x : StdSimplex R M).weights.support.card = 1 := by
  rw [single_weights_support]
  exact Finset.card_singleton x

/-- Mapping over a single-point simplex. -/
@[simp]
theorem map_single {N : Type w} (g : M → N) (x : M) :
    (single x : StdSimplex R M).map g = single (g x) := by
  ext n
  simp only [map, single_weights, Finsupp.mapDomain_single]

/-- Join of a single-point outer simplex: join (single d) = d -/
@[simp]
theorem join_single (d : StdSimplex R M) :
    (single d : StdSimplex R (StdSimplex R M)).join = d := by
  ext m
  simp only [join, single_weights]
  rw [Finsupp.sum_single_index (by simp : (0 : R) • d.weights = 0)]
  simp

/-- Join of duple of singles: the weights are p at x and q at y.
    We take q explicitly to avoid computing 1-p in a semiring. -/
theorem join_duple_single_single (x y : M) {p q : R}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hsum : p + q = 1) :
    (duple (single x) (single y) hp hq hsum).join.weights =
      Finsupp.single x p + Finsupp.single y q := by
  ext m
  simp only [join, duple]
  classical
  rw [Finsupp.sum_add_index (by simp) (by simp [add_smul])]
  rw [Finsupp.sum_single_index (by simp : (0 : R) • (single x).weights = 0),
      Finsupp.sum_single_index (by simp : (0 : R) • (single y).weights = 0)]
  simp only [single_weights, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]

/-- If a simplex has support cardinality 1, it equals single of the unique element. -/
theorem eq_single_of_card_eq_one (f : StdSimplex R M) (h : f.weights.support.card = 1) :
    ∃ x, f = single x := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
  use x
  ext m
  simp only [single_weights]
  by_cases hm : m = x
  · subst hm
    have htotal := f.total
    simp only [Finsupp.sum] at htotal
    rw [hx] at htotal
    simp only [Finset.sum_singleton] at htotal
    simp [htotal]
  · have hmem : m ∉ f.weights.support := by
      rw [hx]
      simp only [Finset.mem_singleton]
      exact hm
    rw [Finsupp.mem_support_iff, not_not] at hmem
    simp [hmem, hm]

/-- Naturality of join: mapping a function after joining equals
    joining after mapping the function over each inner simplex. -/
theorem join_map {M : Type*} {N : Type*} (g : M → N) (f : StdSimplex R (StdSimplex R M)) :
    (f.join).map g = (f.map (fun d => d.map g)).join := by
  apply StdSimplex.ext
  -- Prove the Finsupp equality via a helper on the raw Finsupp
  have key : ∀ (w : (StdSimplex R M) →₀ R),
      Finsupp.mapDomain g (w.sum fun d r => r • d.weights) =
      (Finsupp.mapDomain (fun d => d.map g) w).sum fun d r => r • d.weights := by
    intro w
    change (Finsupp.mapDomain.addMonoidHom g) (w.sum fun d r => r • d.weights) =
      (Finsupp.mapDomain (fun d => d.map g) w).sum fun d r => r • d.weights
    rw [map_finsuppSum]
    simp_rw [Finsupp.mapDomain.addMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Finsupp.mapDomain_smul, map]
    rw [Finsupp.sum_mapDomain_index]
    · intro d; exact zero_smul R _
    · intro d r₁ r₂; exact add_smul r₁ r₂ _
  exact key f.weights

/-- Functoriality of map: composing two maps equals mapping the composition. -/
theorem map_comp {M : Type*} {N : Type*} {P : Type*}
    (g : M → N) (h : N → P) (f : StdSimplex R M) :
    (f.map g).map h = f.map (h ∘ g) := by
  ext p
  simp only [map, Finsupp.mapDomain_comp]

/-- Monad associativity: join after join equals join after mapping join. -/
theorem join_join {M : Type*} (f : StdSimplex R (StdSimplex R (StdSimplex R M))) :
    f.join.join = (f.map StdSimplex.join).join := by
  apply StdSimplex.ext
  -- The goal reduces to showing two Finsupp sums are equal.
  -- LHS: (f.weights.sum (fun d r => r • d.weights)).sum (fun d' r' => r' • d'.weights)
  -- RHS: (mapDomain join f.weights).sum (fun d r => r • d.weights)
  -- Use a helper to avoid the extends coercion issues
  have key : ∀ (w : (StdSimplex R (StdSimplex R M)) →₀ R),
      (w.sum fun d r => r • d.weights).sum (fun d' r' => r' • d'.weights) =
      (Finsupp.mapDomain join w).sum (fun d r => r • d.weights) := by
    intro w
    trans w.sum fun d r => (r • d.weights).sum (fun d' r' => r' • d'.weights)
    · exact Finsupp.sum_sum_index
        (fun d => zero_smul R d.weights) (fun d r₁ r₂ => add_smul r₁ r₂ d.weights)
    · rw [Finsupp.sum_mapDomain_index
        (fun d => zero_smul R d.weights) (fun d r₁ r₂ => add_smul r₁ r₂ d.weights)]
      apply Finsupp.sum_congr
      intro d _
      simp only [join]
      rw [Finsupp.sum_smul_index (fun d' => zero_smul R d'.weights)]
      simp_rw [mul_smul]
      exact Finsupp.smul_sum.symm
  simp only [join, map]
  exact key f.weights

/-- Mapping over a duple distributes to each element. -/
theorem map_duple {M : Type*} {N : Type*} (g : M → N) (x y : M)
    {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) :
    (duple x y hs ht h).map g = duple (g x) (g y) hs ht h := by
  ext n
  simp only [map, duple, Finsupp.mapDomain_add, Finsupp.mapDomain_single]

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

/-!
## Constructing ConvexSpace from Binary Operations

The following section provides a way to construct a `ConvexSpace` instance from a binary
convex combination operation satisfying appropriate axioms. This avoids the need to directly
define n-ary combinations.
-/

section OfBinary

variable {R : Type u} {M : Type v} [CommRing R]

/--
A binary convex combination operation with a splitting unit.

The operation `binCombo t x y` represents the convex combination `(1-t)x + ty`.
The splitting unit `u` is used to recursively construct n-ary combinations:
we only ever need to divide by `u` or `(1-u)`, not by arbitrary elements.

The key axioms are:
- **Mediality**: `C(p, C(q,A,B), C(q,C,D)) = C(q, C(p,A,C), C(p,B,D))`
  (swapping nested combinations when inner ratio is the same)
- **Entropic identity**: `C(p, C(s,x,y), C(r,x,y)) = C((1-p)s + pr, x, y)`
  (distributivity for combining two combinations of the same points)
-/
structure BinaryConvexOp (R : Type u) (M : Type v) [CommRing R] where
  /-- The splitting unit used for recursive construction. -/
  u : R
  /-- The splitting unit is invertible. -/
  [u_inv : Invertible u]
  /-- The complement of the splitting unit is invertible. -/
  [one_sub_u_inv : Invertible (1 - u)]
  /-- The binary combination: `binCombo t x y` computes `(1-t)x + ty`. -/
  binCombo : R → M → M → M
  /-- Endpoint: weight 0 on second point gives first point. -/
  binCombo_zero : ∀ x y, binCombo 0 x y = x
  /-- Endpoint: weight 1 on second point gives second point. -/
  binCombo_one : ∀ x y, binCombo 1 x y = y
  /-- Combining a point with itself gives that point. -/
  binCombo_same : ∀ t x, binCombo t x x = x
  /-- Mediality: swapping nested combinations when inner ratio is the same. -/
  binCombo_mediality : ∀ p q : R, ∀ a b c d : M,
    binCombo p (binCombo q a b) (binCombo q c d) =
      binCombo q (binCombo p a c) (binCombo p b d)
  /-- Entropic identity: combining two combinations of the same points. -/
  binCombo_entropic : ∀ p s r : R, ∀ x y : M,
    binCombo p (binCombo s x y) (binCombo r x y) = binCombo ((1 - p) * s + p * r) x y

attribute [instance] BinaryConvexOp.u_inv BinaryConvexOp.one_sub_u_inv

namespace BinaryConvexOp

variable (op : BinaryConvexOp R M)

/-- Convenient access to the inverse of the splitting unit. -/
noncomputable def invU : R := ⅟op.u

/-- Convenient access to the inverse of (1 - u). -/
noncomputable def invOneSubU : R := ⅟(1 - op.u)

end BinaryConvexOp

/-!
## The Affine Algorithm from convex_plan.md

We work with weighted sequences `List (R × M)` where the weights sum to 1.
The algorithm only divides by `u` and `(1-u)`, never by arbitrary sums.
-/

variable {R : Type u} {M : Type v} [CommRing R]

/-- A weighted sequence: list of (weight, point) pairs. -/
abbrev WeightedSeq (R : Type*) (M : Type*) := List (R × M)

/-- The sum of weights in a weighted sequence. -/
def WeightedSeq.totalWeight (ws : WeightedSeq R M) : R :=
  (ws.map Prod.fst).sum

/-- A weighted sequence is valid if weights sum to 1. -/
def WeightedSeq.isValid (ws : WeightedSeq R M) : Prop :=
  ws.totalWeight = 1

/-- Extract just the points from a weighted sequence. -/
def WeightedSeq.points (ws : WeightedSeq R M) : List M :=
  ws.map Prod.snd

/-- Extract just the weights from a weighted sequence. -/
def WeightedSeq.weights (ws : WeightedSeq R M) : List R :=
  ws.map Prod.fst

/-- Scale all weights in a weighted sequence by a factor. -/
def WeightedSeq.scale (c : R) (ws : WeightedSeq R M) : WeightedSeq R M :=
  ws.map fun (w, x) => (c * w, x)

/-- Combine two weighted sequences over the same points with a convex combination of weights.
    `combineWeights p ws₁ ws₂` computes `(1-p) * ws₁ + p * ws₂` (pointwise on weights). -/
def WeightedSeq.combineWeights (p : R) (ws₁ ws₂ : WeightedSeq R M) : WeightedSeq R M :=
  List.zipWith (fun (w₁, x) (w₂, _) => ((1 - p) * w₁ + p * w₂, x)) ws₁ ws₂

/-- Two weighted sequences have the same points (in the same order). -/
def WeightedSeq.samePoints (ws₁ ws₂ : WeightedSeq R M) : Prop :=
  ws₁.map Prod.snd = ws₂.map Prod.snd

@[simp]
theorem WeightedSeq.combineWeights_length (p : R) (ws₁ ws₂ : WeightedSeq R M) :
    (combineWeights p ws₁ ws₂).length = min ws₁.length ws₂.length := by
  simp [combineWeights, List.length_zipWith]

@[simp]
theorem WeightedSeq.scale_length (c : R) (ws : WeightedSeq R M) :
    (scale c ws).length = ws.length := by
  simp [scale]

/-- Extract the left weighted sequence for the recursive step in affineOfBinary.
    For input of length n ≥ 3, returns a sequence of length n-1 containing
    points x₁, x₂, ..., x_{n-1} with weights scaled by ⅟u and slack at position 2. -/
noncomputable def leftWeightedSeq (op : BinaryConvexOp R M) :
    WeightedSeq R M → WeightedSeq R M
  | [] => []
  | [_] => []
  | [_, _] => []
  | (s₁, x₁) :: (_, x₂) :: (s₃, x₃) :: rest =>
    let invU := ⅟op.u
    let a₁ := invU * s₁
    -- All weights except first two and last: s₃, s₄, ..., s_{n-1}
    let middleWeights := (s₃ :: rest.map Prod.fst).dropLast
    let scaledMiddle := middleWeights.map (invU * ·)
    let a₂ := 1 - a₁ - scaledMiddle.sum
    -- Points: x₃, x₄, ..., x_{n-1}
    let middlePoints := (x₃ :: rest.map Prod.snd).dropLast
    (a₁, x₁) :: (a₂, x₂) :: scaledMiddle.zip middlePoints

/-- Extract the right weighted sequence for the recursive step in affineOfBinary.
    For input of length n ≥ 3, returns a sequence of length n-1 containing
    points x₂, x₃, ..., xₙ with weight ⅟(1-u)·sₙ on xₙ, zeros in middle, and slack at x₂. -/
noncomputable def rightWeightedSeq (op : BinaryConvexOp R M) :
    WeightedSeq R M → WeightedSeq R M
  | [] => []
  | [_] => []
  | [_, _] => []
  | (_, _) :: (_, x₂) :: (s₃, x₃) :: rest =>
    let restPoints := rest.map Prod.snd
    let invOneSubU := ⅟(1 - op.u)
    let sₙ := match rest.getLast? with
      | some (w, _) => w
      | none => s₃
    let bLast := invOneSubU * sₙ
    let b₁ := 1 - bLast
    -- Number of zeros = n - 3 = rest.length (for x₃, x₄, ..., x_{n-1})
    let middleZeros := List.replicate rest.length (0 : R)
    (b₁, x₂) :: (middleZeros ++ [bLast]).zip (x₃ :: restPoints)

-- Key lemmas about the helper functions
section WeightedSeqLemmas

variable [CommRing R]

/-- The left weighted sequence has the same points for inputs with the same points. -/
theorem leftWeightedSeq_samePoints (op : BinaryConvexOp R M)
    {ws₁ ws₂ : WeightedSeq R M}
    (hlen : ws₁.length = ws₂.length)
    (hpts : ws₁.samePoints ws₂) :
    (leftWeightedSeq op ws₁).samePoints (leftWeightedSeq op ws₂) := by
  match ws₁, ws₂ with
  | [], [] => rfl
  | [_], [_] => rfl
  | [_, _], [_, _] => rfl
  | (s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest₁,
    (r₁, y₁) :: (r₂, y₂) :: (r₃, y₃) :: rest₂ =>
    -- Extract the point equalities from hpts
    simp only [WeightedSeq.samePoints, List.map_cons, List.cons.injEq] at hpts
    have hx₁ : x₁ = y₁ := hpts.1
    have hx₂ : x₂ = y₂ := hpts.2.1
    have hx₃ : x₃ = y₃ := hpts.2.2.1
    have hrest : rest₁.map Prod.snd = rest₂.map Prod.snd := hpts.2.2.2
    -- Simplify the goal
    simp only [WeightedSeq.samePoints, leftWeightedSeq, List.map_cons, List.cons.injEq]
    refine ⟨hx₁, hx₂, ?_⟩
    -- Both sides have the same second list in zip
    have hpts' : (x₃ :: rest₁.map Prod.snd).dropLast = (y₃ :: rest₂.map Prod.snd).dropLast := by
      simp [hx₃, hrest]
    simp only [List.length_cons] at hlen
    have hrest_len : rest₁.length = rest₂.length := by omega
    rw [List.map_snd_zip (by simp [hrest_len]),
        List.map_snd_zip (by simp), hpts']

/-- The right weighted sequence has the same points for inputs with the same points. -/
theorem rightWeightedSeq_samePoints (op : BinaryConvexOp R M)
    {ws₁ ws₂ : WeightedSeq R M}
    (hlen : ws₁.length = ws₂.length)
    (hpts : ws₁.samePoints ws₂) :
    (rightWeightedSeq op ws₁).samePoints (rightWeightedSeq op ws₂) := by
  match ws₁, ws₂ with
  | [], [] => rfl
  | [_], [_] => rfl
  | [_, _], [_, _] => rfl
  | (s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest₁,
    (r₁, y₁) :: (r₂, y₂) :: (r₃, y₃) :: rest₂ =>
    -- Extract the point equalities from hpts
    simp only [WeightedSeq.samePoints, List.map_cons, List.cons.injEq] at hpts
    have hx₂ : x₂ = y₂ := hpts.2.1
    have hx₃ : x₃ = y₃ := hpts.2.2.1
    have hrest : rest₁.map Prod.snd = rest₂.map Prod.snd := hpts.2.2.2
    -- Simplify the goal
    simp only [WeightedSeq.samePoints, rightWeightedSeq, List.map_cons, List.cons.injEq]
    refine ⟨hx₂, ?_⟩
    -- Both sides use the same points: x₃ :: restPoints
    have hpts' : x₃ :: rest₁.map Prod.snd = y₃ :: rest₂.map Prod.snd := by
      simp [hx₃, hrest]
    simp only [List.length_cons] at hlen
    have hrest_len : rest₁.length = rest₂.length := by omega
    rw [List.map_snd_zip (by simp [hrest_len]),
        List.map_snd_zip (by simp), hpts']

/-- The left weighted sequence has length n-1 for input of length n ≥ 3. -/
theorem leftWeightedSeq_length (op : BinaryConvexOp R M)
    (ws : WeightedSeq R M) (h : 3 ≤ ws.length) :
    (leftWeightedSeq op ws).length = ws.length - 1 := by
  match ws with
  | (s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest =>
    simp only [leftWeightedSeq, List.length_cons, List.length_zip, List.length_map,
      List.length_dropLast]
    omega

/-- The right weighted sequence has length n-1 for input of length n ≥ 3. -/
theorem rightWeightedSeq_length (op : BinaryConvexOp R M)
    (ws : WeightedSeq R M) (h : 3 ≤ ws.length) :
    (rightWeightedSeq op ws).length = ws.length - 1 := by
  match ws with
  | (s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest =>
    simp only [rightWeightedSeq, List.length_cons, List.length_zip, List.length_append,
      List.length_replicate, List.length_map]
    omega

/-- The weight construction for leftWeightedSeq commutes with combineWeights.
    This is the key linearity property. -/
theorem leftWeightedSeq_combineWeights (op : BinaryConvexOp R M)
    (p : R) (ws₁ ws₂ : WeightedSeq R M)
    (hlen : ws₁.length = ws₂.length)
    (hpts : ws₁.samePoints ws₂) :
    (leftWeightedSeq op ws₁).combineWeights p (leftWeightedSeq op ws₂) =
      leftWeightedSeq op (ws₁.combineWeights p ws₂) := by
  match ws₁, ws₂ with
  | [], [] => rfl
  | [_], [_] => rfl
  | [_, _], [_, _] => rfl
  | (s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest₁,
    (r₁, y₁) :: (r₂, y₂) :: (r₃, y₃) :: rest₂ =>
    simp only [WeightedSeq.samePoints, List.map_cons, List.cons.injEq] at hpts
    have hx₁ : x₁ = y₁ := hpts.1
    have hx₂ : x₂ = y₂ := hpts.2.1
    have hx₃ : x₃ = y₃ := hpts.2.2.1
    have hrest : rest₁.map Prod.snd = rest₂.map Prod.snd := hpts.2.2.2
    subst hx₁ hx₂ hx₃
    simp only [List.length_cons] at hlen
    have hrest_len : rest₁.length = rest₂.length := by omega
    -- Unfold definitions
    simp only [leftWeightedSeq, WeightedSeq.combineWeights, List.zipWith]
    -- Now we need to show equality of lists
    -- LHS: combineWeights of two leftWeightedSeq outputs
    -- RHS: leftWeightedSeq of combined input
    congr 1
    · -- First element: (1-p)*(⅟u * s₁) + p*(⅟u * r₁) = ⅟u * ((1-p)*s₁ + p*r₁)
      simp only [Prod.mk.injEq]
      refine ⟨?_, trivial⟩
      -- Weight component: factor out ⅟u
      ring
    congr 1
    · -- Second element (slack): linearity of slack construction
      simp only [Prod.mk.injEq]
      refine ⟨?_, trivial⟩
      -- The slack is: 1 - a₁ - scaledMiddle.sum
      -- We need: (1-p)*(1 - a₁₁ - sm₁.sum) + p*(1 - a₁₂ - sm₂.sum)
      --        = 1 - ((1-p)*a₁₁ + p*a₁₂) - ((1-p)*sm₁ + p*sm₂).sum
      -- This follows from linearity of sum.
      -- The algebra involves showing:
      -- (1-p)*(1 - ⅟u*s₁ - sum(⅟u*middle₁)) + p*(1 - ⅟u*r₁ - sum(⅟u*middle₂))
      -- = 1 - ⅟u*((1-p)*s₁+p*r₁) - sum(⅟u*((1-p)*middle₁+p*middle₂))
      -- This requires showing List.sum commutes with combineWeights (zipWith).
      sorry
    · -- Tail elements: scaledMiddle.zip middlePoints
      -- The tail is (⅟u * middleWeights).zip middlePoints
      -- combineWeights on zip gives zip of combineWeights on weights
      sorry

/-- The weight construction for rightWeightedSeq commutes with combineWeights.
    This is the key linearity property. -/
theorem rightWeightedSeq_combineWeights (op : BinaryConvexOp R M)
    (p : R) (ws₁ ws₂ : WeightedSeq R M)
    (hlen : ws₁.length = ws₂.length)
    (hpts : ws₁.samePoints ws₂) :
    (rightWeightedSeq op ws₁).combineWeights p (rightWeightedSeq op ws₂) =
      rightWeightedSeq op (ws₁.combineWeights p ws₂) := by
  match ws₁, ws₂ with
  | [], [] => rfl
  | [_], [_] => rfl
  | [_, _], [_, _] => rfl
  | (s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest₁,
    (r₁, y₁) :: (r₂, y₂) :: (r₃, y₃) :: rest₂ =>
    -- Similar to leftWeightedSeq_combineWeights, the weight construction is linear
    simp only [WeightedSeq.samePoints, List.map_cons, List.cons.injEq] at hpts
    have hx₁ : x₁ = y₁ := hpts.1
    have hx₂ : x₂ = y₂ := hpts.2.1
    have hx₃ : x₃ = y₃ := hpts.2.2.1
    have hrest : rest₁.map Prod.snd = rest₂.map Prod.snd := hpts.2.2.2
    subst hx₁ hx₂ hx₃
    simp only [List.length_cons] at hlen
    have hrest_len : rest₁.length = rest₂.length := by omega
    -- Unfold definitions
    simp only [rightWeightedSeq, WeightedSeq.combineWeights, List.zipWith]
    -- The key fact is that bLast = ⅟(1-u) * sₙ and b₁ = 1 - bLast are linear
    -- The middle elements are all zeros, so combining them is trivial
    -- For now, use sorry as this requires showing getLast? behaves correctly
    sorry

end WeightedSeqLemmas

/-- Compute the affine combination using the algorithm from convex_plan.md.
    This only divides by `u` and `(1-u)`, using the Invertible instances from `op`. -/
noncomputable def affineOfBinary [Inhabited M] (op : BinaryConvexOp R M) : WeightedSeq R M → M
  | [] => default  -- Degenerate case, never called on valid input
  | [(_, x)] => x  -- n = 1: just return the point
  | [(_, x₁), (s₂, x₂)] => op.binCombo s₂ x₁ x₂  -- n = 2: binary combination
  | (s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest =>
    -- n ≥ 3: Split into overlapping groups and recurse
    -- Points: x₁, x₂, x₃, ...rest
    -- Weights: s₁, s₂, s₃, ...restWeights
    let restPoints := rest.map Prod.snd
    let u := op.u
    let invU := ⅟u
    let invOneSubU := ⅟(1 - u)
    -- Left group: [x₁, x₂, ..., x_{n-1}] (drop last point)
    -- Left weights from convex_plan.md:
    --   a₁ = u⁻¹ s₁
    --   aₖ = u⁻¹ sₖ for k ∈ {3, ..., n-1}
    --   a₂ = 1 - ∑_{j≠2} aⱼ (slack)
    let a₁ := invU * s₁
    -- All weights except first two and last: s₃, s₄, ..., s_{n-1}
    let middleWeights := (s₃ :: rest.map Prod.fst).dropLast
    let scaledMiddle := middleWeights.map (invU * ·)
    let a₂ := 1 - a₁ - scaledMiddle.sum
    -- Points: x₃, x₄, ..., x_{n-1}
    let middlePoints := (x₃ :: restPoints).dropLast
    -- Left weighted sequence: (a₁, x₁), (a₂, x₂), then (aₖ, xₖ) for k ∈ {3,...,n-1}
    let leftWS : WeightedSeq R M := (a₁, x₁) :: (a₂, x₂) :: scaledMiddle.zip middlePoints
    -- Right group: [x₂, x₃, ..., xₙ] (drop first point)
    -- Right weights from convex_plan.md:
    --   b_{n-1} = (1-u)⁻¹ sₙ
    --   bₖ = 0 for k ∈ {2, ..., n-2}
    --   b₁ = 1 - ∑_{j≠1} bⱼ (slack)
    let sₙ := match rest.getLast? with
      | some (w, _) => w
      | none => s₃  -- n = 3 case: sₙ = s₃
    let bLast := invOneSubU * sₙ
    let b₁ := 1 - bLast
    -- Number of zeros = n - 3 = rest.length (for x₃, x₄, ..., x_{n-1})
    let middleZeros := List.replicate rest.length (0 : R)
    let rightWS : WeightedSeq R M :=
      (b₁, x₂) :: (middleZeros ++ [bLast]).zip (x₃ :: restPoints)
    -- Recursive calls with termination proof
    -- leftWS.length = 2 + (rest.length).min (rest.length) = 2 + rest.length < 3 + rest.length
    have hleft : leftWS.length < ((s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest).length := by
      simp only [leftWS, List.length_cons, List.length_zip, scaledMiddle, middleWeights,
        middlePoints, List.length_map, List.length_dropLast]
      omega
    -- rightWS.length = 1 + (rest.length + 1) = 2 + rest.length < 3 + rest.length
    have hright : rightWS.length < ((s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest).length := by
      simp only [rightWS, List.length_cons, List.length_zip, List.length_append,
        middleZeros, List.length_replicate, restPoints, List.length_map]
      omega
    let L := affineOfBinary op leftWS
    let R := affineOfBinary op rightWS
    -- Final combination: C(1-u, L, R) = u*L + (1-u)*R
    op.binCombo (1 - u) L R
termination_by ws => ws.length

/-- For lists of length ≥ 3, affineOfBinary decomposes as C(1-u, L, R)
    where L and R are the affine combinations of leftWeightedSeq and rightWeightedSeq. -/
theorem affineOfBinary_decompose [Inhabited M] (op : BinaryConvexOp R M)
    (s₁ : R) (x₁ : M) (s₂ : R) (x₂ : M) (s₃ : R) (x₃ : M) (rest : List (R × M)) :
    affineOfBinary op ((s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest) =
      op.binCombo (1 - op.u)
        (affineOfBinary op (leftWeightedSeq op ((s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest)))
        (affineOfBinary op (rightWeightedSeq op ((s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest))) := by
  simp only [affineOfBinary, leftWeightedSeq, rightWeightedSeq]

/-!
### Zero-Weight Invariance

A crucial property: adding a zero-weight point to the beginning or end of a weighted
sequence doesn't change the affine combination. This is used to extend inner simplices
to a common support before applying the linearity lemma.
-/

/-- Adding a zero-weight point at the front doesn't change the affine combination.
    This follows from binCombo_one (when left weight is 0, we get x₁) and entropic. -/
theorem affineOfBinary_cons_zero [Inhabited M] (op : BinaryConvexOp R M)
    (x : M) (ws : WeightedSeq R M) (hvalid : ws.totalWeight = 1) (hne : ws ≠ []) :
    affineOfBinary op ((0, x) :: ws) = affineOfBinary op ws := by
  -- The proof uses: when we prepend (0, x), the left branch gets weight 0 and
  -- reduces to a single point, then the binary combination with (1-u) gives back
  -- the right branch's result (via entropic identity).
  match ws with
  | [] => exact absurd rfl hne
  | [(w, y)] =>
    -- Length 2 case: [(0, x), (w, y)] where w = 1 (since totalWeight = 1)
    -- LHS: affineOfBinary [(0, x), (w, y)] = binCombo(w, x, y)
    -- When w = 1: binCombo(1, x, y) = y
    -- RHS: affineOfBinary [(w, y)] = y
    simp only [affineOfBinary]
    have hw : w = 1 := by simpa [WeightedSeq.totalWeight] using hvalid
    subst hw
    exact op.binCombo_one x y
  | (w₁, y₁) :: (w₂, y₂) :: rest =>
    -- Length ≥ 3 case: [(0, x), (w₁, y₁), (w₂, y₂), ...rest]
    -- We need to show this equals affineOfBinary [(w₁, y₁), (w₂, y₂), ...rest]
    --
    -- The algorithm decomposes [(0, x), (w₁, y₁), (w₂, y₂), ...rest]:
    --   s₁ = 0, x₁ = x
    --   s₂ = w₁, x₂ = y₁
    --   s₃ = w₂, x₃ = y₂
    --   rest = rest
    --
    -- Left sequence: points are [x, y₁, ..., dropLast]
    --   a₁ = ⅟u * 0 = 0
    --   scaledMiddle = [⅟u * w₂, ...] (middle weights scaled)
    --   a₂ = 1 - 0 - scaledMiddle.sum = slack
    --   leftWS = [(0, x), (a₂, y₁), (scaled middle, middle points)]
    --
    -- Right sequence: points are [y₁, y₂, ..., last]
    --   bLast = ⅟(1-u) * last_weight
    --   b₁ = 1 - bLast = slack
    --   rightWS = [(b₁, y₁), (zeros + bLast, y₂::rest)]
    --
    -- Result = binCombo(1-u, L, R)
    --   where L = affineOfBinary leftWS
    --         R = affineOfBinary rightWS
    --
    -- Key observation: leftWS has (0, x) at front, so by IH:
    --   L = affineOfBinary (leftWS without the zero)
    --     = affineOfBinary [(a₂, y₁), (scaled middle)]
    --
    -- But a₂ and the right sequence are chosen such that the final result
    -- only depends on [y₁, y₂, ...rest].
    --
    -- This requires careful algebraic verification that the u factors cancel.
    -- The proof is complex and deferred.
    sorry

/-- Adding a zero-weight point at the end doesn't change the affine combination.
    This follows from binCombo_zero (when right weight is 0, we get previous result). -/
theorem affineOfBinary_append_zero [Inhabited M] (op : BinaryConvexOp R M)
    (ws : WeightedSeq R M) (x : M) (hvalid : ws.totalWeight = 1) (hne : ws ≠ []) :
    affineOfBinary op (ws ++ [(0, x)]) = affineOfBinary op ws := by
  match ws with
  | [] => exact absurd rfl hne
  | [(w, y)] =>
    -- Length 2 case: [(w, y), (0, x)] where w = 1 (since totalWeight = 1)
    -- LHS: affineOfBinary [(w, y), (0, x)] = binCombo(0, y, x) = y (by binCombo_zero)
    -- RHS: affineOfBinary [(w, y)] = y
    simp only [List.singleton_append, affineOfBinary]
    have hw : w = 1 := by simpa [WeightedSeq.totalWeight] using hvalid
    subst hw
    exact op.binCombo_zero y x
  | (w₁, y₁) :: (w₂, y₂) :: rest =>
    -- Length ≥ 3 case: appending (0, x) to a list of length ≥ 2
    -- Similar recursive reasoning as cons_zero
    sorry

/-- More generally, zeros anywhere in the sequence don't affect the result.
    This allows extending to a common support by padding with zeros. -/
theorem affineOfBinary_filter_nonzero [Inhabited M] [DecidableEq R] (op : BinaryConvexOp R M)
    (ws : WeightedSeq R M) (hvalid : ws.totalWeight = 1) :
    affineOfBinary op ws = affineOfBinary op (ws.filter (fun p => p.1 != 0)) := by
  sorry

/-- The total weight at each point in a weighted sequence. -/
def WeightedSeq.toFinsupp (ws : WeightedSeq R M) : M →₀ R :=
  ws.foldl (fun acc (w, x) => acc + Finsupp.single x w) 0

/-- affineOfBinary only depends on the total weights, not the list structure.
    This is the key invariance property needed for the assoc proof. -/
theorem affineOfBinary_eq_of_same_finsupp [Inhabited M] (op : BinaryConvexOp R M)
    (ws₁ ws₂ : WeightedSeq R M)
    (hvalid₁ : ws₁.totalWeight = 1) (hvalid₂ : ws₂.totalWeight = 1)
    (heq : ws₁.toFinsupp = ws₂.toFinsupp) :
    affineOfBinary op ws₁ = affineOfBinary op ws₂ := by
  -- This says: if two weighted sequences give the same total weight at each point,
  -- then affineOfBinary produces the same result.
  --
  -- Proof sketch by strong induction on support size:
  -- - size 0: impossible (totalWeight = 1)
  -- - size 1: both reduce to single point
  -- - size 2: use affineOfBinary_swap_two and binCombo_same for merging
  -- - size ≥ 3: use zero-padding and permutation invariance
  --
  -- The full proof requires:
  -- 1. affineOfBinary_filter_nonzero to remove zeros
  -- 2. Permutation invariance for arbitrary list lengths
  -- This is non-trivial and may require induction on the number of points.
  sorry


/-!
### The Linearity Lemma

The key lemma for proving associativity: a binary combination of two affine sums
(over the same points) equals the affine sum of the combined weights.

`C(p, A(s, x), A(r, x)) = A((1-p)s + pr, x)`
-/

section AlgebraicLemmas
variable {R : Type*} [CommRing R]

/-- Multiplication distributes over convex weight combination.
    c * ((1-p)*s + p*r) = (1-p)*(c*s) + p*(c*r) -/
theorem mul_combineWeight (c p s r : R) :
    c * ((1 - p) * s + p * r) = (1 - p) * (c * s) + p * (c * r) := by ring

/-- The slack variable construction is linear in the weights. -/
theorem slack_linear (p a₁ a₂ sum₁ sum₂ : R) :
    (1 - ((1 - p) * a₁ + p * a₂) - ((1 - p) * sum₁ + p * sum₂)) =
    (1 - p) * (1 - a₁ - sum₁) + p * (1 - a₂ - sum₂) := by ring

end AlgebraicLemmas

/-- The linearity lemma: a binary convex combination of two affine sums over the same points
    equals the affine sum of the convexly combined weights.

    This is proven by strong induction on the length of the weighted sequences:
    - n=0,1: Both sides are the same point, use binCombo_same
    - n=2: Reduces to binCombo_entropic
    - n≥3: Expand both sides, use mediality to swap, apply IH, verify weight arithmetic
-/
theorem affineOfBinary_linear [CommRing R] [Inhabited M] (op : BinaryConvexOp R M)
    (p : R) (ws₁ ws₂ : WeightedSeq R M)
    (hlen : ws₁.length = ws₂.length)
    (hpts : ws₁.samePoints ws₂) :
    op.binCombo p (affineOfBinary op ws₁) (affineOfBinary op ws₂) =
      affineOfBinary op (ws₁.combineWeights p ws₂) := by
  -- Use strong induction on length
  induction h : ws₁.length using Nat.strongRecOn generalizing ws₁ ws₂ with
  | _ n ih =>
    match h₁ : ws₁, h₂ : ws₂ with
    | [], [] =>
      simp only [affineOfBinary, WeightedSeq.combineWeights, List.zipWith_nil_left]
      exact op.binCombo_same p default
    | [(w₁, x₁)], [(w₂, x₂)] =>
      simp only [WeightedSeq.samePoints, List.map_cons, List.map_nil] at hpts
      have hx : x₁ = x₂ := by simpa using hpts
      subst hx
      simp only [affineOfBinary, WeightedSeq.combineWeights, List.zipWith]
      exact op.binCombo_same p x₁
    | [(w₁₁, x₁), (w₁₂, x₂)], [(w₂₁, y₁), (w₂₂, y₂)] =>
      simp only [WeightedSeq.samePoints, List.map_cons, List.map_nil] at hpts
      have hx₁ : x₁ = y₁ := by simp_all
      have hx₂ : x₂ = y₂ := by simp_all
      subst hx₁ hx₂
      simp only [affineOfBinary, WeightedSeq.combineWeights, List.zipWith]
      exact op.binCombo_entropic p w₁₂ w₂₂ x₁ x₂
    | (s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest₁,
      (r₁, y₁) :: (r₂, y₂) :: (r₃, y₃) :: rest₂ =>
      -- The inductive case (n ≥ 3)
      simp only [WeightedSeq.samePoints, List.map_cons] at hpts
      have hx₁ : x₁ = y₁ := by simp_all
      have hx₂ : x₂ = y₂ := by simp_all
      have hx₃ : x₃ = y₃ := by simp_all
      have hrest_pts : rest₁.map Prod.snd = rest₂.map Prod.snd := by simp_all
      subst hx₁ hx₂ hx₃
      simp only [List.length_cons] at hlen h
      have hrest_len : rest₁.length = rest₂.length := by omega
      -- Define the full weighted sequences for clarity
      let ws₁' := (s₁, x₁) :: (s₂, x₂) :: (s₃, x₃) :: rest₁
      let ws₂' := (r₁, x₁) :: (r₂, x₂) :: (r₃, x₃) :: rest₂
      have hpts' : WeightedSeq.samePoints ws₁' ws₂' := by
        simp only [WeightedSeq.samePoints, List.map_cons, ws₁', ws₂', hrest_pts]
      have hlen' : ws₁'.length = ws₂'.length := by simp [ws₁', ws₂', hrest_len]
      -- The proof follows convex_plan.md:
      -- 1. LHS = C(p, C(1-u, L₁, R₁), C(1-u, L₂, R₂))  [by decompose]
      -- 2. = C(1-u, C(p, L₁, L₂), C(p, R₁, R₂))        [by mediality]
      -- 3. = C(1-u, A(combine L), A(combine R))         [by IH]
      -- 4. = A(combine ws)                              [by decompose + combineWeights lemmas]

      -- Step 1: Expand LHS using decomposition
      have hdecomp₁ : affineOfBinary op ws₁' =
          op.binCombo (1 - op.u)
            (affineOfBinary op (leftWeightedSeq op ws₁'))
            (affineOfBinary op (rightWeightedSeq op ws₁')) :=
        affineOfBinary_decompose op s₁ x₁ s₂ x₂ s₃ x₃ rest₁
      have hdecomp₂ : affineOfBinary op ws₂' =
          op.binCombo (1 - op.u)
            (affineOfBinary op (leftWeightedSeq op ws₂'))
            (affineOfBinary op (rightWeightedSeq op ws₂')) :=
        affineOfBinary_decompose op r₁ x₁ r₂ x₂ r₃ x₃ rest₂
      -- Prepare IH applications
      have hlen_left : (leftWeightedSeq op ws₁').length = (leftWeightedSeq op ws₂').length := by
        rw [leftWeightedSeq_length op ws₁' (by simp [ws₁']),
            leftWeightedSeq_length op ws₂' (by simp [ws₂'])]
        simp [ws₁', ws₂', hrest_len]
      have hlen_right : (rightWeightedSeq op ws₁').length = (rightWeightedSeq op ws₂').length := by
        rw [rightWeightedSeq_length op ws₁' (by simp [ws₁']),
            rightWeightedSeq_length op ws₂' (by simp [ws₂'])]
        simp [ws₁', ws₂', hrest_len]
      have hpts_left : (leftWeightedSeq op ws₁').samePoints (leftWeightedSeq op ws₂') :=
        leftWeightedSeq_samePoints op hlen' hpts'
      have hpts_right : (rightWeightedSeq op ws₁').samePoints (rightWeightedSeq op ws₂') :=
        rightWeightedSeq_samePoints op hlen' hpts'
      have h_left_len : (leftWeightedSeq op ws₁').length < n := by
        rw [leftWeightedSeq_length op ws₁' (by simp [ws₁'])]
        simp only [ws₁', List.length_cons] at h ⊢
        omega
      have h_right_len : (rightWeightedSeq op ws₁').length < n := by
        rw [rightWeightedSeq_length op ws₁' (by simp [ws₁'])]
        simp only [ws₁', List.length_cons] at h ⊢
        omega
      -- Rewrite using decompositions
      calc op.binCombo p (affineOfBinary op ws₁') (affineOfBinary op ws₂')
          -- Step 1: Expand using decomposition
          _ = op.binCombo p
                (op.binCombo (1 - op.u)
                  (affineOfBinary op (leftWeightedSeq op ws₁'))
                  (affineOfBinary op (rightWeightedSeq op ws₁')))
                (op.binCombo (1 - op.u)
                  (affineOfBinary op (leftWeightedSeq op ws₂'))
                  (affineOfBinary op (rightWeightedSeq op ws₂'))) := by
            rw [hdecomp₁, hdecomp₂]
          -- Step 2: Apply mediality to swap the order
          _ = op.binCombo (1 - op.u)
                (op.binCombo p
                  (affineOfBinary op (leftWeightedSeq op ws₁'))
                  (affineOfBinary op (leftWeightedSeq op ws₂')))
                (op.binCombo p
                  (affineOfBinary op (rightWeightedSeq op ws₁'))
                  (affineOfBinary op (rightWeightedSeq op ws₂'))) := by
            exact op.binCombo_mediality p (1 - op.u) _ _ _ _
          -- Step 3: Apply IH to the inner combinations
          _ = op.binCombo (1 - op.u)
                (affineOfBinary op (WeightedSeq.combineWeights p
                  (leftWeightedSeq op ws₁') (leftWeightedSeq op ws₂')))
                (affineOfBinary op (WeightedSeq.combineWeights p
                  (rightWeightedSeq op ws₁') (rightWeightedSeq op ws₂'))) := by
            rw [ih _ h_left_len _ _ hlen_left hpts_left rfl,
                ih _ h_right_len _ _ hlen_right hpts_right rfl]
          -- Step 4: Use combineWeights lemmas to simplify
          _ = op.binCombo (1 - op.u)
                (affineOfBinary op
                  (leftWeightedSeq op (WeightedSeq.combineWeights p ws₁' ws₂')))
                (affineOfBinary op
                  (rightWeightedSeq op (WeightedSeq.combineWeights p ws₁' ws₂'))) := by
            rw [leftWeightedSeq_combineWeights op p ws₁' ws₂' hlen' hpts',
                rightWeightedSeq_combineWeights op p ws₁' ws₂' hlen' hpts']
          -- Step 5: Collapse back using decomposition (in reverse)
          _ = affineOfBinary op (WeightedSeq.combineWeights p ws₁' ws₂') := by
            -- The combined sequence has the form needed for decomposition
            simp only [ws₁', ws₂', WeightedSeq.combineWeights, List.zipWith]
            rw [← affineOfBinary_decompose]
    -- Impossible cases (lengths don't match)
    | [], _ :: _ => simp_all
    | _ :: _, [] => simp_all
    | [_], [_, _] => simp_all
    | [_], _ :: _ :: _ :: _ => simp_all
    | [_, _], [_] => simp_all
    | [_, _], _ :: _ :: _ :: _ => simp_all
    | _ :: _ :: _ :: _, [_] => simp_all
    | _ :: _ :: _ :: _, [_, _] => simp_all

/-- Convert a StdSimplex to a WeightedSeq by enumerating the support. -/
noncomputable def StdSimplex.toWeightedSeq [PartialOrder R] [IsStrictOrderedRing R]
    (f : StdSimplex R M) : WeightedSeq R M :=
  f.weights.support.toList.map fun x => (f.weights x, x)

/-- Compute convex combination via the affine algorithm. -/
noncomputable def convexCombinationOfBinary [Inhabited M]
    [PartialOrder R] [IsStrictOrderedRing R]
    (op : BinaryConvexOp R M) (f : StdSimplex R M) : M :=
  affineOfBinary op f.toWeightedSeq

/-- The combination of a single-point simplex returns that point. -/
theorem convexCombinationOfBinary_single [Inhabited M]
    [PartialOrder R] [IsStrictOrderedRing R]
    (op : BinaryConvexOp R M) (x : M) :
    convexCombinationOfBinary op (.single x) = x := by
  simp only [convexCombinationOfBinary, StdSimplex.toWeightedSeq, StdSimplex.single,
    Finsupp.support_single_ne_zero _ one_ne_zero, Finset.toList_singleton, List.map_cons,
    List.map_nil, Finsupp.single_eq_same, affineOfBinary]

/-!
### The Binary Join Lemma

The core of the associativity proof: combining two A-results equals A of joined weights.
-/

/-- Special case: when both inner simplices are single points with x = y. -/
theorem affineOfBinary_binary_join_single_same [Inhabited M]
    [PartialOrder R] [IsStrictOrderedRing R]
    (op : BinaryConvexOp R M) (p : R) (x : M)
    (hp : 0 ≤ p) (hp' : 0 ≤ 1 - p) (hsum : p + (1 - p) = 1) :
    op.binCombo (1 - p) x x =
    affineOfBinary op
      (StdSimplex.duple (.single x) (.single x) hp hp' hsum).join.toWeightedSeq := by
  -- LHS = x by binCombo_same
  rw [op.binCombo_same]
  -- RHS: join of duple(single x, single x) = single x (weights add to 1)
  -- Then A(single x) = x
  -- Need to show: x = affineOfBinary op (join.toWeightedSeq)
  -- where join.weights = p • (single x 1) + (1-p) • (single x 1) = single x 1
  have hjoin_eq : (StdSimplex.duple (.single x) (.single x) hp hp' hsum).join =
      StdSimplex.single x := by
    ext m
    simp only [StdSimplex.duple, StdSimplex.join, StdSimplex.single_weights]
    classical
    rw [Finsupp.sum_add_index (by simp) (by simp [add_smul])]
    rw [Finsupp.sum_single_index (by simp : (0 : R) • (StdSimplex.single x).weights = 0),
        Finsupp.sum_single_index (by simp : (0 : R) • (StdSimplex.single x).weights = 0)]
    simp only [StdSimplex.single_weights, Finsupp.smul_single, smul_eq_mul, mul_one,
      ← Finsupp.single_add, hsum]
  rw [hjoin_eq]
  -- Now toWeightedSeq of single x is [(1, x)]
  simp only [StdSimplex.toWeightedSeq, StdSimplex.single_weights,
    Finsupp.support_single_ne_zero _ one_ne_zero, Finset.toList_singleton,
    List.map_cons, List.map_nil, Finsupp.single_eq_same, affineOfBinary]

/-- For length-2 weighted sequences, affineOfBinary produces binCombo on the weights. -/
theorem affineOfBinary_length_two [Inhabited M] (op : BinaryConvexOp R M)
    (w₁ w₂ : R) (x y : M) :
    affineOfBinary op [(w₁, x), (w₂, y)] = op.binCombo w₂ x y := by
  simp only [affineOfBinary]

/-- Key symmetry: binCombo(1-p, x, y) = binCombo(p, y, x) when p + (1-p) = 1.
    This is because both compute px + (1-p)y. -/
theorem binCombo_swap (op : BinaryConvexOp R M) (p : R) (x y : M) :
    op.binCombo (1 - p) x y = op.binCombo p y x := by
  -- binCombo(1-p, x, y) = (1-(1-p))x + (1-p)y = px + (1-p)y
  -- binCombo(p, y, x) = (1-p)y + px = px + (1-p)y
  -- These are equal because binCombo is defined as (1-t)·first + t·second
  -- So binCombo(1-p, x, y) = p·x + (1-p)·y
  -- And binCombo(p, y, x) = (1-p)·y + p·x
  -- These represent the same affine combination
  -- We need to derive this from the axioms (entropic, mediality, etc.)
  -- Actually, we can prove this using entropic:
  -- binCombo(p, y, x) = binCombo(p, binCombo(1, y, y), binCombo(0, x, x))
  -- Hmm, this approach is getting complicated. Let's use a different approach.
  -- Consider binCombo(1/2, x, y) = binCombo(1/2, y, x) by mediality with p=1/2, q=1/2
  -- Actually mediality gives us:
  -- binCombo(p, binCombo(q, a, b), binCombo(q, c, d))
  --   = binCombo(q, binCombo(p, a, c), binCombo(p, b, d))
  -- We can derive symmetry from this...
  --
  -- Actually, let's use that both expressions compute the same point in an affine sense.
  -- Using entropic: binCombo(t, binCombo(s, x, y), binCombo(r, x, y)) = binCombo((1-t)s + tr, x, y)
  -- Set s = 0, r = 1: binCombo(t, x, y) = binCombo(t, x, y) (tautology)
  -- Set s = 1, r = 0: binCombo(t, y, x) = binCombo((1-t)·1 + t·0, x, y) = binCombo(1-t, x, y)
  -- So binCombo(t, y, x) = binCombo(1-t, x, y)
  -- Therefore binCombo(p, y, x) = binCombo(1-p, x, y) ✓
  have h := op.binCombo_entropic p 1 0 x y
  simp only [mul_one, mul_zero, add_zero, op.binCombo_one, op.binCombo_zero] at h
  exact h.symm

/-- For a length-2 list, swapping the elements preserves affineOfBinary.
    This follows from binCombo_swap. -/
theorem affineOfBinary_swap_two [Inhabited M] (op : BinaryConvexOp R M)
    (w₁ w₂ : R) (x₁ x₂ : M) (hsum : w₁ + w₂ = 1) :
    affineOfBinary op [(w₁, x₁), (w₂, x₂)] = affineOfBinary op [(w₂, x₂), (w₁, x₁)] := by
  -- affineOfBinary [(w₁, x₁), (w₂, x₂)] = binCombo(w₂, x₁, x₂)
  -- affineOfBinary [(w₂, x₂), (w₁, x₁)] = binCombo(w₁, x₂, x₁)
  simp only [affineOfBinary]
  -- Goal: binCombo(w₂, x₁, x₂) = binCombo(w₁, x₂, x₁)
  -- binCombo_swap says: binCombo(1-p, x, y) = binCombo(p, y, x)
  -- With p = w₁: binCombo(1-w₁, x₁, x₂) = binCombo(w₁, x₂, x₁)
  -- Since w₂ = 1 - w₁ (from hsum), this gives: binCombo(w₂, x₁, x₂) = binCombo(w₁, x₂, x₁) ✓
  -- From hsum: w₁ + w₂ = 1, so w₂ = 1 - w₁
  have hw₂_eq : w₂ = 1 - w₁ := by
    have h := hsum
    calc w₂ = w₂ + 0 := by ring
         _ = w₂ + (w₁ - w₁) := by ring
         _ = (w₂ + w₁) - w₁ := by ring
         _ = 1 - w₁ := by rw [add_comm, h]
  rw [hw₂_eq]
  exact binCombo_swap op w₁ x₁ x₂

/-- For a duple of two distinct points, affineOfBinary returns binCombo.
    This handles the non-deterministic ordering of Finset.toList. -/
theorem affineOfBinary_duple [Inhabited M]
    [PartialOrder R] [IsStrictOrderedRing R]
    (op : BinaryConvexOp R M) (a b : M) (hab : a ≠ b)
    {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (hs' : s ≠ 0) (ht' : t ≠ 0) :
    affineOfBinary op (StdSimplex.duple a b hs ht hst).toWeightedSeq =
      op.binCombo t a b := by
  classical
  simp only [StdSimplex.toWeightedSeq, StdSimplex.duple]
  -- The support of single a s + single b t (with a ≠ b, s ≠ 0, t ≠ 0) is {a, b}
  have hsupp : (Finsupp.single a s + Finsupp.single b t).support =
      {a, b} := by
    ext x
    simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      by_contra h
      push_neg at h
      simp [h.1, h.2] at hx
    · rintro (rfl | rfl)
      · simp [hab, hs']
      · simp [Ne.symm hab, ht']
  rw [hsupp]
  -- {a,b}.toList has 2 elements; case split on ordering
  have hcard : ({a, b} : Finset M).card = 2 :=
    Finset.card_pair hab
  have hlen := Finset.length_toList ({a, b} : Finset M)
  have hnodup := Finset.nodup_toList ({a, b} : Finset M)
  -- toList has length 2
  have hlen2 : ({a, b} : Finset M).toList.length = 2 := by
    rw [hlen, hcard]
  match hl : ({a, b} : Finset M).toList, hlen2 with
  | [x, y], _ =>
    have hx : x ∈ ({a, b} : Finset M) := by
      rw [← Finset.mem_toList]; simp [hl]
    have hy : y ∈ ({a, b} : Finset M) := by
      rw [← Finset.mem_toList]; simp [hl]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have hxy : x ≠ y := by
      rw [hl] at hnodup
      exact fun heq => by subst heq; simp [List.nodup_cons] at hnodup
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · -- [a, b]
      simp [List.map, affineOfBinary, hab]
    · -- [b, a]: binCombo s x y = binCombo t y x by swap
      simp only [List.map, Finsupp.coe_add, Pi.add_apply,
        Finsupp.single_apply, Ne.symm hab, ite_false, ite_true,
        add_zero, affineOfBinary]
      -- s + t = 1 implies s = 1 - t
      rw [show s = 1 - t from by rw [← hst]; ring]
      exact binCombo_swap op t x y
    · exact absurd rfl hxy

/-- Special case: when both inner simplices are single points. -/
theorem affineOfBinary_binary_join_single [Inhabited M]
    [PartialOrder R] [IsStrictOrderedRing R]
    (op : BinaryConvexOp R M) (p : R) (x y : M)
    (hp : 0 ≤ p) (hp' : 0 ≤ 1 - p) (hsum : p + (1 - p) = 1) :
    op.binCombo (1 - p) x y =
    affineOfBinary op
      (StdSimplex.duple (.single x) (.single y) hp hp' hsum).join.toWeightedSeq := by
  -- Case split: x = y or x ≠ y
  by_cases hxy : x = y
  · subst hxy
    exact affineOfBinary_binary_join_single_same op p x hp hp' hsum
  · -- x ≠ y case
    -- The join has support {x, y} with weights p at x and (1-p) at y.
    -- First, get the join's weights using our helper lemma.
    have hjoin_weights := StdSimplex.join_duple_single_single x y hp hp' hsum
    -- The goal is to show binCombo(1-p, x, y) = affineOfBinary(join.toWeightedSeq)
    -- The join's support depends on whether p = 0, p = 1, or 0 < p < 1.
    -- Case: p = 0 means LHS = binCombo(1, x, y) = y, RHS = affineOfBinary[(1,y)] = y
    -- Case: p = 1 means LHS = binCombo(0, x, y) = x, RHS = affineOfBinary[(1,x)] = x
    -- Case: 0 < p < 1 means support = {x,y}, toWeightedSeq length 2
    -- For the general 2-element case, affineOfBinary_length_two + binCombo_swap work
    --
    -- The key insight: when x ≠ y and both p and (1-p) are positive, the support has 2 elements.
    -- When one is zero, the support has 1 element.
    --
    -- We can simplify by computing toWeightedSeq directly.
    simp only [StdSimplex.toWeightedSeq]
    -- Goal: binCombo(1-p, x, y) = affineOfBinary(join.weights.support.toList.map ...)
    --
    -- Use the fact that join.weights = single x p + single y (1-p)
    rw [hjoin_weights]
    -- Now we need to handle the support of (single x p + single y (1-p))
    -- when x ≠ y, this is {x, y} if both p and (1-p) are nonzero, otherwise smaller
    classical
    by_cases hp0 : p = 0
    · -- p = 0: LHS = binCombo(1, x, y) = y
      subst hp0
      simp only [Finsupp.single_zero, zero_add, Finsupp.support_single_ne_zero _ one_ne_zero,
        Finset.toList_singleton, List.map_cons, List.map_nil, Finsupp.single_eq_same,
        affineOfBinary, op.binCombo_one, sub_zero]
    · by_cases hp1 : p = 1
      · -- p = 1: LHS = binCombo(0, x, y) = x
        subst hp1
        simp only [sub_self, Finsupp.single_zero, add_zero,
          Finsupp.support_single_ne_zero _ one_ne_zero, Finset.toList_singleton, List.map_cons,
          List.map_nil, Finsupp.single_eq_same, affineOfBinary, op.binCombo_zero]
      · -- 0 < p < 1: support has 2 elements {x, y}
        have hp1' : (1 : R) - p ≠ 0 := by
          intro h; exact hp1 (sub_eq_zero.mp h).symm
        have hsupp : (Finsupp.single x p + Finsupp.single y (1 - p)).support =
            {x, y} := by
          ext m
          simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply,
            Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hm; by_contra h; push_neg at h
            simp [h.1, h.2] at hm
          · rintro (rfl | rfl)
            · simp [hxy, hp0]
            · simp [Ne.symm hxy, hp1']
        rw [hsupp]
        have hcard : ({x, y} : Finset M).card = 2 := Finset.card_pair hxy
        have hnodup := Finset.nodup_toList ({x, y} : Finset M)
        have hlen2 : ({x, y} : Finset M).toList.length = 2 := by
          rw [Finset.length_toList, hcard]
        match hl : ({x, y} : Finset M).toList, hlen2 with
        | [a, b], _ =>
          have ha : a ∈ ({x, y} : Finset M) := by
            rw [← Finset.mem_toList]; simp [hl]
          have hb : b ∈ ({x, y} : Finset M) := by
            rw [← Finset.mem_toList]; simp [hl]
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
          have hab : a ≠ b := by
            rw [hl] at hnodup
            exact fun heq => by subst heq; simp [List.nodup_cons] at hnodup
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact absurd rfl hab
          · -- [x, y]
            simp [List.map, affineOfBinary, hxy]
          · -- [y, x]
            simp only [List.map, Finsupp.coe_add, Pi.add_apply,
              Finsupp.single_apply, Ne.symm hxy, ite_false, ite_true,
              add_zero, affineOfBinary]
            exact binCombo_swap op p b a
          · exact absurd rfl hab

/-- The binary outer case: C(1-p, A(d₁), A(d₂)) = A(join of duple(d₁, d₂, p, 1-p)).

    When d₁, d₂ have the same support, this follows from entropic identity.
    For different supports, we extend to a common support using zero-weight invariance. -/
theorem affineOfBinary_binary_join [Inhabited M]
    [PartialOrder R] [IsStrictOrderedRing R]
    (op : BinaryConvexOp R M) (p : R) (d₁ d₂ : StdSimplex R M)
    (hp : 0 ≤ p) (hp' : 0 ≤ 1 - p) (hsum : p + (1 - p) = 1) :
    op.binCombo (1 - p)
      (affineOfBinary op d₁.toWeightedSeq)
      (affineOfBinary op d₂.toWeightedSeq) =
    affineOfBinary op (StdSimplex.duple d₁ d₂ hp hp' hsum).join.toWeightedSeq := by
  -- The proof strategy:
  -- LHS: binCombo(1-p, A(d₁), A(d₂)) where A = affineOfBinary
  -- RHS: A((duple d₁ d₂).join)
  --
  -- Key insight: Both compute the same weighted combination:
  --   (1-p) · (weighted combo of d₁'s points) + p · (weighted combo of d₂'s points)
  -- = weighted combo of (duple d₁ d₂).join's points
  --
  -- The join of (duple d₁ d₂) has weights:
  --   join.weights(m) = p · d₁.weights(m) + (1-p) · d₂.weights(m)
  --
  -- So the RHS computes ∑_m join.weights(m) · m
  --
  -- The LHS computes binCombo(1-p, ∑_m d₁.weights(m)·m, ∑_n d₂.weights(n)·n)
  --   = (1-p) · ∑_m d₁.weights(m)·m + p · ∑_n d₂.weights(n)·n
  --   [if binCombo distributes over sums, which it does via linearity]
  --   = ∑_m (1-p)·d₁.weights(m)·m + ∑_n p·d₂.weights(n)·n
  --   = ∑_m ((1-p)·d₁.weights(m) + p·d₂.weights(m)) · m
  --   [combining over common support]
  --   = ∑_m join.weights(m) · m = RHS
  --
  -- The formal proof requires:
  -- 1. Extend d₁, d₂ to common support S = d₁.support ∪ d₂.support
  -- 2. Apply affineOfBinary_linear to the extended sequences
  -- 3. Show the combined weights equal (duple d₁ d₂).join.weights
  -- 4. Use affineOfBinary_eq_of_same_finsupp for ordering
  --
  -- Since the supporting lemmas have sorries, we defer.
  sorry

/-- Any simplex with support cardinality ≥ 2 can be expressed as the join of a duple
    of two simplices, each with strictly smaller support cardinality. -/
theorem StdSimplex.exists_duple_join [PartialOrder R] [IsStrictOrderedRing R]
    {X : Type*} {s t : R} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1)
    (f : StdSimplex R X) (hcard : 2 ≤ f.weights.support.card) :
    ∃ (g₁ g₂ : StdSimplex R X)
      (h₁ : g₁.weights.support.card < f.weights.support.card)
      (h₂ : g₂.weights.support.card < f.weights.support.card),
      f = (StdSimplex.duple g₁ g₂ (le_of_lt hs) (le_of_lt ht) hst).join := by
  sorry

/-- The flattening lemma: affine combination of affine combinations equals
    affine combination of joined weights.

    The proof uses strong induction on outer support cardinality:
    - Card 0: impossible (weights sum to 1)
    - Card 1: direct (single simplex)
    - Card 2: uses affineOfBinary_binary_join
    - Card ≥ 3: monadic decomposition via exists_duple_join, reducing to IH -/
theorem affineOfBinary_assoc_flattening [Inhabited M]
    [PartialOrder R] [IsStrictOrderedRing R]
    (op : BinaryConvexOp R M) (hu : 0 < op.u) (h1u : 0 < 1 - op.u)
    (f : StdSimplex R (StdSimplex R M)) :
    affineOfBinary op (f.map (convexCombinationOfBinary op)).toWeightedSeq =
    affineOfBinary op f.join.toWeightedSeq := by
  -- Strong induction on outer support cardinality.
  suffices ∀ n (f : StdSimplex R (StdSimplex R M)), f.weights.support.card = n →
      affineOfBinary op (f.map (convexCombinationOfBinary op)).toWeightedSeq =
      affineOfBinary op f.join.toWeightedSeq from this _ f rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro f hcard
  match n, hcard with
  | 0, hcard =>
    exfalso
    have h : f.weights.sum (fun _ r => r) = 0 := by
      rw [Finsupp.sum]
      apply Finset.sum_eq_zero
      intro x hx
      exact absurd hx (Finset.card_eq_zero.mp hcard ▸ Finset.notMem_empty x)
    rw [f.total] at h
    exact one_ne_zero h
  | 1, hcard =>
    obtain ⟨d, hd⟩ := StdSimplex.eq_single_of_card_eq_one f hcard
    subst hd
    simp only [StdSimplex.map_single, StdSimplex.join_single]
    simp only [StdSimplex.toWeightedSeq, StdSimplex.single_weights,
      Finsupp.support_single_ne_zero _ one_ne_zero, Finset.toList_singleton,
      List.map_cons, List.map_nil, Finsupp.single_eq_same, affineOfBinary,
      convexCombinationOfBinary]
  | 2, hcard =>
    -- Card = 2: Use affineOfBinary_binary_join
    classical
    obtain ⟨d₁, d₂, hne, hsupp⟩ := Finset.card_eq_two.mp hcard
    let w₁ := f.weights d₁
    let w₂ := f.weights d₂
    have hw₁_pos : 0 ≤ w₁ := f.nonneg d₁
    have hw₂_pos : 0 ≤ w₂ := f.nonneg d₂
    have hnotin : d₁ ∉ ({d₂} : Finset _) := Finset.notMem_singleton.mpr hne
    have hsum : w₁ + w₂ = 1 := by
      have htot := f.total
      rw [Finsupp.sum, hsupp, Finset.sum_insert hnotin, Finset.sum_singleton] at htot
      exact htot
    have hw₂_eq : w₂ = 1 - w₁ := by rw [← hsum]; ring
    have hf_eq : f = StdSimplex.duple d₁ d₂ hw₁_pos hw₂_pos hsum := by
      apply StdSimplex.ext
      ext d
      simp only [StdSimplex.duple]
      by_cases hd₁ : d = d₁
      · subst hd₁
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne hne, add_zero]
        rfl
      · by_cases hd₂ : d = d₂
        · subst hd₂
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne (Ne.symm hne),
            Finsupp.single_eq_same, zero_add]
          rfl
        · have hd_notin : d ∉ f.weights.support := by
            rw [hsupp]
            simp only [Finset.mem_insert, Finset.mem_singleton]
            push_neg
            exact ⟨hd₁, hd₂⟩
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne hd₁,
            Finsupp.single_eq_of_ne hd₂, add_zero]
          exact Finsupp.notMem_support_iff.mp hd_notin
    rw [hf_eq]
    have hw₂_pos' : 0 ≤ 1 - w₁ := hw₂_eq ▸ hw₂_pos
    have hsum' : w₁ + (1 - w₁) = 1 := by ring
    have hbinary := affineOfBinary_binary_join op w₁ d₁ d₂ hw₁_pos hw₂_pos' hsum'
    have hduple_eq : StdSimplex.duple d₁ d₂ hw₁_pos hw₂_pos hsum =
        StdSimplex.duple d₁ d₂ hw₁_pos hw₂_pos' hsum' := by
      apply StdSimplex.ext; ext d
      simp only [StdSimplex.duple, Finsupp.coe_add, Pi.add_apply]
      congr 1; rw [hw₂_eq]
    rw [hduple_eq, ← hbinary]
    change affineOfBinary op ((StdSimplex.duple d₁ d₂ hw₁_pos hw₂_pos' hsum').map
      (convexCombinationOfBinary op)).toWeightedSeq = _
    by_cases hAeq : affineOfBinary op d₁.toWeightedSeq = affineOfBinary op d₂.toWeightedSeq
    · rw [hAeq, op.binCombo_same]
      have hAeq' : convexCombinationOfBinary op d₁ = convexCombinationOfBinary op d₂ := by
        simp only [convexCombinationOfBinary]; exact hAeq
      have hmap_eq : (StdSimplex.duple d₁ d₂ hw₁_pos hw₂_pos' hsum').map
          (convexCombinationOfBinary op) =
          StdSimplex.single (convexCombinationOfBinary op d₁) := by
        apply StdSimplex.ext; ext m
        simp only [StdSimplex.map, StdSimplex.duple, StdSimplex.single_weights]
        rw [Finsupp.mapDomain_add]; simp only [Finsupp.mapDomain_single]
        rw [hAeq', ← Finsupp.single_add, hsum']
      rw [hmap_eq]
      simp only [StdSimplex.toWeightedSeq, StdSimplex.single_weights,
        Finsupp.support_single_ne_zero _ one_ne_zero, Finset.toList_singleton,
        List.map_cons, List.map_nil, Finsupp.single_eq_same, affineOfBinary,
        convexCombinationOfBinary]
      exact hAeq
    · have hAne : convexCombinationOfBinary op d₁ ≠ convexCombinationOfBinary op d₂ := by
        simp only [convexCombinationOfBinary]; exact hAeq
      have hmap_weights : (StdSimplex.duple d₁ d₂ hw₁_pos hw₂_pos' hsum').map
          (convexCombinationOfBinary op) =
          StdSimplex.duple (convexCombinationOfBinary op d₁) (convexCombinationOfBinary op d₂)
            hw₁_pos hw₂_pos' hsum' := by
        apply StdSimplex.ext; ext m
        simp only [StdSimplex.map, StdSimplex.duple]
        rw [Finsupp.mapDomain_add]; simp only [Finsupp.mapDomain_single]
      rw [hmap_weights]
      -- Both weights are nonzero since d₁, d₂ are in the support
      have hw₁_ne : w₁ ≠ 0 := by
        intro h
        have : d₁ ∉ f.weights.support := Finsupp.notMem_support_iff.mpr h
        rw [hsupp] at this
        simp at this
      have hw₂_ne : (1 : R) - w₁ ≠ 0 := by
        intro h
        have : w₂ = 0 := by rw [hw₂_eq]; exact h
        have : d₂ ∉ f.weights.support := Finsupp.notMem_support_iff.mpr this
        rw [hsupp] at this
        simp at this
      exact affineOfBinary_duple op _ _ hAne hw₁_pos hw₂_pos' hsum' hw₁_ne hw₂_ne
  | n + 3, hcard =>
    -- Card ≥ 3: Monadic decomposition.
    -- Split f = (duple g₁ g₂).join where g₁, g₂ have smaller outer support card.
    have hst : op.u + (1 - op.u) = 1 := by ring
    have hs := le_of_lt hu
    have ht := le_of_lt h1u
    obtain ⟨g₁, g₂, hg₁, hg₂, hf⟩ :=
      StdSimplex.exists_duple_join hu h1u hst f (by omega)
    -- IH for g₁ and g₂ (they have strictly smaller card)
    have ih₁ := ih g₁.weights.support.card (by omega) g₁ rfl
    have ih₂ := ih g₂.weights.support.card (by omega) g₂ rfl
    -- Rewrite using the splitting: f = (duple g₁ g₂).join
    rw [hf]
    -- LHS: rewrite using join_map + map_duple
    conv_lhs =>
      rw [StdSimplex.join_map (convexCombinationOfBinary op)
            (StdSimplex.duple g₁ g₂ hs ht hst)]
      rw [StdSimplex.map_duple
            (fun d => d.map (convexCombinationOfBinary op)) g₁ g₂ hs ht hst]
    -- RHS: rewrite using join_join + map_duple
    conv_rhs =>
      rw [StdSimplex.join_join (StdSimplex.duple g₁ g₂ hs ht hst)]
      rw [StdSimplex.map_duple StdSimplex.join g₁ g₂ hs ht hst]
    -- Goal: A(D₁.join.toWS) = A(D₂.join.toWS) where
    -- D₁ = duple (g₁.map F) (g₂.map F), D₂ = duple g₁.join g₂.join
    -- F = convexCombinationOfBinary op
    -- Both D₁, D₂ have card ≤ 2 < n + 3.
    -- Card bounds for D₁, D₂ (duple of two elements has support ≤ 2)
    have hD₁_card :
        (StdSimplex.duple (g₁.map (convexCombinationOfBinary op))
          (g₂.map (convexCombinationOfBinary op)) hs ht hst
        ).weights.support.card ≤ 2 :=
      StdSimplex.duple_support_card_le_two _ _ hs ht hst
    have hD₂_card :
        (StdSimplex.duple g₁.join g₂.join hs ht hst
        ).weights.support.card ≤ 2 :=
      StdSimplex.duple_support_card_le_two _ _ hs ht hst
    -- Apply IH to D₁ and D₂
    have ihD₁ := ih _ (by omega)
      (StdSimplex.duple (g₁.map (convexCombinationOfBinary op))
        (g₂.map (convexCombinationOfBinary op)) hs ht hst) rfl
    have ihD₂ := ih _ (by omega)
      (StdSimplex.duple g₁.join g₂.join hs ht hst) rfl
    -- Chain: A(D₁.join) ← ihD₁ → A(D₁.map F) = A(D₂.map F) ← ihD₂ → A(D₂.join)
    rw [← ihD₁, ← ihD₂]
    -- Goal: A(D₁.map F .toWS) = A(D₂.map F .toWS)
    -- D₁.map F = D₂.map F because F(g₁.map F) = F(g₁.join) by ih₁
    congr 1; congr 1
    rw [StdSimplex.map_duple (convexCombinationOfBinary op)
          (g₁.map (convexCombinationOfBinary op))
          (g₂.map (convexCombinationOfBinary op)) hs ht hst,
        StdSimplex.map_duple (convexCombinationOfBinary op)
          g₁.join g₂.join hs ht hst,
        show convexCombinationOfBinary op
              (g₁.map (convexCombinationOfBinary op)) =
            convexCombinationOfBinary op g₁.join from ih₁,
        show convexCombinationOfBinary op
              (g₂.map (convexCombinationOfBinary op)) =
            convexCombinationOfBinary op g₂.join from ih₂]

/-- Build a ConvexSpace from a binary convex operation.

    The algorithm from convex_plan.md only uses ⅟u and ⅟(1-u) for division,
    so this works over any ring with an invertible splitting unit.
    Requires `0 < u` and `0 < 1 - u` for the associativity proof. -/
noncomputable def ConvexSpace.ofBinary [Inhabited M]
    [PartialOrder R] [IsStrictOrderedRing R]
    (op : BinaryConvexOp R M) (hu : 0 < op.u) (h1u : 0 < 1 - op.u) :
    ConvexSpace R M where
  convexCombination := convexCombinationOfBinary op
  single := convexCombinationOfBinary_single op
  assoc f := by
    simp only [convexCombinationOfBinary]
    exact affineOfBinary_assoc_flattening op hu h1u f

end OfBinary
