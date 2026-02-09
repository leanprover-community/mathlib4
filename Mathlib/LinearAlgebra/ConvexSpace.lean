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
public import Mathlib.Tactic.FieldSimp
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
  /-- Absorption: combining x with a combination starting from x absorbs the outer layer.
      `C(p, x, C(q, x, z)) = C(pq, x, z)`. -/
  binCombo_absorb_left : ∀ p q : R, ∀ x z : M,
    binCombo p x (binCombo q x z) = binCombo (p * q) x z
  /-- Parametric associativity: nested combinations can be reassociated.
      When `p(1-q) = (1-pq)r`, we have `C(p, x, C(q, y, z)) = C(pq, C(r, x, y), z)`.
      Over a field, the condition is satisfiable for all p, q (with r = p(1-q)/(1-pq)). -/
  binCombo_assoc : ∀ p q r : R, ∀ x y z : M,
    p * (1 - q) = (1 - p * q) * r →
    binCombo p x (binCombo q y z) = binCombo (p * q) (binCombo r x y) z

attribute [instance] BinaryConvexOp.u_inv BinaryConvexOp.one_sub_u_inv

namespace BinaryConvexOp

variable (op : BinaryConvexOp R M)

/-- Convenient access to the inverse of the splitting unit. -/
noncomputable def invU : R := ⅟op.u

/-- Convenient access to the inverse of (1 - u). -/
noncomputable def invOneSubU : R := ⅟(1 - op.u)

/-- Exchange property: `C(p, y, x) = C(1-p, x, y)`.
    Derived from entropic with s=1, r=0. -/
theorem binCombo_exchange (p : R) (x y : M) :
    op.binCombo p y x = op.binCombo (1 - p) x y := by
  have h := op.binCombo_entropic p 1 0 x y
  rw [op.binCombo_one, op.binCombo_zero] at h
  rw [h]; ring_nf

/-- Mediality variant: `C(p, C(q, a, b), c) = C(q, C(p, a, c), C(p, b, c))`.
    Set d := c in mediality. -/
theorem binCombo_mediality_left (p q : R) (a b c : M) :
    op.binCombo p (op.binCombo q a b) c =
      op.binCombo q (op.binCombo p a c) (op.binCombo p b c) := by
  conv_lhs => rw [← op.binCombo_same q c]
  exact op.binCombo_mediality p q a b c c

/-- Mediality variant: `C(p, a, C(q, c, d)) = C(q, C(p, a, c), C(p, a, d))`.
    Set b := a in mediality. -/
theorem binCombo_mediality_right (p q : R) (a c d : M) :
    op.binCombo p a (op.binCombo q c d) =
      op.binCombo q (op.binCombo p a c) (op.binCombo p a d) := by
  conv_lhs => rw [← op.binCombo_same q a]
  exact op.binCombo_mediality p q a a c d

/-- Mediality variant: `C(p, C(q, a, b), C(q, a, d)) = C(q, a, C(p, b, d))`.
    Set c := a in mediality. -/
theorem binCombo_mediality_common_left (p q : R) (a b d : M) :
    op.binCombo p (op.binCombo q a b) (op.binCombo q a d) =
      op.binCombo q a (op.binCombo p b d) := by
  rw [op.binCombo_mediality p q a b a d, op.binCombo_same p a]

/-- Mediality variant: `C(p, C(q, a, b), C(q, c, b)) = C(q, C(p, a, c), b)`.
    Set d := b in mediality. -/
theorem binCombo_mediality_common_right (p q : R) (a b c : M) :
    op.binCombo p (op.binCombo q a b) (op.binCombo q c b) =
      op.binCombo q (op.binCombo p a c) b := by
  rw [op.binCombo_mediality p q a b c b, op.binCombo_same p b]

/-- Combining with a point on the right: `C(1-u, C(c, x, y), y) = C(u*c + (1-u), x, y)`.
    From entropic with s=c, r=1. -/
theorem binCombo_collapse_right (c : R) (x y : M) :
    op.binCombo (1 - op.u) (op.binCombo c x y) y =
      op.binCombo (op.u * c + (1 - op.u)) x y := by
  have h := op.binCombo_entropic (1 - op.u) c 1 x y
  rw [op.binCombo_one x y] at h
  rw [h]; congr 1; ring

/-- Combining with a point on the left: `C(1-u, x, C(c, x, y)) = C((1-u)*c, x, y)`.
    From entropic with s=0, r=c. -/
theorem binCombo_collapse_left (c : R) (x y : M) :
    op.binCombo (1 - op.u) x (op.binCombo c x y) =
      op.binCombo ((1 - op.u) * c) x y := by
  have h := op.binCombo_entropic (1 - op.u) 0 c x y
  rw [op.binCombo_zero x y] at h
  rw [h]; congr 1; ring

/-- Right absorption: `C(p, C(q, x, z), z) = C(1-(1-p)(1-q), x, z)`.
    Derived from absorb_left via exchange. -/
theorem binCombo_absorb_right (p q : R) (x z : M) :
    op.binCombo p (op.binCombo q x z) z =
      op.binCombo (1 - (1 - p) * (1 - q)) x z := by
  -- C(p, C(q, x, z), z) = C(1-p, z, C(q, x, z))  by exchange
  rw [op.binCombo_exchange p z (op.binCombo q x z)]
  -- C(1-p, z, C(q, x, z)) = C(1-p, z, C(1-q, z, x))  by exchange on inner
  rw [op.binCombo_exchange q z x]
  -- C(1-p, z, C(1-q, z, x)) = C((1-p)(1-q), z, x)  by absorb_left
  rw [op.binCombo_absorb_left (1 - p) (1 - q) z x]
  -- C((1-p)(1-q), z, x) = C(1-(1-p)(1-q), x, z)  by exchange
  exact op.binCombo_exchange ((1 - p) * (1 - q)) x z

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

-- Helper lemmas for list operations
section ListHelpers

variable {α β γ : Type*}

private theorem dropLast_zipWith (f : α → β → γ) (L₁ : List α) (L₂ : List β)
    (hlen : L₁.length = L₂.length) :
    (List.zipWith f L₁ L₂).dropLast = List.zipWith f L₁.dropLast L₂.dropLast := by
  induction L₁ generalizing L₂ with
  | nil => cases L₂ <;> simp_all
  | cons a₁ t₁ ih =>
    cases L₂ with
    | nil => simp at hlen
    | cons b₁ s₁ =>
      simp only [List.zipWith_cons_cons, List.length_cons] at hlen ⊢
      cases t₁ with
      | nil =>
        cases s₁ with
        | nil => simp [List.dropLast]
        | cons _ _ => simp at hlen
      | cons a₂ t₂ =>
        cases s₁ with
        | nil => simp at hlen
        | cons b₂ s₂ =>
          simp only [List.dropLast, List.zipWith_cons_cons]
          congr 1; exact ih (b₂ :: s₂) (by omega)

private theorem dropLast_map (f : α → β) (L : List α) :
    (L.map f).dropLast = L.dropLast.map f := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => simp [List.dropLast]
    | cons _ _ => simp [List.dropLast, ih]

private theorem getLast?_zipWith (f : α → β → γ)
    (a₁ : α) (t₁ : List α) (a₂ : β) (t₂ : List β)
    (hlen : (a₁ :: t₁).length = (a₂ :: t₂).length) :
    (List.zipWith f (a₁ :: t₁) (a₂ :: t₂)).getLast? =
    some (f ((a₁ :: t₁).getLast (by simp)) ((a₂ :: t₂).getLast (by simp))) := by
  induction t₁ generalizing a₁ a₂ t₂ with
  | nil =>
    cases t₂ with
    | nil => simp [List.zipWith, List.getLast?]
    | cons _ _ => simp at hlen
  | cons b₁ u₁ ih =>
    cases t₂ with
    | nil => simp at hlen
    | cons b₂ u₂ =>
      simp only [List.zipWith_cons_cons, List.getLast?_cons_cons,
        List.getLast_cons (List.cons_ne_nil b₁ u₁),
        List.getLast_cons (List.cons_ne_nil b₂ u₂)]
      exact ih b₁ b₂ u₂ (by simp only [List.length_cons] at hlen ⊢; omega)

end ListHelpers

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
      -- Key: sum of dropLast of zipWith linear combo = linear combo of sums of dropLasts
      suffices hsuf : ∀ (L₁ L₂ : List R), L₁.length = L₂.length →
          (List.zipWith (fun a b => (1-p)*a+p*b) L₁ L₂).dropLast.sum =
          (1-p) * L₁.dropLast.sum + p * L₂.dropLast.sum by
        -- Rewrite the zipWith of pairs to zipWith of scalars
        have hlen_mid : (s₃ :: List.map Prod.fst rest₁).length =
            (r₃ :: List.map Prod.fst rest₂).length := by
          simp [hrest_len]
        -- Show the list of combined weights matches zipWith on weight lists
        -- map fst ∘ zipWith on pairs = zipWith on fsts
        have map_fst_zipWith : ∀ (l₁ l₂ : List (R × M)),
            List.map Prod.fst (List.zipWith
              (fun x x_1 => ((1 - p) * x.1 + p * x_1.1, x.2)) l₁ l₂) =
            List.zipWith (fun a b => (1 - p) * a + p * b)
              (List.map Prod.fst l₁) (List.map Prod.fst l₂) := by
          intro l₁ l₂; induction l₁ generalizing l₂ with
          | nil => simp
          | cons h t ih =>
            cases l₂ with
            | nil => simp
            | cons h₂ t₂ =>
              simp only [List.zipWith_cons_cons, List.map_cons]; congr 1
              exact ih t₂
        have hzw : (((1 - p) * s₃ + p * r₃) :: List.map Prod.fst
              (List.zipWith (fun x x_1 => ((1 - p) * x.1 + p * x_1.1, x.2))
                rest₁ rest₂)) =
            List.zipWith (fun a b => (1 - p) * a + p * b)
              (s₃ :: List.map Prod.fst rest₁)
              (r₃ :: List.map Prod.fst rest₂) := by
          simp only [List.zipWith_cons_cons, map_fst_zipWith]
        -- Factor out ⅟u and use hsuf
        rw [hzw]
        -- The goal is now about (map (⅟u*·) (zipWith combine L₁ L₂).dropLast).sum
        -- vs (1-p)*(...) + p*(...)
        -- Factor: (map (c*·) L).sum = c * L.sum
        have hfactor : ∀ (c : R) (L : List R),
            (List.map (c * ·) L).sum = c * L.sum := by
          intro c L; induction L with
          | nil => simp
          | cons a t ih => simp [List.sum_cons, ih, mul_add]
        simp only [hfactor]
        rw [hsuf _ _ hlen_mid]
        ring
      -- Prove the key lemma by strong induction on total length
      intro L₁
      induction L₁ with
      | nil =>
        intro L₂ hlen_eq
        cases L₂ with
        | nil => simp
        | cons _ _ => simp at hlen_eq
      | cons a₁ t₁ iht =>
        intro L₂ hlen_eq
        match L₂ with
        | [] => simp at hlen_eq
        | [a₂] =>
          -- t₁ = [] since lengths match
          cases t₁ with
          | nil => simp [List.dropLast]
          | cons _ _ => simp at hlen_eq
        | a₂ :: b₂ :: u₂ =>
          -- t₁ must be b₁ :: u₁ with same length
          cases t₁ with
          | nil => simp at hlen_eq
          | cons b₁ u₁ =>
            simp only [List.length_cons] at hlen_eq
            -- (a₁ :: b₁ :: u₁).dropLast = a₁ :: (b₁ :: u₁).dropLast  [by def]
            -- (a₂ :: b₂ :: u₂).dropLast = a₂ :: (b₂ :: u₂).dropLast  [by def]
            -- zipWith ... (a₁ :: b₁ :: u₁) (a₂ :: b₂ :: u₂)
            --   = ((1-p)*a₁+p*a₂) :: zipWith ... (b₁::u₁) (b₂::u₂)
            -- dropLast of this = ((1-p)*a₁+p*a₂) :: (zipWith ... (b₁::u₁) (b₂::u₂)).dropLast
            -- sum = ((1-p)*a₁+p*a₂) + (zipWith ...).dropLast.sum
            -- By IH: (zipWith ...).dropLast.sum = (1-p)*(b₁::u₁).dropLast.sum + p*(b₂::u₂).dropLast.sum
            -- Expand zipWith 2 steps to expose 2+ elements for dropLast
            have hzw : List.zipWith (fun a b => (1-p)*a+p*b)
                (a₁::b₁::u₁) (a₂::b₂::u₂) =
                ((1-p)*a₁+p*a₂) :: ((1-p)*b₁+p*b₂) ::
                  List.zipWith (fun a b => (1-p)*a+p*b) u₁ u₂ := by
              simp [List.zipWith_cons_cons]
            rw [hzw]; simp only [List.dropLast, List.sum_cons]
            -- IH: apply to b₁::u₁ and b₂::u₂
            have hlen_t : (b₁ :: u₁).length = (b₂ :: u₂).length := by
              simp only [List.length_cons]; omega
            have h_ih := iht (b₂ :: u₂) hlen_t
            -- h_ih's LHS is (zipWith ... (b₁::u₁) (b₂::u₂)).dropLast.sum
            -- Goal has (((1-p)*b₁+p*b₂) :: zipWith ... u₁ u₂).dropLast.sum
            -- Unfold zipWith_cons_cons in h_ih to match
            rw [List.zipWith_cons_cons] at h_ih
            rw [h_ih]; ring
    · -- Tail: uses helper lemmas about dropLast/zipWith/map/zip
      -- Helper: map snd of zipWith combine preserves first arg's snd
      have map_snd_zipWith : ∀ (l₁ l₂ : List (R × M)),
          l₁.map Prod.snd = l₂.map Prod.snd →
          (List.zipWith (fun x x_1 => ((1 - p) * x.1 + p * x_1.1, x.2)) l₁ l₂).map Prod.snd =
          l₁.map Prod.snd := by
        intro l₁; induction l₁ with
        | nil => simp
        | cons a t ih =>
          intro l₂ h; cases l₂ with
          | nil => simp at h
          | cons b u =>
            simp only [List.zipWith_cons_cons, List.map_cons, List.cons.injEq] at h ⊢
            exact ⟨trivial, ih u h.2⟩
      -- Helper: zipWith combine on scaled-zipped lists = scale-zip of zipWith on weights
      have combine_scaled_zip : ∀ (W₁ W₂ : List R) (P : List M),
          W₁.length = W₂.length → W₁.length = P.length →
          List.zipWith (fun x x_1 => ((1 - p) * x.1 + p * x_1.1, x.2))
            ((W₁.map (⅟op.u * ·)).zip P) ((W₂.map (⅟op.u * ·)).zip P) =
          ((List.zipWith (fun a b => (1 - p) * a + p * b) W₁ W₂).map
            (⅟op.u * ·)).zip P := by
        intro W₁; induction W₁ with
        | nil =>
          intro W₂ P hlen₁ _
          cases W₂ with
          | nil => simp
          | cons _ _ => simp at hlen₁
        | cons w₁ t₁ ih =>
          intro W₂ P hlen₁ hlen₂
          cases W₂ with
          | nil => simp at hlen₁
          | cons w₂ t₂ =>
            cases P with
            | nil => simp at hlen₂
            | cons q qs =>
              simp only [List.map_cons, List.zip_cons_cons, List.zipWith_cons_cons,
                List.length_cons] at hlen₁ hlen₂ ⊢
              congr 1
              · simp only [Prod.mk.injEq]; constructor
                · ring
                · trivial
              · exact ih t₂ qs (by omega) (by omega)
      -- Helper: map fst of zipWith combine = zipWith on fsts
      have map_fst_zipWith : ∀ (l₁ l₂ : List (R × M)),
          (List.zipWith (fun x x_1 => ((1 - p) * x.1 + p * x_1.1, x.2))
            l₁ l₂).map Prod.fst =
          List.zipWith (fun a b => (1 - p) * a + p * b)
            (l₁.map Prod.fst) (l₂.map Prod.fst) := by
        intro l₁; induction l₁ with
        | nil => simp
        | cons a t ih =>
          intro l₂; cases l₂ with
          | nil => simp
          | cons b u =>
            simp only [List.zipWith_cons_cons, List.map_cons]; congr 1
            exact ih u
      -- Rewrite RHS points: map snd of zipWith = map snd of first arg
      have map_snd_eq : (x₃ :: (List.zipWith
          (fun x x_1 => ((1 - p) * x.1 + p * x_1.1, x.2)) rest₁ rest₂).map
          Prod.snd) = (x₃ :: rest₁.map Prod.snd) := by
        congr 1; exact map_snd_zipWith rest₁ rest₂ hrest
      rw [map_snd_eq]
      -- Rewrite RHS weights: cons of combined weights = zipWith on cons'd weights
      have hzw_weights : ((1 - p) * s₃ + p * r₃) ::
          (List.zipWith (fun x x_1 => ((1 - p) * x.1 + p * x_1.1, x.2))
            rest₁ rest₂).map Prod.fst =
          List.zipWith (fun a b => (1 - p) * a + p * b)
            (s₃ :: rest₁.map Prod.fst) (r₃ :: rest₂.map Prod.fst) := by
        simp only [List.zipWith_cons_cons, map_fst_zipWith]
      rw [hzw_weights]
      -- Unify the points on the LHS: rest₂ points = rest₁ points (from hrest)
      have hpts_dl : (x₃ :: rest₂.map Prod.snd).dropLast =
          (x₃ :: rest₁.map Prod.snd).dropLast := by
        simp [hrest]
      rw [hpts_dl]
      -- Apply dropLast_zipWith on RHS weights
      have hlen_W : (s₃ :: rest₁.map Prod.fst).length =
          (r₃ :: rest₂.map Prod.fst).length := by
        simp [hrest_len]
      rw [dropLast_zipWith _ _ _ hlen_W]
      -- Now both sides use W.dropLast and P.dropLast — apply combine_scaled_zip
      have hlen_dl_W : (s₃ :: rest₁.map Prod.fst).dropLast.length =
          (r₃ :: rest₂.map Prod.fst).dropLast.length := by
        simp [List.length_dropLast, hrest_len]
      have hlen_dl_WP : (s₃ :: rest₁.map Prod.fst).dropLast.length =
          (x₃ :: rest₁.map Prod.snd).dropLast.length := by
        simp [List.length_dropLast]
      exact combine_scaled_zip _ _ _ hlen_dl_W hlen_dl_WP

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
    -- Split by cases on rest₁ (and rest₂) to handle getLast?
    match rest₁, rest₂, hrest_len, hrest with
    | [], [], _, _ =>
      -- getLast? of [] is none, so sₙ = s₃ resp. r₃
      simp only [List.getLast?, List.replicate, List.length_nil, List.nil_append,
        List.map_nil, List.map_cons, List.zipWith]
      congr 1
      · simp only [Prod.mk.injEq]; exact ⟨by ring, trivial⟩
      · simp only [List.zip_cons_cons, List.zipWith_cons_cons, List.zipWith_nil_right]
        congr 1; simp only [Prod.mk.injEq]; exact ⟨by ring, trivial⟩
    | h₁ :: t₁, h₂ :: t₂, hrest_len', hrest' =>
      -- All getLast? are some since lists are nonempty
      -- Simplify getLast? to some (getLast ...)
      rw [List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil h₁ t₁),
          List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil h₂ t₂),
          getLast?_zipWith _ h₁ t₁ h₂ t₂ hrest_len']
      -- Simplify zipWith length
      have hlen_zw : (List.zipWith
          (fun x x_1 => ((1 - p) * x.1 + p * x_1.1, x.2))
          (h₁ :: t₁) (h₂ :: t₂)).length = (h₁ :: t₁).length := by
        have h := hrest_len'; simp only [List.length_cons] at h
        simp only [List.length_zipWith, List.length_cons, Nat.min_def]
        split <;> omega
      rw [hlen_zw]
      -- Simplify map snd of zipWith
      have map_snd_zipWith' : ∀ (l₁ l₂ : List (R × M)),
          l₁.map Prod.snd = l₂.map Prod.snd →
          (List.zipWith (fun x x_1 => ((1 - p) * x.1 + p * x_1.1, x.2))
            l₁ l₂).map Prod.snd = l₁.map Prod.snd := by
        intro l₁; induction l₁ with
        | nil => simp
        | cons a t ih =>
          intro l₂ h; cases l₂ with
          | nil => simp at h
          | cons b s =>
            simp only [List.zipWith_cons_cons, List.map_cons, List.cons.injEq] at h ⊢
            exact ⟨trivial, ih s h.2⟩
      have map_snd_zw := map_snd_zipWith' _ _ hrest'
      rw [map_snd_zw]
      -- Now the goal has concrete getLast values
      -- LHS head fst: (1-p)*(1-⅟(1-u)*getLast(h₁::t₁).1)+p*(1-⅟(1-u)*getLast(h₂::t₂).1)
      -- RHS head fst: 1-⅟(1-u)*((1-p)*getLast(h₁::t₁).1+p*getLast(h₂::t₂).1)
      -- These are equal by ring
      -- Tail LHS: zipWith combine over (replicate n 0 ++ [⅟(1-u)*w₁]).zip P₁
      --           and (replicate n 0 ++ [⅟(1-u)*w₂]).zip P₂
      -- Tail RHS: (replicate n 0 ++ [⅟(1-u)*combined_w]).zip P
      congr 1
      · simp only [Prod.mk.injEq]; exact ⟨by ring, trivial⟩
      · -- The tail: combining two (replicate n 0 ++ [v]).zip P lists
        -- Since (1-p)*0+p*0 = 0, the replicated zeros stay as zeros
        -- The last element combines linearly
        -- Simplify the match on some
        simp only [Option.some.injEq]
        -- Unify points: replace (h₂::t₂) snd with (h₁::t₁) snd
        have hpts_eq : (x₃ :: (h₂ :: t₂).map Prod.snd) =
            (x₃ :: (h₁ :: t₁).map Prod.snd) := by
          congr 1; exact hrest'.symm
        rw [hpts_eq]
        -- Unify replicate lengths
        have hlen_eq : (h₂ :: t₂).length = (h₁ :: t₁).length := by
          simp only [List.length_cons] at hrest_len' ⊢; omega
        rw [hlen_eq]
        -- Prove by induction on the replicate length
        have combine_replicate_zip :
            ∀ (n : ℕ) (v₁ v₂ : R) (P : List M),
            n + 1 = P.length →
            List.zipWith (fun x x_1 => ((1 - p) * x.1 + p * x_1.1, x.2))
              ((List.replicate n 0 ++ [v₁]).zip P)
              ((List.replicate n 0 ++ [v₂]).zip P) =
            (List.replicate n 0 ++ [(1 - p) * v₁ + p * v₂]).zip P := by
          intro n; induction n with
          | zero =>
            intro v₁ v₂ P hP; cases P with
            | nil => simp at hP
            | cons q qs =>
              simp only [List.replicate, List.nil_append, List.zip_cons_cons,
                List.zipWith_cons_cons, List.zipWith_nil_left,
                List.zip_nil_left]
          | succ m ih =>
            intro v₁ v₂ P hP; cases P with
            | nil => simp at hP
            | cons q qs =>
              simp only [List.replicate, List.cons_append, List.zip_cons_cons,
                List.zipWith_cons_cons, List.length_cons] at hP ⊢
              congr 1
              · simp only [Prod.mk.injEq]; exact ⟨by ring, trivial⟩
              · exact ih v₁ v₂ qs (by omega)
        convert combine_replicate_zip (h₁ :: t₁).length
          (⅟(1 - op.u) * ((h₁ :: t₁).getLast (List.cons_ne_nil _ _)).1)
          (⅟(1 - op.u) * ((h₂ :: t₂).getLast (List.cons_ne_nil _ _)).1)
          (x₃ :: (h₁ :: t₁).map Prod.snd)
          (by simp [List.length_cons, List.length_map]) using 1
        congr 1; congr 1; congr 1; ring

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

/-- Helper: `List.map (fun _ => c) xs` equals `List.replicate xs.length c`. -/
private theorem list_map_const {α : Type*} (c : R) (xs : List α) :
    xs.map (fun _ => c) = List.replicate xs.length c := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih, List.replicate_succ]

/-- Helper: the sum of a replicated zero list is zero. -/
private theorem sum_replicate_zero (n : Nat) : (List.replicate n (0 : R)).sum = 0 := by
  simp [List.sum_replicate, smul_zero]

/-- Helper: zip of replicated zeros with any list gives zero-weighted pairs. -/
private theorem zip_replicate_zero_map {n : Nat} {zs : List M} (h : n = zs.length) :
    (List.replicate n (0 : R)).zip zs = zs.map fun z => ((0 : R), z) := by
  subst h; induction zs with
  | nil => simp
  | cons z zs ih => simp [List.replicate_succ, ih]

/-- Helper: dropLast of a nonempty replicate is a shorter replicate. -/
private theorem dropLast_replicate_succ (n : Nat) (c : R) :
    (List.replicate (n + 1) c).dropLast = List.replicate n c := by
  induction n with
  | zero => simp [List.replicate, List.dropLast]
  | succ n ih =>
    rw [List.replicate_succ, List.replicate_succ, List.dropLast_cons₂]
    rw [show (c :: List.replicate n c).dropLast = List.replicate n c from ih]

/-- A doubleton followed by zeros: `A([(a,x), (b,y), (0,z₁), ..., (0,zₖ)]) = C(b, x, y)`
    when `a + b = 1`. Proved by strong induction on k.

    The singleton-padded case `A([(1,x), (0,z₁), ..., (0,zₖ)]) = x` follows
    by taking `b = 0` and using `binCombo_zero`. -/
theorem affineOfBinary_doubleton_padded [Inhabited M] (op : BinaryConvexOp R M)
    (a b : R) (x y : M) (zs : List M) (hab : a + b = 1) :
    affineOfBinary op ([(a, x), (b, y)] ++ zs.map fun z => (0, z)) =
      op.binCombo b x y := by
  induction h : zs.length using Nat.strongRecOn generalizing a b x y zs with
  | _ n ih =>
  match zs, h with
  | [], _ => simp [affineOfBinary]
  | [z₁], _ =>
    -- A([(a,x), (b,y), (0,z₁)])
    -- leftWS = [(⅟u*a, x), (1-⅟u*a, y)], rightWS = [(1, y), (0, z₁)]
    simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append, affineOfBinary,
      List.map, List.dropLast, List.sum_nil, List.getLast?_nil,
      List.replicate, List.zip_cons_cons, List.zip_nil_left,
      mul_zero, sub_zero, List.length_nil]
    -- A(rightWS) = C(0, y, z₁) = y
    rw [op.binCombo_zero y z₁]
    -- Now: C(1-u, C(1-⅟u*a, x, y), y)
    rw [op.binCombo_collapse_right]
    congr 1
    -- Goal: u * (1 - ⅟u * a) + (1 - u) = b
    have hinv : op.u * (⅟op.u * a) = a := by rw [← mul_assoc, mul_invOf_self, one_mul]
    have hb : b = 1 - a := by rw [← hab]; ring
    rw [hb, mul_sub, mul_one, hinv]; ring
  | z₁ :: z₂ :: zs', hlen =>
    simp only [List.map_cons, List.cons_append, List.nil_append]
    -- Input: (a,x)::(b,y)::(0,z₁)::(0,z₂)::zs'.map (0,·)
    -- Decompose into C(1-u, A(leftWS), A(rightWS))
    rw [affineOfBinary_decompose]
    -- Prove leftWS and rightWS give the right values
    -- leftWS is doubleton-padded with ⅟u*a, 1-⅟u*a, and fewer zeros → IH
    -- rightWS is doubleton-padded with 1, 0, and fewer zeros → IH, then binCombo_zero
    set rest : WeightedSeq R M := (0, z₂) :: List.map (fun z => ((0 : R), z)) zs'
    -- Compute what leftWeightedSeq and rightWeightedSeq produce
    -- leftWeightedSeq: unfolds to
    --   a₁ = ⅟u * a, middleWeights = (0 :: rest.map fst).dropLast, scaledMiddle = (⅟u * ·) <$> middleWeights
    --   a₂ = 1 - a₁ - scaledMiddle.sum, middlePoints = (z₁ :: rest.map snd).dropLast
    --   result = (a₁, x) :: (a₂, y) :: scaledMiddle.zip middlePoints
    -- Since all weights in rest are 0:
    --   rest.map fst = replicate (zs'.length+1) 0
    --   middleWeights = (0 :: replicate (zs'.length+1) 0).dropLast = replicate (zs'.length+1) 0
    --   scaledMiddle = replicate (zs'.length+1) 0 (since ⅟u * 0 = 0)
    --   scaledMiddle.sum = 0
    --   a₂ = 1 - ⅟u*a
    -- For points:
    --   rest.map snd = z₂ :: zs'
    --   middlePoints = (z₁ :: z₂ :: zs').dropLast
    -- leftWS = (⅟u*a, x) :: (1-⅟u*a, y) :: (replicate (zs'.length+1) 0).zip (z₁ :: z₂ :: zs').dropLast
    --        = (⅟u*a, x) :: (1-⅟u*a, y) :: middlePoints.map (0, ·)
    -- This is doubleton-padded!
    have hrest_fst : rest.map Prod.fst = List.replicate (zs'.length + 1) (0 : R) := by
      show (0 : R) :: (zs'.map (fun z => ((0 : R), z))).map Prod.fst =
        List.replicate (zs'.length + 1) (0 : R)
      rw [show (zs'.map (fun z => ((0 : R), z))).map Prod.fst = zs'.map (fun _ => (0 : R)) from by
        rw [List.map_map]; rfl]
      rw [list_map_const, List.replicate_succ]
    have hrest_snd : rest.map Prod.snd = z₂ :: zs' := by
      show z₂ :: (zs'.map (fun z => ((0 : R), z))).map Prod.snd = z₂ :: zs'
      rw [show (zs'.map (fun z => ((0 : R), z))).map Prod.snd = zs' from by
        rw [List.map_map]; simp [Function.comp]]
    -- The middle weights are all zeros
    have hmiddle_weights :
        ((0 : R) :: rest.map Prod.fst).dropLast =
        List.replicate (zs'.length + 1) (0 : R) := by
      rw [hrest_fst]
      rw [show (0 : R) :: List.replicate (zs'.length + 1) 0 =
        List.replicate (zs'.length + 2) (0 : R) from by simp [List.replicate_succ]]
      exact dropLast_replicate_succ (zs'.length + 1) 0
    have hscaled_middle :
        (((0 : R) :: rest.map Prod.fst).dropLast.map (⅟op.u * ·)) =
        List.replicate (zs'.length + 1) (0 : R) := by
      rw [hmiddle_weights, List.map_replicate, mul_zero]
    have hscaled_sum :
        (((0 : R) :: rest.map Prod.fst).dropLast.map (⅟op.u * ·)).sum = 0 := by
      rw [hscaled_middle, sum_replicate_zero]
    -- For rightWeightedSeq: last weight is 0
    have hrest_getLast :
        (match rest.getLast? with | some (w, _) => w | none => (0 : R)) = 0 := by
      have hall : ∀ p ∈ rest, (p : R × M).1 = 0 := by
        intro p hp
        simp only [rest, List.mem_cons, List.mem_map] at hp
        rcases hp with rfl | ⟨z, _, rfl⟩ <;> rfl
      have hne : rest ≠ [] := List.cons_ne_nil _ _
      rw [List.getLast?_eq_getLast hne]
      exact hall _ (List.getLast_mem hne)
    have hleft : affineOfBinary op
        (leftWeightedSeq op ((a, x) :: (b, y) :: (0, z₁) :: rest)) =
        op.binCombo (1 - ⅟op.u * a) x y := by
      simp only [leftWeightedSeq]
      rw [hscaled_sum, sub_zero]
      -- leftWS = (⅟u*a, x) :: (1-⅟u*a, y) :: scaledMiddle.zip middlePoints
      rw [hscaled_middle]
      -- Now need: A((⅟u*a, x)::(1-⅟u*a, y)::zeros.zip points) = C(1-⅟u*a, x, y)
      rw [hrest_snd]
      set middlePoints := (z₁ :: z₂ :: zs').dropLast
      have hlen : middlePoints.length = zs'.length + 1 := by
        simp [middlePoints, List.length_dropLast]
      rw [zip_replicate_zero_map hlen.symm]
      -- Now: A([(⅟u*a, x), (1-⅟u*a, y)] ++ middlePoints.map (0,·)) = C(1-⅟u*a, x, y)
      have hlt : middlePoints.length < n := by
        have h1 : middlePoints.length = zs'.length + 1 := by
          simp [middlePoints, List.length_dropLast]
        have h2 : n = zs'.length + 2 := by
          have : (z₁ :: z₂ :: zs').length = zs'.length + 2 := by simp
          omega
        omega
      exact ih middlePoints.length hlt _ _ _ _ middlePoints (by ring) rfl
    have hright : affineOfBinary op
        (rightWeightedSeq op ((a, x) :: (b, y) :: (0, z₁) :: rest)) =
        y := by
      simp only [rightWeightedSeq]
      rw [hrest_getLast, mul_zero, sub_zero]
      -- rightWS = (1, y) :: (replicate rest.length 0 ++ [0]).zip (z₁ :: rest.map snd)
      --         = (1, y) :: zeros.zip (z₁ :: z₂ :: zs')
      rw [hrest_snd]
      -- Convert (replicate rest.length 0 ++ [0]).zip (z₁ :: z₂ :: zs') to map form
      have hrl : rest.length = zs'.length + 1 := by simp [rest]
      have hrep : List.replicate (List.length rest) (0 : R) ++ [0] =
          List.replicate (zs'.length + 2) (0 : R) := by
        rw [hrl]; simp [List.replicate_add]
      rw [hrep, zip_replicate_zero_map (by simp)]
      -- Goal: A((1, y) :: (z₁ :: z₂ :: zs').map (0,·)) = y
      -- = A([(1, y), (0, z₁)] ++ (z₂ :: zs').map (0,·))
      simp only [List.map_cons, List.cons_append, List.nil_append]
      -- Use IH with a=1, b=0
      have hlt2 : (z₂ :: zs').length < n := by
        have h1 : (z₂ :: zs').length = zs'.length + 1 := by simp
        have h2 : (z₁ :: z₂ :: zs').length = zs'.length + 2 := by simp
        omega
      have := ih (z₂ :: zs').length hlt2 1 0 y z₁ (z₂ :: zs') (by ring) rfl
      simp only [List.map_cons, List.cons_append, List.nil_append] at this
      rw [this]
      exact op.binCombo_zero y z₁
    rw [hleft, hright]
    rw [op.binCombo_collapse_right]
    congr 1
    have hinv : op.u * (⅟op.u * a) = a := by
      rw [← mul_assoc, mul_invOf_self, one_mul]
    have hb : b = 1 - a := by rw [← hab]; ring
    rw [hb, mul_sub, mul_one, hinv]; ring

/-- A singleton followed by zeros evaluates to the point:
    `A([(1,x), (0,z₁), ..., (0,zₖ)]) = x`. -/
theorem affineOfBinary_singleton_padded [Inhabited M] (op : BinaryConvexOp R M)
    (x : M) (zs : List M) :
    affineOfBinary op ([(1, x)] ++ zs.map fun z => (0, z)) = x := by
  match zs with
  | [] => simp [affineOfBinary]
  | z :: zs' =>
    simp only [List.map_cons, List.cons_append, List.nil_append]
    -- Goal: A((1,x) :: (0,z) :: map ...) = x
    -- This is doubleton_padded with a=1, b=0
    have h : (1 : R) + 0 = 1 := by ring
    have := affineOfBinary_doubleton_padded op 1 0 x z zs' h
    simp only [List.map_cons, List.cons_append, List.nil_append] at this
    rw [this]
    exact op.binCombo_zero x z

/-- Adding a zero-weight point at the front doesn't change the affine combination.
    This follows from binCombo_one (when left weight is 0, we get x₁) and entropic. -/
theorem affineOfBinary_cons_zero [Inhabited M] (op : BinaryConvexOp R M)
    (x : M) (ws : WeightedSeq R M) (hvalid : ws.totalWeight = 1) (hne : ws ≠ []) :
    affineOfBinary op ((0, x) :: ws) = affineOfBinary op ws := by
  induction h : ws.length using Nat.strongRecOn generalizing x ws with
  | _ n ih =>
  match ws, h with
  | [], _ => exact absurd rfl hne
  | [(w, y)], _ =>
    simp only [affineOfBinary]
    have hw : w = 1 := by simpa [WeightedSeq.totalWeight] using hvalid
    subst hw
    exact op.binCombo_one x y
  | [(w₁, y₁), (w₂, y₂)], _ =>
    simp only [affineOfBinary,
      List.map_nil, List.dropLast, List.sum_nil,
      List.getLast?_nil, List.replicate, List.nil_append,
      List.zip_cons_cons, List.zip_nil_left, mul_zero, sub_zero,
      List.length_nil]
    rw [op.binCombo_one x y₁]
    have h := op.binCombo_entropic
      (1 - op.u) 0 (⅟(1 - op.u) * w₂) y₁ y₂
    rw [op.binCombo_zero y₁ y₂] at h; rw [h]; congr 1
    simp only [mul_zero, zero_add, ← mul_assoc,
      mul_invOf_self, one_mul]
  | (w₁, y₁) :: (w₂, y₂) :: r₁ :: rest', hlen =>
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

/-- Adding a zero-weight point at the end doesn't change the affine combination.
    This follows from binCombo_zero (when right weight is 0, we get previous result). -/
theorem affineOfBinary_append_zero [Inhabited M] (op : BinaryConvexOp R M)
    (ws : WeightedSeq R M) (x : M) (hvalid : ws.totalWeight = 1) (hne : ws ≠ []) :
    affineOfBinary op (ws ++ [(0, x)]) = affineOfBinary op ws := by
  match ws with
  | [] => exact absurd rfl hne
  | [(w, y)] =>
    simp only [List.singleton_append, affineOfBinary]
    have hw : w = 1 := by simpa [WeightedSeq.totalWeight] using hvalid
    subst hw
    exact op.binCombo_zero y x
  | (w₁, y₁) :: (w₂, y₂) :: rest =>
    match rest with
    | [] =>
      simp only [List.cons_append, List.nil_append, affineOfBinary,
        List.map_nil, List.dropLast, List.sum_nil,
        List.getLast?_nil, List.replicate,
        List.zip_cons_cons, List.zip_nil_left, mul_zero, sub_zero,
        List.length_nil]
      rw [op.binCombo_zero y₂ x]
      have h := op.binCombo_entropic
        (1 - op.u) (1 - ⅟op.u * w₁) 1 y₁ y₂
      rw [op.binCombo_one y₁ y₂] at h; rw [h]; congr 1
      have hw : w₁ + w₂ = 1 := by
        simpa [WeightedSeq.totalWeight] using hvalid
      have hinv : op.u * (⅟op.u * w₁) = w₁ := by
        rw [← mul_assoc, mul_invOf_self, one_mul]
      have hw₂ : w₂ = 1 - w₁ := by rw [← hw]; ring
      have : (1 - (1 - op.u)) = op.u := by ring
      rw [this, mul_sub, mul_one, hinv, mul_one, hw₂]; ring
    | (w₃, y₃) :: rest' =>
      simp only [List.cons_append]
      rw [affineOfBinary_decompose]
      have hright_eq : affineOfBinary op
          (rightWeightedSeq op
            ((w₁, y₁) :: (w₂, y₂) :: (w₃, y₃) :: (rest' ++ [(0, x)]))) = y₂ := by
        simp only [rightWeightedSeq]
        have hLast : (match (rest' ++ [(0, x)]).getLast? with
          | some (w, _) => w | none => w₃) = (0 : R) := by
          rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
          simp
        rw [hLast]
        simp only [mul_zero, sub_zero]
        set k := (rest' ++ [(0, x)]).length
        set pts := y₃ :: List.map Prod.snd (rest' ++ [(0, x)])
        have hlen_pts : pts.length = k + 1 := by simp [pts, k]
        have hrep : List.replicate k (0 : R) ++ [0] =
            List.replicate (k + 1) (0 : R) := by
          rw [show [0] = List.replicate 1 (0 : R) from rfl,
            List.replicate_append_replicate]
        rw [hrep]
        rw [zip_replicate_zero_map hlen_pts.symm]
        exact affineOfBinary_singleton_padded op y₂ pts
      rw [hright_eq]
      set mw := w₃ :: rest'.map Prod.fst
      set mp := y₃ :: rest'.map Prod.snd
      set sm := mw.map (⅟op.u * ·) with sm_def
      have hmw_len : mw.length = mp.length := by simp [mw, mp]
      have hleft : leftWeightedSeq op
          ((w₁, y₁) :: (w₂, y₂) :: (w₃, y₃) :: (rest' ++ [(0, x)])) =
          (⅟op.u * w₁, y₁) :: (1 - ⅟op.u * w₁ - sm.sum, y₂) ::
            sm.zip mp := by
        simp only [leftWeightedSeq]
        have : (w₃ :: (rest' ++ [(0, x)]).map Prod.fst).dropLast =
            mw := by
          simp only [List.map_append, List.map_cons, List.map_nil,
            Prod.fst, mw]
          rw [show w₃ :: (rest'.map Prod.fst ++ [0]) =
            (w₃ :: rest'.map Prod.fst) ++ [(0 : R)] from by
              rw [List.cons_append]]
          rw [List.dropLast_concat]
        have : (y₃ :: (rest' ++ [(0, x)]).map Prod.snd).dropLast =
            mp := by
          simp only [List.map_append, List.map_cons, List.map_nil,
            Prod.snd, mp]
          rw [show y₃ :: (rest'.map Prod.snd ++ [x]) =
            (y₃ :: rest'.map Prod.snd) ++ [x] from by
              rw [List.cons_append]]
          rw [List.dropLast_concat]
        simp only [*, sm_def]
      rw [hleft]
      -- Goal: C(1-u, A(leftWS), y₂) = A(ws)
      set leftWS : WeightedSeq R M :=
        (⅟op.u * w₁, y₁) :: (1 - ⅟op.u * w₁ - sm.sum, y₂) :: sm.zip mp
      set padY₂ : WeightedSeq R M :=
        ((0 : R), y₁) :: ((1 : R), y₂) :: mp.map (fun z => ((0 : R), z))
      have hsm_len : sm.length = mp.length := by simp [sm, mw, mp]
      have hy₂_pad : y₂ = affineOfBinary op padY₂ := by
        change y₂ = affineOfBinary op
          ([(0, y₁), (1, y₂)] ++ mp.map (fun z => ((0 : R), z)))
        rw [affineOfBinary_doubleton_padded op 0 1 y₁ y₂ mp (by ring)]
        exact (op.binCombo_one y₁ y₂).symm
      -- Only rewrite y₂ in the third argument of binCombo, not inside leftWS
      conv_lhs => rw [show y₂ = affineOfBinary op padY₂ from hy₂_pad]
      -- Goal: C(1-u, A(leftWS), A(padY₂)) = A(ws)
      have hlen : leftWS.length = padY₂.length := by
        simp [leftWS, padY₂, List.length_zip, hsm_len]
      have hpts : leftWS.samePoints padY₂ := by
        simp only [WeightedSeq.samePoints, leftWS, padY₂,
          List.map_cons, Prod.snd]
        congr 1; congr 1
        rw [List.map_snd_zip (le_of_eq hsm_len.symm)]
        simp [List.map_map, Function.comp_def]
      rw [affineOfBinary_linear op (1 - op.u) leftWS padY₂ hlen hpts]
      -- Goal: A(combineWeights (1-u) leftWS padY₂) = A(ws)
      -- It suffices to show the lists are equal
      congr 1
      -- Goal: combineWeights (1-u) leftWS padY₂ = (w₁,y₁)::(w₂,y₂)::(w₃,y₃)::rest'
      simp only [WeightedSeq.combineWeights, leftWS, padY₂,
        List.zipWith_cons_cons]
      -- Goal has three parts: head (w₁,y₁), second (w₂,y₂), tail
      have hu_inv : op.u * ⅟op.u = 1 := mul_invOf_self op.u
      have h1u : (1 : R) - (1 - op.u) = op.u := by ring
      have hinv_mul (a : R) : op.u * (⅟op.u * a) = a := by
        rw [← mul_assoc, hu_inv, one_mul]
      -- Head: (1-(1-u))*(⅟u*w₁) + (1-u)*0 = w₁
      congr 1
      · congr 1; rw [h1u, mul_zero, add_zero, hinv_mul]
      -- Second element and tail
      congr 1
      · -- ((1-(1-u))*(1-⅟u*w₁-sm.sum) + (1-u)*1, y₂) = (w₂, y₂)
        congr 1
        -- u*(1-⅟u*w₁-sm.sum) + (1-u)*1 = w₂
        rw [h1u, mul_one]
        -- u*(1-⅟u*w₁-sm.sum) + (1-u) = w₂
        have hsm_sum : sm.sum = ⅟op.u * mw.sum := by
          simp only [sm]
          induction mw with
          | nil => simp
          | cons h t ih => simp [List.sum_cons, ih, mul_add]
        rw [hsm_sum]
        have hmul_expand : op.u * (1 - ⅟op.u * w₁ - ⅟op.u * mw.sum) =
            op.u - w₁ - mw.sum := by
          rw [mul_sub, mul_sub, mul_one, hinv_mul, hinv_mul]
        rw [hmul_expand]
        -- Goal: u - w₁ - mw.sum + (1 - u) = w₂
        -- This ring-simplifies to 1 - w₁ - mw.sum = w₂
        -- From totalWeight: w₁ + w₂ + mw.sum = 1, so w₂ = 1 - w₁ - mw.sum
        have hmw_sum : mw.sum = w₃ + (rest'.map Prod.fst).sum := by
          simp [mw]
        -- Extract w₁ + w₂ + mw.sum = 1 from hvalid
        have htw : w₁ + w₂ + mw.sum = 1 := by
          have := hvalid
          simp only [WeightedSeq.totalWeight, List.map_cons, List.sum_cons,
            Prod.fst] at this
          -- this : w₁ + (w₂ + (w₃ + rest'.fst.sum)) = 1
          -- need: w₁ + w₂ + mw.sum = 1
          -- = w₁ + w₂ + (w₃ + rest'.fst.sum) = 1 (by hmw_sum)
          -- = w₁ + (w₂ + (w₃ + rest'.fst.sum)) = 1 (by ring)
          calc w₁ + w₂ + mw.sum
              = w₁ + w₂ + (w₃ + (rest'.map Prod.fst).sum) := by rw [hmw_sum]
            _ = w₁ + (w₂ + (w₃ + (rest'.map Prod.fst).sum)) := by ring
            _ = 1 := this
        -- Now: goal = u - w₁ - mw.sum + (1 - u) which ring-equals 1 - w₁ - mw.sum
        -- And htw says w₁ + w₂ + mw.sum = 1, so w₂ = 1 - w₁ - mw.sum
        -- Use omega-style: rewrite goal using htw
        have : op.u - w₁ - mw.sum + (1 - op.u) = 1 - w₁ - mw.sum := by ring
        rw [this]
        -- Now goal: 1 - w₁ - mw.sum = w₂, which is: w₂ + w₁ + mw.sum = 1
        symm
        -- w₂ = 1 - w₁ - mw.sum
        -- From htw: w₁ + w₂ + mw.sum = 1
        -- So w₂ = 1 - w₁ - mw.sum iff 1 - w₁ - mw.sum + w₁ + mw.sum = 1 (trivial ring)
        -- Just do: from htw, w₂ = 1 - (w₁ + mw.sum), and 1 - w₁ - mw.sum = 1 - (w₁ + mw.sum) by ring
        show w₂ = 1 - w₁ - mw.sum
        have : w₁ + w₂ + mw.sum = 1 := htw
        -- Rearranging: w₂ = 1 - w₁ - mw.sum
        -- Proof: from this, w₂ = 1 - w₁ - mw.sum
        calc w₂ = w₁ + w₂ + mw.sum - w₁ - mw.sum := by ring
          _ = 1 - w₁ - mw.sum := by rw [htw]
      -- Remaining goal: zipWith ... (sm.zip mp) (mp.map (0,·)) = (w₃,y₃)::rest'
      -- Each element: (u*(⅟u*wᵢ) + (1-u)*0, yᵢ) = (wᵢ, yᵢ)
      -- This is: combining sm.zip mp with mp.map(0,·) gives mw.zip mp = ws tail
      -- Prove by showing it equals rest of the original list
      -- sm = mw.map (⅟u*·), mw = w₃ :: rest'.map fst, mp = y₃ :: rest'.map snd
      -- Need: for any lists ws ps of same length, zipWith comb ((ws.map(⅟u*·)).zip ps) (ps.map(0,·))
      --   = ws.zip ps when each element simplifies via u*⅟u = 1
      suffices ∀ (ws : List R) (ps : List M), ws.length = ps.length →
          List.zipWith (fun x x_1 => ((1 - (1 - op.u)) * x.1 + (1 - op.u) * x_1.1, x.2))
            ((ws.map (⅟op.u * ·)).zip ps) (ps.map (fun z => ((0 : R), z))) =
          ws.zip ps by
        simp only [sm, mw, mp]
        rw [show (w₃ :: rest'.map Prod.fst).map (⅟op.u * ·) =
          ((w₃ :: rest'.map Prod.fst).map (⅟op.u * ·)) from rfl]
        rw [this (w₃ :: rest'.map Prod.fst) (y₃ :: rest'.map Prod.snd) hmw_len]
        -- Goal: (w₃::rest'.map fst).zip(y₃::rest'.map snd) = (w₃,y₃)::rest'
        simp only [List.zip_cons_cons]
        congr 1
        have : rest'.unzip.fst.zip rest'.unzip.snd = rest' := List.zip_unzip rest'
        rwa [List.unzip_eq_map] at this
      intro ws
      induction ws with
      | nil => intro _ _; simp
      | cons w wt ih =>
        intro ps hlen
        match ps with
        | [] => simp at hlen
        | p :: pt =>
          simp only [List.map_cons, List.zip_cons_cons, List.zipWith_cons_cons,
            Prod.fst, Prod.snd]
          congr 1
          · congr 1; rw [h1u, mul_zero, add_zero, hinv_mul]
          · exact ih pt (by simpa using hlen)
      done

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

/-- When d₁ and d₂ have the same support, their toWeightedSeq have the same points. -/
theorem toWeightedSeq_samePoints_of_support_eq [PartialOrder R] [IsStrictOrderedRing R]
    {d₁ d₂ : StdSimplex R M} (hsupp : d₁.weights.support = d₂.weights.support) :
    d₁.toWeightedSeq.samePoints d₂.toWeightedSeq := by
  simp only [StdSimplex.toWeightedSeq, WeightedSeq.samePoints, List.map_map]
  congr 1
  rw [hsupp]

/-- When d₁ and d₂ have the same support, their toWeightedSeq have the same length. -/
theorem toWeightedSeq_length_of_support_eq [PartialOrder R] [IsStrictOrderedRing R]
    {d₁ d₂ : StdSimplex R M} (hsupp : d₁.weights.support = d₂.weights.support) :
    d₁.toWeightedSeq.length = d₂.toWeightedSeq.length := by
  simp only [StdSimplex.toWeightedSeq, List.length_map]
  rw [hsupp]

/-- The join of a duple has weights p • d₁.weights + (1-p) • d₂.weights. -/
theorem StdSimplex.join_duple_weights [PartialOrder R] [IsStrictOrderedRing R]
    (d₁ d₂ : StdSimplex R M) {p : R} (hp : 0 ≤ p) (hp' : 0 ≤ 1 - p) (hsum : p + (1 - p) = 1) :
    (StdSimplex.duple d₁ d₂ hp hp' hsum).join.weights =
      p • d₁.weights + (1 - p) • d₂.weights := by
  ext m
  classical
  simp only [StdSimplex.join, StdSimplex.duple]
  rw [Finsupp.sum_add_index (by simp) (by simp [add_smul])]
  rw [Finsupp.sum_single_index (by simp : (0 : R) • d₁.weights = 0),
      Finsupp.sum_single_index (by simp : (0 : R) • d₂.weights = 0)]

end OfBinary

/-- Any simplex with support cardinality ≥ 2 can be expressed as the join of a duple
    of two simplices, each with strictly smaller support cardinality.

    The splitting weights s, t are chosen based on f (s = weight of an arbitrary support element). -/
theorem StdSimplex.exists_duple_join {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] {X : Type*}
    (f : StdSimplex R X) (hcard : 2 ≤ f.weights.support.card) :
    ∃ (s t : R) (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1)
      (g₁ g₂ : StdSimplex R X)
      (h₁ : g₁.weights.support.card < f.weights.support.card)
      (h₂ : g₂.weights.support.card < f.weights.support.card),
      f = (StdSimplex.duple g₁ g₂ (le_of_lt hs) (le_of_lt ht) hst).join := by
  classical
  -- Pick any element from the support
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < f.weights.support.card)
  have hwa_ne : f.weights a ≠ 0 := Finsupp.mem_support_iff.mp ha
  have hwa_pos : 0 < f.weights a := lt_of_le_of_ne (f.nonneg a) (Ne.symm hwa_ne)
  have hwa_lt_one : f.weights a < 1 := by
    obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.mp (by omega : 1 < f.weights.support.card)
    obtain ⟨d, hd, hda⟩ : ∃ d ∈ f.weights.support, d ≠ a := by
      by_cases hba : b = a
      · exact ⟨c, hc, fun hca => hbc (hba ▸ hca ▸ rfl)⟩
      · exact ⟨b, hb, hba⟩
    have hwd_pos : 0 < f.weights d :=
      lt_of_le_of_ne (f.nonneg d) (Ne.symm (Finsupp.mem_support_iff.mp hd))
    have htotal := f.total
    rw [Finsupp.sum] at htotal
    have hd_in_erase : d ∈ f.weights.support.erase a :=
      Finset.mem_erase.mpr ⟨hda, hd⟩
    have hd_le : f.weights d ≤ ∑ x ∈ f.weights.support.erase a, f.weights x :=
      Finset.single_le_sum (fun i _ => f.nonneg i) hd_in_erase
    have hsplit : f.weights a + ∑ x ∈ f.weights.support.erase a, f.weights x = 1 :=
      (Finset.add_sum_erase f.weights.support f.weights ha).trans htotal
    linarith
  -- Set s = f(a), t = 1 - f(a)
  set s := f.weights a
  set t := 1 - s with ht_def
  have ht_pos : 0 < t := sub_pos.mpr hwa_lt_one
  have hst : s + t = 1 := by ring
  -- g₁ = single a (support card = 1 < card(f))
  -- g₂ = t⁻¹ • (f.weights.erase a)
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have ht_inv_nonneg : 0 ≤ t⁻¹ := inv_nonneg.mpr (le_of_lt ht_pos)
  have herase_nonneg : 0 ≤ f.weights.erase a := by
    intro x
    simp only [Finsupp.erase_apply]
    split <;> [exact le_refl 0; exact f.nonneg x]
  have herase_sum : (f.weights.erase a).sum (fun _ r => r) = t := by
    have h1 := f.total
    rw [Finsupp.sum] at h1 ⊢
    rw [Finsupp.support_erase]
    have h2 : ∀ x ∈ f.weights.support.erase a,
        (f.weights.erase a) x = f.weights x := fun x hx =>
      Finsupp.erase_ne (Finset.mem_erase.mp hx).1
    rw [Finset.sum_congr rfl h2]
    have h3 : f.weights a + ∑ x ∈ f.weights.support.erase a, f.weights x = 1 :=
      (Finset.add_sum_erase f.weights.support f.weights ha).trans h1
    linarith
  set g₂ : StdSimplex R X := ⟨t⁻¹ • f.weights.erase a,
    smul_nonneg ht_inv_nonneg herase_nonneg,
    by
      have h := Finsupp.sum_smul_index (h0 := fun _ => rfl)
        (b := t⁻¹) (g := f.weights.erase a) (h := fun _ r => r)
      rw [h]
      simp only [← Finsupp.mul_sum, herase_sum, inv_mul_cancel₀ ht_ne]⟩
  refine ⟨s, t, hwa_pos, ht_pos, hst, .single a, g₂, ?_, ?_, ?_⟩
  -- Goal 1: (single a).support.card < f.support.card
  · rw [single_support_card]; omega
  -- Goal 2: g₂.support.card < f.support.card
  · calc g₂.weights.support.card
        ≤ (f.weights.erase a).support.card := by
            apply Finset.card_le_card
            exact Finsupp.support_smul
      _ = (f.weights.support.erase a).card := by
            rw [Finsupp.support_erase]
      _ < f.weights.support.card := Finset.card_erase_lt_of_mem ha
  -- Goal 3: f = (duple (single a) g₂ ...).join
  · apply StdSimplex.ext
    simp only [StdSimplex.join, StdSimplex.duple]
    rw [Finsupp.sum_add_index (by simp) (by simp [add_smul])]
    rw [Finsupp.sum_single_index (by simp : (0 : R) • (single a).weights = 0)]
    rw [Finsupp.sum_single_index (by simp : (0 : R) • g₂.weights = 0)]
    simp only [StdSimplex.single_weights, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [show g₂.weights = t⁻¹ • f.weights.erase a from rfl]
    rw [smul_smul, mul_inv_cancel₀ ht_ne, one_smul]
    rw [add_comm, Finsupp.erase_add_single]

section OfBinaryField

variable {R : Type u} {M : Type v} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Evaluate a StdSimplex on a given list of points, putting zero weight for points
    not in the support. -/
noncomputable def StdSimplex.toWeightedSeqOn (d : StdSimplex R M) (S : List M) :
    WeightedSeq R M :=
  S.map fun x => (d.weights x, x)

/-- Algebraic core for doubleton_padded_end:
    `C(1-u, C(1-⅟u*a, x, z), C(⅟(1-u)*b, z, y)) = C(b, x, y)` when `a + b = 1`. -/
private theorem doubleton_padded_end_algebra (op : BinaryConvexOp R M)
    (a b : R) (x z y : M) (hab : a + b = 1) :
    op.binCombo (1 - op.u) (op.binCombo (1 - ⅟op.u * a) x z)
      (op.binCombo (⅟(1 - op.u) * b) z y) =
    op.binCombo b x y := by
  by_cases ha : a = 0
  · have hb : b = 1 := by linarith
    subst ha; subst hb
    simp only [mul_zero, mul_one, sub_zero]
    rw [op.binCombo_one x z]
    rw [op.binCombo_absorb_left (1 - op.u) (⅟(1 - op.u)) z y]
    rw [mul_invOf_self]
    rw [op.binCombo_one z y, op.binCombo_one x y]
  · set p := (1 : R) - op.u
    set q := ⅟(1 - op.u) * b
    have h1mu_ne : (1 : R) - op.u ≠ 0 := Invertible.ne_zero (1 - op.u)
    have hpq : p * q = b := by
      simp [p, q, ← mul_assoc, mul_invOf_self, one_mul]
    set r := (a - op.u) / a
    have hassoc_cond : p * (1 - q) = (1 - p * q) * r := by
      rw [hpq]
      simp only [p, q, r, invOf_eq_inv]
      rw [show (1 : R) - b = a from by linarith]
      field_simp [ha, h1mu_ne]
      linarith
    rw [op.binCombo_assoc p q r
      (op.binCombo (1 - ⅟op.u * a) x z) z y hassoc_cond]
    rw [hpq]
    rw [op.binCombo_absorb_right r (1 - ⅟op.u * a) x z]
    have hu_ne : op.u ≠ 0 := Invertible.ne_zero op.u
    have hcollapse : 1 - (1 - r) * (1 - (1 - ⅟op.u * a)) = 0 := by
      simp only [r, invOf_eq_inv]
      field_simp [ha, hu_ne]
      ring
    rw [hcollapse, op.binCombo_zero x z]

/-- A doubleton with zeros in between:
    `A([(a,x), (0,z₁), ..., (0,zₖ), (b,y)]) = C(b, x, y)` when `a + b = 1`.

    This is the "reversed" version of `affineOfBinary_doubleton_padded`:
    zeros are between the two nonzero weights rather than after them.
    Proved by strong induction on k (the number of zeros). -/
theorem affineOfBinary_doubleton_padded_end [Inhabited M] (op : BinaryConvexOp R M)
    (a b : R) (x y : M) (zs : List M) (hab : a + b = 1) :
    affineOfBinary op ([(a, x)] ++ zs.map (fun z => (0, z)) ++ [(b, y)]) =
      op.binCombo b x y := by
  induction h : zs.length using Nat.strongRecOn generalizing a b x y zs with
  | _ n ih =>
  match zs, h with
  | [], _ =>
    -- Base case: A([(a,x),(b,y)]) = C(b,x,y)
    simp [affineOfBinary]
  | [z₁], _ =>
    -- One zero: A([(a,x),(0,z₁),(b,y)])
    -- Decomposition: C(1-u, C(1-⅟u*a, x, z₁), C(⅟(1-u)*b, z₁, y))
    simp only [List.map_cons, List.map_nil, List.nil_append, List.cons_append,
      List.singleton_append, affineOfBinary,
      List.map, List.dropLast, List.sum_nil, List.getLast?_nil,
      List.replicate, List.zip_cons_cons, List.zip_nil_left,
      mul_zero, sub_zero, List.length_nil]
    exact doubleton_padded_end_algebra op a b x z₁ y hab
  | z₁ :: z₂ :: zs', hlen =>
    -- Two+ zeros: A([(a,x),(0,z₁),(0,z₂),...,(0,zₖ),(b,y)])
    -- The proof follows the same pattern as [z₁]:
    -- After decompose, leftWS is doubleton_padded → C(1-⅟u*a, x, z₁)
    -- rightWS is doubleton_padded_end with fewer zeros → C(⅟(1-u)*b, z₁, y)
    -- Then doubleton_padded_end_algebra closes the goal.
    simp only [List.map_cons, List.cons_append, List.nil_append]
    rw [affineOfBinary_decompose]
    -- hleft and hright proved below via detailed list plumbing
    set rest : WeightedSeq R M :=
      (List.map (fun z => ((0 : R), z)) zs' ++ [(b, y)])
    -- Auxiliary: all weights in rest except last are 0, last is b
    have hrest_ne : rest ≠ [] := by simp [rest]
    have hrest_map_fst : rest.map Prod.fst =
        List.replicate zs'.length (0 : R) ++ [b] := by
      simp only [rest, List.map_append, List.map_map, Function.comp]
      congr 1
      exact list_map_const (0 : R) zs'
    have hrest_map_snd : rest.map Prod.snd = zs' ++ [y] := by
      simp only [rest, List.map_append, List.map_map, Function.comp]
      congr 1
      simp
    -- Middle weights are all zero (same pattern as doubleton_padded)
    have hmiddle_weights :
        ((0 : R) :: rest.map Prod.fst).dropLast =
        List.replicate (zs'.length + 1) (0 : R) := by
      rw [hrest_map_fst, show (0 : R) :: (List.replicate zs'.length 0 ++ [b]) =
        ((0 : R) :: List.replicate zs'.length 0) ++ [b] from by rw [List.cons_append],
        List.dropLast_concat, List.replicate_succ]
    have hscaled_middle :
        (((0 : R) :: rest.map Prod.fst).dropLast.map (⅟op.u * ·)) =
        List.replicate (zs'.length + 1) (0 : R) := by
      rw [hmiddle_weights, List.map_replicate, mul_zero]
    have hscaled_sum :
        (((0 : R) :: rest.map Prod.fst).dropLast.map (⅟op.u * ·)).sum = 0 := by
      rw [hscaled_middle, sum_replicate_zero]
    -- Middle points after dropLast
    have hmiddle_points :
        (z₂ :: rest.map Prod.snd).dropLast = z₂ :: zs' := by
      rw [hrest_map_snd, show z₂ :: (zs' ++ [y]) =
        (z₂ :: zs') ++ [y] from by rw [List.cons_append],
        List.dropLast_concat]
    have hleft : affineOfBinary op
        (leftWeightedSeq op
          ((a, x) :: (0, z₁) :: (0, z₂) :: rest)) =
        op.binCombo (1 - ⅟op.u * a) x z₁ := by
      simp only [leftWeightedSeq]
      rw [hscaled_sum, sub_zero]
      rw [hscaled_middle]
      rw [hmiddle_points]
      set middlePoints := z₂ :: zs'
      have hmid_len : middlePoints.length = zs'.length + 1 := by simp [middlePoints]
      rw [zip_replicate_zero_map hmid_len.symm]
      -- Now: A([(⅟u*a, x), (1-⅟u*a, z₁)] ++ middlePoints.map (0,·)) = C(1-⅟u*a, x, z₁)
      exact affineOfBinary_doubleton_padded op _ _ x z₁ middlePoints (by ring)
    -- For rightWeightedSeq: last weight is b
    have hrest_getLast :
        (match rest.getLast? with | some (w, _) => w | none => (0 : R)) = b := by
      have : rest.getLast? = some (b, y) := by
        simp only [rest]
        exact List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)
      rw [this]
    have hrest_len : rest.length = zs'.length + 1 := by simp [rest]
    have hright : affineOfBinary op
        (rightWeightedSeq op
          ((a, x) :: (0, z₁) :: (0, z₂) :: rest)) =
        op.binCombo (⅟(1 - op.u) * b) z₁ y := by
      simp only [rightWeightedSeq]
      rw [hrest_getLast]
      rw [hrest_map_snd]
      rw [hrest_len]
      -- Goal now involves:
      -- (1 - ⅟(1-u)*b, z₁) :: (replicate (zs'.length+1) 0 ++ [⅟(1-u)*b]).zip (z₂ :: zs' ++ [y])
      -- Split the zip using zip_append
      conv_lhs => rw [show z₂ :: (zs' ++ [y]) =
        (z₂ :: zs') ++ [y] from by rw [List.cons_append]]
      rw [List.zip_append (by simp)]
      -- Now: (1-⅟(1-u)*b, z₁) :: zeros.zip(z₂::zs') ++ [(⅟(1-u)*b, y)]
      rw [zip_replicate_zero_map (by simp)]
      -- Now: (1-⅟(1-u)*b, z₁) :: (z₂::zs').map(0,·) ++ [(⅟(1-u)*b, y)]
      -- This is affineOfBinary_doubleton_padded_end with zs = z₂::zs'
      -- Transform to the right form for the IH
      simp only [List.map_cons, List.cons_append]
      -- IH: fewer zeros (z₂::zs' has length zs'.length+1, original zs had length zs'.length+2)
      have hlt : (z₂ :: zs').length < n := by
        simp only [List.length_cons] at hlen ⊢
        omega
      exact ih (z₂ :: zs').length hlt _ _ _ _ (z₂ :: zs') (by ring) rfl
    rw [hleft, hright]
    exact doubleton_padded_end_algebra op a b x z₁ y hab

/-- Adding a zero-weight point at the front doesn't change the affine combination (Field version).
    This is the key zero-insertion invariance lemma. -/
theorem affineOfBinary_cons_zero_field [Inhabited M] (op : BinaryConvexOp R M)
    (x : M) (ws : WeightedSeq R M) (hvalid : ws.totalWeight = 1) (hne : ws ≠ []) :
    affineOfBinary op ((0, x) :: ws) = affineOfBinary op ws := by
  induction h : ws.length using Nat.strongRecOn generalizing x ws with
  | _ n ih =>
  match ws, h with
  | [], _ => exact absurd rfl hne
  | [(w, y)], _ =>
    simp only [affineOfBinary]
    have hw : w = 1 := by simpa [WeightedSeq.totalWeight] using hvalid
    subst hw
    exact op.binCombo_one x y
  | [(w₁, y₁), (w₂, y₂)], _ =>
    simp only [affineOfBinary,
      List.map_nil, List.dropLast, List.sum_nil,
      List.getLast?_nil, List.replicate, List.nil_append,
      List.zip_cons_cons, List.zip_nil_left, mul_zero, sub_zero,
      List.length_nil]
    rw [op.binCombo_one x y₁]
    have h := op.binCombo_entropic
      (1 - op.u) 0 (⅟(1 - op.u) * w₂) y₁ y₂
    rw [op.binCombo_zero y₁ y₂] at h; rw [h]; congr 1
    simp only [mul_zero, zero_add, ← mul_assoc,
      mul_invOf_self, one_mul]
  | (w₁, y₁) :: (w₂, y₂) :: (w₃, y₃) :: rest', hlen =>
    -- n ≥ 4 case: decompose both sides, apply IH to leftWS, use doubleton_padded_end for rightWS
    match rest' with
    | [] =>
      -- n = 4: ws = [(w₁,y₁), (w₂,y₂), (w₃,y₃)]
      -- Inline cons_zero_field_algebra: pad each inner binCombo to 3-element sequences
      -- over (y₁,y₂,y₃), apply affineOfBinary_linear, show both sides equal A([(w₁,y₁),(w₂,y₂),(w₃,y₃)]).
      -- Step 1: Decompose both sides
      rw [affineOfBinary_decompose op 0 x w₁ y₁ w₂ y₂ [(w₃, y₃)]]
      have hleftWS : leftWeightedSeq op ((0, x) :: (w₁, y₁) :: (w₂, y₂) :: [(w₃, y₃)]) =
          [(⅟op.u * 0, x), (1 - ⅟op.u * 0 - [⅟op.u * w₂].sum, y₁), (⅟op.u * w₂, y₂)] := by
        simp [leftWeightedSeq]
      have hrightWS : rightWeightedSeq op ((0, x) :: (w₁, y₁) :: (w₂, y₂) :: [(w₃, y₃)]) =
          [(1 - ⅟(1 - op.u) * w₃, y₁), (0, y₂), (⅟(1 - op.u) * w₃, y₃)] := by
        simp [rightWeightedSeq]
      rw [hleftWS, hrightWS]
      simp only [List.sum_cons, List.sum_nil, add_zero, mul_zero, sub_zero]
      -- Step 2: Apply IH to remove leading zero from leftWS
      have hn : n = 3 := by simpa [List.length_cons, List.length_nil] using hlen.symm
      have hleft_valid : WeightedSeq.totalWeight
          [(1 - ⅟op.u * w₂, y₁), (⅟op.u * w₂, y₂)] = 1 := by
        simp [WeightedSeq.totalWeight]
      rw [ih 2 (by omega) x _ hleft_valid (List.cons_ne_nil _ _) rfl]
      -- Step 3: Evaluate A on 2-element lists as binCombo
      conv_lhs => rw [show affineOfBinary op [(1 - ⅟op.u * w₂, y₁), (⅟op.u * w₂, y₂)] =
        op.binCombo (⅟op.u * w₂) y₁ y₂ from by simp [affineOfBinary]]
      conv_lhs =>
        rw [show [(1 - ⅟(1 - op.u) * w₃, y₁), ((0 : R), y₂), (⅟(1 - op.u) * w₃, y₃)] =
          [(1 - ⅟(1 - op.u) * w₃, y₁)] ++ [y₂].map (fun z => ((0 : R), z)) ++
            [(⅟(1 - op.u) * w₃, y₃)] from by simp]
        rw [affineOfBinary_doubleton_padded_end op _ _ y₁ y₃ [y₂] (by ring)]
      rw [affineOfBinary_decompose op w₁ y₁ w₂ y₂ w₃ y₃ []]
      conv_rhs =>
        rw [show leftWeightedSeq op ((w₁, y₁) :: (w₂, y₂) :: [(w₃, y₃)]) =
          [(⅟op.u * w₁, y₁), (1 - ⅟op.u * w₁, y₂)] from by simp [leftWeightedSeq]]
        rw [show rightWeightedSeq op ((w₁, y₁) :: (w₂, y₂) :: [(w₃, y₃)]) =
          [(1 - ⅟(1 - op.u) * w₃, y₂), (⅟(1 - op.u) * w₃, y₃)] from by
            simp [rightWeightedSeq]]
        rw [show affineOfBinary op [(⅟op.u * w₁, y₁), (1 - ⅟op.u * w₁, y₂)] =
          op.binCombo (1 - ⅟op.u * w₁) y₁ y₂ from by simp [affineOfBinary]]
        rw [show affineOfBinary op [(1 - ⅟(1 - op.u) * w₃, y₂), (⅟(1 - op.u) * w₃, y₃)] =
          op.binCombo (⅟(1 - op.u) * w₃) y₂ y₃ from by simp [affineOfBinary]]
      -- Goal: C(1-u, C(⅟u*w₂,y₁,y₂), C(⅟(1-u)*w₃,y₁,y₃))
      --     = C(1-u, C(1-⅟u*w₁,y₁,y₂), C(⅟(1-u)*w₃,y₂,y₃))
      -- Inline cons_zero_field_algebra: pad each inner binCombo to 3-element sequences
      -- over (y₁,y₂,y₃), apply affineOfBinary_linear, show both sides equal
      -- A([(w₁,y₁),(w₂,y₂),(w₃,y₃)]).
      have hsum : w₁ + w₂ + w₃ = 1 := by
        have := hvalid; simp [WeightedSeq.totalWeight] at this; linarith
      have halg : op.binCombo (1 - op.u)
          (op.binCombo (⅟op.u * w₂) y₁ y₂)
          (op.binCombo (⅟(1 - op.u) * w₃) y₁ y₃) =
        op.binCombo (1 - op.u)
          (op.binCombo (1 - ⅟op.u * w₁) y₁ y₂)
          (op.binCombo (⅟(1 - op.u) * w₃) y₂ y₃) := by
        set a := ⅟op.u * w₂ with ha_def
        set b := ⅟(1 - op.u) * w₃ with hb_def
        -- LHS inner terms as affineOfBinary:
        have hL1 : op.binCombo a y₁ y₂ = affineOfBinary op [(1 - a, y₁), (a, y₂)] := by
          simp [affineOfBinary]
        have hL1_pad : affineOfBinary op [(1 - a, y₁), (a, y₂)] =
            affineOfBinary op [(1 - a, y₁), (a, y₂), (0, y₃)] := by
          rw [show [(1 - a, y₁), (a, y₂), (0, y₃)] =
            [(1 - a, y₁), (a, y₂)] ++ [(0, y₃)] from rfl]
          rw [affineOfBinary_append_zero op [(1 - a, y₁), (a, y₂)] y₃]
          · simp [WeightedSeq.totalWeight]
          · exact List.cons_ne_nil _ _
        have hL2 : op.binCombo b y₁ y₃ = affineOfBinary op [(1 - b, y₁), (b, y₃)] := by
          simp [affineOfBinary]
        have hL2_pad : affineOfBinary op [(1 - b, y₁), (b, y₃)] =
            affineOfBinary op [(1 - b, y₁), (0, y₂), (b, y₃)] := by
          rw [show [(1 - b, y₁), (0, y₂), (b, y₃)] =
            [(1 - b, y₁)] ++ [y₂].map (fun z => (0, z)) ++ [(b, y₃)] from by simp]
          rw [affineOfBinary_doubleton_padded_end op (1 - b) b y₁ y₃ [y₂] (by ring)]
          simp [affineOfBinary]
        have hLHS : op.binCombo (1 - op.u)
            (affineOfBinary op [(1 - a, y₁), (a, y₂), (0, y₃)])
            (affineOfBinary op [(1 - b, y₁), (0, y₂), (b, y₃)]) =
            affineOfBinary op (WeightedSeq.combineWeights (1 - op.u)
              [(1 - a, y₁), (a, y₂), (0, y₃)] [(1 - b, y₁), (0, y₂), (b, y₃)]) :=
          affineOfBinary_linear op (1 - op.u)
            [(1 - a, y₁), (a, y₂), (0, y₃)] [(1 - b, y₁), (0, y₂), (b, y₃)]
            (by simp) (by simp [WeightedSeq.samePoints])
        -- RHS inner terms:
        set c := 1 - ⅟op.u * w₁ with hc_def
        have hR1 : op.binCombo c y₁ y₂ = affineOfBinary op [(1 - c, y₁), (c, y₂)] := by
          simp [affineOfBinary]
        have hR1_pad : affineOfBinary op [(1 - c, y₁), (c, y₂)] =
            affineOfBinary op [(1 - c, y₁), (c, y₂), (0, y₃)] := by
          rw [show [(1 - c, y₁), (c, y₂), (0, y₃)] =
            [(1 - c, y₁), (c, y₂)] ++ [(0, y₃)] from rfl]
          rw [affineOfBinary_append_zero op [(1 - c, y₁), (c, y₂)] y₃]
          · simp [WeightedSeq.totalWeight]
          · exact List.cons_ne_nil _ _
        have hR2 : op.binCombo b y₂ y₃ = affineOfBinary op [(1 - b, y₂), (b, y₃)] := by
          simp [affineOfBinary]
        -- Key: use IH instead of affineOfBinary_cons_zero_field (breaks circularity)
        have hR2_pad : affineOfBinary op [(1 - b, y₂), (b, y₃)] =
            affineOfBinary op [(0, y₁), (1 - b, y₂), (b, y₃)] := by
          rw [ih 2 (by omega) y₁ [(1 - b, y₂), (b, y₃)]
            (by simp [WeightedSeq.totalWeight]) (List.cons_ne_nil _ _) rfl]
        have hRHS : op.binCombo (1 - op.u)
            (affineOfBinary op [(1 - c, y₁), (c, y₂), (0, y₃)])
            (affineOfBinary op [(0, y₁), (1 - b, y₂), (b, y₃)]) =
            affineOfBinary op (WeightedSeq.combineWeights (1 - op.u)
              [(1 - c, y₁), (c, y₂), (0, y₃)] [(0, y₁), (1 - b, y₂), (b, y₃)]) :=
          affineOfBinary_linear op (1 - op.u)
            [(1 - c, y₁), (c, y₂), (0, y₃)] [(0, y₁), (1 - b, y₂), (b, y₃)]
            (by simp) (by simp [WeightedSeq.samePoints])
        -- Chain the rewrites
        rw [hL1, hL1_pad, hL2, hL2_pad, hLHS]
        rw [hR1, hR1_pad, hR2, hR2_pad, hRHS]
        -- Show the two combineWeights results are equal
        -- Both combineWeights equal [(w₁,y₁),(w₂,y₂),(w₃,y₃)]
        have hua : op.u * a = w₂ := by rw [ha_def, ← mul_assoc, mul_invOf_self, one_mul]
        have hub : (1 - op.u) * b = w₃ := by rw [hb_def, ← mul_assoc, mul_invOf_self, one_mul]
        have huc : op.u * c = op.u - w₁ := by
          rw [hc_def]; ring_nf; rw [mul_invOf_self]; ring
        simp only [WeightedSeq.combineWeights, List.zipWith,
          sub_sub_cancel, mul_zero, add_zero, zero_add, mul_sub, mul_one]
        rw [hua, hub, huc]
        congr 1
        simp only [Prod.mk.injEq, List.cons.injEq, and_true]
        constructor <;> linarith
      exact halg
    | r₂ :: rest₂ =>
      -- n ≥ 5 case: ws = (w₁,y₁)::(w₂,y₂)::(w₃,y₃)::r₂::rest₂
      -- Strategy: Compute leftWS and rightWS explicitly, apply IH on leftWS
      -- (which has leading zero), pad the tail with (0,yₙ) via append_zero,
      -- apply affineOfBinary_linear, show combineWeights = ws.
      have hn : n = rest₂.length + 4 := by
        simp only [List.length_cons] at hlen; omega
      -- Define the concrete components
      set rest := (w₃, y₃) :: r₂ :: rest₂
      set mw := (w₂ :: rest.map Prod.fst).dropLast
      set mp := (y₂ :: rest.map Prod.snd).dropLast
      set sm := mw.map (⅟op.u * ·)
      have hmw_mp : mw.length = mp.length := by simp [mw, mp]
      have hsm_mp : sm.length = mp.length := by simp [sm, mw, mp]
      -- leftTail is what remains after removing the leading (0,x) from leftWS
      set leftTail : WeightedSeq R M := (1 - sm.sum, y₁) :: sm.zip mp
      -- Step 1: Compute leftWS explicitly
      have hleftWS : leftWeightedSeq op
          ((0, x) :: (w₁, y₁) :: (w₂, y₂) :: rest) =
          (0, x) :: leftTail := by
        simp only [leftWeightedSeq, mul_zero, sub_zero, leftTail, sm, mw, mp, rest]
      -- Step 2: Decompose LHS
      rw [affineOfBinary_decompose (op := op) (s₁ := 0) (x₁ := x)
        (s₂ := w₁) (x₂ := y₁) (s₃ := w₂) (x₃ := y₂)
        (rest := rest)]
      rw [hleftWS]
      -- Apply IH to remove leading zero
      have hleft_valid : WeightedSeq.totalWeight leftTail = 1 := by
        simp only [WeightedSeq.totalWeight, leftTail, List.map_cons, List.sum_cons, Prod.fst]
        rw [List.map_fst_zip (le_of_eq hsm_mp)]
        ring
      have hleft_ne : leftTail ≠ [] := List.cons_ne_nil _ _
      have hleft_lt : leftTail.length < n := by
        simp only [leftTail, List.length_cons, List.length_zip, hsm_mp, Nat.min_self]
        have hmp_len : mp.length = rest₂.length + 2 := by
          simp only [mp, rest, List.length_dropLast, List.length_cons, List.length_map]; omega
        rw [hmp_len]; omega
      rw [ih leftTail.length hleft_lt x leftTail hleft_valid hleft_ne rfl]
      -- Goal: C(1-u, A(leftTail), A(rightWS)) = A(ws)
      -- Step 3: Pad leftTail with (0, yₙ)
      set yₙ := (r₂ :: rest₂).getLast (List.cons_ne_nil _ _) |>.2
      have hpad : affineOfBinary op leftTail =
          affineOfBinary op (leftTail ++ [(0, yₙ)]) := by
        rw [affineOfBinary_append_zero op leftTail yₙ hleft_valid hleft_ne]
      rw [hpad]
      -- Step 4: Compute rightWS explicitly
      set wₙ := ((r₂ :: rest₂).getLast (List.cons_ne_nil _ _)).1
      set bLast := ⅟(1 - op.u) * wₙ
      set b₁ := 1 - bLast
      have hrightWS : rightWeightedSeq op
          ((0, x) :: (w₁, y₁) :: (w₂, y₂) :: rest) =
          (b₁, y₁) :: (List.replicate rest.length (0 : R) ++ [bLast]).zip
            (y₂ :: rest.map Prod.snd) := by
        simp only [rightWeightedSeq, rest]
        congr 1 <;> simp [b₁, bLast, wₙ]
      -- Step 5: Key fact: mp ++ [yₙ] = y₂ :: rest.map snd
      -- mp = (y₂ :: rest.map snd).dropLast and yₙ is the last point
      have hmp_yₙ : mp ++ [yₙ] = y₂ :: rest.map Prod.snd := by
        -- mp = (y₂ :: rest.map snd).dropLast by definition
        change (y₂ :: rest.map Prod.snd).dropLast ++ [yₙ] = _
        -- yₙ = (y₂ :: rest.map snd).getLast _
        have hne : (y₂ :: rest.map Prod.snd) ≠ [] := List.cons_ne_nil _ _
        suffices h : yₙ = (y₂ :: rest.map Prod.snd).getLast hne by
          rw [h, List.dropLast_append_getLast hne]
        -- getLast commutes with map Prod.snd
        simp only [yₙ, rest, List.map_cons]
        conv_rhs => rw [List.getLast_cons (List.cons_ne_nil _ _),
          List.getLast_cons (List.cons_ne_nil _ _)]
        -- Now: ((r₂::rest₂).getLast _).2 = (r₂.snd :: map snd rest₂).getLast _
        -- Prove by a local suffices to avoid capturing context in the IH
        suffices ∀ (a : R × M) (l : List (R × M)),
            ((a :: l).getLast (List.cons_ne_nil _ _)).2 =
            (a.2 :: l.map Prod.snd).getLast (List.cons_ne_nil _ _) from this r₂ rest₂
        intro a l
        induction l generalizing a with
        | nil => simp
        | cons b t ih =>
          simp only [List.getLast_cons (List.cons_ne_nil _ _), List.map_cons]
          exact ih b
      -- Step 6: Compute padded left sequence
      set leftPadded : WeightedSeq R M := leftTail ++ [(0, yₙ)]
      have hleftPadded : leftPadded = (1 - sm.sum, y₁) :: (sm.zip mp ++ [(0, yₙ)]) := by
        simp [leftPadded, leftTail]
      -- Step 7: Show same length
      have hrest_len : rest.length = rest₂.length + 2 := by
        simp [rest]
      have hmp_len : mp.length = rest₂.length + 2 := by
        simp only [mp, rest, List.length_dropLast, List.length_cons, List.length_map]; omega
      have hleftPadded_len : leftPadded.length = rest₂.length + 4 := by
        simp only [leftPadded, leftTail, List.length_append, List.length_cons,
          List.length_zip, hsm_mp, Nat.min_self, List.length_singleton, List.length_nil,
          hmp_len]
      -- rightWS length
      set rightWS := rightWeightedSeq op
        ((0, x) :: (w₁, y₁) :: (w₂, y₂) :: rest)
      have hrightWS_len : rightWS.length = rest₂.length + 4 := by
        rw [show rightWS = (b₁, y₁) :: (List.replicate rest.length (0 : R) ++ [bLast]).zip
            (y₂ :: rest.map Prod.snd) from hrightWS]
        simp only [List.length_cons, List.length_zip, List.length_append,
          List.length_replicate, List.length_singleton, List.length_map, hrest_len]
        omega
      have hlen_eq : leftPadded.length = rightWS.length := by
        rw [hleftPadded_len, hrightWS_len]
      -- Step 8: Show same points
      have hpts : leftPadded.samePoints rightWS := by
        simp only [WeightedSeq.samePoints, hleftPadded, hrightWS]
        simp only [List.map_cons, Prod.snd]
        congr 1
        -- Both sides equal y₂ :: rest.map snd
        -- LHS = map snd (sm.zip mp) ++ [yₙ] = mp ++ [yₙ] = y₂ :: rest.map snd
        have lhs_eq : List.map Prod.snd (sm.zip mp ++ [(0, yₙ)]) =
            y₂ :: List.map Prod.snd rest := by
          rw [List.map_append, List.map_snd_zip (le_of_eq hsm_mp.symm)]
          simpa using hmp_yₙ
        -- RHS = y₂ :: rest.map snd (map snd of a zip with ≤ length condition)
        have rhs_eq : List.map Prod.snd
            ((List.replicate rest.length 0 ++ [bLast]).zip
              (y₂ :: List.map Prod.snd rest)) =
            y₂ :: List.map Prod.snd rest := by
          apply List.map_snd_zip
          simp [List.length_append, List.length_replicate]
        rw [lhs_eq, rhs_eq]
      -- Step 9: Apply affineOfBinary_linear
      rw [affineOfBinary_linear op (1 - op.u) leftPadded rightWS hlen_eq hpts]
      -- Step 10: Show combineWeights (1-u) leftPadded rightWS = ws
      -- It suffices to show the lists are equal
      congr 1
      -- Step 10: Show combineWeights (1 - u) leftPadded rightWS = ws
      -- Unfold definitions
      simp only [hleftPadded, hrightWS, WeightedSeq.combineWeights, List.zipWith_cons_cons]
      -- Head element: ((1-(1-u))*(1-sm.sum) + (1-u)*b₁, y₁) should = (w₁, y₁)
      -- Arithmetic helpers
      have hu_inv : op.u * ⅟op.u = 1 := mul_invOf_self op.u
      have h1u_inv : (1 - op.u) * ⅟(1 - op.u) = 1 := mul_invOf_self (1 - op.u)
      -- Prove the head weight = w₁
      -- (1-(1-u))*(1-sm.sum) + (1-u)*(1-bLast)
      -- = u*(1 - ⅟u * mw.sum) + (1-u)*(1 - ⅟(1-u)*wₙ)
      -- = u - mw.sum + (1-u) - wₙ = 1 - mw.sum - wₙ
      -- mw.sum + wₙ = (w₂::rest.map fst).sum = 1 - w₁
      -- So head weight = 1 - (1-w₁) = w₁
      have hsm_eq : sm.sum = ⅟op.u * mw.sum := by
        change (mw.map (⅟op.u * ·)).sum = ⅟op.u * mw.sum
        induction mw with
        | nil => simp
        | cons a t ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih, mul_add]
      -- Key fact: mw ++ [wₙ] = w₂ :: rest.map fst
      have hmw_wₙ_eq : mw ++ [wₙ] = w₂ :: List.map Prod.fst rest := by
        have hwₙ_eq : wₙ = (w₂ :: List.map Prod.fst rest).getLast (List.cons_ne_nil _ _) := by
          simp only [wₙ, rest, List.map_cons]
          rw [List.getLast_cons (List.cons_ne_nil _ _),
            List.getLast_cons (List.cons_ne_nil _ _)]
          suffices ∀ (a : R × M) (l : List (R × M)),
              ((a :: l).getLast (List.cons_ne_nil _ _)).1 =
              (a.1 :: l.map Prod.fst).getLast (List.cons_ne_nil _ _) from this r₂ rest₂
          intro a l; induction l generalizing a with
          | nil => simp
          | cons b t ih =>
            simp only [List.getLast_cons (List.cons_ne_nil _ _), List.map_cons]; exact ih b
        simp only [mw, hwₙ_eq]
        exact List.dropLast_append_getLast (List.cons_ne_nil _ _)
      -- Key fact about mw.sum + wₙ
      have hmw_wₙ_sum : mw.sum + wₙ + w₁ = 1 := by
        have hfst_sum : (w₂ :: List.map Prod.fst rest).sum = 1 - w₁ := by
          have := hvalid
          simp only [WeightedSeq.totalWeight, List.map_cons, List.sum_cons] at this
          simp only [List.sum_cons]
          linarith
        rw [show mw.sum + wₙ = (mw ++ [wₙ]).sum from by
            rw [List.sum_append, List.sum_singleton]]
        rw [hmw_wₙ_eq, hfst_sum]
        linarith
      -- Now prove the head pair and tail
      congr 1
      · -- Head pair: (u*(1-sm.sum) + (1-u)*b₁, y₁) = (w₁, y₁)
        congr 1
        -- The weight is (1-(1-u))*(1-sm.sum) + (1-u)*b₁
        -- b₁ = 1 - ⅟(1-u)*wₙ, sm.sum = ⅟u * mw.sum
        -- Expand and simplify using invOf cancellation
        calc (1 - (1 - op.u)) * (1 - sm.sum) + (1 - op.u) * b₁
            = op.u * (1 - sm.sum) + (1 - op.u) * (1 - ⅟(1 - op.u) * wₙ) := by
              ring
          _ = op.u - op.u * sm.sum + ((1 - op.u) - (1 - op.u) * (⅟(1 - op.u) * wₙ)) := by
              ring
          _ = op.u - op.u * (⅟op.u * mw.sum) +
              ((1 - op.u) - (1 - op.u) * ⅟(1 - op.u) * wₙ) := by
              rw [hsm_eq, mul_assoc]
          _ = op.u - mw.sum + ((1 - op.u) - wₙ) := by
              rw [← mul_assoc, hu_inv, one_mul, h1u_inv, one_mul]
          _ = 1 - (mw.sum + wₙ) := by ring
          _ = w₁ := by linarith [hmw_wₙ_sum]
      · -- Tail: zipWith ... = (w₂, y₂) :: rest
        -- Rewrite the right zip using hmp_yₙ
        have hrest_mp_len : rest.length = mp.length := by
          rw [hrest_len, hmp_len]
        rw [show List.replicate rest.length (0 : R) = List.replicate mp.length (0 : R)
          from by rw [hrest_mp_len]]
        rw [← hmp_yₙ, List.zip_append (by simp)]
        -- Split zipWith over append
        rw [List.zipWith_append (by simp [hsm_mp])]
        -- Simplify the singleton zipWith on the right
        simp only [List.zip_cons_cons, List.zip_nil_right, List.zipWith_cons_cons,
          List.zipWith_nil_left, List.append_nil]
        -- Now: zipWith f (sm.zip mp) ((repl 0).zip mp) ++
        --      [((1-(1-u))*0 + (1-u)*bLast, yₙ)] = (w₂,y₂)::rest
        -- Simplify the last element weight
        conv_lhs => rw [show (1 - (1 - op.u)) * (0 : R) + (1 - op.u) * bLast = wₙ from by
          simp only [mul_zero, zero_add, bLast, ← mul_assoc, h1u_inv, one_mul]]
        -- Now: zipWith f (sm.zip mp) ((repl 0).zip mp) ++ [(wₙ, yₙ)] = (w₂,y₂)::rest
        -- Show the main zipWith = mw.zip mp
        suffices hzw : List.zipWith
            (fun x x_1 ↦ ((1 - (1 - op.u)) * x.1 + (1 - op.u) * x_1.1, x.2))
            (sm.zip mp) ((List.replicate mp.length (0 : R)).zip mp) =
            mw.zip mp by
          rw [hzw]
          -- mw.zip mp ++ [(wₙ, yₙ)] = (w₂,y₂) :: rest
          have := (List.zip_append hmw_mp (r₁ := [wₙ]) (r₂ := [yₙ])).symm
          simp only [List.zip_cons_cons, List.zip_nil_right] at this
          rw [this, hmw_wₙ_eq, hmp_yₙ]
          simp only [List.zip_cons_cons, List.cons.injEq, true_and]
          rw [← List.unzip_fst, ← List.unzip_snd, List.zip_unzip]
        -- Prove zipWith f (sm.zip mp) ((repl 0).zip mp) = mw.zip mp
        -- sm = mw.map (⅟u * ·), so proceed by induction on mw/mp
        change List.zipWith
            (fun x x_1 ↦ ((1 - (1 - op.u)) * x.1 + (1 - op.u) * x_1.1, x.2))
            ((mw.map (⅟op.u * ·)).zip mp)
            ((List.replicate mp.length (0 : R)).zip mp) =
            mw.zip mp
        suffices ∀ (ws : List R) (ps : List M), ws.length = ps.length →
            List.zipWith (fun x x_1 ↦ ((1 - (1 - op.u)) * x.1 + (1 - op.u) * x_1.1, x.2))
              ((ws.map (⅟op.u * ·)).zip ps) ((List.replicate ps.length (0 : R)).zip ps)
            = ws.zip ps by
          exact this mw mp hmw_mp
        intro ws ps hlen
        induction ws generalizing ps with
        | nil => simp
        | cons w wt ih =>
          match ps, hlen with
          | p :: pt, hlen => ?_
          simp only [List.map_cons, List.zip_cons_cons, List.length_cons, List.replicate,
            List.replicate_succ, List.zipWith_cons_cons, List.cons.injEq]
          have hlen' : wt.length = pt.length := by
            simp only [List.length_cons] at hlen; omega
          refine ⟨?_, ih pt hlen'⟩
          simp only [Prod.mk.injEq, and_true]
          have : (1 - (1 - op.u)) * (⅟op.u * w) + (1 - op.u) * 0 = w := by
            rw [mul_zero, add_zero, show (1 - (1 - op.u)) = op.u from by ring]
            rw [← mul_assoc, mul_invOf_self, one_mul]
          exact this

/-- Appending multiple zero-weight points at the end doesn't change the affine combination. -/
theorem affineOfBinary_append_zero_many [Inhabited M] (op : BinaryConvexOp R M)
    (ws : WeightedSeq R M) (xs : List M) (hvalid : ws.totalWeight = 1) (hne : ws ≠ []) :
    affineOfBinary op (ws ++ xs.map fun x => (0, x)) = affineOfBinary op ws := by
  induction xs generalizing ws with
  | nil => simp
  | cons x xs ih =>
    rw [show (x :: xs).map (fun x => ((0 : R), x)) = [(0, x)] ++ xs.map (fun x => (0, x))
      from by simp]
    rw [← List.append_assoc]
    have hvalid' : (ws ++ [(0, x)]).totalWeight = 1 := by
      unfold WeightedSeq.totalWeight at hvalid ⊢
      simp only [List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      linarith
    have hne' : ws ++ [(0, x)] ≠ [] := by simp
    rw [ih (ws ++ [(0, x)]) hvalid' hne', affineOfBinary_append_zero op ws x hvalid hne]

/-- Prepending multiple zero-weight points at the front doesn't change the affine combination. -/
theorem affineOfBinary_cons_zero_many [Inhabited M] (op : BinaryConvexOp R M)
    (xs : List M) (ws : WeightedSeq R M) (hvalid : ws.totalWeight = 1) (hne : ws ≠ []) :
    affineOfBinary op (xs.map (fun x => ((0 : R), x)) ++ ws) = affineOfBinary op ws := by
  induction xs generalizing ws with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.cons_append]
    have hvalid' : WeightedSeq.totalWeight (xs.map (fun x => ((0 : R), x)) ++ ws) = 1 := by
      unfold WeightedSeq.totalWeight at hvalid ⊢
      rw [List.map_append, List.sum_append, List.map_map]
      simp only [Function.comp_def]
      have : (xs.map (fun (_ : M) => (0 : R))).sum = 0 := by
        induction xs with
        | nil => simp
        | cons _ _ ih₂ => simp_all
      rw [this, zero_add, hvalid]
    have hne' : xs.map (fun x => ((0 : R), x)) ++ ws ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ hne
    rw [affineOfBinary_cons_zero_field op x _ hvalid' hne',
      ih ws hvalid hne]

/-- Position-0 swap for a triple: A([(a,x),(b,y),(c,z)]) = A([(b,y),(a,x),(c,z)]).
    Proof: decompose both sides, pad to common ordering, apply linear.
    Both sides equal A([(b,y),(a,x),(c,z)]) via the padding+linear technique. -/
private theorem affineOfBinary_swap_triple [Inhabited M] (op : BinaryConvexOp R M)
    (a b c : R) (x y z : M) (hvalid : a + b + c = 1) :
    affineOfBinary op [(a, x), (b, y), (c, z)] =
    affineOfBinary op [(b, y), (a, x), (c, z)] := by
  -- Decompose LHS, pad sub-sequences to common ordering [(b,y),(a,x),(c,z)], apply linear.
  -- The RHS is already [(b,y),(a,x),(c,z)] by definition.
  set invU := ⅟op.u
  set inv1mU := ⅟(1 - op.u)
  have hu_ne : op.u ≠ 0 := Invertible.ne_zero op.u
  have h1mu_ne : (1 : R) - op.u ≠ 0 := Invertible.ne_zero (1 - op.u)
  set target : WeightedSeq R M := [(b, y), (a, x), (c, z)]
  set padL : WeightedSeq R M := [(1 - invU * a, y), (invU * a, x), (0, z)]
  set padR : WeightedSeq R M := [(1 - inv1mU * c, y), (0, x), (inv1mU * c, z)]
  have hmulU : op.u * a + op.u * b + op.u * c = op.u := by
    have := congr_arg (op.u * ·) hvalid
    simp only [mul_add, mul_one] at this; linarith
  have hmul1mU : (1 - op.u) * a + (1 - op.u) * b + (1 - op.u) * c = 1 - op.u := by
    have := congr_arg ((1 - op.u) * ·) hvalid
    simp only [mul_add, mul_one] at this; linarith
  have hcombL : padL.combineWeights (1 - op.u) padR = target := by
    simp only [padL, padR, target, WeightedSeq.combineWeights, List.zipWith]
    simp only [invU, inv1mU, invOf_eq_inv]
    refine List.cons_eq_cons.mpr ⟨Prod.ext ?_ rfl,
      List.cons_eq_cons.mpr ⟨Prod.ext ?_ rfl,
        List.cons_eq_cons.mpr ⟨Prod.ext ?_ rfl, rfl⟩⟩⟩
    all_goals (simp only []; field_simp [hu_ne, h1mu_ne]; linarith [hmulU, hmul1mU])
  -- Show LHS = A(target) via decompose → pad → linear → hcombL
  suffices affineOfBinary op [(a, x), (b, y), (c, z)] = affineOfBinary op target by rw [this]
  rw [affineOfBinary_decompose op a x b y c z []]
  simp only [leftWeightedSeq, rightWeightedSeq,
    List.map, List.dropLast, List.sum_nil, List.getLast?_nil,
    List.zip, List.replicate, List.length_nil,
    List.nil_append, sub_zero, List.zipWith]
  simp only [show ⅟op.u = invU from rfl, show ⅟(1 - op.u) = inv1mU from rfl]
  conv_lhs =>
    rw [show affineOfBinary op [(invU * a, x), (1 - invU * a, y)] =
        op.binCombo (1 - invU * a) x y from by simp [affineOfBinary]]
    rw [show affineOfBinary op [(1 - inv1mU * c, y), (inv1mU * c, z)] =
        op.binCombo (inv1mU * c) y z from by simp [affineOfBinary]]
  have hpadL : op.binCombo (1 - invU * a) x y = affineOfBinary op padL := by
    rw [show op.binCombo (1 - invU * a) x y =
        affineOfBinary op [(invU * a, x), (1 - invU * a, y)] from by simp [affineOfBinary]]
    rw [affineOfBinary_swap_two op (invU * a) (1 - invU * a) x y (by ring)]
    rw [← affineOfBinary_append_zero op [(1 - invU * a, y), (invU * a, x)] z
        (by simp [WeightedSeq.totalWeight]) (by simp)]
    simp only [padL, List.cons_append, List.nil_append]
  have hpadR : op.binCombo (inv1mU * c) y z = affineOfBinary op padR := by
    rw [← affineOfBinary_doubleton_padded_end op (1 - inv1mU * c) (inv1mU * c) y z [x] (by ring)]
    simp only [padR, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [hpadL, hpadR]
  rw [affineOfBinary_linear op (1 - op.u) padL padR
      (by simp [padL, padR]) (by simp [padL, padR, WeightedSeq.samePoints])]
  rw [hcombL]

/-- Combining scaled weights with zero weights recovers the original weights.
    zipWith((1-(1-u))*w₁+(1-u)*w₂, .2) on (invU*w,p).zip and (0,p).zip gives (w,p).zip.
    Here u*(invU*w) + (1-u)*0 = w since u*invU = 1. -/
private theorem combineWeights_scale_zero_append
    (u invU inv1mU : R) (hmulU : u * invU = 1) (hmul1mU : (1 - u) * inv1mU = 1)
    (ws : List R) (ps : List M) (hlen : ws.length = ps.length)
    (sₙ : R) (xₙ : M) :
    List.zipWith (fun x₁ x₂ => ((1 - (1 - u)) * x₁.1 + (1 - u) * x₂.1, x₁.2))
      ((ws.map (invU * ·)).zip ps ++ [(0, xₙ)])
      (ps.map (fun p => ((0 : R), p)) ++ [(inv1mU * sₙ, xₙ)]) =
    ws.zip ps ++ [(sₙ, xₙ)] := by
  rw [List.zipWith_append (by simp [hlen])]
  congr 1
  · -- Middle part: zipWith on scaled and zeros
    induction ws generalizing ps with
    | nil => cases ps <;> simp_all
    | cons w ws' ih =>
      cases ps with
      | nil => simp at hlen
      | cons p ps' =>
        simp only [List.map_cons, List.zip_cons_cons, List.zipWith_cons_cons, List.cons.injEq]
        refine ⟨Prod.ext ?_ rfl, ih ps' (by simp at hlen; exact hlen)⟩
        simp only [mul_zero, add_zero]
        rw [show (1 - (1 - u)) = u from by ring, ← mul_assoc, hmulU, one_mul]
  · -- Last element: (1-u)*inv1mU*sₙ = sₙ
    simp only [List.zipWith, List.cons.injEq, and_true]
    refine Prod.ext ?_ rfl
    simp only [Prod.fst]
    rw [show (1 - (1 - u)) * 0 + (1 - u) * (inv1mU * sₙ) =
        (1 - u) * inv1mU * sₙ from by ring]
    rw [hmul1mU, one_mul]

/-- Position-0 swap for a weighted sequence of any length ≥ 2.
    `A([(a,x),(b,y)] ++ ws) = A([(b,y),(a,x)] ++ ws)`.
    Proof: by strong induction on length.
    - n=2: swap_two
    - n=3: swap_triple
    - n≥4: decompose LHS, pad leftWS (using IH for position-0 swap) and rightWS
      (using doubleton_padded_end) to n elements, apply linear. -/
private theorem affineOfBinary_swap_zero [Inhabited M] (op : BinaryConvexOp R M)
    (a b : R) (x y : M) (ws : WeightedSeq R M)
    (hvalid : WeightedSeq.totalWeight ((a, x) :: (b, y) :: ws) = 1) :
    affineOfBinary op ((a, x) :: (b, y) :: ws) =
    affineOfBinary op ((b, y) :: (a, x) :: ws) := by
  induction h : ws.length using Nat.strongRecOn generalizing a b x y ws with
  | _ n ih =>
  match ws, h with
  | [], _ =>
    -- n = 2: use swap_two
    have hab : a + b = 1 := by simpa [WeightedSeq.totalWeight] using hvalid
    exact affineOfBinary_swap_two op a b x y hab
  | [(c, z)], _ =>
    -- n = 3: use swap_triple
    have habc : a + b + c = 1 := by
      have := hvalid; simp [WeightedSeq.totalWeight] at this; linarith
    exact affineOfBinary_swap_triple op a b c x y z habc
  | (s₃, x₃) :: r₁ :: rest', hlen =>
    -- n ≥ 4: use padding+linear technique.
    -- Decompose LHS, pad leftWS (swap via IH, append zero) and rightWS
    -- (insert zero via doubleton_padded_end) to n elements in target ordering
    -- [(b,y),(a,x),(s₃,x₃),...], then apply linear.
    set rest := r₁ :: rest'
    set invU := ⅟op.u
    set inv1mU := ⅟(1 - op.u)
    have hu_ne : op.u ≠ 0 := Invertible.ne_zero op.u
    have h1mu_ne : (1 : R) - op.u ≠ 0 := Invertible.ne_zero (1 - op.u)
    -- Step 1: Decompose LHS
    rw [affineOfBinary_decompose op a x b y s₃ x₃ rest]
    -- Step 2: Compute leftWS and rightWS explicitly
    set middleWeights := (s₃ :: rest.map Prod.fst).dropLast
    set scaledMiddle := middleWeights.map (invU * ·)
    set middlePoints := (x₃ :: rest.map Prod.snd).dropLast
    set slackL := 1 - invU * a - scaledMiddle.sum
    -- Extract last weight
    set sₙ := match rest.getLast? with
      | some (w, _) => w
      | none => s₃
    set bLast := inv1mU * sₙ
    -- Show leftWS and rightWS
    have hleftWS : leftWeightedSeq op ((a, x) :: (b, y) :: (s₃, x₃) :: rest) =
        (invU * a, x) :: (slackL, y) :: scaledMiddle.zip middlePoints := by
      simp [leftWeightedSeq, invU, slackL, middleWeights, scaledMiddle, middlePoints]
    have hrightWS : rightWeightedSeq op ((a, x) :: (b, y) :: (s₃, x₃) :: rest) =
        (1 - bLast, y) :: (List.replicate rest.length (0 : R) ++ [bLast]).zip
          (x₃ :: rest.map Prod.snd) := by
      simp [rightWeightedSeq, inv1mU, bLast, sₙ]
    rw [hleftWS, hrightWS]
    -- Step 3: Apply IH to swap leftWS at position 0
    have hrest_pos : 0 < rest.length := by simp [rest]
    have hn_ge : n ≥ 2 := by simp only [List.length_cons] at hlen; omega
    have hmw_len : middleWeights.length = rest.length := by
      simp only [middleWeights, List.length_dropLast, List.length_cons, List.length_map]
      omega
    have hmp_len : middlePoints.length = rest.length := by
      simp only [middlePoints, List.length_dropLast, List.length_cons, List.length_map]
      omega
    have hleftWS_len : (scaledMiddle.zip middlePoints).length = n - 1 := by
      simp only [List.length_zip, scaledMiddle, List.length_map, hmw_len, hmp_len, Nat.min_self]
      simp only [List.length_cons] at hlen; omega
    have hleftWS_valid : WeightedSeq.totalWeight
        ((invU * a, x) :: (slackL, y) :: scaledMiddle.zip middlePoints) = 1 := by
      simp only [WeightedSeq.totalWeight, List.map_cons, List.sum_cons]
      -- Goal: invU*a + slackL + (scaledMiddle.zip middlePoints).map fst .sum = 1
      -- (zip middlePoints).map fst = scaledMiddle (since lengths match)
      have hzip_fst : (scaledMiddle.zip middlePoints).map Prod.fst = scaledMiddle := by
        rw [List.map_zip_fst (by simp [scaledMiddle, hmw_len, hmp_len] :
          scaledMiddle.length ≤ middlePoints.length)]
      rw [hzip_fst]
      simp [slackL]
      ring
    have hih : affineOfBinary op
        ((invU * a, x) :: (slackL, y) :: scaledMiddle.zip middlePoints) =
        affineOfBinary op
        ((slackL, y) :: (invU * a, x) :: scaledMiddle.zip middlePoints) := by
      apply ih (scaledMiddle.zip middlePoints).length
      · rw [hleftWS_len]; simp only [List.length_cons] at hlen; omega
      · exact hleftWS_valid
      · rfl
    rw [hih]
    -- Step 4: Define padL and padR with target point ordering (y, x, x₃, ..., xₙ)
    set xₙ := (x₃ :: rest.map Prod.snd).getLast (by simp)
    set allMiddlePoints := (x₃ :: rest.map Prod.snd).dropLast
    -- padL = swapped leftWS ++ [(0, xₙ)]
    set padL : WeightedSeq R M :=
      ((slackL, y) :: (invU * a, x) :: scaledMiddle.zip middlePoints) ++ [(0, xₙ)]
    -- padR = [(1-bLast, y), (0, x)] ++ middlePoints.map (0, ·) ++ [(bLast, xₙ)]
    set padR : WeightedSeq R M :=
      [(1 - bLast, y)] ++ ((x :: middlePoints).map fun p => ((0 : R), p)) ++ [(bLast, xₙ)]
    -- Step 5: Show A(swapped leftWS) = A(padL) via append_zero
    have hpadL : affineOfBinary op
        ((slackL, y) :: (invU * a, x) :: scaledMiddle.zip middlePoints) =
        affineOfBinary op padL := by
      symm
      rw [show padL = ((slackL, y) :: (invU * a, x) :: scaledMiddle.zip middlePoints) ++
          [(0, xₙ)] from rfl]
      have hswap_valid : WeightedSeq.totalWeight
          ((slackL, y) :: (invU * a, x) :: scaledMiddle.zip middlePoints) = 1 := by
        simp only [WeightedSeq.totalWeight, List.map_cons, List.sum_cons] at hleftWS_valid ⊢
        linarith
      exact affineOfBinary_append_zero op _ xₙ hswap_valid (by simp)
    -- Step 6: Show A(rightWS) = A(padR) via doubleton_padded_end
    have hpadR : affineOfBinary op
        ((1 - bLast, y) :: (List.replicate rest.length (0 : R) ++ [bLast]).zip
          (x₃ :: rest.map Prod.snd)) =
        affineOfBinary op padR := by
      -- Both sides equal C(bLast, y, xₙ) via doubleton_padded_end
      have hab : (1 - bLast) + bLast = 1 := by ring
      -- Massage rightWS into doubleton_padded_end form
      have hright_eq : (1 - bLast, y) :: (List.replicate rest.length (0 : R) ++ [bLast]).zip
          (x₃ :: rest.map Prod.snd) =
          [(1 - bLast, y)] ++ allMiddlePoints.map (fun z => ((0 : R), z)) ++
          [(bLast, xₙ)] := by
        simp only [List.singleton_append, List.cons_append, List.cons.injEq, true_and]
        rw [show allMiddlePoints = (x₃ :: rest.map Prod.snd).dropLast from rfl]
        -- Need: (replicate n 0 ++ [bLast]).zip (x₃ :: rest.map snd)
        --     = (x₃ :: rest.map snd).dropLast.map (0, ·) ++ [(bLast, xₙ)]
        set pts := x₃ :: rest.map Prod.snd
        have hpts_ne : pts ≠ [] := List.cons_ne_nil _ _
        -- Split zip as dropLast ++ [last]
        rw [List.zip_append (by simp [pts])]
        congr 1
        · -- replicate.zip(dropLast) = dropLast.map(0, ·)
          rw [zip_replicate_zero_map (by simp [pts, hmw_len, hmp_len, middlePoints]; omega)]
        · -- [bLast].zip [getLast] = [(bLast, xₙ)]
          simp only [List.zip_cons_cons, List.zip_nil_left, List.cons.injEq, and_true,
            Prod.mk.injEq, and_true]
          exact (hmap_ne.symm ▸ (List.getLast_cons hmap_ne).symm ▸ rfl :
            (x₃ :: rest.map Prod.snd).getLast hpts_ne = xₙ).symm ▸ rfl
      -- Massage padR into doubleton_padded_end form
      have hpadR_eq : (padR : WeightedSeq R M) =
          [(1 - bLast, y)] ++ (x :: allMiddlePoints).map (fun z => ((0 : R), z)) ++
          [(bLast, xₙ)] := by
        simp [padR]
      rw [hright_eq, hpadR_eq,
          affineOfBinary_doubleton_padded_end op _ _ y xₙ allMiddlePoints hab,
          affineOfBinary_doubleton_padded_end op _ _ y xₙ (x :: allMiddlePoints) hab]
    rw [hpadL, hpadR]
    -- Step 7: Apply affineOfBinary_linear
    have hlen_eq : padL.length = padR.length := by
      simp only [padL, padR, List.length_append, List.length_cons, List.length_singleton,
        List.length_map, List.length_zip, scaledMiddle, List.length_map, hmw_len, hmp_len,
        Nat.min_self, List.length_nil]
      omega
    have hpts_eq : padL.samePoints padR := by
      simp only [WeightedSeq.samePoints, padL, padR]
      simp only [List.map_append, List.map_cons, List.map_singleton, List.singleton_append,
        List.cons_append, List.map_map]
      congr 1
      · -- y = y: trivial
        rfl
      congr 1
      · -- x = x: trivial
        rfl
      congr 1
      · -- (scaledMiddle.zip middlePoints).map snd = middlePoints.map (fun p => p)
        simp only [List.map_zip_snd (by rw [scaledMiddle]; simp [hmw_len, hmp_len] :
          middlePoints.length ≤ scaledMiddle.length), List.map_id]
      · -- [xₙ] = [xₙ]
        rfl
    rw [affineOfBinary_linear op (1 - op.u) padL padR hlen_eq hpts_eq]
    -- Step 8: Show combineWeights(1-u, padL, padR) = target
    suffices hcomb : WeightedSeq.combineWeights (1 - op.u) padL padR =
        (b, y) :: (a, x) :: (s₃, x₃) :: rest by
      rw [hcomb]
    -- Unfold combineWeights and padL, padR
    simp only [padL, padR, WeightedSeq.combineWeights]
    -- Simplify the RHS: [(1-bLast,y)] ++ map ... ++ ... = (1-bLast,y) :: ...
    simp only [List.singleton_append, List.map_cons, List.cons_append]
    -- Unfold first two cons of zipWith
    simp only [List.zipWith_cons_cons]
    -- Position 0 (y) and position 1 (x): show weight equalities
    refine List.cons_eq_cons.mpr ⟨Prod.ext ?_ rfl,
      List.cons_eq_cons.mpr ⟨Prod.ext ?_ rfl, ?_⟩⟩
    · -- Weight at position 0: u*slackL + (1-u)*(1-bLast) = b
      have hfactor : ∀ (c : R) (L : List R),
          (List.map (c * ·) L).sum = c * L.sum := by
        intro c L; induction L with
        | nil => simp
        | cons a t ih => simp [List.sum_cons, ih, mul_add]
      have hscaled_sum : scaledMiddle.sum = invU * middleWeights.sum := by
        simp only [scaledMiddle]; rw [hfactor]
      have hmiddle_plus_last : middleWeights.sum + sₙ = s₃ + (rest.map Prod.fst).sum := by
        -- Key: middleWeights = (s₃ :: rest.map Prod.fst).dropLast, sₙ = getLast of that list
        -- so dropLast.sum + getLast = sum = s₃ + rest.map fst .sum
        have dropLast_sum_getLast : ∀ (L : List R) (hL : L ≠ []),
            L.dropLast.sum + L.getLast hL = L.sum := by
          intro L hL
          induction L with
          | nil => exact absurd rfl hL
          | cons a t ih =>
            by_cases ht : t = []
            · simp [ht]
            · rw [List.getLast_cons ht]
              obtain ⟨b, t', rfl⟩ := List.exists_cons_of_ne_nil ht
              simp only [List.dropLast_cons₂, List.sum_cons, add_assoc]
              congr 1
              exact ih (List.cons_ne_nil b t')
        set L := s₃ :: rest.map Prod.fst
        have hL_ne : L ≠ [] := List.cons_ne_nil _ _
        have hsₙ_eq : sₙ = L.getLast hL_ne := by
          simp only [sₙ, L]
          have hmap_ne : rest.map Prod.fst ≠ [] := by simp [hrest_ne]
          rw [List.getLast_cons hmap_ne, List.getLast_map]
          simp [List.getLast?_eq_some_getLast hrest_ne]
        rw [hsₙ_eq, show middleWeights = L.dropLast from rfl,
            dropLast_sum_getLast L hL_ne]
        simp [L, List.sum_cons]
      have hmulU_scaled : op.u * scaledMiddle.sum = middleWeights.sum := by
        rw [hscaled_sum, ← mul_assoc]
        simp [invU, mul_invOf_self]
      have hmul1mU_sn : (1 - op.u) * (inv1mU * sₙ) = sₙ := by
        rw [show inv1mU = ⅟(1 - op.u) from rfl, ← mul_assoc, mul_invOf_self, one_mul]
      -- The goal is (1-(1-u))*(1-invU*a-scaledMiddle.sum)+(1-u)*(1-inv1mU*sₙ)=b
      -- = u - u*invU*a - u*scaledMiddle.sum + (1-u) - (1-u)*inv1mU*sₙ
      -- = u - a - middleWeights.sum + (1-u) - sₙ
      -- = 1 - a - middleWeights.sum - sₙ
      -- = 1 - a - (s₃ + rest.map fst .sum)  [by hmiddle_plus_last]
      -- = b  [by htw]
      have hmulU_invU_a : op.u * (invU * a) = a := by
        rw [show invU = ⅟op.u from rfl, ← mul_assoc, mul_invOf_self, one_mul]
      simp only [slackL, bLast]
      have htw := hvalid; simp [WeightedSeq.totalWeight] at htw
      nlinarith [hmulU_scaled, hmul1mU_sn, hmiddle_plus_last, hmulU_invU_a]
    · -- Weight at position 1: u*(invU*a) + (1-u)*0 = a
      simp only [invU, invOf_eq_inv]
      field_simp [hu_ne, h1mu_ne]; ring
    · -- Remaining positions: zipWith on middle ++ last = (s₃,x₃)::rest
      -- Use combineWeights_scale_zero_append to simplify
      have hmulU_inv : op.u * invU = 1 := by
        rw [show invU = ⅟op.u from rfl]; exact mul_invOf_self op.u
      have hmul1mU_inv : (1 - op.u) * inv1mU = 1 := by
        rw [show inv1mU = ⅟(1 - op.u) from rfl]; exact mul_invOf_self (1 - op.u)
      rw [show scaledMiddle = middleWeights.map (invU * ·) from rfl]
      rw [show bLast = inv1mU * sₙ from rfl]
      simp only [List.append_eq]
      rw [combineWeights_scale_zero_append op.u invU inv1mU hmulU_inv hmul1mU_inv
          middleWeights middlePoints (by rw [hmw_len, hmp_len]) sₙ xₙ]
      -- Goal: middleWeights.zip middlePoints ++ [(sₙ, xₙ)] = (s₃,x₃)::rest
      -- Key: zip(map fst L, map snd L) = L, and dropLast ++ [getLast] = L
      -- First: zip(map fst, map snd) recovers the original list of pairs
      have hzip_fst_snd : ∀ (L : List (R × M)),
          (L.map Prod.fst).zip (L.map Prod.snd) = L := by
        intro L; induction L with
        | nil => rfl
        | cons h t ih => simp [ih]
      -- zip commutes with dropLast (when lengths match)
      have hzip_dropLast : ∀ (L₁ : List R) (L₂ : List M),
          L₁.length = L₂.length →
          L₁.dropLast.zip L₂.dropLast = (L₁.zip L₂).dropLast := by
        intro L₁ L₂ hlen_eq
        exact (dropLast_zipWith Prod.mk L₁ L₂ hlen_eq).symm
      set fsts := s₃ :: rest.map Prod.fst
      set snds := x₃ :: rest.map Prod.snd
      have hfsts_snds_len : fsts.length = snds.length := by
        simp [fsts, snds]
      rw [show middleWeights = fsts.dropLast from rfl,
          show middlePoints = snds.dropLast from rfl]
      rw [hzip_dropLast fsts snds hfsts_snds_len]
      -- recover fsts.zip snds = (s₃,x₃)::rest
      have hrecover : fsts.zip snds = (s₃, x₃) :: rest := by
        simp only [fsts, snds, List.zip_cons_cons, List.cons.injEq, Prod.mk.injEq, true_and]
        exact hzip_fst_snd rest
      rw [hrecover]
      -- Goal: ((s₃,x₃)::rest).dropLast ++ [(sₙ, xₙ)] = (s₃,x₃)::rest
      -- sₙ is the fst of the last element, xₙ is the snd
      have hrest_ne : rest ≠ [] := List.cons_ne_nil r₁ rest'
      have hsₙ : sₙ = (rest.getLast hrest_ne).fst := by
        simp only [sₙ, List.getLast?_eq_getLast hrest_ne]
      have hmap_ne : rest.map Prod.snd ≠ [] := by simp [hrest_ne]
      have hxₙ : xₙ = (rest.getLast hrest_ne).snd := by
        simp only [xₙ]
        rw [List.getLast_cons hmap_ne, List.getLast_map]
      rw [hsₙ, hxₙ, Prod.eta]
      rw [show rest.getLast hrest_ne =
          ((s₃, x₃) :: rest).getLast (List.cons_ne_nil _ _) from by
        simp [List.getLast_cons hrest_ne]]
      exact List.dropLast_append_getLast (List.cons_ne_nil _ _)

/-- Helper for cons_strip: zipWith of zero-padded and scaled tail recovers the original tail. -/
private theorem zipWith_recover_tail (w : R) (tail : WeightedSeq R M)
    (h1w : (1 : R) - w ≠ 0) :
    List.zipWith (fun (p₁ : R × M) (p₂ : R × M) => ((1 - (1 - w)) * p₁.1 + (1 - w) * p₂.1, p₁.2))
      (tail.map fun (_, x) => ((0 : R), x))
      (WeightedSeq.scale ((1 - w)⁻¹) tail) = tail := by
  induction tail with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨wi, xi⟩ := hd
    simp only [List.map_cons, WeightedSeq.scale, List.zipWith_cons_cons]
    refine List.cons_eq_cons.mpr ⟨?_, ih⟩
    ext <;> simp only [Prod.fst, Prod.snd]
    rw [show (1 - (1 - w)) = w from by ring, mul_zero, zero_add,
        ← mul_assoc, mul_inv_cancel₀ h1w, one_mul]

/-- Strip the first element using the linearity lemma:
    `A((w,p) :: tail) = C(1-w, p, A(tail.scale (1-w)⁻¹))` when `w ≠ 1` and totalWeight = 1. -/
private theorem affineOfBinary_cons_strip [Inhabited M] (op : BinaryConvexOp R M)
    (w : R) (p : M) (tail : WeightedSeq R M)
    (hw : w ≠ 1)
    (hvalid : WeightedSeq.totalWeight ((w, p) :: tail) = 1) :
    affineOfBinary op ((w, p) :: tail) =
      op.binCombo (1 - w) p (affineOfBinary op (WeightedSeq.scale ((1 - w)⁻¹) tail)) := by
  have h1w : (1 : R) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have htail_tw : WeightedSeq.totalWeight tail = 1 - w := by
    simp only [WeightedSeq.totalWeight, List.map_cons, List.sum_cons] at hvalid ⊢; linarith
  have htail_ne : tail ≠ [] := by
    intro h; rw [h] at htail_tw; simp [WeightedSeq.totalWeight] at htail_tw
    exact h1w htail_tw.symm
  have scale_tw : ∀ (c : R) (ws : WeightedSeq R M),
      WeightedSeq.totalWeight (WeightedSeq.scale c ws) = c * WeightedSeq.totalWeight ws := by
    intro c ws; simp only [WeightedSeq.totalWeight, WeightedSeq.scale, List.map_map, Function.comp_def]
    induction ws with
    | nil => simp
    | cons hd tl ih => simp only [List.map_cons, List.sum_cons, mul_add]; rw [ih]
  have hscale_tw : WeightedSeq.totalWeight (WeightedSeq.scale ((1 - w)⁻¹) tail) = 1 := by
    rw [scale_tw, htail_tw, inv_mul_cancel₀ h1w]
  have hne_scale : WeightedSeq.scale ((1 - w)⁻¹) tail ≠ [] := by
    simp [WeightedSeq.scale, htail_ne]
  -- Define the two sequences
  set ws_A : WeightedSeq R M := (1, p) :: tail.map (fun (_, x) => ((0 : R), x)) with hws_A_def
  set ws_B : WeightedSeq R M := (0, p) :: WeightedSeq.scale ((1 - w)⁻¹) tail with hws_B_def
  -- Same points
  have hpts : ws_A.samePoints ws_B := by
    simp only [WeightedSeq.samePoints, hws_A_def, hws_B_def,
      List.map_cons, List.map_map, Function.comp_def, WeightedSeq.scale]
  -- Same length
  have hlen : ws_A.length = ws_B.length := by
    simp only [hws_A_def, hws_B_def, List.length_cons, List.length_map, WeightedSeq.scale]
  -- combineWeights recovers the original
  have hcomb : ws_A.combineWeights (1 - w) ws_B = (w, p) :: tail := by
    simp only [WeightedSeq.combineWeights, hws_A_def, hws_B_def, List.zipWith_cons_cons]
    congr 1
    · ext <;> simp [mul_one, mul_zero, sub_sub_cancel]
    · exact zipWith_recover_tail w tail h1w
  -- Apply linear
  rw [show (w, p) :: tail = ws_A.combineWeights (1 - w) ws_B from hcomb.symm]
  rw [← affineOfBinary_linear op (1 - w) ws_A ws_B hlen hpts]
  congr 1
  · -- A(ws_A) = A([(1,p)]) = p
    simp only [hws_A_def]
    have hws_A_form : (1, p) :: tail.map (fun (_, x) => ((0 : R), x)) =
        [(1, p)] ++ (tail.map Prod.snd).map (fun x => ((0 : R), x)) := by
      simp [List.map_map, Function.comp_def]
    rw [hws_A_form]
    rw [affineOfBinary_append_zero_many op [(1, p)] (tail.map Prod.snd)
      (by simp [WeightedSeq.totalWeight]) (by simp)]
    simp [affineOfBinary]
  · -- A(ws_B) = A((0,p) :: tail.scale c) = A(tail.scale c)
    simp only [hws_B_def]
    exact affineOfBinary_cons_zero_field op p _ hscale_tw hne_scale

/-- Permutation preserves totalWeight. -/
private theorem perm_totalWeight (ws₁ ws₂ : WeightedSeq R M) (h : ws₁.Perm ws₂) :
    ws₁.totalWeight = ws₂.totalWeight := by
  simp only [WeightedSeq.totalWeight]
  exact h.map Prod.fst |>.sum_eq

/-- Scaling distributes over scaling: scale a (scale b ws) = scale (a * b) ws. -/
private theorem scale_scale (a b : R) (ws : WeightedSeq R M) :
    WeightedSeq.scale a (WeightedSeq.scale b ws) = WeightedSeq.scale (a * b) ws := by
  simp [WeightedSeq.scale, List.map_map, Function.comp_def, mul_assoc]

/-- Generalized permutation invariance: for any scaling factor c such that
    c * totalWeight = 1, A(scale c ws₁) = A(scale c ws₂).
    Requires non-negativity of weights to handle the degenerate case c*w = 1. -/
private theorem affineOfBinary_perm_scaled [Inhabited M] (op : BinaryConvexOp R M)
    (ws₁ ws₂ : WeightedSeq R M) (hperm : ws₁.Perm ws₂)
    (c : R) (hc : c ≠ 0) (hctw : c * ws₁.totalWeight = 1)
    (hnn : ∀ e ∈ ws₁, 0 ≤ e.1) :
    affineOfBinary op (WeightedSeq.scale c ws₁) =
    affineOfBinary op (WeightedSeq.scale c ws₂) := by
  induction hperm generalizing c with
  | nil => rfl
  | cons x hperm ih =>
    rename_i l₁ l₂
    obtain ⟨w, p⟩ := x
    -- Don't simp hctw; keep it abstract
    have scale_tw : ∀ (c' : R) (ws : WeightedSeq R M),
        WeightedSeq.totalWeight (WeightedSeq.scale c' ws) =
        c' * WeightedSeq.totalWeight ws := by
      intro c' ws
      simp only [WeightedSeq.totalWeight, WeightedSeq.scale, List.map_map, Function.comp_def]
      induction ws with
      | nil => simp
      | cons hd tl ih₂ => simp only [List.map_cons, List.sum_cons, mul_add]; rw [ih₂]
    have hcons_tw : WeightedSeq.totalWeight ((w, p) :: l₁) =
        w + WeightedSeq.totalWeight l₁ := by
      simp [WeightedSeq.totalWeight]
    have htail_tw : c * WeightedSeq.totalWeight l₁ = 1 - c * w := by
      rw [hcons_tw] at hctw; linarith [mul_add c w (WeightedSeq.totalWeight l₁)]
    have hnn_tail : ∀ e ∈ l₁, 0 ≤ e.1 := fun e he => hnn e (List.mem_cons_of_mem _ he)
    by_cases hcw : c * w = 1
    · -- c*w = 1 case: totalWeight l₁ = 0, all weights ≥ 0 → all weights = 0
      -- So scale c l₁ and scale c l₂ are both all-zero-weight lists, and both sides equal p.
      have htw_zero : WeightedSeq.totalWeight l₁ = 0 := by
        have h := htail_tw; rw [hcw, sub_self] at h
        exact (mul_eq_zero.mp h).resolve_left hc
      -- All weights in l₁ are 0 (non-negative and sum to 0)
      have hfst_nn : ∀ x ∈ l₁.map Prod.fst, (0 : R) ≤ x := by
        intro x hx; obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx; exact hnn_tail e' he'
      have hall_zero : ∀ e ∈ l₁, e.1 = 0 := by
        intro e he
        exact List.all_zero_of_le_zero_le_of_sum_eq_zero hfst_nn htw_zero
          (List.mem_map.mpr ⟨e, he, rfl⟩)
      -- scale c l₁ has all weights 0
      have hscale_zero₁ : WeightedSeq.scale c l₁ = l₁.map (fun e => ((0 : R), e.2)) := by
        simp only [WeightedSeq.scale, List.map_map, Function.comp_def]
        apply List.map_congr_left; intro e he
        simp [hall_zero e he]
      -- All weights in l₂ are also 0 (permutation)
      have hall_zero₂ : ∀ e ∈ l₂, e.1 = 0 := by
        intro e he; exact hall_zero e (hperm.symm.mem_iff.mp he)
      have hscale_zero₂ : WeightedSeq.scale c l₂ = l₂.map (fun e => ((0 : R), e.2)) := by
        simp only [WeightedSeq.scale, List.map_map, Function.comp_def]
        apply List.map_congr_left; intro e he
        simp [hall_zero₂ e he]
      -- Both sides: A((1, p) :: zeros) = p
      change affineOfBinary op ((c * w, p) :: WeightedSeq.scale c l₁) =
             affineOfBinary op ((c * w, p) :: WeightedSeq.scale c l₂)
      rw [hcw, hscale_zero₁, hscale_zero₂]
      -- Now both sides are A((1, p) :: zeros_with_points_from_lᵢ)
      -- Rewrite as [(1, p)] ++ zeros, then use cons_zero_many
      -- Note: (fun e => (0, e.2)) = (fun e => (0, e.snd)) on pairs
      have hmap_eq₁ : (1, p) :: l₁.map (fun e => ((0 : R), e.2)) =
          [(1, p)] ++ (l₁.map Prod.snd).map (fun x => ((0 : R), x)) := by
        simp [List.map_map, Function.comp_def]
      have hmap_eq₂ : (1, p) :: l₂.map (fun e => ((0 : R), e.2)) =
          [(1, p)] ++ (l₂.map Prod.snd).map (fun x => ((0 : R), x)) := by
        simp [List.map_map, Function.comp_def]
      rw [hmap_eq₁, hmap_eq₂,
        affineOfBinary_append_zero_many op [(1, p)] (l₁.map Prod.snd)
          (by simp [WeightedSeq.totalWeight]) (by simp),
        affineOfBinary_append_zero_many op [(1, p)] (l₂.map Prod.snd)
          (by simp [WeightedSeq.totalWeight]) (by simp)]
    · have h1cw : (1 : R) - c * w ≠ 0 := sub_ne_zero.mpr (Ne.symm hcw)
      -- Unfold scale for the goal only
      show affineOfBinary op ((c * w, p) :: WeightedSeq.scale c l₁) =
           affineOfBinary op ((c * w, p) :: WeightedSeq.scale c l₂)
      have hvalid₁ : WeightedSeq.totalWeight
          ((c * w, p) :: WeightedSeq.scale c l₁) = 1 := by
        have : WeightedSeq.totalWeight ((c * w, p) :: WeightedSeq.scale c l₁) =
            c * w + WeightedSeq.totalWeight (WeightedSeq.scale c l₁) := by
          simp [WeightedSeq.totalWeight]
        rw [this, scale_tw, htail_tw]; ring
      have hvalid₂ : WeightedSeq.totalWeight
          ((c * w, p) :: WeightedSeq.scale c l₂) = 1 := by
        have : WeightedSeq.totalWeight ((c * w, p) :: WeightedSeq.scale c l₂) =
            c * w + WeightedSeq.totalWeight (WeightedSeq.scale c l₂) := by
          simp [WeightedSeq.totalWeight]
        rw [this, scale_tw, ← perm_totalWeight l₁ l₂ hperm, htail_tw]; ring
      rw [affineOfBinary_cons_strip op (c * w) p _ hcw hvalid₁]
      rw [affineOfBinary_cons_strip op (c * w) p _ hcw hvalid₂]
      congr 1
      rw [scale_scale, scale_scale]
      exact ih ((1 - c * w)⁻¹ * c)
        (mul_ne_zero (inv_ne_zero h1cw) hc)
        (by rw [mul_assoc, htail_tw, inv_mul_cancel₀ h1cw])
        hnn_tail
  | swap x y =>
    rename_i l
    obtain ⟨a, px⟩ := x
    obtain ⟨b, py⟩ := y
    show affineOfBinary op ((c * b, py) :: (c * a, px) :: WeightedSeq.scale c l) =
         affineOfBinary op ((c * a, px) :: (c * b, py) :: WeightedSeq.scale c l)
    have scale_tw : ∀ (c' : R) (ws : WeightedSeq R M),
        WeightedSeq.totalWeight (WeightedSeq.scale c' ws) =
        c' * WeightedSeq.totalWeight ws := by
      intro c' ws
      simp only [WeightedSeq.totalWeight, WeightedSeq.scale, List.map_map, Function.comp_def]
      induction ws with
      | nil => simp
      | cons hd tl ih₂ => simp only [List.map_cons, List.sum_cons, mul_add]; rw [ih₂]
    have hvalid_swap : WeightedSeq.totalWeight
        ((c * b, py) :: (c * a, px) :: WeightedSeq.scale c l) = 1 := by
      have : WeightedSeq.totalWeight ((c * b, py) :: (c * a, px) :: WeightedSeq.scale c l) =
          c * b + (c * a + WeightedSeq.totalWeight (WeightedSeq.scale c l)) := by
        simp [WeightedSeq.totalWeight]
      rw [this, scale_tw]
      have : WeightedSeq.totalWeight ((b, py) :: (a, px) :: l) =
          b + (a + WeightedSeq.totalWeight l) := by simp [WeightedSeq.totalWeight]
      rw [this] at hctw; linarith [mul_add c b (a + WeightedSeq.totalWeight l),
        mul_add c a (WeightedSeq.totalWeight l)]
    exact affineOfBinary_swap_zero op (c * b) (c * a) py px
      (WeightedSeq.scale c l) hvalid_swap
  | trans h₁₂ h₂₃ ih₁₂ ih₂₃ =>
    rename_i l₁ l₂ l₃
    have htw₂ : c * WeightedSeq.totalWeight l₂ = 1 := by
      rw [perm_totalWeight _ _ h₁₂] at hctw; exact hctw
    have hnn₂ : ∀ e ∈ l₂, 0 ≤ e.1 := fun e he => hnn e (h₁₂.symm.mem_iff.mp he)
    exact (ih₁₂ c hc hctw hnn).trans (ih₂₃ c hc htw₂ hnn₂)

private theorem affineOfBinary_perm [Inhabited M] (op : BinaryConvexOp R M)
    (ws₁ ws₂ : WeightedSeq R M) (hperm : ws₁.Perm ws₂)
    (hvalid : ws₁.totalWeight = 1)
    (hnn : ∀ e ∈ ws₁, 0 ≤ e.1) :
    affineOfBinary op ws₁ = affineOfBinary op ws₂ := by
  have h := affineOfBinary_perm_scaled op ws₁ ws₂ hperm 1 one_ne_zero (by simp [hvalid]) hnn
  simp only [WeightedSeq.scale, one_mul, List.map_id'] at h
  exact h

/-- affineOfBinary on a simplex extended to a larger support equals the original.
    Uses permutation invariance and zero removal. -/
theorem affineOfBinary_toWeightedSeqOn [Inhabited M] (op : BinaryConvexOp R M)
    (d : StdSimplex R M) (S : List M)
    (hS : ∀ m ∈ d.weights.support, m ∈ S) (hnodup : S.Nodup) :
    affineOfBinary op (d.toWeightedSeqOn S) = affineOfBinary op d.toWeightedSeq := by
  -- Strategy: reorder S to put non-support (zero weight) elements first,
  -- strip them with cons_zero_many, then permute remaining to match support.toList.
  classical
  set f := fun x => (d.weights x, x)
  change affineOfBinary op (S.map f) = affineOfBinary op (d.weights.support.toList.map f)
  set p := fun x => x ∈ d.weights.support
  set S_in := S.filter (fun x => decide (p x))
  set S_out := S.filter (fun x => !decide (p x))
  -- S_in is the support elements of S, S_out is the non-support elements
  -- Step 0: totalWeight of S.map f = 1
  have htw_S : WeightedSeq.totalWeight (S.map f) = 1 := by
    unfold WeightedSeq.totalWeight
    simp only [List.map_map, Function.comp_def, f]
    rw [← List.sum_toFinset _ hnodup]
    have hsupp_sub : d.weights.support ⊆ S.toFinset :=
      fun m hm => List.mem_toFinset.mpr (hS m hm)
    rw [← Finset.sum_sdiff hsupp_sub]
    have h_sdiff : (S.toFinset \ d.weights.support).sum (fun x => d.weights x) = 0 :=
      Finset.sum_eq_zero (fun m hm => Finsupp.notMem_support_iff.mp (Finset.mem_sdiff.mp hm).2)
    rw [h_sdiff, zero_add]
    have := d.total; rw [Finsupp.sum] at this; convert this using 1
  -- Step 1: S_in is a perm of support.toList
  have hperm_in : S_in.Perm d.weights.support.toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact hnodup.filter _
    · exact d.weights.support.nodup_toList
    · ext x
      simp only [List.mem_toFinset, List.mem_filter, Finset.mem_toList, decide_eq_true_eq, S_in, p]
      exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨hS x hx, hx⟩⟩
  -- Step 2: S_out elements all have weight 0
  have hout_zero : ∀ x ∈ S_out, d.weights x = 0 := by
    intro x hx
    have hx' : x ∉ d.weights.support := by
      simp only [S_out, p, List.mem_filter] at hx
      simpa using hx.2
    exact Finsupp.notMem_support_iff.mp hx'
  -- Step 3: S_out.map f = S_out.map (fun x => (0, x))
  have hout_map : S_out.map f = S_out.map (fun x => ((0 : R), x)) := by
    apply List.map_congr_left; intro x hx
    simp [f, hout_zero x hx]
  -- Step 4: S ~ S_out ++ S_in (filter partition)
  have hperm_partition : S.Perm (S_out ++ S_in) := by
    show S.Perm (S.filter (fun x => !decide (p x)) ++ S.filter (fun x => decide (p x)))
    suffices ∀ (l : List M), l.Perm
        (l.filter (fun x => !decide (p x)) ++ l.filter (fun x => decide (p x))) from this S
    intro l; induction l with
    | nil => simp
    | cons y ys ih =>
      simp only [List.filter_cons]
      by_cases hy : decide (p y)
      · -- decide (p y) = true: y goes to S_in
        simp only [hy, ite_true, Bool.not_true, ite_false]
        -- Goal: (y :: ys) ~ (filter_not ys ++ (y :: filter ys))
        exact (ih.cons y).trans (List.perm_middle.symm)
      · -- decide (p y) = false: y goes to S_out
        simp only [show decide (p y) = false from by simpa using hy, ite_true, ite_false,
          Bool.not_false, List.cons_append]
        exact ih.cons y
  -- Step 5: Map the partition perm through f
  have hperm_mapped : (S.map f).Perm ((S_out.map f) ++ (S_in.map f)) := by
    rw [← List.map_append]; exact hperm_partition.map f
  -- Step 6: S_out.map f = S_out.map (fun x => (0, x)) (rewrite)
  rw [hout_map] at hperm_mapped
  -- Step 7: S_in.map f ~ support.toList.map f
  have hperm_in_mapped : (S_in.map f).Perm (d.weights.support.toList.map f) :=
    hperm_in.map f
  -- Step 8: Combine: S.map f ~ S_out.map (0,·) ++ support.toList.map f
  have hperm_full : (S.map f).Perm
      (S_out.map (fun x => ((0 : R), x)) ++ d.weights.support.toList.map f) :=
    hperm_mapped.trans (List.Perm.append_left _ hperm_in_mapped)
  -- Step 9: Apply perm invariance to reorder
  have hnn_S : ∀ e ∈ S.map f, 0 ≤ e.1 := by
    intro e he
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp he
    exact d.nonneg m
  rw [affineOfBinary_perm op _ _ hperm_full htw_S hnn_S]
  -- Step 10: Strip the zero-weight prefix using cons_zero_many
  have htw_supp : WeightedSeq.totalWeight (d.weights.support.toList.map f) = 1 := by
    unfold WeightedSeq.totalWeight
    simp only [List.map_map, Function.comp_def, f]
    rw [Finset.sum_map_toList]
    have := d.total; rw [Finsupp.sum] at this; convert this using 1
  have hne_supp : d.weights.support.toList.map f ≠ [] := by
    intro h; simp at h
    have := d.total; rw [Finsupp.sum, h] at this; simp at this
  exact affineOfBinary_cons_zero_many op S_out (d.weights.support.toList.map f) htw_supp hne_supp

/-- The binary outer case: C(1-p, A(d₁), A(d₂)) = A(join of duple(d₁, d₂, p, 1-p)).

    When d₁, d₂ have the same support, this follows from entropic identity.
    For different supports, we extend to a common support using zero-weight invariance. -/
theorem affineOfBinary_binary_join [Inhabited M]
    (op : BinaryConvexOp R M) (p : R) (d₁ d₂ : StdSimplex R M)
    (hp : 0 ≤ p) (hp' : 0 ≤ 1 - p) (hsum : p + (1 - p) = 1) :
    op.binCombo (1 - p)
      (affineOfBinary op d₁.toWeightedSeq)
      (affineOfBinary op d₂.toWeightedSeq) =
    affineOfBinary op (StdSimplex.duple d₁ d₂ hp hp' hsum).join.toWeightedSeq := by
  by_cases hsupp : d₁.weights.support = d₂.weights.support
  · -- Same support case: use affineOfBinary_linear directly
    have hlen := toWeightedSeq_length_of_support_eq hsupp
    have hpts := toWeightedSeq_samePoints_of_support_eq hsupp
    rw [affineOfBinary_linear op (1 - p) d₁.toWeightedSeq d₂.toWeightedSeq hlen hpts]
    have hjw := StdSimplex.join_duple_weights d₁ d₂ hp hp' hsum
    have hjoin_supp : (StdSimplex.duple d₁ d₂ hp hp' hsum).join.weights.support =
        d₁.weights.support := by
      ext m
      simp only [Finsupp.mem_support_iff, hjw, Finsupp.coe_add, Pi.add_apply,
        Finsupp.smul_apply, smul_eq_mul]
      constructor
      · intro h hm
        have hm₂ : d₂.weights m = 0 :=
          Finsupp.notMem_support_iff.mp (hsupp ▸ Finsupp.notMem_support_iff.mpr hm)
        simp [hm, hm₂] at h
      · intro h heq
        have hd₁_pos : 0 < d₁.weights m :=
          lt_of_le_of_ne (d₁.nonneg m) (Ne.symm h)
        have hd₂_nn : 0 ≤ d₂.weights m := d₂.nonneg m
        have h1 : 0 ≤ p * d₁.weights m := mul_nonneg hp (le_of_lt hd₁_pos)
        have h2 : 0 ≤ (1 - p) * d₂.weights m := mul_nonneg hp' hd₂_nn
        have h3 : p * d₁.weights m ≤ 0 := by
          have : p * d₁.weights m = -(((1 - p) * d₂.weights m)) := by
            rw [eq_neg_iff_add_eq_zero]; exact heq
          rw [this]; exact neg_nonpos.mpr h2
        have h3' : p * d₁.weights m = 0 := le_antisymm h3 h1
        have hp0 : p = 0 := by
          by_contra hp_ne
          exact absurd h3' (ne_of_gt (mul_pos (lt_of_le_of_ne hp (Ne.symm hp_ne)) hd₁_pos))
        rw [hp0, zero_mul, zero_add, sub_zero, one_mul] at heq
        have : m ∉ d₂.weights.support := Finsupp.notMem_support_iff.mpr heq
        rw [← hsupp] at this
        exact h (Finsupp.notMem_support_iff.mp this)
    simp only [WeightedSeq.combineWeights, StdSimplex.toWeightedSeq]
    rw [hjoin_supp]
    rw [List.zipWith_map, ← hsupp, List.zipWith_self]
    congr 1
    apply List.map_congr_left
    intro m _
    simp only [hjw, Finsupp.coe_add, Pi.add_apply,
      Finsupp.smul_apply, smul_eq_mul]
    ring_nf
  · -- Different support case: extend to common support
    -- Handle edge cases p = 0, p = 1 first
    have hjw := StdSimplex.join_duple_weights d₁ d₂ hp hp' hsum
    by_cases hp0 : p = 0
    · -- p = 0: C(1, A(d₁), A(d₂)) = A(d₂), join = d₂
      simp only [hp0, sub_zero] at *
      rw [op.binCombo_one]
      congr 1; congr 1; apply StdSimplex.ext; ext m
      simp only [hjw, Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply,
        smul_eq_mul, zero_mul, zero_add, one_mul]
    by_cases hp1 : p = 1
    · -- p = 1: C(0, A(d₁), A(d₂)) = A(d₁), join = d₁
      simp only [hp1, sub_self] at *
      rw [op.binCombo_zero]
      congr 1; congr 1; apply StdSimplex.ext; ext m
      simp only [hjw, Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply,
        smul_eq_mul, one_mul, zero_mul, add_zero]
    -- Now 0 < p < 1, d₁.support ≠ d₂.support
    -- Strategy: extend both d₁.toWS and d₂.toWS to the common support
    -- join.support.toList, apply affineOfBinary_linear, then show the
    -- combined result equals join.toWS.
    classical
    have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hp'_pos : 0 < 1 - p := by
      have : p < 1 := by
        by_contra h
        push_neg at h
        have : p = 1 := le_antisymm (by linarith [hp']) h
        exact hp1 this
      linarith
    -- The join support equals d₁.support ∪ d₂.support
    set j := (StdSimplex.duple d₁ d₂ hp hp' hsum).join
    set S := j.weights.support.toList
    have hS_nodup : S.Nodup := Finset.nodup_toList _
    -- d₁.support ⊆ join.support
    have hd₁_sub : ∀ m ∈ d₁.weights.support, m ∈ S := by
      intro m hm
      rw [Finset.mem_toList, Finsupp.mem_support_iff]
      rw [show j.weights m = p * d₁.weights m + (1 - p) * d₂.weights m from by
        simp [j, hjw, Finsupp.coe_add, Pi.add_apply, smul_eq_mul]]
      have := d₁.nonneg m
      have hd₁m := Finsupp.mem_support_iff.mp hm
      have hd₂m := d₂.nonneg m
      linarith [mul_pos hp_pos (lt_of_le_of_ne this (Ne.symm hd₁m)),
                mul_nonneg (le_of_lt hp'_pos) hd₂m]
    -- d₂.support ⊆ join.support
    have hd₂_sub : ∀ m ∈ d₂.weights.support, m ∈ S := by
      intro m hm
      rw [Finset.mem_toList, Finsupp.mem_support_iff]
      rw [show j.weights m = p * d₁.weights m + (1 - p) * d₂.weights m from by
        simp [j, hjw, Finsupp.coe_add, Pi.add_apply, smul_eq_mul]]
      have := d₂.nonneg m
      have hd₂m := Finsupp.mem_support_iff.mp hm
      have hd₁m := d₁.nonneg m
      linarith [mul_nonneg (le_of_lt hp_pos) hd₁m,
                mul_pos hp'_pos (lt_of_le_of_ne this (Ne.symm hd₂m))]
    -- Rewrite using toWeightedSeqOn
    rw [show affineOfBinary op d₁.toWeightedSeq =
          affineOfBinary op (d₁.toWeightedSeqOn S) from
        (affineOfBinary_toWeightedSeqOn op d₁ S hd₁_sub hS_nodup).symm]
    rw [show affineOfBinary op d₂.toWeightedSeq =
          affineOfBinary op (d₂.toWeightedSeqOn S) from
        (affineOfBinary_toWeightedSeqOn op d₂ S hd₂_sub hS_nodup).symm]
    -- Both extended sequences have same points (S) and same length
    have hlen : (d₁.toWeightedSeqOn S).length = (d₂.toWeightedSeqOn S).length := by
      simp [StdSimplex.toWeightedSeqOn]
    have hpts : (d₁.toWeightedSeqOn S).samePoints (d₂.toWeightedSeqOn S) := by
      simp [WeightedSeq.samePoints, StdSimplex.toWeightedSeqOn, List.map_map, Function.comp]
    -- Apply linearity
    rw [affineOfBinary_linear op (1 - p) (d₁.toWeightedSeqOn S) (d₂.toWeightedSeqOn S)
          hlen hpts]
    -- Show combineWeights gives join.toWS
    congr 1
    simp only [WeightedSeq.combineWeights, StdSimplex.toWeightedSeqOn, StdSimplex.toWeightedSeq]
    rw [List.zipWith_map, List.zipWith_self]
    apply List.map_congr_left
    intro m _
    simp only [j, hjw, Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, smul_eq_mul]
    ring_nf

/-- The flattening lemma: affine combination of affine combinations equals
    affine combination of joined weights.

    The proof uses strong induction on outer support cardinality:
    - Card 0: impossible (weights sum to 1)
    - Card 1: direct (single simplex)
    - Card 2: uses affineOfBinary_binary_join
    - Card ≥ 3: monadic decomposition via exists_duple_join, reducing to IH -/
theorem affineOfBinary_assoc_flattening [Inhabited M]
    (op : BinaryConvexOp R M)
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
    obtain ⟨s, t, hs, ht, hst, g₁, g₂, hg₁, hg₂, hf⟩ :=
      StdSimplex.exists_duple_join f (by omega)
    have hs' := le_of_lt hs
    have ht' := le_of_lt ht
    -- IH for g₁ and g₂ (they have strictly smaller card)
    have ih₁ := ih g₁.weights.support.card (by omega) g₁ rfl
    have ih₂ := ih g₂.weights.support.card (by omega) g₂ rfl
    -- Rewrite using the splitting: f = (duple g₁ g₂).join
    rw [hf]
    -- LHS: rewrite using join_map + map_duple
    conv_lhs =>
      rw [StdSimplex.join_map (convexCombinationOfBinary op)
            (StdSimplex.duple g₁ g₂ hs' ht' hst)]
      rw [StdSimplex.map_duple
            (fun d => d.map (convexCombinationOfBinary op)) g₁ g₂ hs' ht' hst]
    -- RHS: rewrite using join_join + map_duple
    conv_rhs =>
      rw [StdSimplex.join_join (StdSimplex.duple g₁ g₂ hs' ht' hst)]
      rw [StdSimplex.map_duple StdSimplex.join g₁ g₂ hs' ht' hst]
    -- Goal: A(D₁.join.toWS) = A(D₂.join.toWS) where
    -- D₁ = duple (g₁.map F) (g₂.map F), D₂ = duple g₁.join g₂.join
    -- F = convexCombinationOfBinary op
    -- Both D₁, D₂ have card ≤ 2 < n + 3.
    -- Card bounds for D₁, D₂ (duple of two elements has support ≤ 2)
    have hD₁_card :
        (StdSimplex.duple (g₁.map (convexCombinationOfBinary op))
          (g₂.map (convexCombinationOfBinary op)) hs' ht' hst
        ).weights.support.card ≤ 2 :=
      StdSimplex.duple_support_card_le_two _ _ hs' ht' hst
    have hD₂_card :
        (StdSimplex.duple g₁.join g₂.join hs' ht' hst
        ).weights.support.card ≤ 2 :=
      StdSimplex.duple_support_card_le_two _ _ hs' ht' hst
    -- Apply IH to D₁ and D₂
    have ihD₁ := ih _ (by omega)
      (StdSimplex.duple (g₁.map (convexCombinationOfBinary op))
        (g₂.map (convexCombinationOfBinary op)) hs' ht' hst) rfl
    have ihD₂ := ih _ (by omega)
      (StdSimplex.duple g₁.join g₂.join hs' ht' hst) rfl
    -- Chain: A(D₁.join) ← ihD₁ → A(D₁.map F) = A(D₂.map F) ← ihD₂ → A(D₂.join)
    rw [← ihD₁, ← ihD₂]
    -- Goal: A(D₁.map F .toWS) = A(D₂.map F .toWS)
    -- D₁.map F = D₂.map F because F(g₁.map F) = F(g₁.join) by ih₁
    congr 1; congr 1
    rw [StdSimplex.map_duple (convexCombinationOfBinary op)
          (g₁.map (convexCombinationOfBinary op))
          (g₂.map (convexCombinationOfBinary op)) hs' ht' hst,
        StdSimplex.map_duple (convexCombinationOfBinary op)
          g₁.join g₂.join hs' ht' hst,
        show convexCombinationOfBinary op
              (g₁.map (convexCombinationOfBinary op)) =
            convexCombinationOfBinary op g₁.join from ih₁,
        show convexCombinationOfBinary op
              (g₂.map (convexCombinationOfBinary op)) =
            convexCombinationOfBinary op g₂.join from ih₂]

/-- Build a ConvexSpace from a binary convex operation.

    The algorithm from convex_plan.md only uses ⅟u and ⅟(1-u) for division,
    so this works over any ordered field with an invertible splitting unit. -/
noncomputable def ConvexSpace.ofBinary [Inhabited M]
    (op : BinaryConvexOp R M) :
    ConvexSpace R M where
  convexCombination := convexCombinationOfBinary op
  single := convexCombinationOfBinary_single op
  assoc f := by
    simp only [convexCombinationOfBinary]
    exact affineOfBinary_assoc_flattening op f

end OfBinaryField
