/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.ConvexSpace
public import Mathlib.Algebra.AddTorsor.Defs

/-!
# Affine space

In this file we introduce the following notation:

* `AffineSpace V P` is an alternative notation for `AddTorsor V P` introduced at the end of this
  file.

We tried to use an `abbreviation` instead of a `notation` but this led to hard-to-debug elaboration
errors. So, we introduce a localized notation instead. When this notation is enabled with
`open Affine`, Lean will use `AffineSpace` instead of `AddTorsor` both in input and in the
proof state.

Here is an incomplete list of notions related to affine spaces, all of them are defined in other
files:

* `AffineMap`: a map between affine spaces that preserves the affine structure;
* `AffineEquiv`: an equivalence between affine spaces that preserves the affine structure;
* `AffineSubspace`: a subset of an affine space closed w.r.t. affine combinations of points;
* `AffineCombination`: an affine combination of points;
* `AffineIndependent`: affine independent set of points;
* `AffineBasis.coord`: the barycentric coordinate of a point.

## TODO

Some key definitions are not yet present.

* Affine frames.  An affine frame might perhaps be represented as an `AffineEquiv` to a `Finsupp`
  (in the general case) or function type (in the finite-dimensional case) that gives the
  coordinates, with appropriate proofs of existence when `k` is a field.
-/

public section

@[inherit_doc] scoped[Affine] notation "AffineSpace" => AddTorsor

noncomputable section

/--
A finitely supported weighting over elements of `M` with coefficients in `R`. The weights sum to 1.
-/
structure AffineWeights (R : Type*) [AddCommMonoid R] [One R] (M : Type*)
    extends weights : M →₀ R where
  /-- The weights sum to 1. -/
  total : weights.sum (fun _ r => r) = 1

attribute [simp] AffineWeights.total
grind_pattern AffineWeights.total => self.weights

namespace AffineWeights

variable {R : Type*} [AddCommMonoid R] [One R] {M : Type*}

@[ext]
theorem ext {f g : AffineWeights R M} (h : f.weights = g.weights) : f = g := by
  cases f; cases g; simp_all

/-- The weighting that puts all weight on `x`. -/
def single (x : M) : AffineWeights R M where
  weights := Finsupp.single x 1
  total := by simp

@[simp]
theorem mk_single (x : M) {total} :
    (AffineWeights.mk (Finsupp.single x (1 : R)) total) = single x := by simp [single]

/-- A weighting with weight `s` on `x` and weight `t` on `y`. -/
def duple (x y : M) {s t : R} (h : s + t = 1) : AffineWeights R M where
  weights := Finsupp.single x s + Finsupp.single y t
  total := by
    classical
    rw [Finsupp.sum_add_index] <;> simp [h]

/--
Map a function over the support of an affine weighting.
For each n : N, the weight is the sum of weights of all m : M with g m = n.
-/
def map {M : Type*} {N : Type*} (g : M → N) (f : AffineWeights R M) : AffineWeights R N where
  weights := f.weights.mapDomain g
  total := by simp [Finsupp.sum_mapDomain_index]

/--
Join operation for affine weightings (monadic join).
Given a weighting of a weighting, flattens it to a single weighting.
-/
def join {R : Type*} [Semiring R] {M : Type*} (f : AffineWeights R (AffineWeights R M)) :
    AffineWeights R M where
  weights := f.weights.sum (fun d r => r • d.weights)
  total := by
    rw [Finsupp.sum_sum_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
    convert f.total
    rw [Finsupp.sum_smul_index (fun _ ↦ rfl), ← Finsupp.mul_sum, AffineWeights.total, mul_one]

end AffineWeights

/--
A set equipped with an operation of finite affine combinations, where the coefficients sum to 1.
-/
class AffineSpace (R : Type*) (M : Type*) [Semiring R] where
  /-- Take a affine combination with the given weighting. -/
  affineCombination (f : AffineWeights R M) : M
  /-- Associativity of affine combination (monadic join law). -/
  assoc (f : AffineWeights R (AffineWeights R M)) :
    affineCombination (f.map affineCombination) = affineCombination f.join
  /-- A affine combination of a single point is that point. -/
  single (x : M) : affineCombination (.single x) = x

namespace AffineSpace

section ConvexSpace

variable {R : Type*} {M : Type*} [LE R] [Semiring R] in
-- its probably nicer to redefine StdSimplex to extend AffineWeights?
instance : Coe (StdSimplex R M) (AffineWeights R M) where
  coe f := ⟨f.weights, f.total⟩

variable {R : Type*} {M : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

instance : Coe (StdSimplex R (StdSimplex R M)) (AffineWeights R (AffineWeights R M)) where
  coe f := f.map (Coe.coe (β := (AffineWeights R M)))

instance [af : AffineSpace R M] : ConvexSpace R M where
  convexCombination (f : StdSimplex R M) := af.affineCombination f
  assoc (f : StdSimplex R (StdSimplex R M)) := by
    convert af.assoc f
    · simp only [StdSimplex.map, AffineWeights.map, ← Finsupp.mapDomain_comp]; rfl
    · simp only [StdSimplex.join, AffineWeights.join, StdSimplex.map]
      rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]
  single (x : M) := by convert af.single x

end ConvexSpace

end AffineSpace

end
