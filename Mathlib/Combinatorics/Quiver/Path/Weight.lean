/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Algebra.Order.Ring.Defs


/-!
# Path weights in a Quiver

This file defines the weight of a path in a quiver. The weight of a path is the product of the
weights of its edges, where weights are taken from a monoid.

## Main definitions

* `Quiver.Path.weight`: The weight of a path, defined as the multiplicative product of the
  weights of its constituent edges.
* `Quiver.Path.weightOfEPs`: A convenience version of `weight` where the weight of an edge
  is determined by a function of its source and target vertices.

## Main results

* `Quiver.Path.weight_comp`: The weight of a composition of paths is the product of their weights.
* `Quiver.Path.weight_pos`: If all edge weights are positive, the path weight is positive.
* `Quiver.Path.weightOfEPs_nonneg`: If all edge weights are non-negative, so is the path weight.
-/

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*}

section Weight

variable [Monoid R]

/-- The weight of a path is the product of the weights of its edges. -/
def weight (w : ∀ {i j : V}, (i ⟶ j) → R) : ∀ {i j : V}, Path i j → R
  | _, _, Path.nil => 1
  | _, _, Path.cons p e => weight w p * w e

/-- The additive weight of a path is the sum of the weights of its edges. -/
def addWeight {R : Type*} [AddMonoid R] (w : ∀ {i j : V}, (i ⟶ j) → R) : ∀ {i j : V}, Path i j → R
  | _, _, Path.nil => 0
  | _, _, Path.cons p e => addWeight w p + w e

attribute [to_additive existing addWeight] weight

/-- The weight of a path, where the weight of an edge is defined by a function on its endpoints. -/
@[to_additive addWeightOfEPs /-- The additive weight of a path, where the weight of an edge is
defined by a function on its endpoints. -/]
def weightOfEPs (w : V → V → R) : ∀ {i j : V}, Path i j → R :=
  weight (fun {i j} (_ : i ⟶ j) => w i j)

@[to_additive (attr := simp) addWeight_nil]
lemma weight_nil (w : ∀ {i j : V}, (i ⟶ j) → R) (a : V) :
    weight w (Path.nil : Path a a) = 1 := by
  simp [weight]

@[to_additive (attr := simp) addWeight_cons]
lemma weight_cons (w : ∀ {i j : V}, (i ⟶ j) → R) {a b c : V} (p : Path a b) (e : b ⟶ c) :
    weight w (p.cons e) = weight w p * w e := by
  simp [weight]

@[to_additive addWeightOfEPs_nil]
lemma weightOfEPs_nil (w : V → V → R) (a : V) :
    weightOfEPs w (Path.nil : Path a a) = 1 := by simp [weightOfEPs]

@[to_additive addWeightOfEPs_cons]
lemma weightOfEPs_cons (w : V → V → R) {a b c : V} (p : Path a b) (e : b ⟶ c) :
    weightOfEPs w (p.cons e) = weightOfEPs w p * w b c := by unfold weightOfEPs; simp

@[to_additive (attr := simp) addWeight_comp]
lemma weight_comp (w : ∀ {i j : V}, (i ⟶ j) → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weight w (p.comp q) = weight w p * weight w q := by
  induction q with
  | nil => simp
  | cons _ _ ih => simp [ih, mul_assoc]

@[to_additive addWeightOfEPs_comp]
lemma weightOfEPs_comp (w : V → V → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weightOfEPs w (p.comp q) = weightOfEPs w p * weightOfEPs w q := by
  simp [weightOfEPs, weight_comp]

end Weight

section OrderedWeight

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- If all edge weights are positive, then the weight of any path is positive. -/
lemma weight_pos {w : ∀ {i j : V}, (i ⟶ j) → R}
    (hw : ∀ {i j : V} (e : i ⟶ j), 0 < w e) {i j : V} (p : Path i j) :
    0 < weight w p := by
  induction p with
  | nil =>
      simp
  | cons p e ih =>
      have he : 0 < w e := hw e
      simpa [weight_cons] using mul_pos ih he

/-- If all edge weights are non-negative, then the weight of any path is non-negative. -/
lemma weight_nonneg {w : ∀ {i j : V}, (i ⟶ j) → R}
    (hw : ∀ {i j : V} (e : i ⟶ j), 0 ≤ w e) {i j : V} (p : Path i j) :
    0 ≤ weight w p := by
  induction p with
  | nil =>
      simp
  | cons p e ih =>
      have he : 0 ≤ w e := hw e
      simpa [weight_cons] using mul_nonneg ih he

/-- If all edge weights (given by a function on vertices) are positive, so is the path weight. -/
lemma weightOfEPs_pos {w : V → V → R}
    (hw : ∀ i j : V, 0 < w i j) {i j : V} (p : Path i j) :
    0 < weightOfEPs w p := by
  apply weight_pos
  intro i j e
  exact hw _ _

/-- If all edge weights (given by a function on vertices) are non-negative,
so is the path weight. -/
lemma weightOfEPs_nonneg {w : V → V → R}
    (hw : ∀ i j : V, 0 ≤ w i j) {i j : V} (p : Path i j) :
    0 ≤ weightOfEPs w p := by
  apply weight_nonneg
  intro i j e
  exact hw _ _

end OrderedWeight

end Quiver.Path
