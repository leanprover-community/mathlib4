/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Real.Basic

/-!
# Path weights in a Quiver

This file defines the weight of a path in a quiver. The weight of a path is the product of the
weights of its edges, where weights are taken from a monoid.

## Main definitions

* `Quiver.Path.weight`: The weight of a path, defined as the multiplicative product of the
  weights of its constituent edges.
* `Quiver.Path.weight_of_fn`: A convenience version of `weight` where the weight of an edge
  is determined by a function of its source and target vertices.

## Main results

* `Quiver.Path.weight_comp`: The weight of a composition of paths is the product of their weights.
* `Quiver.Path.weight_pos`: If all edge weights are positive, the path weight is positive.
* `Quiver.Path.weight_of_fn_nonneg`: If all edge weights are non-negative, so is the path weight.
-/

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*}

section Weight

variable [Monoid R]

/-- The weight of a path is the product of the weights of its edges. -/
def weight (w : ∀ {i j : V}, (i ⟶ j) → R) : ∀ {i j : V}, Path i j → R
  | _, _, Path.nil => 1
  | _, _, Path.cons p e => weight w p * w e

/-- The weight of a path, where the weight of an edge is defined by a function on its endpoints. -/
def weight_of_fn (w : V → V → R) : ∀ {i j : V}, Path i j → R :=
  weight (fun {i j} (_ : i ⟶ j) => w i j)

@[simp]
lemma weight_nil (w : ∀ {i j : V}, (i ⟶ j) → R) (a : V) :
    weight (fun {_ _} => w) (Path.nil : Path a a) = 1 := by unfold weight; simp

@[simp]
lemma weight_cons (w : ∀ {i j : V}, (i ⟶ j) → R) {a b c : V} (p : Path a b) (e : b ⟶ c) :
    weight w (p.cons e) = weight w p * w e := by
  cases p
  · simp [weight]
  · simp [weight, mul_assoc]

lemma weight_of_fn_nil (w : V → V → R) (a : V) :
    weight_of_fn w (Path.nil : Path a a) = 1 := by simp [weight_of_fn]

lemma weight_of_fn_cons (w : V → V → R) {a b c : V} (p : Path a b) (e : b ⟶ c) :
    weight_of_fn w (p.cons e) = weight_of_fn w p * w b c := by unfold weight_of_fn; simp

@[simp]
lemma weight_comp (w : ∀ {i j : V}, (i ⟶ j) → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weight w (p.comp q) = weight w p * weight w q := by
  induction q with
  | nil => simp
  | cons _ _ ih => simp [ih, mul_assoc]

lemma weight_of_fn_comp (w : V → V → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weight_of_fn w (p.comp q) = weight_of_fn w p * weight_of_fn w q := by
  simp [weight_of_fn, weight_comp]

end Weight

section PositiveWeight

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R]

/-- If all edge weights are positive, then the weight of any path is positive. -/
lemma weight_pos {w : ∀ {i j : V}, (i ⟶ j) → R}
    (hw : ∀ {i j : V} (e : i ⟶ j), 0 < w e) {i j : V} (p : Path i j) :
    0 < weight w p := by
  induction p with
  | nil => simp
  | cons _ e ih => simp [mul_pos ih (hw e)]

end PositiveWeight

section RealWeight

/-- If all edge weights (from a function on vertices) are positive, so is the path weight. -/
lemma weight_of_fn_pos {w : V → V → ℝ}
    (hw : ∀ i j : V, 0 < w i j) {i j : V} (p : Path i j) :
    0 < weight_of_fn w p := by
  apply weight_pos; intro i j _; exact hw i j

/-- If all edge weights (from a function on vertices) are non-negative, so is the path weight. -/
lemma weight_of_fn_nonneg {w : V → V → ℝ}
    (hw : ∀ i j : V, 0 ≤ w i j) {i j : V} (p : Path i j) :
    0 ≤ weight_of_fn w p := by
  induction p with
  | nil => rw [@weight_of_fn_nil, ← Real.mk_zero, Real.mk_zero]; simp_all only [zero_le_one]
  | cons p' _ ih => rw [@weight_of_fn_cons, @mul_nonneg_iff]; simp_all only [and_self, true_or]

end RealWeight

end Quiver.Path
