/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-!
# Basic theory of heights

This is an attempt at formalizing some basic properties of height functions.

We aim at a level of generality that allows to apply the theory to algebraic number fields
and to function fields (and possibly beyond).

The general set-up for heights is the following. Let `K` be a field.
* We have a `Multiset` of archimedean absolute values on `K` (with values in `ℝ`).
* We also have a `Set` of non-archimedean (i.e., `|x+y| ≤ max |x| |y|`) absolute values.
* For a given `x ≠ 0` in `K`, `|x|ᵥ = 1` for all but finitely many (non-archimedean) `v`.
* We have the *product formula* `∏ v : arch, |x|ᵥ * ∏ v : nonarch, |x|ᵥ = 1`
  for all `x ≠ 0` in `K`, where the first product is over the multiset of archimedean
  absolute values.

We realize this implementation via the class `Height.AdmissibleAbsValues K`.

## Main definitions

We define *multiplicative heights* and *logarithmic heights* (which are just defined to
be the (real) logarithm of the corresponding multiplicative height). This leads to some
duplication (in the definitions and statements; the proofs are reduced to those for the
multiplicative height), which is justified, as both versions are frequently used.

We define the following variants.
* `Height.mulHeight₁ x` and `Height.logHeight₁ x` for `x : K`.
  This is the height of an element of `K`.
* (TODO)
  `Height.mulHeight x` and `Height.logHeight x` for `x : ι → K` with `ι` finite. This is the height
  of a tuple of elements of `K` representing a point in projective space.
  It is invariant under scaling by nonzero elements of `K` (for `x ≠ 0`).
* (TODO)
  `Finsupp.mulHeight x` and `Finsupp.logHeight x` for `x : α →₀ K`. This is the same
  as the height of `x` restricted to the support of `x`.
* (TODO)
  `Projectivization.mulHeight` and `Projectivization.logHeight` on
  `Projectivization K (ι → K)` (with a `Fintype ι`). This is the height of a point
  on projective space (with fixed basis).

## Tags

Height, absolute value

-/

@[expose] public noncomputable section

namespace Height

universe u

/-!
### Families of admissible absolute values

We define the class `AdmissibleAbsValues K` for a field `K`, which captures the notion of a
family of absolute values on `K` satisfying a product formula.
-/

/-- A type class capturing an admissible family of absolute values. -/
class AdmissibleAbsValues (K : Type*) [Field K] where
  /-- The archimedean absolute values as a multiset of `ℝ`-valued absolute values on `K`. -/
  archAbsVal : Multiset (AbsoluteValue K ℝ)
  /-- The nonarchimedean absolute values as a set of `ℝ`-valued absolute values on `K`. -/
  nonarchAbsVal : Set (AbsoluteValue K ℝ)
  /-- The nonarchimedean absolute values are indeed nonarchimedean. -/
  isNonarchimedean : ∀ v ∈ nonarchAbsVal, IsNonarchimedean v
  /-- Only finitely many (nonarchimedean) absolute values are `≠ 1` for any nonzero `x : K`. -/
  mulSupport_finite {x : K} (_ : x ≠ 0) : (fun v : nonarchAbsVal ↦ v.val x).mulSupport.Finite
  /-- The product formula. The archimedean absolute values are taken with their multiplicity. -/
  product_formula {x : K} (_ : x ≠ 0) :
      (archAbsVal.map (· x)).prod * ∏ᶠ v : nonarchAbsVal, v.val x = 1

open AdmissibleAbsValues Real

variable (K : Type*) [Field K] [AdmissibleAbsValues K]

/-- The `totalWeight` of a field with `AdmissibleAbsValues` is the sum of the multiplicities of
the archimedean places. -/
def totalWeight : ℕ := archAbsVal (K := K) |>.card

variable {K}

/-!
### Heights of field elements

We use the subscipt `₁` to denote multiplicative and logarithmic heights of field elements
(this is because we are in the one-dimensional case of (affine) heights).
-/

/-- The multiplicative height of an element of `K`. -/
def mulHeight₁ (x : K) : ℝ :=
  (archAbsVal.map fun v ↦ max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1

lemma mulHeight₁_eq (x : K) :
    mulHeight₁ x =
      (archAbsVal.map fun v ↦ max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1 :=
  rfl

@[simp]
lemma mulHeight₁_zero : mulHeight₁ (0 : K) = 1 := by
  simp [mulHeight₁_eq]

@[simp]
lemma mulHeight₁_one : mulHeight₁ (1 : K) = 1 := by
  simp [mulHeight₁_eq]

/-- The mutliplicative height of a field element is always at least `1`. -/
lemma one_le_mulHeight₁ (x : K) : 1 ≤ mulHeight₁ x := by
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod fun _ h ↦ ?_) ?_
  · obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp h
    exact le_max_right ..
  · exact one_le_finprod fun _ ↦ le_max_right ..

-- This is needed as a side condition in proofs about logarithmic heights
lemma mulHeight₁_pos (x : K) : 0 < mulHeight₁ x :=
  zero_lt_one.trans_le <| one_le_mulHeight₁ x

-- This is needed as a side condition in proofs about logarithmic heights
lemma mulHeight₁_ne_zero (x : K) : mulHeight₁ x ≠ 0 :=
  (mulHeight₁_pos x).ne'

lemma zero_le_mulHeight₁ (x : K) : 0 ≤ mulHeight₁ x :=
  (mulHeight₁_pos x).le

/-- The logarithmic height of an element of `K`. -/
def logHeight₁ (x : K) : ℝ := log (mulHeight₁ x)

lemma logHeight₁_eq_log_mulHeight₁ (x : K) : logHeight₁ x = log (mulHeight₁ x) := rfl

@[simp]
lemma logHeight₁_zero : logHeight₁ (0 : K) = 0 := by
  simp [logHeight₁_eq_log_mulHeight₁]

@[simp]
lemma logHeight₁_one : logHeight₁ (1 : K) = 0 := by
  simp [logHeight₁_eq_log_mulHeight₁]

lemma zero_le_logHeight₁ (x : K) : 0 ≤ logHeight₁ x :=
  Real.log_nonneg <| one_le_mulHeight₁ x

end Height
