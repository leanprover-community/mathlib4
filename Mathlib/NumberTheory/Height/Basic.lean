/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Basic theory of heights

This is an attempt at formalizing some basic properties of height functions.

We aim at a level of generality that allows to apply the theory to algebraic number fields
and to function fields (and possibly beyond).

The general set-up for heights is the following. Let `K` be a field.
* We need a finite family of archimedean absolute values on `K` (with values in `ℝ`).
* Each of these comes with a weight `weight v`.
* We also have a familiy of non-archimedean (i.e., `|x + y| ≤ max |x| |y|`) absolute values.
* For a given `x ≠ 0` in `K`, `|x|ᵥ = 1` for all but finitely many (nonarchimedean) `v`.
* We have the *product formula* `∏ v : arch, |x|ᵥ ^ weight v * ∏ v : nonarch, |x|ᵥ = 1`
  for all `x ≠ 0` in `K`.

This is implementated via the class `Height.AdmissibleAbsValues K`.

## Main definitions

We define *multiplicative heights* and *logarithmic heights* (which are just defined to
be the (real) logarithm of the corresponding multiplicative height). This leads to some
duplication (in the definitions and statements; the proofs are reduced to those for the
multiplicative height), which is justified, as both versions are frequently used.

We define the following variants.
* `mulHeight₁ x` and `logHeight₁ x` for `x : K`. This is the height of an element of `K`.
* (TODO) `mulHeight x` and `logHeight x` for `x : ι → K` with `ι` finite. This is the height
  of a tuple of elements of `K` representing a point in projective space.
  It is invariant under scaling by nonzero elements of `K` (for `x ≠ 0`).
* (TODO) `mulHeight_finsupp x` and `logHeight_finsupp x` for `x : α →₀ K`. This is the same
  as the height of `x` restricted to any finite subtype containing the support of `x`.
* (TODO) `Projectivization.mulHeight` and `Projectivization.logHeight` on
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
  /-- The type indexing the family of archimedean absolute values -/
  ArchAbsVal : Type u
  /-- The archimedean absolute values. -/
  archAbsVal : ArchAbsVal → AbsoluteValue K ℝ
  /-- There are only finitely many archimedean absolute values. -/
  [archAbsVal_fintype : Fintype ArchAbsVal]
  /-- The weights of the archimedean absolute values.
      They show up as exponents in the product formula. -/
  weight : ArchAbsVal → ℕ
  /-- The weights are positive. -/
  weight_pos : ∀ v, 0 < weight v
  /-- The type indexing the nonarchimedean absolute values. -/
  NonarchAbsVal : Type u
  /-- The nonarchimedean absolute values. -/
  nonarchAbsVal : NonarchAbsVal → AbsoluteValue K ℝ
  /-- The nonarchimedean absolute values are indeed nonarchimedean. -/
  strong_triangle_ineq (v : NonarchAbsVal) : IsNonarchimedean (nonarchAbsVal v)
  /-- Only finitely many absolute values are `≠ 1` for any nonzero `x : K`. -/
  mulSupport_nonarchAbsVal_finite {x : K} (_ : x ≠ 0) : (nonarchAbsVal · x).mulSupport.Finite
  /-- The product formula -/
  product_formula {x : K} (_ : x ≠ 0) :
      (∏ v, archAbsVal v x ^ weight v) * ∏ᶠ v, nonarchAbsVal v x = 1

open AdmissibleAbsValues

attribute [instance] archAbsVal_fintype

variable (K : Type*) [Field K] [aav : AdmissibleAbsValues K]

/-- The `totalWeight` of a field with `AdmissibleAbsValues` is the sum of the weights of
the archimedean places. -/
def totalWeight : ℕ := ∑ v : ArchAbsVal K, weight v

variable {K}

/-!
### Heights of field elements
-/

/-- The multiplicative height of an element of `K`. -/
def mulHeight₁ (x : K) : ℝ :=
  (∏ v, max (archAbsVal v x) 1 ^ weight v) * ∏ᶠ v, max (nonarchAbsVal v x) 1

@[simp]
lemma mulHeight₁_zero : mulHeight₁ (0 : K) = 1 := by
  simp [mulHeight₁]

@[simp]
lemma mulHeight₁_one : mulHeight₁ (1 : K) = 1 := by
  simp [mulHeight₁]

lemma one_le_mulHeight₁ (x : K) : 1 ≤ mulHeight₁ x := by
  classical
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  · exact Finset.univ.one_le_prod fun _ ↦ one_le_pow₀ <| le_max_right ..
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
def logHeight₁ (x : K) : ℝ := (mulHeight₁ x).log

@[simp]
lemma logHeight₁_zero : logHeight₁ (0 : K) = 0 := by
  simp [logHeight₁]

@[simp]
lemma logHeight₁_one : logHeight₁ (1 : K) = 0 := by
  simp [logHeight₁]

lemma zero_le_logHeight₁ (x : K) : 0 ≤ logHeight₁ x :=
  Real.log_nonneg <| one_le_mulHeight₁ x

end Height
