/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Majorization

Given two vectors `x y : n → R` (with `n` finite), we say that

* `y` submajorizes `x` (`x ≼ₛ y`) if `∀ k, ∑ i ≤ k, x↓ i ≤ ∑ i ≤ k, y↓ i` where `x↓` denotes
the values of `x` sorted in decreasing order (this notation is not used here, only in the
docstring).
* `y` supermajorizes `x` (`x ≼ˢ y`) if `∀ k, ∑ i ≤ k, y↑ i ≤ ∑ i ≤ k, x↑ i`.
* `y` majorizes `x` (`x ≼ y`) if `x ≼ₛ y` and `∑ i, x i = ∑ i, y i`.

This file provides the bare definitions for the above, as well as for increasing and
decreasing sums.

## Main definitions

* `Fintype.incSum k x`: The sum of the `k` smallest elements of `x`.
* `Fintype.decSum k x`: The sum of the `k` largest elements of `x`.
* `IsSubmajorizedBy x y`, `x` is submajorized by `y` (notation: `x ≼ₛ y`)
* `IsSupermajorizedBy x y`, `x` is supermajorized by `y` (notation: `x ≼ˢ y`)
* `IsMajorizedBy x y`, `x` is majorized by `y` (notation: `x ≼ y`)

## Notation

The above notation is available in the scope `Majorization`.

## Implementation notes

There are several characterizations of this notion, and one that is more amenable to
formalization (since it avoids having to introduce equivs to sort values), is the one that
makes use of the fact that
`∑ i ≤ k, x↓ i = max_{s, #s = k} ∑ i ∈ s, x i`
and likewise for the increasing sum. This is what we take as the definition here.

## References

* [Rajendra Bhatia, *Matrix Analysis*, Chapter 2][bhatia1997]
-/

@[expose] public section

namespace Fintype
open Finset

variable {n m R : Type*} [Fintype n] [LinearOrder R] [Semiring R]
  [Fintype m]

open Function Finset

/-- The sum of the `k` smallest elements of `x`. -/
irreducible_def incSum (k : ℕ) (x : n → R) : R :=
  if h : k ≤ card n then
    min' ((powersetCard k (univ : Finset n)).image fun s => ∑ i ∈ s, x i) <| by simp [h]
  else ∑ i, x i

/-- The sum of the `k` largest elements of `x`. -/
irreducible_def decSum (k : ℕ) (x : n → R) : R :=
  if h : k ≤ card n then
    max' ((powersetCard k (univ : Finset n)).image fun s => ∑ i ∈ s, x i) <| by simp [h]
  else ∑ i, x i

/-- An arbitrary set that achieves the value of `incSum k x`. -/
noncomputable irreducible_def incSumSet (k : ℕ) (x : n → R) :=
  if hk : k ≤ card n then
    Classical.choose (exists_min'_image (powersetCard k (univ : Finset n))
      (fun s => ∑ i ∈ s, x i) (by grind))
  else ∅

/-- An arbitrary set that achieves the value of `decSum k x`. -/
noncomputable irreducible_def decSumSet (k : ℕ) (x : n → R) :=
  if hk : k ≤ card n then
    Classical.choose (exists_max'_image (powersetCard k (univ : Finset n))
      (fun s => ∑ i ∈ s, x i) (by grind))
  else ∅

end Fintype

section majorization
open Fintype

variable {m n R : Type*} [Fintype m] [Fintype n] [LinearOrder R] [Semiring R]

/-- `x` is submajorized by `y` if the sum of the `k` largest elements of `y` is at least
as large as the largest `k` elements of `x`, for all `k` -/
def IsSubmajorizedBy (x : m → R) (y : n → R) :=
  ∀ k, decSum k x ≤ decSum k y

/-- `x` is supermajorized by `y` if the sum of the `k` smallest elements of `y` is at most
as large as the smallest `k` elements of `x`, for all `k`. -/
def IsSupermajorizedBy (x : m → R) (y : n → R) :=
  ∀ k, incSum k y ≤ incSum k x

/-- `x` is majorized by `y` if `x` is submajorized by `y` and they have equal sums. -/
def IsMajorizedBy (x : m → R) (y : n → R) := IsSubmajorizedBy x y ∧ ∑ i, x i = ∑ i, y i

/-- The supermajorization relation on vectors. -/
scoped[Majorization] infixl:50 " ≼ˢ " => IsSupermajorizedBy
/-- The submajorization relation on vectors. -/
scoped[Majorization] infixl:50 " ≼ₛ " => IsSubmajorizedBy
/-- The majorization relation on vectors. -/
scoped[Majorization] infixl:50 " ≼ " => IsMajorizedBy

open scoped Majorization

lemma isSubmajorizedBy_def (x : m → R) (y : n → R) :
  x ≼ₛ y ↔ ∀ k, decSum k x ≤ decSum k y := Iff.rfl

lemma isSupermajorizedBy_def (x : m → R) (y : n → R) :
  x ≼ˢ y ↔ ∀ k, incSum k y ≤ incSum k x := Iff.rfl

lemma isMajorizedBy_def (x : m → R) (y : n → R) :
  x ≼ y ↔ x ≼ₛ y ∧ ∑ i, x i = ∑ i, y i := Iff.rfl

@[trans]
lemma IsSubmajorizedBy.trans {o : Type*} [Fintype o] {x : m → R} {y : n → R} {z : o → R}
    (h₁ : x ≼ₛ y) (h₂ : y ≼ₛ z) : x ≼ₛ z := by
  rw [isSubmajorizedBy_def] at h₁ h₂ ⊢
  grind

instance transIsSubmajorizedByIsSubmajorizedBy {o : Type*} [Fintype o] :
    @Trans (m → R) (n → R) (o → R) (· ≼ₛ ·) (· ≼ₛ ·) (· ≼ₛ ·) where
  trans := IsSubmajorizedBy.trans

@[trans]
lemma IsSupermajorizedBy.trans {o : Type*} [Fintype o] {x : m → R} {y : n → R} {z : o → R}
    (h₁ : x ≼ˢ y) (h₂ : y ≼ˢ z) : x ≼ˢ z := by
  rw [isSupermajorizedBy_def] at h₁ h₂ ⊢
  grind

instance transIsSupermajorizedByIsSupermajorizedBy {o : Type*} [Fintype o] :
    @Trans (m → R) (n → R) (o → R) (· ≼ˢ ·) (· ≼ˢ ·) (· ≼ˢ ·) where
  trans := IsSupermajorizedBy.trans

@[trans]
lemma IsMajorizedBy.trans {o : Type*} [Fintype o] {x : m → R} {y : n → R} {z : o → R}
    (h₁ : x ≼ y) (h₂ : y ≼ z) : x ≼ z := by
  rw [isMajorizedBy_def] at h₁ h₂ ⊢
  exact ⟨h₁.1.trans h₂.1, by grind⟩

instance transIsMajorizedByIsMajorizedBy {o : Type*} [Fintype o] :
    @Trans (m → R) (n → R) (o → R) (· ≼ ·) (· ≼ ·) (· ≼ ·) where
  trans := IsMajorizedBy.trans


end majorization
