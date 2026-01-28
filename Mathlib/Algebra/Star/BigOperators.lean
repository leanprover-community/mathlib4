/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Star.SelfAdjoint

/-! # Big-operators lemmas about `star` algebraic operations

These results are kept separate from `Algebra.Star.Basic` to avoid it needing to import `Finset`.
-/

public section


variable {R : Type*}

@[simp]
theorem star_prod [CommMonoid R] [StarMul R] {α : Type*} (s : Finset α) (f : α → R) :
    star (∏ x ∈ s, f x) = ∏ x ∈ s, star (f x) := map_prod (starMulAut : R ≃* R) _ _

@[simp]
theorem star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : Finset α) (f : α → R) :
    star (∑ x ∈ s, f x) = ∑ x ∈ s, star (f x) := map_sum (starAddEquiv : R ≃+ R) _ _

theorem isSelfAdjoint_sum {ι : Type*} [AddCommMonoid R] [StarAddMonoid R] (s : Finset ι)
    {x : ι → R} (h : ∀ i ∈ s, IsSelfAdjoint (x i)) : IsSelfAdjoint (∑ i ∈ s, x i) := by
  simpa [IsSelfAdjoint, star_sum] using Finset.sum_congr rfl fun _ hi => h _ hi

@[simp]
theorem star_finsuppSum {ι : Type*} {M : Type*} [Zero M] [AddCommMonoid R] [StarAddMonoid R]
    (s : ι →₀ M) (f : ι → M → R) : star (s.sum f) = s.sum (fun i m ↦ star f i m) := by
  simp [Finsupp.sum]

@[simp]
theorem star_finsuppProd {ι : Type*} {M : Type*} [Zero M] [CommMonoid R] [StarMul R]
    (s : ι →₀ M) (f : ι → M → R) : star (s.prod f) = s.prod (fun i m ↦ star f i m) := by
  simp [Finsupp.prod]
