/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint

/-! # Big-operators lemmas about `star` algebraic operations

These results are kept separate from `Algebra.Star.Basic` to avoid it needing to import `Finset`.
-/


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
