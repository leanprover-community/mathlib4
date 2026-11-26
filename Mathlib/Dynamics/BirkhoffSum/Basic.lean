/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Birkhoff sums

In this file we define `birkhoffSum f g n x` to be the sum `∑ k ∈ Finset.range n, g (f^[k] x)`.
This sum (more precisely, the corresponding average `n⁻¹ • birkhoffSum f g n x`)
appears in various ergodic theorems
saying that these averages converge to the "space average" `⨍ x, g x ∂μ` in some sense.

See also `birkhoffAverage` defined in `Dynamics/BirkhoffSum/Average`.
-/

@[expose] public section

open Finset Function

section AddCommMonoid

variable {α M : Type*} [AddCommMonoid M]

/-- The sum of values of `g` on the first `n` points of the orbit of `x` under `f`. -/
def birkhoffSum (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := ∑ k ∈ range n, g (f^[k] x)

theorem birkhoffSum_zero_apply (f : α → α) (g : α → M) (x : α) : birkhoffSum f g 0 x = 0 :=
  sum_range_zero _

@[simp]
theorem birkhoffSum_zero (f : α → α) (g : α → M) : birkhoffSum f g 0 = 0 :=
  funext <| birkhoffSum_zero_apply _ _

@[deprecated (since := "2026-08-06")] alias birkhoffSum_zero' := birkhoffSum_zero

theorem birkhoffSum_one_apply (f : α → α) (g : α → M) (x : α) : birkhoffSum f g 1 x = g x :=
  sum_range_one _

@[simp]
theorem birkhoffSum_one (f : α → α) (g : α → M) : birkhoffSum f g 1 = g :=
  funext <| birkhoffSum_one_apply f g

@[deprecated (since := "2026-08-06")] alias birkhoffSum_one' := birkhoffSum_one

theorem birkhoffSum_succ_apply (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffSum f g (n + 1) x = birkhoffSum f g n x + g (f^[n] x) :=
  sum_range_succ _ _

theorem birkhoffSum_succ (f : α → α) (g : α → M) (n : ℕ) :
    birkhoffSum f g (n + 1) = birkhoffSum f g n + g ∘ f^[n] :=
  funext <| birkhoffSum_succ_apply f g n

theorem birkhoffSum_succ_apply' (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffSum f g (n + 1) x = g x + birkhoffSum f g n (f x) :=
  (sum_range_succ' _ _).trans (add_comm _ _)

theorem birkhoffSum_succ' (f : α → α) (g : α → M) (n : ℕ) :
    birkhoffSum f g (n + 1) = g + birkhoffSum f g n ∘ f :=
  funext <| birkhoffSum_succ_apply' f g n

theorem birkhoffSum_add_apply (f : α → α) (g g' : α → M) (n : ℕ) (x : α) :
    birkhoffSum f (g + g') n x = birkhoffSum f g n x + birkhoffSum f g' n x := by
  simpa [birkhoffSum] using sum_add_distrib

theorem birkhoffSum_add (f : α → α) (g g' : α → M) :
    birkhoffSum f (g + g') = birkhoffSum f g + birkhoffSum f g' :=
  funext₂ <| birkhoffSum_add_apply f g g'

theorem birkhoffSum_add_right_apply (f : α → α) (g : α → M) (m n : ℕ) (x : α) :
    birkhoffSum f g (m + n) x = birkhoffSum f g m x + birkhoffSum f g n (f^[m] x) := by
  simp_rw [birkhoffSum, sum_range_add, add_comm m, iterate_add_apply]

theorem birkhoffSum_add_right (f : α → α) (g : α → M) (m n : ℕ) :
    birkhoffSum f g (m + n) = birkhoffSum f g m + birkhoffSum f g n ∘ f^[m] :=
  funext <| birkhoffSum_add_right_apply f g m n

theorem Function.IsFixedPt.birkhoffSum_eq {f : α → α} {x : α} (h : IsFixedPt f x) (g : α → M)
    (n : ℕ) : birkhoffSum f g n x = n • g x := by
  simp [birkhoffSum, (h.iterate _).eq]

theorem map_birkhoffSum {F N : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (g' : F) (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    g' (birkhoffSum f g n x) = birkhoffSum f (g' ∘ g) n x :=
  map_sum g' _ _

theorem map_comp_birkhoffSum {F N : Type*} [AddCommMonoid N] [FunLike F M N]
    [AddMonoidHomClass F M N] (g' : F) (f : α → α) (g : α → M) (n : ℕ) :
    ⇑g' ∘ birkhoffSum f g n = birkhoffSum f (g' ∘ g) n :=
  funext <| map_birkhoffSum g' f g n

/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`), then the Birkhoff sum
of `φ` over `f` for `n` iterations is equal to `n • φ x` at every point `x`. -/
theorem birkhoffSum_apply_of_comp_eq {f : α → α} {φ : α → M} (h : φ ∘ f = φ) (n : ℕ) (x : α) :
    birkhoffSum f φ n x = n • φ x := by
  suffices ∀ k, φ (f^[k] x) = φ x by simp [birkhoffSum, this]
  intro k
  exact congrFun (iterate_invariant h k) x

/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`), then the Birkhoff sum
of `φ` over `f` for `n` iterations is equal to `n • φ`. -/
theorem birkhoffSum_of_comp_eq {f : α → α} {φ : α → M} (h : φ ∘ f = φ) (n : ℕ) :
    birkhoffSum f φ n = n • φ :=
  funext <| birkhoffSum_apply_of_comp_eq h n

end AddCommMonoid

section AddCommGroup

variable {α G : Type*} [AddCommGroup G]

theorem birkhoffSum_neg_apply (f : α → α) (g : α → G) (n : ℕ) (x : α) :
    birkhoffSum f (-g) n x = -birkhoffSum f g n x := by
  simp [birkhoffSum]

theorem birkhoffSum_neg (f : α → α) (g : α → G) :
    birkhoffSum f (-g) = -birkhoffSum f g :=
  funext₂ <| birkhoffSum_neg_apply f g

theorem birkhoffSum_sub_apply (f : α → α) (g g' : α → G) (n : ℕ) (x : α) :
    birkhoffSum f (g - g') n x = birkhoffSum f g n x - birkhoffSum f g' n x := by
  simp [birkhoffSum]

theorem birkhoffSum_sub (f : α → α) (g g' : α → G) :
    birkhoffSum f (g - g') = birkhoffSum f g - birkhoffSum f g' :=
  funext₂ <| birkhoffSum_sub_apply f g g'

/-- Birkhoff sum is "almost invariant" under `f`:
the difference between `birkhoffSum f g n (f x)` and `birkhoffSum f g n x`
is equal to `g (f^[n] x) - g x`. -/
theorem birkhoffSum_apply_sub_birkhoffSum (f : α → α) (g : α → G) (n : ℕ) (x : α) :
    birkhoffSum f g n (f x) - birkhoffSum f g n x = g (f^[n] x) - g x := by
  rw [← sub_eq_iff_eq_add.2 (birkhoffSum_succ_apply f g n x),
    ← sub_eq_iff_eq_add.2 (birkhoffSum_succ_apply' f g n x),
    ← sub_add, ← sub_add, sub_add_comm]

/-- Birkhoff sum is "almost invariant" under `f`:
the difference between `birkhoffSum f g n ∘ f` and `birkhoffSum f g n`
is equal to `g ∘ f^[n] - g`. -/
theorem birkhoffSum_comp_sub_birkhoffSum (f : α → α) (g : α → G) (n : ℕ) :
    birkhoffSum f g n ∘ f - birkhoffSum f g n = g ∘ f^[n] - g :=
  funext <| birkhoffSum_apply_sub_birkhoffSum f g n

end AddCommGroup
