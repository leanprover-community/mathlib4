/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Birkhoff sums

In this file we define `birkhoffSum f g n x` to be the sum `∑ k in Finset.range n, g (f^[k] x)`.
This sum (more precisely, the corresponding average `n⁻¹ • birkhoffSum f g n x`)
appears in various ergodic theorems
saying that these averages converge to the "space average" `⨍ x, g x ∂μ` in some sense.

See also `birkhoffAverage` defined in `Dynamics/BirkhoffSum/Average`.
-/

open Finset Function
open scoped BigOperators

section AddCommMonoid

variable {α M : Type*} [AddCommMonoid M]

/-- The sum of values of `g` on the first `n` points of the orbit of `x` under `f`. -/
def birkhoffSum (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := ∑ k in range n, g (f^[k] x)

theorem birkhoffSum_zero (f : α → α) (g : α → M) (x : α) : birkhoffSum f g 0 x = 0 :=
  sum_range_zero _

@[simp]
theorem birkhoffSum_zero' (f : α → α) (g : α → M) : birkhoffSum f g 0 = 0 :=
  funext <| birkhoffSum_zero _ _

theorem birkhoffSum_one (f : α → α) (g : α → M) (x : α) : birkhoffSum f g 1 x = g x :=
  sum_range_one _

@[simp]
theorem birkhoffSum_one' (f : α → α) (g : α → M) : birkhoffSum f g 1 = g :=
  funext <| birkhoffSum_one f g

theorem birkhoffSum_succ (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffSum f g (n + 1) x = birkhoffSum f g n x + g (f^[n] x) :=
  sum_range_succ _ _

theorem birkhoffSum_succ' (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffSum f g (n + 1) x = g x + birkhoffSum f g n (f x) :=
  (sum_range_succ' _ _).trans (add_comm _ _)

theorem birkhoffSum_add (f : α → α) (g : α → M) (m n : ℕ) (x : α) :
    birkhoffSum f g (m + n) x = birkhoffSum f g m x + birkhoffSum f g n (f^[m] x) := by
  simp_rw [birkhoffSum, sum_range_add, add_comm m, iterate_add_apply]
  -- 🎉 no goals

theorem Function.IsFixedPt.birkhoffSum_eq {f : α → α} {x : α} (h : IsFixedPt f x) (g : α → M)
    (n : ℕ) : birkhoffSum f g n x = n • g x := by
  simp [birkhoffSum, (h.iterate _).eq]
  -- 🎉 no goals

theorem map_birkhoffSum {F N : Type*} [AddCommMonoid N] [AddMonoidHomClass F M N]
    (g' : F) (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    g' (birkhoffSum f g n x) = birkhoffSum f (g' ∘ g) n x :=
  map_sum g' _ _

end AddCommMonoid

section AddCommGroup

variable {α G : Type*} [AddCommGroup G]

/-- Birkhoff sum is "almost invariant" under `f`:
the difference between `birkhoffSum f g n (f x)` and `birkhoffSum f g n x`
is equal to `g (f^[n] x) - g x`. -/
theorem birkhoffSum_apply_sub_birkhoffSum (f : α → α) (g : α → G) (n : ℕ) (x : α) :
    birkhoffSum f g n (f x) - birkhoffSum f g n x = g (f^[n] x) - g x := by
  rw [← sub_eq_iff_eq_add.2 (birkhoffSum_succ f g n x),
    ← sub_eq_iff_eq_add.2 (birkhoffSum_succ' f g n x),
    ← sub_add, ← sub_add, sub_add_comm]

end AddCommGroup
