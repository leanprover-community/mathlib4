/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-!
# Nonarchimedean absolute values

An absolute value `f` is nonarchimedean if it satisfies `f (x + y) ≤ max (f x) (f y)` for all
`x` and `y` in `R`.
-/

variable {α R S : Type*}

namespace AbsoluteValue

section LinearOrderedSemiring

variable [LinearOrderedSemiring S]

end LinearOrderedSemiring

section LinearOrderedRing

variable [Semiring R] [Nontrivial R] [LinearOrderedRing S]

lemma apply_natCast_le_one_of_isNonarchimedean {abv : AbsoluteValue R S}
    (nonarch : IsNonarchimedean abv) (n : ℕ) : abv n ≤ 1 := by
  exact IsNonarchimedean.apply_natCast_le_one_of_isNonarchimedean nonarch

end LinearOrderedRing

section LinearOrderedCommRing

section Ring

variable [Ring R] [LinearOrderedCommRing S]

lemma apply_intCast_le_one_of_isNonarchimedean [Nontrivial R] {abv : AbsoluteValue R S}
    (nonarch : IsNonarchimedean abv) (x : ℤ) : abv x ≤ 1 := by
  refine IsNonarchimedean.apply_intCast_le_one_of_isNonarchimedean nonarch ?_
  exact fun a ↦ AbsoluteValue.map_neg abv a

lemma apply_sum_eq_of_lt {f : AbsoluteValue R S} (nonarch : IsNonarchimedean f) {x y : R}
    (h_ne : f x < f y) : f (x + y) = f y := by
  by_contra! h
  have h1 : f (x + y) ≤ f y := le_trans (nonarch x y) (le_of_eq <| max_eq_right_of_lt h_ne)
  apply lt_irrefl (f y)
  calc
    f y = f (y + x + -x) := by simp
    _   ≤ max (f (y + x)) (f (-x)) := nonarch (y + x) (-x)
    _   < max (f y) (f y) := by
      rw [max_self, AbsoluteValue.map_neg, add_comm]
      exact max_lt (lt_of_le_of_ne h1 h) h_ne
    _   = f y := max_self (f y)

lemma apply_sum_eq_max_of_ne {f : AbsoluteValue R S} (nonarch : IsNonarchimedean f) {x y : R}
    (h_ne : f x ≠ f y) : f (x + y) = max (f x) (f y) := by
  rcases h_ne.lt_or_lt with h_lt | h_lt
  · rw [apply_sum_eq_of_lt nonarch h_lt]
    exact (max_eq_right_of_lt h_lt).symm
  · rw [add_comm, apply_sum_eq_of_lt nonarch h_lt]
    exact (max_eq_left_of_lt h_lt).symm

end Ring

end LinearOrderedCommRing

end AbsoluteValue

#min_imports
