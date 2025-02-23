/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic

/-!
# Nonarchimedean absolute values

An absolute value `f` is nonarchimedean if it satisfies `f (x + y) ≤ max (f x) (f y)` for all
`x` and `y` in `R`.
-/

variable {α R S : Type*}

namespace AbsoluteValue

section LinearOrderedSemiring

variable [LinearOrderedSemiring S]

/-- An absolute value `f` is nonarchimedean if it satisfies `f (x + y) ≤ max (f x) (f y)` for all
`x` and `y` in `R`. -/
def IsNonarchimedean [Semiring R] (f : AbsoluteValue R S) : Prop :=
  ∀ x y : R, f (x + y) ≤ max (f x) (f y)

open Finset in
/-- Ultrametric inequality with `Finset.Sum`. -/
lemma apply_sum_le_sup_of_isNonarchimedean [Semiring R] {f : AbsoluteValue R S}
    (nonarch : IsNonarchimedean f) {s : Finset α} (hnonempty : s.Nonempty) {l : α → R} :
    f (∑ i ∈ s, l i) ≤ s.sup' hnonempty fun i => f (l i) := by
  induction hnonempty using Nonempty.cons_induction with
  | singleton i => simp
  | cons i s _ hs hind =>
    simp only [sum_cons, le_sup'_iff, mem_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
    rcases le_max_iff.mp <| nonarch (l i) (∑ i ∈ s, l i) with h₁ | h₂
    · exact .inl h₁
    · exact .inr <| le_trans h₂ hind

end LinearOrderedSemiring

section LinearOrderedRing

variable [Semiring R] [Nontrivial R] [LinearOrderedRing S]

lemma apply_nat_le_one_of_isNonarchimedean {abv : AbsoluteValue R S}
    (nonarch : IsNonarchimedean abv) (n : ℕ) : abv n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n hn =>
    push_cast
    exact le_trans (nonarch n 1) (max_le hn <| le_of_eq abv.map_one)

end LinearOrderedRing

section LinearOrderedCommRing

section Ring

variable [Ring R] [LinearOrderedCommRing S]

lemma apply_int_le_one_of_isNonarchimedean [Nontrivial R] {abv : AbsoluteValue R S}
    (nonarch : IsNonarchimedean abv) (x : ℤ) : abv x ≤ 1 := by
  rw [← AbsoluteValue.apply_natAbs_eq]
  exact apply_nat_le_one_of_isNonarchimedean nonarch x.natAbs

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
