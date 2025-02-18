/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic

/-!
# Nonarchimedean absolute values

An `AbsoluteValue` `f` is nonarchimean if it satisfies `f (x + y) ≤ max (f x) (f y)` for all
`x` and `y` in `R`.
-/

variable {α R S : Type*}

namespace AbsoluteValue

section LinearOrderedSemiring

variable [Semiring R] [LinearOrderedSemiring S]

/--An `AbsoluteValue` `f` is nonarchimean if it satisfies `f (x + y) ≤ max (f x) (f y)` for all
`x` and `y` in `R`-/
def IsNonarchimedean  (f : AbsoluteValue R S) : Prop := ∀ x y : R, f (x + y) ≤ max (f x) (f y)

open Finset in
/--Ultrametric inequality with Finset.Sum-/
lemma sum_le_sup_of_isNonarchimedean {f : AbsoluteValue R S} (nonarch : IsNonarchimedean f)
    {s : Finset α} (hnonempty : s.Nonempty) {l : α → R} :
    f (∑ i ∈ s, l i) ≤ s.sup' hnonempty fun i => f (l i) := by
  apply Nonempty.cons_induction (p := fun a hn ↦ f (∑ i ∈ a, l i) ≤ a.sup' hn fun i ↦ f (l i))
  · simp
  · intro a s _ hs hind
    simp only [le_sup'_iff, mem_cons, sum_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
    rcases le_max_iff.mp <| nonarch (l a) (∑ i ∈ s, l i) with h₁ | h₂
    · exact .inl h₁
    · exact .inr <| le_trans h₂ hind

end LinearOrderedSemiring

section LinearOrderedRing

variable [Semiring R] [Nontrivial R] [LinearOrderedRing S]

lemma apply_nat_le_one_of_isNonarchimedean {abv : AbsoluteValue R S}
    (nonarch : AbsoluteValue.IsNonarchimedean abv) (n : ℕ) : abv n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n hn =>
    push_cast
    exact le_trans (nonarch n 1) (max_le hn <| le_of_eq abv.map_one)

end LinearOrderedRing

section LinearOrderedCommRing

section Ring

variable [Ring R] [Nontrivial R] [LinearOrderedCommRing S]

lemma apply_int_le_one_of_isNonarchimedean {abv : AbsoluteValue R S}
    (nonarch : IsNonarchimedean abv) (x : ℤ) : abv x ≤ 1 := by
  rw [← AbsoluteValue.apply_natAbs_eq]
  exact apply_nat_le_one_of_isNonarchimedean nonarch x.natAbs

end Ring

end LinearOrderedCommRing

end AbsoluteValue
