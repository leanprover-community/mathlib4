/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Abhimanyu Pallavi Sudhir
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Ordered monoid instances on the space of germs of a function at a filter

For each of the following structures we prove that if `β` has this structure, then so does
`Germ l β`:

* `IsOrderedCancelMonoid` and `IsOrderedCancelAddMonoid`.

## Tags

filter, germ
-/

public section

namespace Filter.Germ

variable {α : Type*} {β : Type*} {l : Filter α}

@[to_additive]
instance instIsOrderedMonoid [CommMonoid β] [Preorder β] [IsOrderedMonoid β] :
    IsOrderedMonoid (Germ l β) where
  mul_le_mul_left := by
    intro a b hab c
    by_cases h : l.NeBot
    · induction a, b, c using inductionOn₃ with | coe a b c
      rw [coe_le] at hab
      rw [← coe_mul, ← coe_mul, coe_le]
      exact hab.mono fun x hx => mul_le_mul_left hx (c x)
    · simp only [le_def]
      rw [liftRel_iff_map₂_eq_const_true]
      exact (subsingleton_of_bot (Filter.not_neBot.1 h)).allEq _ _

@[to_additive]
instance instIsOrderedCancelMonoid [CommMonoid β] [Preorder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (Germ l β) where
  le_of_mul_le_mul_left := by
    intro u v w hvw
    by_cases h : l.NeBot
    · induction u, v, w using inductionOn₃ with | coe u v w
      rw [← coe_mul, ← coe_mul, coe_le] at hvw
      rw [coe_le]
      exact hvw.mono fun x hx => le_of_mul_le_mul_left' hx
    · simp only [le_def]
      rw [liftRel_iff_map₂_eq_const_true]
      exact (subsingleton_of_bot (Filter.not_neBot.1 h)).allEq _ _

@[to_additive]
instance instCanonicallyOrderedMul [Mul β] [LE β] [CanonicallyOrderedMul β] :
    CanonicallyOrderedMul (Germ l β) where
  le_mul_self := by
    intro x y
    by_cases h : l.NeBot
    · induction x, y using inductionOn₂ with | coe x y
      rw [← coe_mul, coe_le]
      exact .of_forall fun _ => le_mul_self
    · simp only [le_def]
      rw [liftRel_iff_map₂_eq_const_true]
      exact (subsingleton_of_bot (Filter.not_neBot.1 h)).allEq _ _
  le_self_mul := by
    intro x y
    by_cases h : l.NeBot
    · induction x, y using inductionOn₂ with | coe x y
      rw [← coe_mul, coe_le]
      exact .of_forall fun _ => le_self_mul
    · simp only [le_def]
      rw [liftRel_iff_map₂_eq_const_true]
      exact (subsingleton_of_bot (Filter.not_neBot.1 h)).allEq _ _

end Filter.Germ
