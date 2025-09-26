/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Hom.Ring

/-!
### Uniqueness of ring homomorphisms to archimedean fields.

There is at most one ordered ring homomorphism from a linear ordered field to an archimedean linear
ordered field. Reciprocally, such an ordered ring homomorphism exists when the codomain is further
conditionally complete.
-/

assert_not_exists Finset

variable {α β : Type*} [Field α] [LinearOrder α] [Field β] [LinearOrder β]

/-- There is at most one ordered ring homomorphism from a linear ordered field to an archimedean
linear ordered field. -/
instance OrderRingHom.subsingleton [IsStrictOrderedRing β] [Archimedean β] :
    Subsingleton (α →+*o β) :=
  ⟨fun f g => by
    ext x
    by_contra! h' : f x ≠ g x
    wlog h : f x < g x with h₂
    · exact h₂ g f x (Ne.symm h') (h'.lt_or_gt.resolve_left h)
    obtain ⟨q, hf, hg⟩ := exists_rat_btwn h
    rw [← map_ratCast f] at hf
    rw [← map_ratCast g] at hg
    exact
      (lt_asymm ((OrderHomClass.mono g).reflect_lt hg) <|
          (OrderHomClass.mono f).reflect_lt hf).elim⟩

/-- There is at most one ordered ring isomorphism between a linear ordered field and an archimedean
linear ordered field. -/
instance OrderRingIso.subsingleton_right [IsStrictOrderedRing β] [Archimedean β] :
    Subsingleton (α ≃+*o β) :=
  OrderRingIso.toOrderRingHom_injective.subsingleton

/-- There is at most one ordered ring isomorphism between an archimedean linear ordered field and a
linear ordered field. -/
instance OrderRingIso.subsingleton_left [IsStrictOrderedRing α] [Archimedean α] :
    Subsingleton (α ≃+*o β) :=
  OrderRingIso.symm_bijective.injective.subsingleton

theorem OrderRingHom.eq_id [IsStrictOrderedRing α] [Archimedean α] (f : α →+*o α) : f = .id _ :=
  Subsingleton.elim ..

theorem OrderRingIso.eq_refl [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α) : f = .refl _ :=
  Subsingleton.elim ..

theorem OrderRingHom.apply_eq_self [IsStrictOrderedRing α] [Archimedean α] (f : α →+*o α) (x : α) :
    f x = x := by
  rw [f.eq_id]; rfl

theorem OrderRingIso.apply_eq_self [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α) (x : α) :
    f x = x :=
  f.toOrderRingHom.apply_eq_self x
