/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags

/-!

# Order Monoid Isomorphisms on `Additve` and `Multiplicative`.

-/

section TypeTags

/-- Reinterpret `G ≃*o H` as `Additive G ≃+o Additive H`. -/
def OrderMonoidIso.toAdditive {G H : Type*}
    [CommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] :
    (G ≃*o H) ≃ (Additive G ≃+o Additive H) where
  toFun e := ⟨MulEquiv.toAdditive e, by simp⟩
  invFun e := ⟨MulEquiv.toAdditive.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/-- Reinterpret `G ≃+o H` as `Multiplicative G ≃*o Multiplicative H`. -/
def OrderAddMonoidIso.toMultiplicative {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] :
    (G ≃+o H) ≃ (Multiplicative G ≃*o Multiplicative H) where
  toFun e := ⟨AddEquiv.toMultiplicative e, by simp⟩
  invFun e := ⟨AddEquiv.toMultiplicative.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/-- Reinterpret `Additive G ≃+o H` as `G ≃*o Multiplicative H`. -/
def OrderAddMonoidIso.toMultiplicative' {G H : Type*}
    [CommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] :
    (Additive G ≃+o H) ≃ (G ≃*o Multiplicative H) where
  toFun e := ⟨AddEquiv.toMultiplicative' e, by simp⟩
  invFun e := ⟨AddEquiv.toMultiplicative'.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/-- Reinterpret `G ≃* Multiplicative H` as `Additive G ≃+ H`. -/
abbrev OrderMonoidIso.toAdditive' {G H : Type*}
    [CommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] :
    (G ≃*o Multiplicative H) ≃ (Additive G ≃+o H) :=
  OrderAddMonoidIso.toMultiplicative'.symm

/-- Reinterpret `G ≃+o Additive H` as `Multiplicative G ≃*o H`. -/
def OrderAddMonoidIso.toMultiplicative'' {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] :
    (G ≃+o Additive H) ≃ (Multiplicative G ≃*o H) where
  toFun e := ⟨AddEquiv.toMultiplicative'' e, by simp⟩
  invFun e := ⟨AddEquiv.toMultiplicative''.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/-- Reinterpret `Multiplicative G ≃*o H` as `G ≃+o Additive H` as. -/
abbrev OrderMonoidIso.toAdditive'' {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] :
    (Multiplicative G ≃*o H) ≃ (G ≃+o Additive H) :=
  OrderAddMonoidIso.toMultiplicative''.symm

/-- The multiplicative version of an additivized ordered monoid is order-mul-equivalent to itself.
-/
def OrderMonoidIso.toMultiplicative_toAdditive {G : Type*} [CommMonoid G] [PartialOrder G] :
    Multiplicative (Additive G) ≃*o G :=
  OrderAddMonoidIso.toMultiplicative'' <| OrderMonoidIso.toAdditive (.refl _)

/-- The additive version of an multiplicativized ordered additive monoid is
order-add-equivalent to itself. -/
def OrderAddMonoidIso.toAdditive_toMultiplicative {G : Type*} [AddCommMonoid G] [PartialOrder G] :
    Additive (Multiplicative G) ≃+o G :=
  OrderMonoidIso.toAdditive' <| OrderAddMonoidIso.toMultiplicative (.refl _)

instance Additive.instUniqueOrderAddMonoidIso {G H : Type*}
    [CommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] [Unique (G ≃*o H)] :
    Unique (Additive G ≃+o Additive H) :=
  OrderMonoidIso.toAdditive.symm.unique

instance Multiplicative.instUniqueOrderdMonoidIso {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] [Unique (G ≃+o H)] :
    Unique (Multiplicative G ≃*o Multiplicative H) :=
  OrderAddMonoidIso.toMultiplicative.symm.unique

end TypeTags
