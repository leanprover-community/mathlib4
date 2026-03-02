/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.Algebra.Order.Monoid.Basic

/-! # The range of a MonoidWithZeroHom

Given a `MonoidWithZeroHom` `f : A → B` whose codomain `B` is a `LinearOrderedCommGroupWithZero`,
we provide some order properties of the `MonoidWithZeroHom.ValueGroup₀` as defined in
`Mathlib.Algebra.GroupWithZero.Range`.

-/

@[expose] public section

namespace MonoidWithZeroHom

variable {A B : Type*} [MonoidWithZero A] [LinearOrderedCommGroupWithZero B] {f : A →*₀ B}

namespace ValueGroup₀

open WithZero

variable (f) in
/-- The inclusion of `ValueGroup₀ f` into `WithZero Bˣ` as a homomorphism of monoids with zero. -/
def orderMonoidWithZeroHom : ValueGroup₀ f →*₀o WithZero Bˣ where
  __ := WithZero.map' (valueGroup f).subtype
  monotone' := map'_strictMono (Subtype.strictMono_coe _)|>.monotone

lemma monoidWithZeroHom_strictMono :
    StrictMono (orderMonoidWithZeroHom f) :=
  map'_strictMono (Subtype.strictMono_coe _)

variable (f) in
/-- The inclusion of `ValueGroup₀ f` into `WithZero Bˣ` as an order embedding. In general, prefer
the use of `MonoidWithZeroHom` and apply the above lemma
`MonoidWithZeroHom_strictMono` if properties about ordering are needed. -/
def orderEmbedding : ValueGroup₀ f ↪o WithZero Bˣ where
  __ := orderMonoidWithZeroHom f
  inj' := monoidWithZeroHom_strictMono.injective
  map_rel_iff' := monoidWithZeroHom_strictMono.le_iff_le

@[simp]
lemma orderEmbedding_apply (x : ValueGroup₀ f) :
    orderEmbedding f x = orderMonoidWithZeroHom f x := rfl

lemma orderEmbedding_mul (x y : ValueGroup₀ f) :
    orderEmbedding f (x * y) = orderEmbedding f x * orderEmbedding f y := by simp

instance : IsOrderedMonoid (ValueGroup₀ f) :=
  Function.Injective.isOrderedMonoid (orderEmbedding f) orderEmbedding_mul
    <| OrderEmbedding.le_iff_le (orderEmbedding f)

instance : LinearOrderedCommGroupWithZero (ValueGroup₀ f) where
  zero_le := by simp
  mul_lt_mul_of_pos_left a ha b c hbc := by
    simp only [← OrderEmbedding.lt_iff_lt (orderEmbedding f), orderEmbedding_mul] at *
    exact (mul_lt_mul_iff_of_pos_left ha).mpr hbc

end ValueGroup₀

end MonoidWithZeroHom
