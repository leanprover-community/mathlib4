/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
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

variable {A B : Type*}
variable [MonoidWithZero A] [LinearOrderedCommGroupWithZero B]
variable {f : A →*₀ B}

open WithZero

namespace ValueGroup₀

/-- The inclusion of `ValueGroup₀ f` into `WithZero Bˣ` as an homomorphism of monoids with zero. -/
@[simps!]
def orderMonoidWithZeroHom : ValueGroup₀ f →*₀o WithZero Bˣ where
  __ := WithZero.map' (valueGroup f).subtype
  monotone' := map'_strictMono (Subtype.strictMono_coe _)|>.monotone

lemma monoidWithZeroHom_strictMono :
    StrictMono (ValueGroup₀.orderMonoidWithZeroHom (f := f)) :=
  map'_strictMono (Subtype.strictMono_coe _)

/-- The inclusion of `ValueGroup₀ f` into `WithZero Bˣ` as an order embedding. In general, prefer
the use of `ValueGroup₀.MonoidWithZeroHom` and apply the above lemma
`ValueGroup₀.MonoidWithZeroHom_strictMono` if properties about ordering are needed. -/
def orderEmbedding : ValueGroup₀ f ↪o WithZero Bˣ where
  __ := ValueGroup₀.orderMonoidWithZeroHom
  inj' := monoidWithZeroHom_strictMono.injective
  map_rel_iff' := monoidWithZeroHom_strictMono.le_iff_le

@[simp]
lemma orderEmbedding_apply (x : ValueGroup₀ f) :
    orderEmbedding x = WithZero.map' (valueGroup f).subtype x := rfl

lemma orderEmbedding_mul (x y : ValueGroup₀ f) :
    orderEmbedding (x * y) =
      orderEmbedding x * orderEmbedding y := by simp

/-- The inclusion of `ValueGroup₀ f` into `B` as an order embedding. -/
def orderEmbedding' : ValueGroup₀ f ↪o B :=
  orderEmbedding.trans OrderIso.withZeroUnits.toOrderEmbedding

lemma orderEmbedding'_apply (x : ValueGroup₀ f) :
    orderEmbedding' x =
      OrderIso.withZeroUnits.toOrderEmbedding (WithZero.map' (valueGroup f).subtype x) := rfl

lemma orderEmbedding'_mul (x y : ValueGroup₀ f) :
    orderEmbedding' (x * y) = orderEmbedding' x * orderEmbedding' y := by
  simp [orderEmbedding'_apply, map_mul, OrderIso.withZeroUnits]
instance : IsOrderedMonoid (ValueGroup₀ f) :=
  Function.Injective.isOrderedMonoid orderEmbedding' orderEmbedding'_mul
    <| OrderEmbedding.le_iff_le orderEmbedding'

instance : LinearOrderedCommGroupWithZero (ValueGroup₀ f) where
  zero_le := by simp
  mul_lt_mul_of_pos_left a ha b c hbc := by
    simp only [← OrderEmbedding.lt_iff_lt orderEmbedding', orderEmbedding'_mul] at *
    exact (mul_lt_mul_iff_of_pos_left ha).mpr hbc

lemma orderEmbedding'_eq_embedding (x : ValueGroup₀ f) :
    orderEmbedding' x = embedding x := by simp [embedding_apply, orderEmbedding'_apply]

lemma embedding_strictMono :
    StrictMono (embedding (f := f)) := by
  intro x y hxy
  simp only [← orderEmbedding'_eq_embedding]
  exact (OrderEmbedding.lt_iff_lt orderEmbedding').mpr hxy

lemma embedding_unit_pos (a : (ValueGroup₀ f)ˣ) :
    0 < embedding a.1 := by
  --rw [← map_zero f, ← embedding_restrict₀ (0 : A)] -- fails; problem with Dec. inst.
  conv_lhs => rw [← map_zero f, ← ValueGroup₀.embedding_restrict₀ (0 : A)]
  rw [embedding_strictMono.lt_iff_lt]
  simp

lemma embedding_unit_ne_zero (a : (ValueGroup₀ f)ˣ) :
    embedding a.1 ≠ 0 := (embedding_unit_pos a).ne.symm

end ValueGroup₀

end MonoidWithZeroHom
