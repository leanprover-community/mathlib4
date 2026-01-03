/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.Algebra.Order.Hom.MonoidWithZero

/-! # The range of a MonoidWithZeroHom

Given a `MonoidWithZeroHom` `f : A → B` whose codomain `B` is a `LinearOrderedCommGroupWithZero`,
we provide some order properties of the `MonoidWithZeroHom.ValueGroup₀` as defined in
`Mathlib.Algebra.GroupWithZero.Range`.

-/

namespace MonoidWithZeroHom

variable {A B : Type*}
variable [MonoidWithZero A] [LinearOrderedCommGroupWithZero B]
variable {f : A →*₀ B}

open WithZero

/-- The inclusion of `ValueGroup₀ f` into `WithZero Bˣ` as an homomorphism of monoids with zero. -/
@[simps!]
def ValueGroup₀.orderMonoidWithZeroHom : ValueGroup₀ f →*₀o WithZero Bˣ where
  __ := WithZero.map' (valueGroup f).subtype
  monotone' := map'_strictMono (Subtype.strictMono_coe _)|>.monotone

lemma ValueGroup₀.monoidWithZeroHom_strictMono :
    StrictMono (ValueGroup₀.orderMonoidWithZeroHom (f := f)) :=
  map'_strictMono (Subtype.strictMono_coe _)

/-- The inclusion of `ValueGroup₀ f` into `WithZero Bˣ` as an order embedding. In general, prefer
the use of `ValueGroup₀.MonoidWithZeroHom` and apply the above lemma
`ValueGroup₀.MonoidWithZeroHom_strictMono` if properties about ordering are needed. -/
def ValueGroup₀.orderEmbedding : ValueGroup₀ f ↪o WithZero Bˣ where
  __ := ValueGroup₀.orderMonoidWithZeroHom
  inj' := ValueGroup₀.monoidWithZeroHom_strictMono.injective
  map_rel_iff' := ValueGroup₀.monoidWithZeroHom_strictMono.le_iff_le

@[simp]
lemma ValueGroup₀.orderEmbedding_apply (x : ValueGroup₀ f) :
    ValueGroup₀.orderEmbedding x = WithZero.map' (valueGroup f).subtype x := rfl

lemma ValueGroup₀.orderEmbedding_mul (x y : ValueGroup₀ f) :
    ValueGroup₀.orderEmbedding (x * y) =
      ValueGroup₀.orderEmbedding x * ValueGroup₀.orderEmbedding y := by simp

/-- The inclusion of `ValueGroup₀ f` into `B` as an order embedding. -/
def ValueGroup₀.orderEmbedding' : ValueGroup₀ f ↪o B :=
  ValueGroup₀.orderEmbedding.trans OrderIso.withZeroUnits.toOrderEmbedding

lemma ValueGroup₀.orderEmbedding'_apply (x : ValueGroup₀ f) :
    ValueGroup₀.orderEmbedding' x =
      OrderIso.withZeroUnits.toOrderEmbedding (WithZero.map' (valueGroup f).subtype x) := rfl

lemma ValueGroup₀.orderEmbedding'_mul (x y : ValueGroup₀ f) :
    ValueGroup₀.orderEmbedding' (x * y) =
      ValueGroup₀.orderEmbedding' x * ValueGroup₀.orderEmbedding' y := by
  simp [ValueGroup₀.orderEmbedding'_apply, map_mul, OrderIso.withZeroUnits]
instance : IsOrderedMonoid (ValueGroup₀ f) :=
  Function.Injective.isOrderedMonoid ValueGroup₀.orderEmbedding' ValueGroup₀.orderEmbedding'_mul
    <| OrderEmbedding.le_iff_le ValueGroup₀.orderEmbedding'

instance : LinearOrderedCommGroupWithZero (ValueGroup₀ f) where
  zero_le_one := by simp

end MonoidWithZeroHom
