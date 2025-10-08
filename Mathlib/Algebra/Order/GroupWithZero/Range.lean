/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.GroupWithZero.WithZero

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
def ValueGroup₀.monoidWithZeroHom : ValueGroup₀ f →*₀ WithZero Bˣ :=
  WithZero.map' (valueGroup f).subtype

lemma ValueGroup₀.monoidWithZeroHom_strictMono :
    StrictMono (ValueGroup₀.monoidWithZeroHom (f := f)) :=
  map'_strictMono (Subtype.strictMono_coe _)

/-- The inclusion of `ValueGroup₀ f` into `WithZero Bˣ` as an order embedding. In general, prefer
the use of `ValueGroup₀.MonoidWithZeroHom` and apply the above lemma
`ValueGroup₀.MonoidWithZeroHom_strictMono` if properties about ordering are needed. -/
def ValueGroup₀_OrderEmbedding : ValueGroup₀ f ↪o WithZero Bˣ where
  toFun := ValueGroup₀.monoidWithZeroHom
  inj' := ValueGroup₀.monoidWithZeroHom_strictMono.injective
  map_rel_iff' := ValueGroup₀.monoidWithZeroHom_strictMono.le_iff_le

@[simp]
lemma ValueGroup₀_OrderEmbedding_apply (x : ValueGroup₀ f) :
    ValueGroup₀_OrderEmbedding x = WithZero.map' (valueGroup f).subtype x := rfl

lemma ValueGroup₀_OrderEmbedding_mul (x y : ValueGroup₀ f) :
    ValueGroup₀_OrderEmbedding (x * y) =
      ValueGroup₀_OrderEmbedding x * ValueGroup₀_OrderEmbedding y := by simp

/-- The inclusion of `ValueGroup₀ f` into `B` as an order embedding. -/
def ValueGroup₀_OrderEmbedding' : ValueGroup₀ f ↪o B :=
  ValueGroup₀_OrderEmbedding.trans OrderIso.withZeroUnits.toOrderEmbedding

lemma ValueGroup₀_OrderEmbedding'_apply (x : ValueGroup₀ f) :
    ValueGroup₀_OrderEmbedding' x =
      OrderIso.withZeroUnits.toOrderEmbedding (WithZero.map' (valueGroup f).subtype x) := rfl

lemma ValueGroup₀_OrderEmbedding'_mul (x y : ValueGroup₀ f) :
    ValueGroup₀_OrderEmbedding' (x * y) =
      ValueGroup₀_OrderEmbedding' x * ValueGroup₀_OrderEmbedding' y := by
  simp [ValueGroup₀_OrderEmbedding'_apply, map_mul, OrderIso.withZeroUnits]
instance : IsOrderedMonoid (ValueGroup₀ f) :=
  Function.Injective.isOrderedMonoid ValueGroup₀_OrderEmbedding' ValueGroup₀_OrderEmbedding'_mul
    <| OrderEmbedding.le_iff_le ValueGroup₀_OrderEmbedding'

instance : LinearOrderedCommGroupWithZero (ValueGroup₀ f) where
  zero_le_one := by simp

end MonoidWithZeroHom
