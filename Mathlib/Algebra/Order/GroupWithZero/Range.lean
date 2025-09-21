/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.GroupWithZero.WithZero

/-! # The range of a MonoidWithZeroHom

Given a `MonoidWithZeroHom` `f : A → B` whose codomain `B` is a `LinearOrderedCommGroupWithZero`,
we provide some order properties of the `MonoidWithZeroHom.valueGroup₀` as defined in
`Mathlib.Algebra.GroupWithZero.Range`.

-/

namespace MonoidWithZeroHom

variable {A B : Type*}
variable [MonoidWithZero A] [LinearOrderedCommGroupWithZero B]
variable {f : A →*₀ B}

open WithZero

/-- The inclusion of `valueGroup₀ f` into `WithZero Bˣ` as an homomorphism of monoids with zero. -/
@[simps!]
def valueGroup₀.MonoidWithZeroHom : ValueGroup₀ f →*₀ WithZero Bˣ :=
  WithZero.map' (valueGroup f).subtype

lemma valueGroup₀.MonoidWithZeroHom_strictMono :
    StrictMono (valueGroup₀.MonoidWithZeroHom (f := f)):= map'_strictMono (Subtype.strictMono_coe _)

/-- The inclusion of `ValueGroup₀ f` into `WithZero Bˣ` as an order embedding. In general, prefer
the use of `valueGroup₀.MonoidWithZeroHom` and apply the above lemma
`valueGroup₀.MonoidWithZeroHom_strictMono` if properties about ordering are needed. -/
def valueGroup₀_OrderEmbedding : ValueGroup₀ f ↪o WithZero Bˣ where
  toFun := valueGroup₀.MonoidWithZeroHom
  inj' := valueGroup₀.MonoidWithZeroHom_strictMono.injective
  map_rel_iff' := valueGroup₀.MonoidWithZeroHom_strictMono.le_iff_le

@[simp]
lemma valueGroup₀_OrderEmbedding_apply (x : ValueGroup₀ f) :
    valueGroup₀_OrderEmbedding x = WithZero.map' (valueGroup f).subtype x := rfl

lemma valueGroup₀_OrderEmbedding_mul (x y : ValueGroup₀ f) :
    valueGroup₀_OrderEmbedding (x * y) =
      valueGroup₀_OrderEmbedding x * valueGroup₀_OrderEmbedding y := by simp

/-- The inclusion of `valueGroup₀ f` into `B` as an order embedding. -/
def valueGroup₀_OrderEmbedding' : ValueGroup₀ f ↪o B :=
  valueGroup₀_OrderEmbedding.trans OrderIso.withZeroUnits.toOrderEmbedding

lemma valueGroup₀_OrderEmbedding'_apply (x : ValueGroup₀ f) :
    valueGroup₀_OrderEmbedding' x =
      OrderIso.withZeroUnits.toOrderEmbedding (WithZero.map' (valueGroup f).subtype x) := rfl
lemma valueGroup₀_OrderEmbedding'_mul (x y : ValueGroup₀ f) :
    valueGroup₀_OrderEmbedding' (x * y) =
      valueGroup₀_OrderEmbedding' x * valueGroup₀_OrderEmbedding' y := by
  simp [valueGroup₀_OrderEmbedding'_apply, map_mul, OrderIso.withZeroUnits]

instance : IsOrderedMonoid B := inferInstance

instance : IsOrderedMonoid (WithZero Bˣ) := inferInstance

instance : IsOrderedMonoid (ValueGroup₀ f) :=
  Function.Injective.isOrderedMonoid valueGroup₀_OrderEmbedding' valueGroup₀_OrderEmbedding'_mul
    <| OrderEmbedding.le_iff_le valueGroup₀_OrderEmbedding'

instance : LinearOrderedCommGroupWithZero (ValueGroup₀ f) where
  zero_le_one := by simp

end MonoidWithZeroHom
