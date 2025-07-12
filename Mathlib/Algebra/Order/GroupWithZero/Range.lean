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

variable {A B F : Type*} [FunLike F A B]
variable [MonoidWithZero A] [LinearOrderedCommGroupWithZero B]
variable [MonoidWithZeroHomClass F A B] {f : F}

open WithZero

/-- The inclusion of `valueGroup₀ f` into `WithZero Bˣ` as an monoid with zero hom. -/
@[simps!]
def valueGroup₀_MonoidWithZeroHom : valueGroup₀ f →*₀ WithZero Bˣ :=
  WithZero.map' (valueGroup f).subtype

lemma valueGroup₀_MonoidWithZeroHom_strictMono :
    StrictMono (valueGroup₀_MonoidWithZeroHom (f := f)) :=
  map'_strictMono (Subtype.strictMono_coe _)

/-- The inclusion of `valueGroup₀ f` into `WithZero Bˣ` as an order embedding. -/
@[simps!]
def valueGroup₀_OrderEmbedding : valueGroup₀ f ↪o WithZero Bˣ where
  toFun := valueGroup₀_MonoidWithZeroHom
  inj' := valueGroup₀_MonoidWithZeroHom_strictMono.injective
  map_rel_iff' := valueGroup₀_MonoidWithZeroHom_strictMono.le_iff_le

instance : IsOrderedMonoid B := inferInstance
instance : IsOrderedMonoid (WithZero Bˣ) := .comap WithZero.withZeroUnitsEquiv_strictMono
instance : IsOrderedMonoid (valueGroup₀ f) := .comap valueGroup₀_MonoidWithZeroHom_strictMono

instance : LinearOrderedCommGroupWithZero (valueGroup₀ f) where
  zero_le_one := by simp

end MonoidWithZeroHom
