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

/-- The inclusion of `valueGroup₀ f` into `WithZero Bˣ` as an order embedding. -/
def valueGroup₀_OrderEmbedding : valueGroup₀ f ↪o WithZero Bˣ where
  toFun := WithZero.map' (valueGroup f).subtype
  inj' := WithZero.map'_injective Subtype.val_injective ..
  map_rel_iff' {a b} := by
    refine ⟨fun h ↦ ?_, fun h ↦ WithZero.map'_mono (fun _ _ x ↦ x) h⟩
    · revert a
      simp only [Function.Embedding.coeFn_mk, «forall», map_zero, WithZero.zero_le, imp_self,
        map'_coe, Subgroup.subtype_apply, Subtype.forall, true_and]
      intro a _ h_le
      have hb : b ≠ 0 := by
        intro H
        apply lt_iff_not_ge.mp <| zero_lt_coe a
        grw [h_le, H, map_zero]
      obtain ⟨_, rfl⟩ := ne_zero_iff_exists.mp hb
      simp [coe_le_coe, ge_iff_le, map'_coe, Subgroup.subtype_apply] at h_le ⊢
      exact h_le

@[simp]
lemma valueGroup₀_OrderEmbedding_apply (x : valueGroup₀ f) :
    valueGroup₀_OrderEmbedding x = WithZero.map' (valueGroup f).subtype x := rfl

lemma valueGroup₀_OrderEmbedding_mul (x y : valueGroup₀ f) :
    valueGroup₀_OrderEmbedding (x * y) =
      valueGroup₀_OrderEmbedding x * valueGroup₀_OrderEmbedding y := by simp

/-- The inclusion of `valueGroup₀ f` into `B` as an order embedding. -/
def valueGroup₀_OrderEmbedding' : valueGroup₀ f ↪o B :=
  valueGroup₀_OrderEmbedding.trans OrderIso.withZeroUnits.toOrderEmbedding

lemma valueGroup₀_OrderEmbedding'_apply (x : valueGroup₀ f) :
    valueGroup₀_OrderEmbedding' x =
      OrderIso.withZeroUnits.toOrderEmbedding (WithZero.map' (valueGroup f).subtype x) := rfl


lemma valueGroup₀_OrderEmbedding'_mul (x y : valueGroup₀ f) :
    valueGroup₀_OrderEmbedding' (x * y) =
      valueGroup₀_OrderEmbedding' x * valueGroup₀_OrderEmbedding' y := by
  simp [valueGroup₀_OrderEmbedding'_apply, map_mul, OrderIso.withZeroUnits]


instance : IsOrderedMonoid (valueGroup₀ f) where
  mul_le_mul_left := by
    intro a b h c
    match a, b, c with
    | _, _, 0 => simp
    | 0, _, (c : valueGroup f) => simp
    | some a, 0, _ => exact (not_le_of_gt (WithZero.zero_lt_coe a) h).elim
    | (x : valueGroup f), (y : valueGroup f), (c : valueGroup f) =>
      simp only [← valueGroup₀_OrderEmbedding'.le_iff_le, valueGroup₀_OrderEmbedding'_mul]
      rw [mul_le_mul_left]
      · rwa [coe_le_coe] at h
      simp [valueGroup₀_OrderEmbedding', OrderIso.withZeroUnits_apply]

instance : LinearOrderedCommGroupWithZero (valueGroup₀ f) where
  zero_le_one := by simp

end MonoidWithZeroHom
