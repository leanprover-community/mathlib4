/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio, Edison Xie
-/
module

public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Algebra.Order.GroupWithZero.Cyclic
public import Mathlib.Algebra.Order.GroupWithZero.Subgroup

/-! # The range of a MonoidWithZeroHom

Given a `MonoidWithZeroHom` `f : A → B` whose codomain `B` is a `LinearOrderedCommGroupWithZero`,
we provide some order properties of the `MonoidWithZeroHom.ValueGroup₀` as defined in
`Mathlib.Algebra.GroupWithZero.Range`.

The `LinearOrderedCommGroupWithZero (ValueGroup₀ f)` instance itself is supplied generically by
`SubgroupWithZeroClass.toLinearOrderedCommGroupWithZero`, since `ValueGroup₀ f` is a
`SetLike` subobject of `B`.
-/

@[expose] public section

namespace MonoidWithZeroHom

variable {A B : Type*} [MonoidWithZero A] [LinearOrderedCommGroupWithZero B] {f : A →*₀ B}

namespace ValueGroup₀

lemma embedding_strictMono : StrictMono (embedding (f := f)) :=
  SubmonoidWithZeroClass.subtype_strictMono _

lemma embedding_monotone : Monotone (embedding (f := f)) := embedding_strictMono.monotone

lemma embedding_le_embedding {a b : ValueGroup₀ f} : embedding a ≤ embedding b ↔ a ≤ b :=
  embedding_strictMono.le_iff_le

lemma embedding_lt_embedding {a b : ValueGroup₀ f} : embedding a < embedding b ↔ a < b :=
  embedding_strictMono.lt_iff_lt

lemma embedding_unit_ne_zero (a : (ValueGroup₀ f)ˣ) : embedding a.1 ≠ 0 := by
  rw [embedding_apply, ne_eq, ZeroMemClass.coe_eq_zero]
  exact a.ne_zero

lemma embedding_unit_pos (a : (ValueGroup₀ f)ˣ) : 0 < embedding a.1 :=
  zero_lt_iff.2 (embedding_unit_ne_zero a)

variable {r₁ s₁ r₂ s₂ : A}

/-- Comparing two ratios, when the denominators do not vanish. -/
theorem mk_le_mk_iff (f : A →*₀ B) (hr₁ : f r₁ ≠ 0) (hr₂ : f r₂ ≠ 0) :
    mk f r₁ s₁ ≤ mk f r₂ s₂ ↔ f (s₁ * r₂) ≤ f (s₂ * r₁) := by
  rw [← Subtype.coe_le_coe, coe_mk, coe_mk, inv_mul_eq_div, inv_mul_eq_div,
    div_le_div_iff₀ (zero_lt_iff.2 hr₁) (zero_lt_iff.2 hr₂), map_mul, map_mul]

end ValueGroup₀

/-! ### Bridging the with-zero hypotheses to the `Subgroup Bˣ` API

`valueGroup f` is by definition `(valueGroup₀ f).units`, but instance search does not unfold it,
so the transfers are declared explicitly. This is what lets downstream statements be phrased in
`ValueGroup₀ f` while their proofs still use the `Subgroup` API. -/

instance [Nontrivial (ValueGroup₀ f)ˣ] : Nontrivial ↥(valueGroup f) :=
  SubgroupWithZero.nontrivial_units_subgroup (valueGroup₀ f)

instance [IsCyclicWithZero (ValueGroup₀ f)] : IsCyclic ↥(valueGroup f) :=
  SubgroupWithZero.isCyclic_units (valueGroup₀ f)

end MonoidWithZeroHom
