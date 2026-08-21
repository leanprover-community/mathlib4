/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio, Edison Xu
-/
module

public import Mathlib.Algebra.GroupWithZero.Range
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

@[simp]
lemma embedding_le_embedding {a b : ValueGroup₀ f} : embedding a ≤ embedding b ↔ a ≤ b :=
  embedding_strictMono.le_iff_le

@[simp]
lemma embedding_lt_embedding {a b : ValueGroup₀ f} : embedding a < embedding b ↔ a < b :=
  embedding_strictMono.lt_iff_lt

lemma embedding_unit_ne_zero (a : (ValueGroup₀ f)ˣ) : embedding a.1 ≠ 0 := by
  rw [embedding_apply, ne_eq, ZeroMemClass.coe_eq_zero]
  exact a.ne_zero

lemma embedding_unit_pos (a : (ValueGroup₀ f)ˣ) : 0 < embedding a.1 :=
  zero_lt_iff.2 (embedding_unit_ne_zero a)

end ValueGroup₀

end MonoidWithZeroHom
