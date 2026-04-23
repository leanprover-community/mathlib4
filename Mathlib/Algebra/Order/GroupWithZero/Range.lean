/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

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
  monotone' := map'_strictMono (Subtype.strictMono_coe _) |>.monotone

lemma monoidWithZeroHom_strictMono :
    StrictMono (orderMonoidWithZeroHom f) :=
  map'_strictMono (Subtype.strictMono_coe _)

lemma embedding_strictMono : StrictMono (embedding (f := f)) := by
  intro x y hxy
  rw [← monoidWithZeroHom_strictMono.lt_iff_lt] at hxy
  simpa using (OrderEmbedding.lt_iff_lt (OrderIso.withZeroUnits.toOrderEmbedding)).mpr hxy

instance : IsOrderedMonoid (ValueGroup₀ f) :=
  Function.Injective.isOrderedMonoid embedding (map_mul _) embedding_strictMono.le_iff_le

instance : LinearOrderedCommGroupWithZero (ValueGroup₀ f) where
  zero_le := by simp
  mul_lt_mul_of_pos_left a ha b c hbc := by
    simp only [← (embedding_strictMono (f := f)).lt_iff_lt, map_mul] at *
    exact (mul_lt_mul_iff_of_pos_left ha).mpr hbc

lemma embedding_unit_pos (a : (ValueGroup₀ f)ˣ) :
    0 < embedding a.1 := by
  conv_lhs => rw [← map_zero f, ← ValueGroup₀.embedding_restrict₀ (0 : A)]
  rw [embedding_strictMono.lt_iff_lt]
  simp

lemma embedding_unit_ne_zero (a : (ValueGroup₀ f)ˣ) :
    embedding a.1 ≠ 0 := (embedding_unit_pos a).ne.symm

end ValueGroup₀

end MonoidWithZeroHom
