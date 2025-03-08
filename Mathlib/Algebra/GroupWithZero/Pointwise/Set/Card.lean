/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.SetTheory.Cardinal.ENat
import Mathlib.Data.Set.Card

/-!
# Cardinality of sets under pointwise group with zero operations
-/

assert_not_exists Field

open scoped Cardinal Pointwise

variable {G₀ M₀ : Type*}

namespace Set
variable [GroupWithZero G₀] [Zero M₀] [MulActionWithZero G₀ M₀] {a : G₀}

lemma _root_.Cardinal.mk_smul_set₀ (ha : a ≠ 0) (s : Set M₀) : #↥(a • s) = #s :=
  Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective₀ ha).injOn

lemma natCard_smul_set₀ (ha : a ≠ 0) (s : Set M₀) : Nat.card ↥(a • s) = Nat.card s := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact ncard_image_of_injective _ <| MulAction.injective₀ ha

end Set
