/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Defs

/-!
# Faithful group actions

This file provides typeclasses for faithful actions.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M G α : Type*}

/-! ### Faithful actions -/

/-- Typeclass for faithful actions. -/
class FaithfulVAdd (G : Type*) (P : Type*) [VAdd G P] : Prop where
  /-- Two elements `g₁` and `g₂` are equal whenever they act in the same way on all points. -/
  eq_of_vadd_eq_vadd : ∀ {g₁ g₂ : G}, (∀ p : P, g₁ +ᵥ p = g₂ +ᵥ p) → g₁ = g₂

/-- Typeclass for faithful actions. -/
@[to_additive]
class FaithfulSMul (M : Type*) (α : Type*) [SMul M α] : Prop where
  /-- Two elements `m₁` and `m₂` are equal whenever they act in the same way on all points. -/
  eq_of_smul_eq_smul : ∀ {m₁ m₂ : M}, (∀ a : α, m₁ • a = m₂ • a) → m₁ = m₂

export FaithfulSMul (eq_of_smul_eq_smul)
export FaithfulVAdd (eq_of_vadd_eq_vadd)

@[to_additive]
lemma smul_left_injective' [SMul M α] [FaithfulSMul M α] : Injective ((· • ·) : M → α → α) :=
  fun _ _ h ↦ FaithfulSMul.eq_of_smul_eq_smul (congr_fun h)

/-- `Monoid.toMulAction` is faithful on cancellative monoids. -/
@[to_additive /-- `AddMonoid.toAddAction` is faithful on additive cancellative monoids. -/]
instance RightCancelMonoid.faithfulSMul [RightCancelMonoid α] : FaithfulSMul α α :=
  ⟨fun h ↦ mul_right_cancel (h 1)⟩

/-- `Monoid.toOppositeMulAction` is faithful on cancellative monoids. -/
@[to_additive /-- `AddMonoid.toOppositeAddAction` is faithful on additive cancellative monoids. -/]
instance LeftCancelMonoid.to_faithfulSMul_mulOpposite [LeftCancelMonoid α] : FaithfulSMul αᵐᵒᵖ α :=
  ⟨fun h ↦ MulOpposite.unop_injective <| mul_left_cancel (h 1)⟩

@[deprecated (since := "2025-09-15")]
alias LefttCancelMonoid.to_faithfulSMul_mulOpposite := LeftCancelMonoid.to_faithfulSMul_mulOpposite

instance (R : Type*) [MulOneClass R] : FaithfulSMul R R := ⟨fun {r₁ r₂} h ↦ by simpa using h 1⟩

lemma faithfulSMul_iff_injective_smul_one (R A : Type*)
    [MulOneClass A] [SMul R A] [IsScalarTower R A A] :
    FaithfulSMul R A ↔ Injective (fun r : R ↦ r • (1 : A)) := by
  refine ⟨fun ⟨h⟩ {r₁ r₂} hr ↦ h fun a ↦ ?_, fun h ↦ ⟨fun {r₁ r₂} hr ↦ h ?_⟩⟩
  · simp only at hr
    rw [← one_mul a, ← smul_mul_assoc, ← smul_mul_assoc, hr]
  · simpa using hr 1

/--
Let `Q / P / N / M` be a tower. If `Q / N / M`, `Q / P / M` and `Q / P / N` are
scalar towers, then `P / N / M` is also a scalar tower.
-/
@[to_additive] lemma IsScalarTower.to₁₂₃ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul N P] [SMul N Q] [SMul P Q] [FaithfulSMul P Q]
    [IsScalarTower M N Q] [IsScalarTower M P Q] [IsScalarTower N P Q] : IsScalarTower M N P where
  smul_assoc m n p := by simp_rw [← (smul_left_injective' (α := Q)).eq_iff, smul_assoc]
