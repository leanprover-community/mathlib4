/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.RingTheory.Ideal.Maps


/-! # Pointwise instances on `Ideal`s

This file provides the action `Ideal.pointwiseMulAction` which morally matches the action of
`mulActionSet` (though here an extra `Ideal.span` is inserted).

This actions is available in the `Pointwise` locale.

## Implementation notes

This file is similar (but not identical) to `RingTheory/Subring/Pointwise.lean`.
Where possible, try to keep them in sync.

-/


open Set

variable {M R : Type*}

namespace Ideal

section Monoid

variable [Monoid M] [CommRing R] [MulSemiringAction M R]

/-- The action on an ideal corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulSemiringAction : MulSemiringAction M (Ideal R) where
  smul a I := Ideal.map (MulSemiringAction.toRingHom _ _ a) I
  one_smul I :=
    congr_arg (I.map ·) (RingHom.ext <| one_smul M) |>.trans I.map_id
  mul_smul _a₁ _a₂ I :=
    congr_arg (I.map ·) (RingHom.ext <| mul_smul _ _) |>.trans (I.map_map _ _).symm
  smul_one a := by simp only [Ideal.one_eq_top]; exact Ideal.map_top _
  smul_mul a I J := Ideal.map_mul (MulSemiringAction.toRingHom _ _ a) I J
  smul_add a I J := Ideal.map_sup _ I J
  smul_zero a := Ideal.map_bot

scoped[Pointwise] attribute [instance] Ideal.pointwiseMulSemiringAction

open Pointwise

theorem pointwise_smul_def {a : M} (S : Ideal R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl

-- note: unlike with `Subring`, `pointwise_smul_toAddSubgroup` wouldn't be true

theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Ideal R) : r ∈ S → m • r ∈ m • S :=
  fun h => subset_span <| Set.smul_mem_smul_set h

instance : CovariantClass M (Ideal R) HSMul.hSMul LE.le :=
  ⟨fun _ _ => map_mono⟩

-- note: unlike with `Subring`, `mem_smul_pointwise_iff_exists` wouldn't be true

@[simp]
theorem smul_bot (a : M) : a • (⊥ : Ideal R) = ⊥ :=
  map_bot

theorem smul_sup (a : M) (S T : Ideal R) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _

theorem smul_closure (a : M) (s : Set R) : a • span s = span (a • s) :=
  Ideal.map_span _ _

instance pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] :
    IsCentralScalar M (Ideal R) :=
  ⟨fun _ S => (congr_arg fun f => S.map f) <| RingHom.ext <| op_smul_eq_smul _⟩

end Monoid

-- TODO
/-
section Group

variable [Group M] [CommRing R] [MulSemiringAction M R]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : M} {S : Ideal R} {x : R} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Ideal R} {x : R} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : M} {S : Ideal R} {x : R} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Ideal R} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff

theorem pointwise_smul_subset_iff {a : M} {S T : Ideal R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff

theorem subset_pointwise_smul_iff {a : M} {S T : Ideal R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff

/-! TODO: add `equivSMul` like we have for subgroup. -/


end Group

section GroupWithZero

variable [GroupWithZero M] [CommRing R] [MulSemiringAction M R]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Ideal R) (x : R) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set R) x

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : M} (ha : a ≠ 0) (S : Ideal R) (x : R) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set R) x

theorem mem_inv_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Ideal R) (x : R) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set R) x

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Ideal R} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha

theorem pointwise_smul_le_iff₀ {a : M} (ha : a ≠ 0) {S T : Ideal R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha

theorem le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Ideal R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha

end GroupWithZero
--/

end Ideal
