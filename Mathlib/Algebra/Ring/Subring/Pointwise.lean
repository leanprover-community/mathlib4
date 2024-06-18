/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Subsemiring.Pointwise
import Mathlib.Data.Set.Pointwise.Basic

#align_import ring_theory.subring.pointwise from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-! # Pointwise instances on `Subring`s

This file provides the action `Subring.pointwiseMulAction` which matches the action of
`mulActionSet`.

This actions is available in the `Pointwise` locale.

## Implementation notes

This file is almost identical to `RingTheory/Subsemiring/Pointwise.lean`. Where possible, try to
keep them in sync.

-/


open Set

variable {M R : Type*}

namespace Subring

section Monoid

variable [Monoid M] [Ring R] [MulSemiringAction M R]

/-- The action on a subring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulAction : MulAction M (Subring R) where
  smul a S := S.map (MulSemiringAction.toRingHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (RingHom.ext <| one_smul M)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f => S.map f) (RingHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm
#align subring.pointwise_mul_action Subring.pointwiseMulAction

scoped[Pointwise] attribute [instance] Subring.pointwiseMulAction

open Pointwise

theorem pointwise_smul_def {a : M} (S : Subring R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl
#align subring.pointwise_smul_def Subring.pointwise_smul_def

@[simp]
theorem coe_pointwise_smul (m : M) (S : Subring R) : ↑(m • S) = m • (S : Set R) :=
  rfl
#align subring.coe_pointwise_smul Subring.coe_pointwise_smul

@[simp]
theorem pointwise_smul_toAddSubgroup (m : M) (S : Subring R) :
    (m • S).toAddSubgroup = m • S.toAddSubgroup :=
  rfl
#align subring.pointwise_smul_to_add_subgroup Subring.pointwise_smul_toAddSubgroup

@[simp]
theorem pointwise_smul_toSubsemiring (m : M) (S : Subring R) :
    (m • S).toSubsemiring = m • S.toSubsemiring :=
  rfl
#align subring.pointwise_smul_to_subsemiring Subring.pointwise_smul_toSubsemiring

theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Subring R) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set R))
#align subring.smul_mem_pointwise_smul Subring.smul_mem_pointwise_smul

instance : CovariantClass M (Subring R) HSMul.hSMul LE.le :=
  ⟨fun _ _ => image_subset _⟩

theorem mem_smul_pointwise_iff_exists (m : M) (r : R) (S : Subring R) :
    r ∈ m • S ↔ ∃ s : R, s ∈ S ∧ m • s = r :=
  (Set.mem_smul_set : r ∈ m • (S : Set R) ↔ _)
#align subring.mem_smul_pointwise_iff_exists Subring.mem_smul_pointwise_iff_exists

@[simp]
theorem smul_bot (a : M) : a • (⊥ : Subring R) = ⊥ :=
  map_bot _
#align subring.smul_bot Subring.smul_bot

theorem smul_sup (a : M) (S T : Subring R) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _
#align subring.smul_sup Subring.smul_sup

theorem smul_closure (a : M) (s : Set R) : a • closure s = closure (a • s) :=
  RingHom.map_closure _ _
#align subring.smul_closure Subring.smul_closure

instance pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] :
    IsCentralScalar M (Subring R) :=
  ⟨fun _ S => (congr_arg fun f => S.map f) <| RingHom.ext <| op_smul_eq_smul _⟩
#align subring.pointwise_central_scalar Subring.pointwise_central_scalar

end Monoid

section Group

variable [Group M] [Ring R] [MulSemiringAction M R]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : M} {S : Subring R} {x : R} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff
#align subring.smul_mem_pointwise_smul_iff Subring.smul_mem_pointwise_smul_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Subring R} {x : R} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
#align subring.mem_pointwise_smul_iff_inv_smul_mem Subring.mem_pointwise_smul_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : M} {S : Subring R} {x : R} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff
#align subring.mem_inv_pointwise_smul_iff Subring.mem_inv_pointwise_smul_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Subring R} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff
#align subring.pointwise_smul_le_pointwise_smul_iff Subring.pointwise_smul_le_pointwise_smul_iff

theorem pointwise_smul_subset_iff {a : M} {S T : Subring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff
#align subring.pointwise_smul_subset_iff Subring.pointwise_smul_subset_iff

theorem subset_pointwise_smul_iff {a : M} {S T : Subring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff
#align subring.subset_pointwise_smul_iff Subring.subset_pointwise_smul_iff

/-! TODO: add `equivSMul` like we have for subgroup. -/


end Group

section GroupWithZero

variable [GroupWithZero M] [Ring R] [MulSemiringAction M R]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subring R) (x : R) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set R) x
#align subring.smul_mem_pointwise_smul_iff₀ Subring.smul_mem_pointwise_smul_iff₀

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : M} (ha : a ≠ 0) (S : Subring R) (x : R) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set R) x
#align subring.mem_pointwise_smul_iff_inv_smul_mem₀ Subring.mem_pointwise_smul_iff_inv_smul_mem₀

theorem mem_inv_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subring R) (x : R) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set R) x
#align subring.mem_inv_pointwise_smul_iff₀ Subring.mem_inv_pointwise_smul_iff₀

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subring R} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha
#align subring.pointwise_smul_le_pointwise_smul_iff₀ Subring.pointwise_smul_le_pointwise_smul_iff₀

theorem pointwise_smul_le_iff₀ {a : M} (ha : a ≠ 0) {S T : Subring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha
#align subring.pointwise_smul_le_iff₀ Subring.pointwise_smul_le_iff₀

theorem le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha
#align subring.le_pointwise_smul_iff₀ Subring.le_pointwise_smul_iff₀

end GroupWithZero

end Subring
