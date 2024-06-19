/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Data.Set.Pointwise.Basic

#align_import ring_theory.subsemiring.pointwise from "leanprover-community/mathlib"@"59694bd07f0a39c5beccba34bd9f413a160782bf"

/-! # Pointwise instances on `Subsemiring`s

This file provides the action `Subsemiring.PointwiseMulAction` which matches the action of
`MulActionSet`.

This actions is available in the `Pointwise` locale.

## Implementation notes

This file is almost identical to `GroupTheory/Submonoid/Pointwise.lean`. Where possible, try to
keep them in sync.
-/


open Set

variable {M R : Type*}

namespace Subsemiring

section Monoid

variable [Monoid M] [Semiring R] [MulSemiringAction M R]

/-- The action on a subsemiring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulAction : MulAction M (Subsemiring R) where
  smul a S := S.map (MulSemiringAction.toRingHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (RingHom.ext <| one_smul M)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f => S.map f) (RingHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm
#align subsemiring.pointwise_mul_action Subsemiring.pointwiseMulAction

scoped[Pointwise] attribute [instance] Subsemiring.pointwiseMulAction

open Pointwise

theorem pointwise_smul_def {a : M} (S : Subsemiring R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl
#align subsemiring.pointwise_smul_def Subsemiring.pointwise_smul_def

@[simp]
theorem coe_pointwise_smul (m : M) (S : Subsemiring R) : ↑(m • S) = m • (S : Set R) :=
  rfl
#align subsemiring.coe_pointwise_smul Subsemiring.coe_pointwise_smul

@[simp]
theorem pointwise_smul_toAddSubmonoid (m : M) (S : Subsemiring R) :
    (m • S).toAddSubmonoid = m • S.toAddSubmonoid :=
  rfl
#align subsemiring.pointwise_smul_to_add_submonoid Subsemiring.pointwise_smul_toAddSubmonoid

theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Subsemiring R) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set R))
#align subsemiring.smul_mem_pointwise_smul Subsemiring.smul_mem_pointwise_smul

instance : CovariantClass M (Subsemiring R) HSMul.hSMul LE.le :=
  ⟨fun _ _ => image_subset _⟩

theorem mem_smul_pointwise_iff_exists (m : M) (r : R) (S : Subsemiring R) :
    r ∈ m • S ↔ ∃ s : R, s ∈ S ∧ m • s = r :=
  (Set.mem_smul_set : r ∈ m • (S : Set R) ↔ _)
#align subsemiring.mem_smul_pointwise_iff_exists Subsemiring.mem_smul_pointwise_iff_exists

@[simp]
theorem smul_bot (a : M) : a • (⊥ : Subsemiring R) = ⊥ :=
  map_bot _
#align subsemiring.smul_bot Subsemiring.smul_bot

theorem smul_sup (a : M) (S T : Subsemiring R) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _
#align subsemiring.smul_sup Subsemiring.smul_sup

theorem smul_closure (a : M) (s : Set R) : a • closure s = closure (a • s) :=
  RingHom.map_closureS _ _
#align subsemiring.smul_closure Subsemiring.smul_closure

instance pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] :
    IsCentralScalar M (Subsemiring R) :=
  ⟨fun _a S => (congr_arg fun f => S.map f) <| RingHom.ext <| op_smul_eq_smul _⟩
#align subsemiring.pointwise_central_scalar Subsemiring.pointwise_central_scalar

end Monoid

section Group

variable [Group M] [Semiring R] [MulSemiringAction M R]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : M} {S : Subsemiring R} {x : R} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff
#align subsemiring.smul_mem_pointwise_smul_iff Subsemiring.smul_mem_pointwise_smul_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Subsemiring R} {x : R} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
#align subsemiring.mem_pointwise_smul_iff_inv_smul_mem Subsemiring.mem_pointwise_smul_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : M} {S : Subsemiring R} {x : R} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff
#align subsemiring.mem_inv_pointwise_smul_iff Subsemiring.mem_inv_pointwise_smul_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Subsemiring R} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff
#align subsemiring.pointwise_smul_le_pointwise_smul_iff Subsemiring.pointwise_smul_le_pointwise_smul_iff

theorem pointwise_smul_subset_iff {a : M} {S T : Subsemiring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff
#align subsemiring.pointwise_smul_subset_iff Subsemiring.pointwise_smul_subset_iff

theorem subset_pointwise_smul_iff {a : M} {S T : Subsemiring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff
#align subsemiring.subset_pointwise_smul_iff Subsemiring.subset_pointwise_smul_iff

/-! TODO: add `equiv_smul` like we have for subgroup. -/


end Group

section GroupWithZero

variable [GroupWithZero M] [Semiring R] [MulSemiringAction M R]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set R) x
#align subsemiring.smul_mem_pointwise_smul_iff₀ Subsemiring.smul_mem_pointwise_smul_iff₀

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set R) x
#align subsemiring.mem_pointwise_smul_iff_inv_smul_mem₀ Subsemiring.mem_pointwise_smul_iff_inv_smul_mem₀

theorem mem_inv_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set R) x
#align subsemiring.mem_inv_pointwise_smul_iff₀ Subsemiring.mem_inv_pointwise_smul_iff₀

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subsemiring R} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha
#align subsemiring.pointwise_smul_le_pointwise_smul_iff₀ Subsemiring.pointwise_smul_le_pointwise_smul_iff₀

theorem pointwise_smul_le_iff₀ {a : M} (ha : a ≠ 0) {S T : Subsemiring R} :
    a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha
#align subsemiring.pointwise_smul_le_iff₀ Subsemiring.pointwise_smul_le_iff₀

theorem le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subsemiring R} :
    S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha
#align subsemiring.le_pointwise_smul_iff₀ Subsemiring.le_pointwise_smul_iff₀

end GroupWithZero

end Subsemiring
