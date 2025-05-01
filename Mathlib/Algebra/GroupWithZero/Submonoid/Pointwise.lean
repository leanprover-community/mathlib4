/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set

/-!
# Submonoids in a group with zero
-/

assert_not_exists Ring

open Set
open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

namespace Submonoid
section GroupWithZero
variable [GroupWithZero G₀] [MulDistribMulAction G₀ M] {a : G₀}

@[simp]
lemma smul_mem_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set M) x

lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set M) x

lemma mem_inv_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set M) x

@[simp]
lemma pointwise_smul_le_pointwise_smul_iff₀ (ha : a ≠ 0) {S T : Submonoid M} :
    a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff₀ ha

lemma pointwise_smul_le_iff₀ (ha : a ≠ 0) {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff₀ ha

lemma le_pointwise_smul_iff₀ (ha : a ≠ 0) {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff₀ ha

end GroupWithZero
end Submonoid

namespace AddSubmonoid
section Monoid
variable [DistribMulAction M A]

/-- The action on an additive submonoid corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulAction : MulAction M (AddSubmonoid A) where
  smul a S := S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] AddSubmonoid.pointwiseMulAction

@[simp]
lemma coe_pointwise_smul (m : M) (S : AddSubmonoid A) : ↑(m • S) = m • (S : Set A) := rfl

lemma smul_mem_pointwise_smul (a : A) (m : M) (S : AddSubmonoid A) : a ∈ S → m • a ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set A))

lemma mem_smul_pointwise_iff_exists (a : A) (m : M) (S : AddSubmonoid A) :
    a ∈ m • S ↔ ∃ s : A, s ∈ S ∧ m • s = a :=
  (Set.mem_smul_set : a ∈ m • (S : Set A) ↔ _)

@[simp]
lemma smul_bot (m : M) : m • (⊥ : AddSubmonoid A) = ⊥ := map_bot _

lemma smul_sup (m : M) (S T : AddSubmonoid A) : m • (S ⊔ T) = m • S ⊔ m • T :=
  map_sup _ _ _

@[simp]
lemma smul_closure (m : M) (s : Set A) : m • closure s = closure (m • s) :=
  AddMonoidHom.map_mclosure _ _

lemma pointwise_isCentralScalar [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A] :
    IsCentralScalar M (AddSubmonoid A) :=
  ⟨fun _ S =>
    (congr_arg fun f : AddMonoid.End A => S.map f) <| AddMonoidHom.ext <| op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] AddSubmonoid.pointwise_isCentralScalar

end Monoid

section Group
variable [Group G] [DistribMulAction G A] {a : G}

@[simp]
lemma smul_mem_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {S : AddSubmonoid A} {x : A} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
lemma pointwise_smul_le_pointwise_smul_iff {S T : AddSubmonoid A} :
    a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff

lemma pointwise_smul_le_iff {S T : AddSubmonoid A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff_subset_inv_smul_set

lemma le_pointwise_smul_iff {S T : AddSubmonoid A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff

end Group

section GroupWithZero
variable [GroupWithZero G₀] [DistribMulAction G₀ A] {S T : AddSubmonoid A} {a : G₀}

@[simp]
lemma smul_mem_pointwise_smul_iff₀ (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set A) x

lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x

lemma mem_inv_pointwise_smul_iff₀ (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]
lemma pointwise_smul_le_pointwise_smul_iff₀ (ha : a ≠ 0) : a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff₀ ha

lemma pointwise_smul_le_iff₀ (ha : a ≠ 0) : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff₀ ha
lemma le_pointwise_smul_iff₀ (ha : a ≠ 0) : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

end GroupWithZero
end AddSubmonoid
