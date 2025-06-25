/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise

/-!
# Subgroups in a group with zero
-/

assert_not_exists Ring

open Set
open scoped Pointwise

variable {G₀ G M A : Type*}

namespace Subgroup
section GroupWithZero
variable [GroupWithZero G₀] [Group G] [MulDistribMulAction G₀ G] {S T : Subgroup G} {a : G₀}

@[simp]
lemma smul_mem_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set G) x

lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set G) x

lemma mem_inv_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set G) x

@[simp]
lemma pointwise_smul_le_pointwise_smul_iff₀ (ha : a ≠ 0) : a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff₀ ha

lemma pointwise_smul_le_iff₀ (ha : a ≠ 0) : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff₀ ha
lemma le_pointwise_smul_iff₀ (ha : a ≠ 0) : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

end GroupWithZero
end Subgroup

namespace AddSubgroup
section Monoid
variable [Monoid M] [AddGroup A] [DistribMulAction M A] {a : M}

/-- The action on an additive subgroup corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulAction : MulAction M (AddSubgroup A) where
  smul a S := S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] AddSubgroup.pointwiseMulAction

lemma pointwise_smul_def (S : AddSubgroup A) :
    a • S = S.map (DistribMulAction.toAddMonoidEnd _ _ a) :=
  rfl

@[simp]
lemma coe_pointwise_smul (a : M) (S : AddSubgroup A) : ↑(a • S) = a • (S : Set A) :=
  rfl

@[simp]
lemma pointwise_smul_toAddSubmonoid (a : M) (S : AddSubgroup A) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid :=
  rfl

lemma smul_mem_pointwise_smul (m : A) (a : M) (S : AddSubgroup A) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set A))

lemma mem_smul_pointwise_iff_exists (m : A) (a : M) (S : AddSubgroup A) :
    m ∈ a • S ↔ ∃ s : A, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set A) ↔ _)

instance pointwise_isCentralScalar [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A] :
    IsCentralScalar M (AddSubgroup A) :=
  ⟨fun _ S => (congr_arg fun f => S.map f) <| AddMonoidHom.ext <| op_smul_eq_smul _⟩

-- TODO: Check that these lemmas are useful and uncomment.
-- @[simp]
-- lemma smul_bot (m : M) : m • (⊥ : AddSubgroup A) = ⊥ := map_bot _

-- lemma smul_sup (m : M) (S T : AddSubgroup A) : m • (S ⊔ T) = m • S ⊔ m • T := map_sup _ _ _

-- @[simp]
-- lemma smul_closure (m : M) (s : Set A) : m • closure s = closure (m • s) :=
--   AddMonoidHom.map_closure ..

scoped[Pointwise] attribute [instance] AddSubgroup.pointwise_isCentralScalar

end Monoid

section Group
variable [Group G] [AddGroup A] [DistribMulAction G A] {S T : AddSubgroup A} {a : G} {x : A}

@[simp] lemma smul_mem_pointwise_smul_iff : a • x ∈ a • S ↔ x ∈ S := smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff : x ∈ a⁻¹ • S ↔ a • x ∈ S := mem_inv_smul_set_iff

@[simp]
lemma pointwise_smul_le_pointwise_smul_iff : a • S ≤ a • T ↔ S ≤ T := smul_set_subset_smul_set_iff

lemma pointwise_smul_le_iff : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff_subset_inv_smul_set
lemma le_pointwise_smul_iff : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff

end Group

section GroupWithZero
variable [GroupWithZero G₀] [AddGroup A] [DistribMulAction G₀ A] {S T : AddSubgroup A} {a : G₀}

@[simp]
lemma smul_mem_pointwise_smul_iff₀ (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set A) x

lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x

lemma mem_inv_pointwise_smul_iff₀ (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]
lemma pointwise_smul_le_pointwise_smul_iff₀ (ha : a ≠ 0) : a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff₀ ha

lemma pointwise_smul_le_iff₀ (ha : a ≠ 0) : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff₀ ha
lemma le_pointwise_smul_iff₀ (ha : a ≠ 0) : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

end GroupWithZero
end AddSubgroup
