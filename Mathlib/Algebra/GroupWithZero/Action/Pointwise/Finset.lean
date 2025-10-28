/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Algebra.GroupWithZero.Pointwise.Finset

/-!
# Pointwise operations of finsets in a group with zero

This file proves properties of pointwise operations of finsets in a group with zero.
-/

assert_not_exists Ring

open scoped Pointwise

namespace Finset
variable {α β : Type*} [DecidableEq β]

/-- If scalar multiplication by elements of `α` sends `(0 : β)` to zero,
then the same is true for `(0 : Finset β)`. -/
protected def smulZeroClass [Zero β] [SMulZeroClass α β] : SMulZeroClass α (Finset β) :=
  coe_injective.smulZeroClass ⟨_, coe_zero⟩ coe_smul_finset

/-- If the scalar multiplication `(· • ·) : α → β → β` is distributive,
then so is `(· • ·) : α → Finset β → Finset β`. -/
protected noncomputable def distribSMul [AddZeroClass β] [DistribSMul α β] :
    DistribSMul α (Finset β) :=
  coe_injective.distribSMul coeAddMonoidHom coe_smul_finset

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `Finset β`. -/
protected noncomputable def distribMulAction [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Finset β) :=
  coe_injective.distribMulAction coeAddMonoidHom coe_smul_finset

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `Set β`. -/
protected noncomputable def mulDistribMulAction [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Finset β) :=
  coe_injective.mulDistribMulAction coeMonoidHom coe_smul_finset

scoped[Pointwise] attribute [instance] Finset.smulZeroClass Finset.distribSMul
  Finset.distribMulAction Finset.mulDistribMulAction

instance [DecidableEq α] [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Finset α) :=
  Function.Injective.noZeroDivisors _ coe_injective coe_zero coe_mul

instance noZeroSMulDivisors [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors (Finset α) (Finset β) where
  eq_zero_or_eq_zero_of_smul_eq_zero {s t} := by
    exact_mod_cast eq_zero_or_eq_zero_of_smul_eq_zero (c := (s : Set α)) (x := (t : Set β))

instance noZeroSMulDivisors_finset [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors α (Finset β) :=
  Function.Injective.noZeroSMulDivisors _ coe_injective coe_zero coe_smul_finset

section SMulZeroClass
variable [Zero β] [SMulZeroClass α β] {s : Finset α} {t : Finset β} {a : α}

lemma smul_zero_subset (s : Finset α) : s • (0 : Finset β) ⊆ 0 := by simp [subset_iff, mem_smul]

lemma Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Finset β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using hs

lemma zero_mem_smul_finset (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
  mem_smul_finset.2 ⟨0, h, smul_zero _⟩

variable [Zero α] [NoZeroSMulDivisors α β]

lemma zero_mem_smul_finset_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t := by
  rw [← mem_coe, coe_smul_finset, Set.zero_mem_smul_set_iff ha, mem_coe]

end SMulZeroClass

section SMulWithZero
variable [Zero α] [Zero β] [SMulWithZero α β] {s : Finset α} {t : Finset β}

/-!
Note that we have neither `SMulWithZero α (Finset β)` nor `SMulWithZero (Finset α) (Finset β)`
because `0 • ∅ ≠ 0`.
-/

lemma zero_smul_subset (t : Finset β) : (0 : Finset α) • t ⊆ 0 := by simp [subset_iff, mem_smul]

lemma Nonempty.zero_smul (ht : t.Nonempty) : (0 : Finset α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using ht

/-- A nonempty set is scaled by zero to the singleton set containing zero. -/
@[simp] lemma zero_smul_finset {s : Finset β} (h : s.Nonempty) : (0 : α) • s = (0 : Finset β) :=
  coe_injective <| by simpa using @Set.zero_smul_set α _ _ _ _ _ h

lemma zero_smul_finset_subset (s : Finset β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ ↦ mem_zero.2 <| zero_smul α x

variable [NoZeroSMulDivisors α β]

lemma zero_mem_smul_iff :
    (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.Nonempty ∨ (0 : β) ∈ t ∧ s.Nonempty := by
  rw [← mem_coe, coe_smul, Set.zero_mem_smul_iff]; rfl

end SMulWithZero

section GroupWithZero
variable [GroupWithZero α]

section MulAction
variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

@[simp] lemma smul_mem_smul_finset_iff₀ (ha : a ≠ 0) : a • b ∈ a • s ↔ b ∈ s :=
  smul_mem_smul_finset_iff (Units.mk0 a ha)

lemma inv_smul_mem_iff₀ (ha : a ≠ 0) : a⁻¹ • b ∈ s ↔ b ∈ a • s :=
  show _ ↔ _ ∈ Units.mk0 a ha • _ from inv_smul_mem_iff

lemma mem_inv_smul_finset_iff₀ (ha : a ≠ 0) : b ∈ a⁻¹ • s ↔ a • b ∈ s :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_finset_iff

@[simp]
lemma smul_finset_subset_smul_finset_iff₀ (ha : a ≠ 0) : a • s ⊆ a • t ↔ s ⊆ t :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_finset_subset_smul_finset_iff

lemma smul_finset_subset_iff₀ (ha : a ≠ 0) : a • s ⊆ t ↔ s ⊆ a⁻¹ • t :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_finset_subset_iff

lemma subset_smul_finset_iff₀ (ha : a ≠ 0) : s ⊆ a • t ↔ a⁻¹ • s ⊆ t :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_smul_finset_iff

lemma smul_finset_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter _ _ <| MulAction.injective₀ ha

lemma smul_finset_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t :=
  image_sdiff _ _ <| MulAction.injective₀ ha

open scoped symmDiff in
lemma smul_finset_symmDiff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff _ _ <| MulAction.injective₀ ha

lemma smul_finset_univ₀ [Fintype β] (ha : a ≠ 0) : a • (univ : Finset β) = univ :=
  coe_injective <| by push_cast; exact Set.smul_set_univ₀ ha

lemma smul_univ₀ [Fintype β] {s : Finset α} (hs : ¬s ⊆ 0) : s • (univ : Finset β) = univ :=
  coe_injective <| by
    rw [← coe_subset] at hs
    push_cast at hs ⊢
    exact Set.smul_univ₀ hs

lemma smul_univ₀' [Fintype β] {s : Finset α} (hs : s.Nontrivial) : s • (univ : Finset β) = univ :=
  coe_injective <| by push_cast; exact Set.smul_univ₀' hs

end MulAction

variable [DecidableEq α] {s : Finset α}

open scoped RightActions

@[simp] lemma inv_smul_finset_distrib₀ (a : α) (s : Finset α) : (a • s)⁻¹ = s⁻¹ <• a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, not_false_eq_true, ← inv_smul_mem_iff₀, smul_eq_mul,
      MulOpposite.op_inv, inv_eq_zero, MulOpposite.op_eq_zero_iff, inv_inv,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_inv_rev, ha]

lemma inv_op_smul_finset_distrib₀ (a : α) (s : Finset α) : (s <• a)⁻¹ = a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, MulOpposite.op_eq_zero_iff, not_false_eq_true, ←
      inv_smul_mem_iff₀, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_inv, MulOpposite.unop_op,
      inv_eq_zero, inv_inv, smul_eq_mul, mul_inv_rev, ha]

end GroupWithZero

section Monoid
variable [Monoid α] [AddGroup β] [DistribMulAction α β]

@[simp]
lemma smul_finset_neg (a : α) (t : Finset β) : a • -t = -(a • t) := by
  simp only [← image_smul, ← image_neg_eq_neg, Function.comp_def, image_image, smul_neg]

@[simp]
protected lemma smul_neg (s : Finset α) (t : Finset β) : s • -t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]; exact image_image₂_right_comm smul_neg

end Monoid
end Finset
