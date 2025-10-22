/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.GroupWithZero.Pointwise.Set.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs

/-!
# Pointwise operations of sets in a group with zero

This file proves properties of pointwise operations of sets in a group with zero.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

assert_not_exists Ring

open Function
open scoped Pointwise

variable {α β : Type*}

namespace Set

lemma smul_set_pi₀ {M ι : Type*} {α : ι → Type*} [GroupWithZero M] [∀ i, MulAction M (α i)]
    {c : M} (hc : c ≠ 0) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) :=
  smul_set_pi_of_isUnit (.mk0 _ hc) I s

/-- A slightly more general version of `Set.smul_set_pi₀`. -/
lemma smul_set_pi₀' {M ι : Type*} {α : ι → Type*} [GroupWithZero M] [∀ i, MulAction M (α i)]
    {c : M} {I : Set ι} (h : c ≠ 0 ∨ I = univ) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) :=
  h.elim (fun hc ↦ smul_set_pi_of_isUnit (.mk0 _ hc) I s) (fun hI ↦ hI ▸ smul_set_univ_pi ..)

section SMulZeroClass
variable [Zero β] [SMulZeroClass α β] {s : Set α} {t : Set β} {a : α}

/-- If scalar multiplication by elements of `α` sends `(0 : β)` to zero,
then the same is true for `(0 : Set β)`. -/
protected def smulZeroClassSet [Zero β] [SMulZeroClass α β] : SMulZeroClass α (Set β) where
  smul_zero _ := image_singleton.trans <| by rw [smul_zero, singleton_zero]

scoped[Pointwise] attribute [instance] Set.smulZeroClassSet

lemma smul_zero_subset (s : Set α) : s • (0 : Set β) ⊆ 0 := by simp [subset_def, mem_smul]

lemma Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using hs

lemma zero_mem_smul_set (h : (0 : β) ∈ t) : (0 : β) ∈ a • t := ⟨0, h, smul_zero _⟩

variable [Zero α] [NoZeroSMulDivisors α β]

lemma zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t := by
  refine ⟨?_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha] at hb

end SMulZeroClass
section SMulWithZero

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

/-!
Note that we have neither `SMulWithZero α (Set β)` nor `SMulWithZero (Set α) (Set β)`
because `0 * ∅ ≠ 0`.
-/

lemma zero_smul_subset (t : Set β) : (0 : Set α) • t ⊆ 0 := by simp [subset_def, mem_smul]

lemma Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using ht

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
@[simp] lemma zero_smul_set {s : Set β} (h : s.Nonempty) : (0 : α) • s = (0 : Set β) := by
  simp only [← image_smul, zero_smul, h.image_const, singleton_zero]

lemma zero_smul_set_subset (s : Set β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ ↦ zero_smul α x

lemma subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton :=
  subsingleton_singleton.anti <| zero_smul_set_subset s

variable [NoZeroSMulDivisors α β] {a : α}

lemma zero_mem_smul_iff : 0 ∈ s • t ↔ 0 ∈ s ∧ t.Nonempty ∨ 0 ∈ t ∧ s.Nonempty where
  mp := by
    rintro ⟨a, ha, b, hb, h⟩
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h
    · exact Or.inl ⟨ha, b, hb⟩
    · exact Or.inr ⟨hb, a, ha⟩
  mpr := by
    rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact ⟨0, hs, b, hb, zero_smul _ _⟩
    · exact ⟨a, ha, 0, ht, smul_zero _⟩

end SMulWithZero

/-- If the scalar multiplication `(· • ·) : α → β → β` is distributive,
then so is `(· • ·) : α → Set β → Set β`. -/
protected noncomputable def distribSMulSet [AddZeroClass β] [DistribSMul α β] :
    DistribSMul α (Set β) where
  smul_add _ _ _ := image_image2_distrib <| smul_add _

scoped[Pointwise] attribute [instance] Set.distribSMulSet

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `Set β`. -/
protected noncomputable def distribMulActionSet [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Set β) where
  smul_add := smul_add
  smul_zero := smul_zero

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `Set β`. -/
protected noncomputable def mulDistribMulActionSet [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Set β) where
  smul_mul _ _ _ := image_image2_distrib <| smul_mul' _
  smul_one _ := image_singleton.trans <| by rw [smul_one, singleton_one]

scoped[Pointwise] attribute [instance] Set.distribMulActionSet Set.mulDistribMulActionSet

instance instNoZeroSMulDivisors [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors (Set α) (Set β) where
  eq_zero_or_eq_zero_of_smul_eq_zero {s t} h := by
    by_contra! H
    have hst : (s • t).Nonempty := h.symm.subst zero_nonempty
    rw [Ne, ← hst.of_smul_left.subset_zero_iff, Ne,
      ← hst.of_smul_right.subset_zero_iff] at H
    simp only [not_subset, mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul hs ht).elim ha hb

instance noZeroSMulDivisors_set [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors α (Set β) where
  eq_zero_or_eq_zero_of_smul_eq_zero {a s} h := by
    by_contra! H
    have hst : (a • s).Nonempty := h.symm.subst zero_nonempty
    rw [Ne, Ne, ← hst.of_image.subset_zero_iff, not_subset] at H
    obtain ⟨ha, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul_set ht).elim ha hb

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Set α) where
  eq_zero_or_eq_zero_of_mul_eq_zero h := eq_zero_or_eq_zero_of_smul_eq_zero h

section GroupWithZero
variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

@[simp]
lemma smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : a • x ∈ a • A ↔ x ∈ A :=
  show Units.mk0 a ha • _ ∈ _ ↔ _ from smul_mem_smul_set_iff

lemma mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show _ ∈ Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem

lemma mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff

lemma preimage_smul₀ (ha : a ≠ 0) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t :=
  preimage_smul (Units.mk0 a ha) t

lemma preimage_smul_inv₀ (ha : a ≠ 0) (t : Set β) : (fun x ↦ a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (Units.mk0 a ha)⁻¹ t

@[simp]
lemma smul_set_subset_smul_set_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_set_subset_smul_set_iff

lemma smul_set_subset_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_set_subset_iff_subset_inv_smul_set

lemma subset_smul_set_iff₀ (ha : a ≠ 0) {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_smul_set_iff

lemma smul_set_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  show Units.mk0 a ha • _ = _ from smul_set_inter

lemma smul_set_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t :=
  image_diff (MulAction.injective₀ ha) _ _

open scoped symmDiff in
lemma smul_set_symmDiff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff (MulAction.injective₀ ha) _ _

lemma smul_set_univ₀ (ha : a ≠ 0) : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective₀ ha

lemma smul_univ₀ {s : Set α} (hs : ¬s ⊆ 0) : s • (univ : Set β) = univ :=
  let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b ↦ ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul₀ ha₀ _⟩

lemma smul_univ₀' {s : Set α} (hs : s.Nontrivial) : s • (univ : Set β) = univ :=
  smul_univ₀ hs.not_subset_singleton

open scoped RightActions in
@[simp] lemma inv_smul_set_distrib₀ (a : α) (s : Set α) : (a • s)⁻¹ = s⁻¹ <• a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]

open scoped RightActions in
@[simp] lemma inv_op_smul_set_distrib₀ (a : α) (s : Set α) : (s <• a)⁻¹ = a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]

end GroupWithZero
end Set
