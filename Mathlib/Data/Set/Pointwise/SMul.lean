/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Set.Pairwise.Basic

/-!
# Pointwise action on sets

This file proves that several kinds of actions of a type `α` on another type `β` transfer to actions
of `α`/`Set α` on `Set β`.

## Implementation notes

* We put all instances in the locale `Pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

-/

open Function MulOpposite

variable {F α β γ : Type*}

namespace Set

open Pointwise

/-! ### Translation/scaling of sets -/


section SMul

section Mul

variable [Mul α] {s t u : Set α} {a : α}

@[to_additive] lemma smul_set_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image2_right

open scoped RightActions in
@[to_additive] lemma op_smul_set_subset_mul : a ∈ t → s <• a ⊆ s * t := image_subset_image2_left

@[to_additive]
theorem image_op_smul : (op '' s) • t = t * s := by
  rw [← image2_smul, ← image2_mul, image2_image_left, image2_swap]
  rfl

@[to_additive (attr := simp)]
theorem iUnion_op_smul_set (s t : Set α) : ⋃ a ∈ t, MulOpposite.op a • s = s * t :=
  iUnion_image_right _

@[to_additive]
theorem mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u :=
  image2_subset_iff_left

@[to_additive]
theorem mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
  image2_subset_iff_right

@[to_additive] lemma pair_mul (a b : α) (s : Set α) : {a, b} * s = a • s ∪ b • s := by
  rw [insert_eq, union_mul, singleton_mul, singleton_mul]; rfl

open scoped RightActions
@[to_additive] lemma mul_pair (s : Set α) (a b : α) : s * {a, b} = s <• a ∪ s <• b := by
  rw [insert_eq, mul_union, mul_singleton, mul_singleton]; rfl

end Mul

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

@[to_additive] lemma range_mul [Mul α] {ι : Sort*} (a : α) (f : ι → α) :
    range (fun i ↦ a * f i) = a • range f := range_smul a f

@[to_additive]
instance smulCommClass_set [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Set γ) :=
  ⟨fun _ _ ↦ Commute.set_image <| smul_comm _ _⟩

@[to_additive]
instance smulCommClass_set' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image_image2_distrib_right <| smul_comm _⟩

@[to_additive]
instance smulCommClass_set'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) β (Set γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image2_left_comm smul_comm⟩

@[to_additive vaddAssocClass]
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Set γ) where
  smul_assoc a b T := by simp only [← image_smul, image_image, smul_assoc]

@[to_additive vaddAssocClass']
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image2_image_left_comm <| smul_assoc _⟩

@[to_additive vaddAssocClass'']
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Set α) (Set β) (Set γ) where
  smul_assoc _ _ _ := image2_assoc smul_assoc

@[to_additive]
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Set β) :=
  ⟨fun _ S ↦ (congr_arg fun f ↦ f '' S) <| funext fun _ ↦ op_smul_eq_smul _ _⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `Set α`
on `Set β`. -/
@[to_additive
      "An additive action of an additive monoid `α` on a type `β` gives an additive action of
      `Set α` on `Set β`"]
protected def mulAction [Monoid α] [MulAction α β] : MulAction (Set α) (Set β) where
  mul_smul _ _ _ := image2_assoc mul_smul
  one_smul s := image2_singleton_left.trans <| by simp_rw [one_smul, image_id']

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `Set β`. -/
@[to_additive
      "An additive action of an additive monoid on a type `β` gives an additive action on `Set β`."]
protected def mulActionSet [Monoid α] [MulAction α β] : MulAction α (Set β) where
  mul_smul _ _ _ := by simp only [← image_smul, image_image, ← mul_smul]
  one_smul _ := by simp only [← image_smul, one_smul, image_id']

scoped[Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction

/-- If scalar multiplication by elements of `α` sends `(0 : β)` to zero,
then the same is true for `(0 : Set β)`. -/
protected def smulZeroClassSet [Zero β] [SMulZeroClass α β] :
    SMulZeroClass α (Set β) where
  smul_zero _ := image_singleton.trans <| by rw [smul_zero, singleton_zero]

scoped[Pointwise] attribute [instance] Set.smulZeroClassSet

/-- If the scalar multiplication `(· • ·) : α → β → β` is distributive,
then so is `(· • ·) : α → Set β → Set β`. -/
protected def distribSMulSet [AddZeroClass β] [DistribSMul α β] :
    DistribSMul α (Set β) where
  smul_add _ _ _ := image_image2_distrib <| smul_add _

scoped[Pointwise] attribute [instance] Set.distribSMulSet

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `Set β`. -/
protected def distribMulActionSet [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Set β) where
  smul_add := smul_add
  smul_zero := smul_zero

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `Set β`. -/
protected def mulDistribMulActionSet [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Set β) where
  smul_mul _ _ _ := image_image2_distrib <| smul_mul' _
  smul_one _ := image_singleton.trans <| by rw [smul_one, singleton_one]

scoped[Pointwise] attribute [instance] Set.distribMulActionSet Set.mulDistribMulActionSet

instance [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors (Set α) (Set β) :=
  ⟨fun {s t} h ↦ by
    by_contra! H
    have hst : (s • t).Nonempty := h.symm.subst zero_nonempty
    rw [Ne, ← hst.of_smul_left.subset_zero_iff, Ne,
      ← hst.of_smul_right.subset_zero_iff] at H
    simp only [not_subset, mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul hs ht).elim ha hb⟩

instance noZeroSMulDivisors_set [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors α (Set β) :=
  ⟨fun {a s} h ↦ by
    by_contra! H
    have hst : (a • s).Nonempty := h.symm.subst zero_nonempty
    rw [Ne, Ne, ← hst.of_image.subset_zero_iff, not_subset] at H
    obtain ⟨ha, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul_set ht).elim ha hb⟩

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Set α) :=
  ⟨fun h ↦ eq_zero_or_eq_zero_of_smul_eq_zero h⟩

end SMul

open Pointwise

@[to_additive]
theorem image_smul_distrib [MulOneClass α] [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β]
    (f : F) (a : α) (s : Set α) :
    f '' (a • s) = f a • f '' s :=
  image_comm <| map_mul _ _

section SMul

variable [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

-- TODO: replace hypothesis and conclusion with a typeclass
@[to_additive]
theorem op_smul_set_smul_eq_smul_smul_set (a : α) (s : Set β) (t : Set γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext
  simp [mem_smul, mem_smul_set, h]

end SMul

section SMulZeroClass

variable [Zero β] [SMulZeroClass α β] {s : Set α} {t : Set β} {a : α}

theorem smul_zero_subset (s : Set α) : s • (0 : Set β) ⊆ 0 := by simp [subset_def, mem_smul]

theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using hs

theorem zero_mem_smul_set (h : (0 : β) ∈ t) : (0 : β) ∈ a • t := ⟨0, h, smul_zero _⟩

variable [Zero α] [NoZeroSMulDivisors α β]

theorem zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t := by
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

theorem zero_smul_subset (t : Set β) : (0 : Set α) • t ⊆ 0 := by simp [subset_def, mem_smul]

theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using ht

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
@[simp] theorem zero_smul_set {s : Set β} (h : s.Nonempty) : (0 : α) • s = (0 : Set β) := by
  simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]

theorem zero_smul_set_subset (s : Set β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ ↦ zero_smul α x

theorem subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton :=
  subsingleton_singleton.anti <| zero_smul_set_subset s

variable [NoZeroSMulDivisors α β] {a : α}

theorem zero_mem_smul_iff :
    (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.Nonempty ∨ (0 : β) ∈ t ∧ s.Nonempty := by
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h
    · exact Or.inl ⟨ha, b, hb⟩
    · exact Or.inr ⟨hb, a, ha⟩
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact ⟨0, hs, b, hb, zero_smul _ _⟩
    · exact ⟨a, ha, 0, ht, smul_zero _⟩

end SMulWithZero

section Semigroup

variable [Semigroup α]

@[to_additive]
theorem op_smul_set_mul_eq_mul_smul_set (a : α) (s : Set α) (t : Set α) :
    op a • s * t = s * a • t :=
  op_smul_set_smul_eq_smul_smul_set _ _ _ fun _ _ _ => mul_assoc _ _ _

end Semigroup

section IsLeftCancelMul

variable [Mul α] [IsLeftCancelMul α] {s t : Set α}

@[to_additive]
theorem pairwiseDisjoint_smul_iff :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t).InjOn fun p ↦ p.1 * p.2 :=
  pairwiseDisjoint_image_right_iff fun _ _ ↦ mul_right_injective _

end IsLeftCancelMul

section Group

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

@[to_additive (attr := simp)]
theorem smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s :=
  (MulAction.injective _).mem_set_image

@[to_additive]
theorem mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show x ∈ MulAction.toPerm a '' A ↔ _ from mem_image_equiv

@[to_additive]
theorem mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A := by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive (attr := simp)]
lemma mem_smul_set_inv {s : Set α} : a ∈ b • s⁻¹ ↔ b ∈ a • s := by
  simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive]
theorem preimage_smul (a : α) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).symm.image_eq_preimage _).symm

@[to_additive]
theorem preimage_smul_inv (a : α) (t : Set β) : (fun x ↦ a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (toUnits a)⁻¹ t

@[to_additive (attr := simp)]
theorem set_smul_subset_set_smul_iff : a • A ⊆ a • B ↔ A ⊆ B :=
  image_subset_image_iff <| MulAction.injective _

@[to_additive]
theorem set_smul_subset_iff : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  image_subset_iff.trans <|
    iff_of_eq <| congr_arg _ <| preimage_equiv_eq_image_symm _ <| MulAction.toPerm _

@[to_additive]
theorem subset_set_smul_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  Iff.symm <|
    image_subset_iff.trans <|
      Iff.symm <| iff_of_eq <| congr_arg _ <| image_equiv_eq_preimage_symm _ <| MulAction.toPerm _

@[to_additive]
theorem smul_set_inter : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter <| MulAction.injective a

@[to_additive]
theorem smul_set_iInter {ι : Sort*}
    (a : α) (t : ι → Set β) : (a • ⋂ i, t i) = ⋂ i, a • t i :=
  image_iInter (MulAction.bijective a) t

@[to_additive]
theorem smul_set_sdiff : a • (s \ t) = a • s \ a • t :=
  image_diff (MulAction.injective a) _ _

open scoped symmDiff in
@[to_additive]
theorem smul_set_symmDiff : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff (MulAction.injective a) _ _

@[to_additive (attr := simp)]
theorem smul_set_univ : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective a

@[to_additive (attr := simp)]
theorem smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set β) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b ↦ ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul _ _⟩

@[to_additive]
theorem smul_set_compl : a • sᶜ = (a • s)ᶜ := by
  simp_rw [Set.compl_eq_univ_diff, smul_set_sdiff, smul_set_univ]

@[to_additive]
theorem smul_inter_ne_empty_iff {s t : Set α} {x : α} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x := by
  rw [← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩

@[to_additive]
theorem smul_inter_ne_empty_iff' {s t : Set α} {x : α} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x := by
  simp_rw [smul_inter_ne_empty_iff, div_eq_mul_inv]

@[to_additive]
theorem op_smul_inter_ne_empty_iff {s t : Set α} {x : αᵐᵒᵖ} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = MulOpposite.unop x := by
  rw [← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, H⟩
    have : MulOpposite.op (a⁻¹ * b) = x := congr_arg MulOpposite.op H
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩

@[to_additive (attr := simp)]
theorem iUnion_inv_smul : ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s :=
  (Function.Surjective.iSup_congr _ inv_surjective) fun _ ↦ rfl

@[to_additive]
theorem iUnion_smul_eq_setOf_exists {s : Set β} : ⋃ g : α, g • s = { a | ∃ g : α, g • a ∈ s } := by
  simp_rw [← iUnion_setOf, ← iUnion_inv_smul, ← preimage_smul, preimage]

@[to_additive (attr := simp)]
lemma inv_smul_set_distrib (a : α) (s : Set α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]
lemma inv_op_smul_set_distrib (a : α) (s : Set α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]
lemma disjoint_smul_set : Disjoint (a • s) (a • t) ↔ Disjoint s t :=
  disjoint_image_iff <| MulAction.injective _

@[to_additive]
lemma disjoint_smul_set_left : Disjoint (a • s) t ↔ Disjoint s (a⁻¹ • t) := by
  simpa using disjoint_smul_set (a := a) (t := a⁻¹ • t)

@[to_additive]
lemma disjoint_smul_set_right : Disjoint s (a • t) ↔ Disjoint (a⁻¹ • s) t := by
  simpa using disjoint_smul_set (a := a) (s := a⁻¹ • s)

@[to_additive] alias smul_set_disjoint_iff := disjoint_smul_set

-- `alias` doesn't add the deprecation suggestion to the `to_additive` version
-- see https://github.com/leanprover-community/mathlib4/issues/19424
attribute [deprecated disjoint_smul_set (since := "2024-10-18")] smul_set_disjoint_iff
attribute [deprecated disjoint_vadd_set (since := "2024-10-18")] vadd_set_disjoint_iff


/-- Any intersection of translates of two sets `s` and `t` can be covered by a single translate of
`(s⁻¹ * s) ∩ (t⁻¹ * t)`.

This is useful to show that the intersection of approximate subgroups is an approximate subgroup. -/
@[to_additive
"Any intersection of translates of two sets `s` and `t` can be covered by a single translate of
`(-s + s) ∩ (-t + t)`.

This is useful to show that the intersection of approximate subgroups is an approximate subgroup."]
lemma exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul (s t : Set α) (a b : α) :
    ∃ z : α, a • s ∩ b • t ⊆ z • ((s⁻¹ * s) ∩ (t⁻¹ * t)) := by
  obtain hAB | ⟨z, hzA, hzB⟩ := (a • s ∩ b • t).eq_empty_or_nonempty
  · exact ⟨1, by simp [hAB]⟩
  refine ⟨z, ?_⟩
  calc
    a • s ∩ b • t ⊆ (z • s⁻¹) * s ∩ ((z • t⁻¹) * t) := by
      gcongr <;> apply smul_set_subset_mul <;> simpa
    _ = z • ((s⁻¹ * s) ∩ (t⁻¹ * t)) := by simp_rw [Set.smul_set_inter, smul_mul_assoc]

end Group

section Monoid
variable [Monoid α] [MulAction α β] {s : Set β} {a : α} {b : β}

@[simp] lemma mem_invOf_smul_set [Invertible a] : b ∈ ⅟a • s ↔ a • b ∈ s :=
  mem_inv_smul_set_iff (a := unitOfInvertible a)

end Monoid

section Group
variable [Group α] [CommGroup β] [FunLike F α β] [MonoidHomClass F α β]

@[to_additive]
lemma smul_graphOn (x : α × β) (s : Set α) (f : F) :
    x • s.graphOn f = (x.1 • s).graphOn fun a ↦ x.2 / f x.1 * f a := by
  ext ⟨a, b⟩
  simp [mem_smul_set_iff_inv_smul_mem, Prod.ext_iff, and_comm (a := _ = a), inv_mul_eq_iff_eq_mul,
    mul_left_comm _ _⁻¹, eq_inv_mul_iff_mul_eq, ← mul_div_right_comm, div_eq_iff_eq_mul, mul_comm b]

@[to_additive]
lemma smul_graphOn_univ (x : α × β) (f : F) :
    x • univ.graphOn f = univ.graphOn fun a ↦ x.2 / f x.1 * f a := by simp [smul_graphOn]

end Group

section CommGroup
variable [CommGroup α]

@[to_additive] lemma smul_div_smul_comm (a : α) (s : Set α) (b : α) (t : Set α) :
    a • s / b • t = (a / b) • (s / t) := by
  simp_rw [← image_smul, smul_eq_mul, ← singleton_mul, mul_div_mul_comm _ s,
    singleton_div_singleton]

end CommGroup

section GroupWithZero

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

@[simp]
theorem smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : a • x ∈ a • A ↔ x ∈ A :=
  show Units.mk0 a ha • _ ∈ _ ↔ _ from smul_mem_smul_set_iff

theorem mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show _ ∈ Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem

theorem mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff

theorem preimage_smul₀ (ha : a ≠ 0) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t :=
  preimage_smul (Units.mk0 a ha) t

theorem preimage_smul_inv₀ (ha : a ≠ 0) (t : Set β) : (fun x ↦ a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (Units.mk0 a ha)⁻¹ t

@[simp]
theorem set_smul_subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_set_smul_iff

theorem set_smul_subset_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_iff

theorem subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_set_smul_iff

theorem smul_set_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  show Units.mk0 a ha • _ = _ from smul_set_inter

theorem smul_set_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t :=
  image_diff (MulAction.injective₀ ha) _ _

open scoped symmDiff in
theorem smul_set_symmDiff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff (MulAction.injective₀ ha) _ _

theorem smul_set_univ₀ (ha : a ≠ 0) : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective₀ ha

theorem smul_univ₀ {s : Set α} (hs : ¬s ⊆ 0) : s • (univ : Set β) = univ :=
  let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b ↦ ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul₀ ha₀ _⟩

theorem smul_univ₀' {s : Set α} (hs : s.Nontrivial) : s • (univ : Set β) = univ :=
  smul_univ₀ hs.not_subset_singleton

@[simp] protected lemma inv_zero : (0 : Set α)⁻¹ = 0 := by ext; simp

@[simp] lemma inv_smul_set_distrib₀ (a : α) (s : Set α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]

@[simp] lemma inv_op_smul_set_distrib₀ (a : α) (s : Set α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]

end GroupWithZero

section Monoid

variable [Monoid α] [AddGroup β] [DistribMulAction α β] (a : α) (s : Set α) (t : Set β)

@[simp]
theorem smul_set_neg : a • -t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, smul_neg]

@[simp]
protected theorem smul_neg : s • -t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image_image2_right_comm smul_neg

end Monoid

section Semiring

variable [Semiring α] [AddCommMonoid β] [Module α β]

theorem add_smul_subset (a b : α) (s : Set β) : (a + b) • s ⊆ a • s + b • s := by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [add_smul] using add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hx)

end Semiring

section Ring

variable [Ring α] [AddCommGroup β] [Module α β] (a : α) (s : Set α) (t : Set β)

@[simp]
theorem neg_smul_set : -a • t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, neg_smul]

@[simp]
protected theorem neg_smul : -s • t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image2_image_left_comm neg_smul

end Ring

end Set
