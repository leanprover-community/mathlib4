/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Set.Pointwise.Basic

/-!
# Pointwise operations of sets

This file defines pointwise algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:
* `s • t`: Scalar multiplication, set of all `x • y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t`: Scalar addition, set of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s -ᵥ t`: Scalar subtraction, set of all `x -ᵥ y` where `x ∈ s` and `y ∈ t`.
* `a • s`: Scaling, set of all `a • x` where `x ∈ s`.
* `a +ᵥ s`: Translation, set of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `Set α` is a semigroup/monoid.

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

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

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in locale `Pointwise`. -/
@[to_additive
      "The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in
      locale `Pointwise`."]
protected def smulSet [SMul α β] : SMul α (Set β) :=
  ⟨fun a ↦ image (a • ·)⟩

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
locale `Pointwise`. -/
@[to_additive
      "The pointwise scalar addition of sets `s +ᵥ t` is defined as
      `{x +ᵥ y | x ∈ s, y ∈ t}` in locale `Pointwise`."]
protected def smul [SMul α β] : SMul (Set α) (Set β) :=
  ⟨image2 (· • ·)⟩

scoped[Pointwise] attribute [instance] Set.smulSet Set.smul

scoped[Pointwise] attribute [instance] Set.vaddSet Set.vadd

section SMul

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

@[to_additive (attr := simp)]
theorem image2_smul : image2 SMul.smul s t = s • t :=
  rfl

@[to_additive vadd_image_prod]
theorem image_smul_prod : (fun x : α × β ↦ x.fst • x.snd) '' s ×ˢ t = s • t :=
  image_prod _

@[to_additive]
theorem mem_smul : b ∈ s • t ↔ ∃ x ∈ s, ∃ y ∈ t, x • y = b :=
  Iff.rfl

@[to_additive]
theorem smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t :=
  mem_image2_of_mem

@[to_additive (attr := simp)]
theorem empty_smul : (∅ : Set α) • t = ∅ :=
  image2_empty_left

@[to_additive (attr := simp)]
theorem smul_empty : s • (∅ : Set β) = ∅ :=
  image2_empty_right

@[to_additive (attr := simp)]
theorem smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[to_additive (attr := simp)]
theorem smul_nonempty : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

@[to_additive]
theorem Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty :=
  Nonempty.image2

@[to_additive]
theorem Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left

@[to_additive]
theorem Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right

@[to_additive (attr := simp low+1)]
theorem smul_singleton : s • ({b} : Set β) = (· • b) '' s :=
  image2_singleton_right

@[to_additive (attr := simp low+1)]
theorem singleton_smul : ({a} : Set α) • t = a • t :=
  image2_singleton_left

@[to_additive (attr := simp high)]
theorem singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b} :=
  image2_singleton

@[to_additive (attr := mono)]
theorem smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ :=
  image2_subset

@[to_additive]
theorem smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ :=
  image2_subset_left

@[to_additive]
theorem smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t :=
  image2_subset_right

@[to_additive]
theorem smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u :=
  image2_subset_iff


@[to_additive]
theorem union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
  image2_union_left

@[to_additive]
theorem smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ :=
  image2_union_right

@[to_additive]
theorem inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image2_inter_subset_left

@[to_additive]
theorem smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
  image2_inter_subset_right

@[to_additive]
theorem inter_smul_union_subset_union : (s₁ ∩ s₂) • (t₁ ∪ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image2_inter_union_subset_union

@[to_additive]
theorem union_smul_inter_subset_union : (s₁ ∪ s₂) • (t₁ ∩ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image2_union_inter_subset_union

@[to_additive]
theorem iUnion_smul_left_image : ⋃ a ∈ s, a • t = s • t :=
  iUnion_image_left _

@[to_additive]
theorem iUnion_smul_right_image : ⋃ a ∈ t, (· • a) '' s = s • t :=
  iUnion_image_right _

@[to_additive]
theorem iUnion_smul (s : ι → Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
  image2_iUnion_left _ _ _

@[to_additive]
theorem smul_iUnion (s : Set α) (t : ι → Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i :=
  image2_iUnion_right _ _ _

@[to_additive]
theorem iUnion₂_smul (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋃ (i) (j), s i j) • t = ⋃ (i) (j), s i j • t :=
  image2_iUnion₂_left _ _ _

@[to_additive]
theorem smul_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋃ (i) (j), t i j) = ⋃ (i) (j), s • t i j :=
  image2_iUnion₂_right _ _ _

@[to_additive]
theorem iInter_smul_subset (s : ι → Set α) (t : Set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
  image2_iInter_subset_left _ _ _

@[to_additive]
theorem smul_iInter_subset (s : Set α) (t : ι → Set β) : (s • ⋂ i, t i) ⊆ ⋂ i, s • t i :=
  image2_iInter_subset_right _ _ _

@[to_additive]
theorem iInter₂_smul_subset (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋂ (i) (j), s i j) • t ⊆ ⋂ (i) (j), s i j • t :=
  image2_iInter₂_subset_left _ _ _

@[to_additive]
theorem smul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s • t i j :=
  image2_iInter₂_subset_right _ _ _

@[to_additive]
theorem smul_set_subset_smul {s : Set α} : a ∈ s → a • t ⊆ s • t :=
  image_subset_image2_right

@[to_additive (attr := simp)]
theorem iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a ∈ s, a • t = s • t :=
  iUnion_image_left _

end SMul

section SMulSet

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

@[to_additive]
theorem image_smul : (fun x ↦ a • x) '' t = a • t :=
  rfl

scoped[Pointwise] attribute [simp] Set.image_smul Set.image_vadd

@[to_additive]
theorem mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x :=
  Iff.rfl

@[to_additive]
theorem smul_mem_smul_set : b ∈ s → a • b ∈ a • s :=
  mem_image_of_mem _

@[to_additive (attr := simp)]
theorem smul_set_empty : a • (∅ : Set β) = ∅ :=
  image_empty _

@[to_additive (attr := simp)]
theorem smul_set_eq_empty : a • s = ∅ ↔ s = ∅ :=
  image_eq_empty

@[to_additive (attr := simp)]
theorem smul_set_nonempty : (a • s).Nonempty ↔ s.Nonempty :=
  image_nonempty

@[to_additive (attr := simp)]
theorem smul_set_singleton : a • ({b} : Set β) = {a • b} :=
  image_singleton

@[to_additive]
theorem smul_set_mono : s ⊆ t → a • s ⊆ a • t :=
  image_subset _

@[to_additive]
theorem smul_set_subset_iff : a • s ⊆ t ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ t :=
  image_subset_iff

@[to_additive]
theorem smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ :=
  image_union _ _ _

@[to_additive]
theorem smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ a • t₂ :=
  image_inter_subset _ _ _

@[to_additive]
theorem smul_set_iUnion (a : α) (s : ι → Set β) : (a • ⋃ i, s i) = ⋃ i, a • s i :=
  image_iUnion

@[to_additive]
theorem smul_set_iUnion₂ (a : α) (s : ∀ i, κ i → Set β) :
    (a • ⋃ (i) (j), s i j) = ⋃ (i) (j), a • s i j :=
  image_iUnion₂ _ _

@[to_additive]
theorem smul_set_iInter_subset (a : α) (t : ι → Set β) : (a • ⋂ i, t i) ⊆ ⋂ i, a • t i :=
  image_iInter_subset _ _

@[to_additive]
theorem smul_set_iInter₂_subset (a : α) (t : ∀ i, κ i → Set β) :
    (a • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), a • t i j :=
  image_iInter₂_subset _ _

@[to_additive]
theorem Nonempty.smul_set : s.Nonempty → (a • s).Nonempty :=
  Nonempty.image _

end SMulSet

section Mul

variable [Mul α] {s t u : Set α} {a : α}

@[to_additive]
theorem op_smul_set_subset_mul : a ∈ t → op a • s ⊆ s * t :=
  image_subset_image2_left

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

end Mul

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

@[to_additive]
theorem range_smul_range {ι κ : Type*} [SMul α β] (b : ι → α) (c : κ → β) :
    range b • range c = range fun p : ι × κ ↦ b p.1 • c p.2 :=
  image2_range ..

@[to_additive]
theorem smul_set_range [SMul α β] {ι : Sort*} (a : α) (f : ι → β) :
    a • range f = range fun i ↦ a • f i :=
  (range_comp _ _).symm

@[to_additive] lemma range_smul [SMul α β] {ι : Sort*} (a : α) (f : ι → β) :
    range (fun i ↦ a • f i) = a • range f := (smul_set_range ..).symm

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

section VSub

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

instance vsub : VSub (Set α) (Set β) :=
  ⟨image2 (· -ᵥ ·)⟩

@[simp]
theorem image2_vsub : (image2 VSub.vsub s t : Set α) = s -ᵥ t :=
  rfl

theorem image_vsub_prod : (fun x : β × β ↦ x.fst -ᵥ x.snd) '' s ×ˢ t = s -ᵥ t :=
  image_prod _

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ x ∈ s, ∃ y ∈ t, x -ᵥ y = a :=
  Iff.rfl

theorem vsub_mem_vsub (hb : b ∈ s) (hc : c ∈ t) : b -ᵥ c ∈ s -ᵥ t :=
  mem_image2_of_mem hb hc

@[simp]
theorem empty_vsub (t : Set β) : ∅ -ᵥ t = ∅ :=
  image2_empty_left

@[simp]
theorem vsub_empty (s : Set β) : s -ᵥ ∅ = ∅ :=
  image2_empty_right

@[simp]
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[simp]
theorem vsub_nonempty : (s -ᵥ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Set α).Nonempty :=
  Nonempty.image2

theorem Nonempty.of_vsub_left : (s -ᵥ t : Set α).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left

theorem Nonempty.of_vsub_right : (s -ᵥ t : Set α).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right

@[simp low+1]
theorem vsub_singleton (s : Set β) (b : β) : s -ᵥ {b} = (· -ᵥ b) '' s :=
  image2_singleton_right

@[simp low+1]
theorem singleton_vsub (t : Set β) (b : β) : {b} -ᵥ t = (b -ᵥ ·) '' t :=
  image2_singleton_left

@[simp high]
theorem singleton_vsub_singleton : ({b} : Set β) -ᵥ {c} = {b -ᵥ c} :=
  image2_singleton

@[mono]
theorem vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image2_subset

theorem vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image2_subset_left

theorem vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image2_subset_right

theorem vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x -ᵥ y ∈ u :=
  image2_subset_iff

theorem vsub_self_mono (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t :=
  vsub_subset_vsub h h

theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image2_union_left

theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image2_union_right

theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image2_inter_subset_left

theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image2_inter_subset_right

theorem inter_vsub_union_subset_union : s₁ ∩ s₂ -ᵥ (t₁ ∪ t₂) ⊆ s₁ -ᵥ t₁ ∪ (s₂ -ᵥ t₂) :=
  image2_inter_union_subset_union

theorem union_vsub_inter_subset_union : s₁ ∪ s₂ -ᵥ t₁ ∩ t₂ ⊆ s₁ -ᵥ t₁ ∪ (s₂ -ᵥ t₂) :=
  image2_union_inter_subset_union

theorem iUnion_vsub_left_image : ⋃ a ∈ s, (a -ᵥ ·) '' t = s -ᵥ t :=
  iUnion_image_left _

theorem iUnion_vsub_right_image : ⋃ a ∈ t, (· -ᵥ a) '' s = s -ᵥ t :=
  iUnion_image_right _

theorem iUnion_vsub (s : ι → Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
  image2_iUnion_left _ _ _

theorem vsub_iUnion (s : Set β) (t : ι → Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i :=
  image2_iUnion_right _ _ _

theorem iUnion₂_vsub (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋃ (i) (j), s i j) -ᵥ t = ⋃ (i) (j), s i j -ᵥ t :=
  image2_iUnion₂_left _ _ _

theorem vsub_iUnion₂ (s : Set β) (t : ∀ i, κ i → Set β) :
    (s -ᵥ ⋃ (i) (j), t i j) = ⋃ (i) (j), s -ᵥ t i j :=
  image2_iUnion₂_right _ _ _

theorem iInter_vsub_subset (s : ι → Set β) (t : Set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
  image2_iInter_subset_left _ _ _

theorem vsub_iInter_subset (s : Set β) (t : ι → Set β) : (s -ᵥ ⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
  image2_iInter_subset_right _ _ _

theorem iInter₂_vsub_subset (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋂ (i) (j), s i j) -ᵥ t ⊆ ⋂ (i) (j), s i j -ᵥ t :=
  image2_iInter₂_subset_left _ _ _

theorem vsub_iInter₂_subset (s : Set β) (t : ∀ i, κ i → Set β) :
    (s -ᵥ ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s -ᵥ t i j :=
  image2_iInter₂_subset_right _ _ _

end VSub

open Pointwise

@[to_additive]
theorem image_smul_comm [SMul α β] [SMul α γ] (f : β → γ) (a : α) (s : Set β) :
    (∀ b, f (a • b) = a • f b) → f '' (a • s) = a • f '' s :=
  image_comm

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

variable [Group α] [MulAction α β] {s t A B : Set β} {a : α} {x : β}

@[to_additive (attr := simp)]
theorem smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s :=
  (MulAction.injective _).mem_set_image

@[to_additive]
theorem mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show x ∈ MulAction.toPerm a '' A ↔ _ from mem_image_equiv

@[to_additive]
theorem mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A := by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

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
theorem smul_set_iInter {ι : Type*}
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
lemma smul_set_disjoint_iff : Disjoint (a • s) (a • t) ↔ Disjoint s t := by
  simp [disjoint_iff, ← smul_set_inter]

end Group

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
  simp_rw [← image_smul, ← image_neg, image_image, smul_neg]

@[simp]
protected theorem smul_neg : s • -t = -(s • t) := by
  simp_rw [← image_neg]
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
  simp_rw [← image_smul, ← image_neg, image_image, neg_smul]

@[simp]
protected theorem neg_smul : -s • t = -(s • t) := by
  simp_rw [← image_neg]
  exact image2_image_left_comm neg_smul

end Ring

end Set
