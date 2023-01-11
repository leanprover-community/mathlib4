/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn

! This file was ported from Lean 3 source module data.set.pointwise.smul
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Data.Set.Pairwise
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Tactic.ByContra

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

For `α` a semigroup/monoid, `set α` is a semigroup/monoid.

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

-/


open Function

variable {F α β γ : Type _}

namespace Set

open Pointwise

/-! ### Translation/scaling of sets -/


section Smul

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in locale `pointwise`. -/
@[to_additive
      "The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in\nlocale `pointwise`."]
protected def hasSmulSet [HasSmul α β] : HasSmul α (Set β) :=
  ⟨fun a => image (HasSmul.smul a)⟩
#align set.has_smul_set Set.hasSmulSet

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive
      "The pointwise scalar addition of sets `s +ᵥ t` is defined as\n`{x +ᵥ y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def hasSmul [HasSmul α β] : HasSmul (Set α) (Set β) :=
  ⟨image2 HasSmul.smul⟩
#align set.has_smul Set.hasSmul

scoped[Pointwise] attribute [instance] Set.hasSmulSet Set.hasSmul

scoped[Pointwise] attribute [instance] Set.hasVaddSet Set.hasVadd

section HasSmul

variable {ι : Sort _} {κ : ι → Sort _} [HasSmul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

@[simp, to_additive]
theorem image2_smul : image2 HasSmul.smul s t = s • t :=
  rfl
#align set.image2_smul Set.image2_smul

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive add_image_prod]
theorem image_smul_prod : (fun x : α × β => x.fst • x.snd) '' s ×ˢ t = s • t :=
  image_prod _
#align set.image_smul_prod Set.image_smul_prod

@[to_additive]
theorem mem_smul : b ∈ s • t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x • y = b :=
  Iff.rfl
#align set.mem_smul Set.mem_smul

@[to_additive]
theorem smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t :=
  mem_image2_of_mem
#align set.smul_mem_smul Set.smul_mem_smul

@[simp, to_additive]
theorem empty_smul : (∅ : Set α) • t = ∅ :=
  image2_empty_left
#align set.empty_smul Set.empty_smul

@[simp, to_additive]
theorem smul_empty : s • (∅ : Set β) = ∅ :=
  image2_empty_right
#align set.smul_empty Set.smul_empty

@[simp, to_additive]
theorem smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.smul_eq_empty Set.smul_eq_empty

@[simp, to_additive]
theorem smul_nonempty : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.smul_nonempty Set.smul_nonempty

@[to_additive]
theorem Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty :=
  nonempty.image2
#align set.nonempty.smul Set.Nonempty.smul

@[to_additive]
theorem Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty :=
  nonempty.of_image2_left
#align set.nonempty.of_smul_left Set.Nonempty.of_smul_left

@[to_additive]
theorem Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty :=
  nonempty.of_image2_right
#align set.nonempty.of_smul_right Set.Nonempty.of_smul_right

@[simp, to_additive]
theorem smul_singleton : s • {b} = (· • b) '' s :=
  image2_singleton_right
#align set.smul_singleton Set.smul_singleton

@[simp, to_additive]
theorem singleton_smul : ({a} : Set α) • t = a • t :=
  image2_singleton_left
#align set.singleton_smul Set.singleton_smul

@[simp, to_additive]
theorem singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b} :=
  image2_singleton
#align set.singleton_smul_singleton Set.singleton_smul_singleton

@[to_additive, mono]
theorem smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ :=
  image2_subset
#align set.smul_subset_smul Set.smul_subset_smul

@[to_additive]
theorem smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ :=
  image2_subset_left
#align set.smul_subset_smul_left Set.smul_subset_smul_left

@[to_additive]
theorem smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t :=
  image2_subset_right
#align set.smul_subset_smul_right Set.smul_subset_smul_right

@[to_additive]
theorem smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u :=
  image2_subset_iff
#align set.smul_subset_iff Set.smul_subset_iff

attribute [mono] vadd_subset_vadd

@[to_additive]
theorem union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
  image2_union_left
#align set.union_smul Set.union_smul

@[to_additive]
theorem smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ :=
  image2_union_right
#align set.smul_union Set.smul_union

@[to_additive]
theorem inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image2_inter_subset_left
#align set.inter_smul_subset Set.inter_smul_subset

@[to_additive]
theorem smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
  image2_inter_subset_right
#align set.smul_inter_subset Set.smul_inter_subset

@[to_additive]
theorem Union_smul_left_image : (⋃ a ∈ s, a • t) = s • t :=
  unionᵢ_image_left _
#align set.Union_smul_left_image Set.Union_smul_left_image

@[to_additive]
theorem Union_smul_right_image : (⋃ a ∈ t, (· • a) '' s) = s • t :=
  unionᵢ_image_right _
#align set.Union_smul_right_image Set.Union_smul_right_image

@[to_additive]
theorem Union_smul (s : ι → Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
  image2_unionᵢ_left _ _ _
#align set.Union_smul Set.Union_smul

@[to_additive]
theorem smul_Union (s : Set α) (t : ι → Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i :=
  image2_unionᵢ_right _ _ _
#align set.smul_Union Set.smul_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Union₂_smul (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋃ (i) (j), s i j) • t = ⋃ (i) (j), s i j • t :=
  image2_unionᵢ₂_left _ _ _
#align set.Union₂_smul Set.Union₂_smul

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_Union₂ (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋃ (i) (j), t i j) = ⋃ (i) (j), s • t i j :=
  image2_unionᵢ₂_right _ _ _
#align set.smul_Union₂ Set.smul_Union₂

@[to_additive]
theorem Inter_smul_subset (s : ι → Set α) (t : Set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
  image2_interᵢ_subset_left _ _ _
#align set.Inter_smul_subset Set.Inter_smul_subset

@[to_additive]
theorem smul_Inter_subset (s : Set α) (t : ι → Set β) : (s • ⋂ i, t i) ⊆ ⋂ i, s • t i :=
  image2_interᵢ_subset_right _ _ _
#align set.smul_Inter_subset Set.smul_Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Inter₂_smul_subset (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋂ (i) (j), s i j) • t ⊆ ⋂ (i) (j), s i j • t :=
  image2_interᵢ₂_subset_left _ _ _
#align set.Inter₂_smul_subset Set.Inter₂_smul_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_Inter₂_subset (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s • t i j :=
  image2_interᵢ₂_subset_right _ _ _
#align set.smul_Inter₂_subset Set.smul_Inter₂_subset

@[simp, to_additive]
theorem bUnion_smul_set (s : Set α) (t : Set β) : (⋃ a ∈ s, a • t) = s • t :=
  unionᵢ_image_left _
#align set.bUnion_smul_set Set.bUnion_smul_set

end HasSmul

section HasSmulSet

variable {ι : Sort _} {κ : ι → Sort _} [HasSmul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

@[simp, to_additive]
theorem image_smul : (fun x => a • x) '' t = a • t :=
  rfl
#align set.image_smul Set.image_smul

@[to_additive]
theorem mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x :=
  Iff.rfl
#align set.mem_smul_set Set.mem_smul_set

@[to_additive]
theorem smul_mem_smul_set : b ∈ s → a • b ∈ a • s :=
  mem_image_of_mem _
#align set.smul_mem_smul_set Set.smul_mem_smul_set

@[simp, to_additive]
theorem smul_set_empty : a • (∅ : Set β) = ∅ :=
  image_empty _
#align set.smul_set_empty Set.smul_set_empty

@[simp, to_additive]
theorem smul_set_eq_empty : a • s = ∅ ↔ s = ∅ :=
  image_eq_empty
#align set.smul_set_eq_empty Set.smul_set_eq_empty

@[simp, to_additive]
theorem smul_set_nonempty : (a • s).Nonempty ↔ s.Nonempty :=
  nonempty_image_iff
#align set.smul_set_nonempty Set.smul_set_nonempty

@[simp, to_additive]
theorem smul_set_singleton : a • ({b} : Set β) = {a • b} :=
  image_singleton
#align set.smul_set_singleton Set.smul_set_singleton

@[to_additive]
theorem smul_set_mono : s ⊆ t → a • s ⊆ a • t :=
  image_subset _
#align set.smul_set_mono Set.smul_set_mono

@[to_additive]
theorem smul_set_subset_iff : a • s ⊆ t ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ t :=
  image_subset_iff
#align set.smul_set_subset_iff Set.smul_set_subset_iff

@[to_additive]
theorem smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ :=
  image_union _ _ _
#align set.smul_set_union Set.smul_set_union

@[to_additive]
theorem smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ a • t₂ :=
  image_inter_subset _ _ _
#align set.smul_set_inter_subset Set.smul_set_inter_subset

@[to_additive]
theorem smul_set_Union (a : α) (s : ι → Set β) : (a • ⋃ i, s i) = ⋃ i, a • s i :=
  image_Union
#align set.smul_set_Union Set.smul_set_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_set_Union₂ (a : α) (s : ∀ i, κ i → Set β) :
    (a • ⋃ (i) (j), s i j) = ⋃ (i) (j), a • s i j :=
  image_unionᵢ₂ _ _
#align set.smul_set_Union₂ Set.smul_set_Union₂

@[to_additive]
theorem smul_set_Inter_subset (a : α) (t : ι → Set β) : (a • ⋂ i, t i) ⊆ ⋂ i, a • t i :=
  image_interᵢ_subset _ _
#align set.smul_set_Inter_subset Set.smul_set_Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_set_Inter₂_subset (a : α) (t : ∀ i, κ i → Set β) :
    (a • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), a • t i j :=
  image_interᵢ₂_subset _ _
#align set.smul_set_Inter₂_subset Set.smul_set_Inter₂_subset

@[to_additive]
theorem Nonempty.smul_set : s.Nonempty → (a • s).Nonempty :=
  Nonempty.image _
#align set.nonempty.smul_set Set.Nonempty.smul_set

end HasSmulSet

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

@[simp, to_additive]
theorem bUnion_op_smul_set [Mul α] (s t : Set α) : (⋃ a ∈ t, MulOpposite.op a • s) = s * t :=
  unionᵢ_image_right _
#align set.bUnion_op_smul_set Set.bUnion_op_smul_set

@[to_additive]
theorem range_smul_range {ι κ : Type _} [HasSmul α β] (b : ι → α) (c : κ → β) :
    range b • range c = range fun p : ι × κ => b p.1 • c p.2 :=
  ext fun x =>
    ⟨fun hx =>
      let ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := Set.mem_smul.1 hx
      ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
      fun ⟨⟨i, j⟩, h⟩ => Set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩
#align set.range_smul_range Set.range_smul_range

@[to_additive]
theorem smul_set_range [HasSmul α β] {ι : Sort _} {f : ι → β} :
    a • range f = range fun i => a • f i :=
  (range_comp _ _).symm
#align set.smul_set_range Set.smul_set_range

@[to_additive]
instance smul_comm_class_set [HasSmul α γ] [HasSmul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Set γ) :=
  ⟨fun _ _ => commute.set_image <| smul_comm _ _⟩
#align set.smul_comm_class_set Set.smul_comm_class_set

@[to_additive]
instance smul_comm_class_set' [HasSmul α γ] [HasSmul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Set β) (Set γ) :=
  ⟨fun _ _ _ => image_image2_distrib_right <| smul_comm _⟩
#align set.smul_comm_class_set' Set.smul_comm_class_set'

@[to_additive]
instance smul_comm_class_set'' [HasSmul α γ] [HasSmul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) β (Set γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _
#align set.smul_comm_class_set'' Set.smul_comm_class_set''

@[to_additive]
instance smul_comm_class [HasSmul α γ] [HasSmul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) (Set β) (Set γ) :=
  ⟨fun _ _ _ => image2_left_comm smul_comm⟩
#align set.smul_comm_class Set.smul_comm_class

@[to_additive]
instance is_scalar_tower [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Set γ)
    where smul_assoc a b T := by simp only [← image_smul, image_image, smul_assoc]
#align set.is_scalar_tower Set.is_scalar_tower

@[to_additive]
instance is_scalar_tower' [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Set β) (Set γ) :=
  ⟨fun _ _ _ => image2_image_left_comm <| smul_assoc _⟩
#align set.is_scalar_tower' Set.is_scalar_tower'

@[to_additive]
instance is_scalar_tower'' [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Set α) (Set β) (Set γ) where smul_assoc T T' T'' := image2_assoc smul_assoc
#align set.is_scalar_tower'' Set.is_scalar_tower''

instance is_central_scalar [HasSmul α β] [HasSmul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Set β) :=
  ⟨fun a S => (congr_arg fun f => f '' S) <| funext fun _ => op_smul_eq_smul _ _⟩
#align set.is_central_scalar Set.is_central_scalar

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `set α`
on `set β`. -/
@[to_additive
      "An additive action of an additive monoid `α` on a type `β` gives an additive action\nof `set α` on `set β`"]
protected def mulAction [Monoid α] [MulAction α β] : MulAction (Set α) (Set β)
    where
  mul_smul _ _ _ := image2_assoc mul_smul
  one_smul s := image2_singleton_left.trans <| by simp_rw [one_smul, image_id']
#align set.mul_action Set.mulAction

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `set β`. -/
@[to_additive
      "An additive action of an additive monoid on a type `β` gives an additive action\non `set β`."]
protected def mulActionSet [Monoid α] [MulAction α β] : MulAction α (Set β)
    where
  mul_smul := by
    intros
    simp only [← image_smul, image_image, ← mul_smul]
  one_smul := by
    intros
    simp only [← image_smul, one_smul, image_id']
#align set.mul_action_set Set.mulActionSet

scoped[Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `set β`. -/
protected def distribMulActionSet [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Set β)
    where
  smul_add _ _ _ := image_image2_distrib <| smul_add _
  smul_zero _ := image_singleton.trans <| by rw [smul_zero, singleton_zero]
#align set.distrib_mul_action_set Set.distribMulActionSet

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mulDistribMulActionSet [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Set β)
    where
  smul_mul _ _ _ := image_image2_distrib <| smul_mul' _
  smul_one _ := image_singleton.trans <| by rw [smul_one, singleton_one]
#align set.mul_distrib_mul_action_set Set.mulDistribMulActionSet

scoped[Pointwise] attribute [instance] Set.distribMulActionSet Set.mulDistribMulActionSet

instance [Zero α] [Zero β] [HasSmul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors (Set α) (Set β) :=
  ⟨fun s t h => by
    by_contra' H
    have hst : (s • t).Nonempty := h.symm.subst zero_nonempty
    simp_rw [← hst.of_smul_left.subset_zero_iff, ← hst.of_smul_right.subset_zero_iff, not_subset,
      mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul hs ht).elim ha hb⟩

instance no_zero_smul_divisors_set [Zero α] [Zero β] [HasSmul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors α (Set β) :=
  ⟨fun a s h => by
    by_contra' H
    have hst : (a • s).Nonempty := h.symm.subst zero_nonempty
    simp_rw [← hst.of_image.subset_zero_iff, not_subset, mem_zero] at H
    obtain ⟨ha, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul_set ht).elim ha hb⟩
#align set.no_zero_smul_divisors_set Set.no_zero_smul_divisors_set

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Set α) :=
  ⟨fun s t h => eq_zero_or_eq_zero_of_smul_eq_zero h⟩

end Smul

section Vsub

variable {ι : Sort _} {κ : ι → Sort _} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

include α

instance hasVsub : VSub (Set α) (Set β) :=
  ⟨image2 (· -ᵥ ·)⟩
#align set.has_vsub Set.hasVsub

@[simp]
theorem image2_vsub : (image2 VSub.vsub s t : Set α) = s -ᵥ t :=
  rfl
#align set.image2_vsub Set.image2_vsub

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem image_vsub_prod : (fun x : β × β => x.fst -ᵥ x.snd) '' s ×ˢ t = s -ᵥ t :=
  image_prod _
#align set.image_vsub_prod Set.image_vsub_prod

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x -ᵥ y = a :=
  Iff.rfl
#align set.mem_vsub Set.mem_vsub

theorem vsub_mem_vsub (hb : b ∈ s) (hc : c ∈ t) : b -ᵥ c ∈ s -ᵥ t :=
  mem_image2_of_mem hb hc
#align set.vsub_mem_vsub Set.vsub_mem_vsub

@[simp]
theorem empty_vsub (t : Set β) : ∅ -ᵥ t = ∅ :=
  image2_empty_left
#align set.empty_vsub Set.empty_vsub

@[simp]
theorem vsub_empty (s : Set β) : s -ᵥ ∅ = ∅ :=
  image2_empty_right
#align set.vsub_empty Set.vsub_empty

@[simp]
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.vsub_eq_empty Set.vsub_eq_empty

@[simp]
theorem vsub_nonempty : (s -ᵥ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.vsub_nonempty Set.vsub_nonempty

theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Set α).Nonempty :=
  nonempty.image2
#align set.nonempty.vsub Set.Nonempty.vsub

theorem Nonempty.of_vsub_left : (s -ᵥ t : Set α).Nonempty → s.Nonempty :=
  nonempty.of_image2_left
#align set.nonempty.of_vsub_left Set.Nonempty.of_vsub_left

theorem Nonempty.of_vsub_right : (s -ᵥ t : Set α).Nonempty → t.Nonempty :=
  nonempty.of_image2_right
#align set.nonempty.of_vsub_right Set.Nonempty.of_vsub_right

@[simp]
theorem vsub_singleton (s : Set β) (b : β) : s -ᵥ {b} = (· -ᵥ b) '' s :=
  image2_singleton_right
#align set.vsub_singleton Set.vsub_singleton

@[simp]
theorem singleton_vsub (t : Set β) (b : β) : {b} -ᵥ t = (· -ᵥ ·) b '' t :=
  image2_singleton_left
#align set.singleton_vsub Set.singleton_vsub

@[simp]
theorem singleton_vsub_singleton : ({b} : Set β) -ᵥ {c} = {b -ᵥ c} :=
  image2_singleton
#align set.singleton_vsub_singleton Set.singleton_vsub_singleton

@[mono]
theorem vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image2_subset
#align set.vsub_subset_vsub Set.vsub_subset_vsub

theorem vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image2_subset_left
#align set.vsub_subset_vsub_left Set.vsub_subset_vsub_left

theorem vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image2_subset_right
#align set.vsub_subset_vsub_right Set.vsub_subset_vsub_right

theorem vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x -ᵥ y ∈ u :=
  image2_subset_iff
#align set.vsub_subset_iff Set.vsub_subset_iff

theorem vsub_self_mono (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t :=
  vsub_subset_vsub h h
#align set.vsub_self_mono Set.vsub_self_mono

theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image2_union_left
#align set.union_vsub Set.union_vsub

theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image2_union_right
#align set.vsub_union Set.vsub_union

theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image2_inter_subset_left
#align set.inter_vsub_subset Set.inter_vsub_subset

theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image2_inter_subset_right
#align set.vsub_inter_subset Set.vsub_inter_subset

theorem Union_vsub_left_image : (⋃ a ∈ s, (· -ᵥ ·) a '' t) = s -ᵥ t :=
  unionᵢ_image_left _
#align set.Union_vsub_left_image Set.Union_vsub_left_image

theorem Union_vsub_right_image : (⋃ a ∈ t, (· -ᵥ a) '' s) = s -ᵥ t :=
  unionᵢ_image_right _
#align set.Union_vsub_right_image Set.Union_vsub_right_image

theorem Union_vsub (s : ι → Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
  image2_unionᵢ_left _ _ _
#align set.Union_vsub Set.Union_vsub

theorem vsub_Union (s : Set β) (t : ι → Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i :=
  image2_unionᵢ_right _ _ _
#align set.vsub_Union Set.vsub_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Union₂_vsub (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋃ (i) (j), s i j) -ᵥ t = ⋃ (i) (j), s i j -ᵥ t :=
  image2_unionᵢ₂_left _ _ _
#align set.Union₂_vsub Set.Union₂_vsub

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem vsub_Union₂ (s : Set β) (t : ∀ i, κ i → Set β) :
    (s -ᵥ ⋃ (i) (j), t i j) = ⋃ (i) (j), s -ᵥ t i j :=
  image2_unionᵢ₂_right _ _ _
#align set.vsub_Union₂ Set.vsub_Union₂

theorem Inter_vsub_subset (s : ι → Set β) (t : Set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
  image2_interᵢ_subset_left _ _ _
#align set.Inter_vsub_subset Set.Inter_vsub_subset

theorem vsub_Inter_subset (s : Set β) (t : ι → Set β) : (s -ᵥ ⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
  image2_interᵢ_subset_right _ _ _
#align set.vsub_Inter_subset Set.vsub_Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Inter₂_vsub_subset (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋂ (i) (j), s i j) -ᵥ t ⊆ ⋂ (i) (j), s i j -ᵥ t :=
  image2_interᵢ₂_subset_left _ _ _
#align set.Inter₂_vsub_subset Set.Inter₂_vsub_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem vsub_Inter₂_subset (s : Set β) (t : ∀ i, κ i → Set β) :
    (s -ᵥ ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s -ᵥ t i j :=
  image2_interᵢ₂_subset_right _ _ _
#align set.vsub_Inter₂_subset Set.vsub_Inter₂_subset

end Vsub

open Pointwise

section SMulWithZero

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

/-!
Note that we have neither `smul_with_zero α (set β)` nor `smul_with_zero (set α) (set β)`
because `0 * ∅ ≠ 0`.
-/


theorem smul_zero_subset (s : Set α) : s • (0 : Set β) ⊆ 0 := by simp [subset_def, mem_smul]
#align set.smul_zero_subset Set.smul_zero_subset

theorem zero_smul_subset (t : Set β) : (0 : Set α) • t ⊆ 0 := by simp [subset_def, mem_smul]
#align set.zero_smul_subset Set.zero_smul_subset

theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using hs
#align set.nonempty.smul_zero Set.Nonempty.smul_zero

theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using ht
#align set.nonempty.zero_smul Set.Nonempty.zero_smul

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
theorem zero_smul_set {s : Set β} (h : s.Nonempty) : (0 : α) • s = (0 : Set β) := by
  simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]
#align set.zero_smul_set Set.zero_smul_set

theorem zero_smul_set_subset (s : Set β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ => zero_smul α x
#align set.zero_smul_set_subset Set.zero_smul_set_subset

theorem subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton :=
  subsingleton_singleton.anti <| zero_smul_set_subset s
#align set.subsingleton_zero_smul_set Set.subsingleton_zero_smul_set

theorem zero_mem_smul_set {t : Set β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
  ⟨0, h, smul_zero _⟩
#align set.zero_mem_smul_set Set.zero_mem_smul_set

variable [NoZeroSMulDivisors α β] {a : α}

theorem zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.Nonempty ∨ (0 : β) ∈ t ∧ s.Nonempty :=
  by
  constructor
  · rintro ⟨a, b, ha, hb, h⟩
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h
    · exact Or.inl ⟨ha, b, hb⟩
    · exact Or.inr ⟨hb, a, ha⟩
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact ⟨0, b, hs, hb, zero_smul _ _⟩
    · exact ⟨a, 0, ha, ht, smul_zero _⟩
#align set.zero_mem_smul_iff Set.zero_mem_smul_iff

theorem zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t :=
  by
  refine' ⟨_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha] at hb
#align set.zero_mem_smul_set_iff Set.zero_mem_smul_set_iff

end SMulWithZero

section LeftCancelSemigroup

variable [LeftCancelSemigroup α] {s t : Set α}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem pairwise_disjoint_smul_iff :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t).InjOn fun p => p.1 * p.2 :=
  pairwise_disjoint_image_right_iff fun _ _ => mul_right_injective _
#align set.pairwise_disjoint_smul_iff Set.pairwise_disjoint_smul_iff

end LeftCancelSemigroup

section Group

variable [Group α] [MulAction α β] {s t A B : Set β} {a : α} {x : β}

@[simp, to_additive]
theorem smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s :=
  (MulAction.injective _).mem_set_image
#align set.smul_mem_smul_set_iff Set.smul_mem_smul_set_iff

@[to_additive]
theorem mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show x ∈ MulAction.toPerm a '' A ↔ _ from mem_image_equiv
#align set.mem_smul_set_iff_inv_smul_mem Set.mem_smul_set_iff_inv_smul_mem

@[to_additive]
theorem mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A := by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]
#align set.mem_inv_smul_set_iff Set.mem_inv_smul_set_iff

@[to_additive]
theorem preimage_smul (a : α) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).symm.image_eq_preimage _).symm
#align set.preimage_smul Set.preimage_smul

@[to_additive]
theorem preimage_smul_inv (a : α) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (toUnits a)⁻¹ t
#align set.preimage_smul_inv Set.preimage_smul_inv

@[simp, to_additive]
theorem set_smul_subset_set_smul_iff : a • A ⊆ a • B ↔ A ⊆ B :=
  image_subset_image_iff <| MulAction.injective _
#align set.set_smul_subset_set_smul_iff Set.set_smul_subset_set_smul_iff

@[to_additive]
theorem set_smul_subset_iff : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  image_subset_iff.trans <|
    iff_of_eq <| congr_arg _ <| preimage_equiv_eq_image_symm _ <| MulAction.toPerm _
#align set.set_smul_subset_iff Set.set_smul_subset_iff

@[to_additive]
theorem subset_set_smul_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  Iff.symm <|
    image_subset_iff.trans <|
      Iff.symm <| iff_of_eq <| congr_arg _ <| image_equiv_eq_preimage_symm _ <| MulAction.toPerm _
#align set.subset_set_smul_iff Set.subset_set_smul_iff

@[to_additive]
theorem smul_set_inter : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter <| MulAction.injective a
#align set.smul_set_inter Set.smul_set_inter

@[to_additive]
theorem smul_set_sdiff : a • (s \ t) = a • s \ a • t :=
  image_diff (MulAction.injective a) _ _
#align set.smul_set_sdiff Set.smul_set_sdiff

@[to_additive]
theorem smul_set_symm_diff : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symm_diff (MulAction.injective a) _ _
#align set.smul_set_symm_diff Set.smul_set_symm_diff

@[simp, to_additive]
theorem smul_set_univ : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective a
#align set.smul_set_univ Set.smul_set_univ

@[simp, to_additive]
theorem smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set β) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul _ _⟩
#align set.smul_univ Set.smul_univ

@[to_additive]
theorem smul_inter_ne_empty_iff {s t : Set α} {x : α} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x :=
  by
  rw [← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩
#align set.smul_inter_ne_empty_iff Set.smul_inter_ne_empty_iff

@[to_additive]
theorem smul_inter_ne_empty_iff' {s t : Set α} {x : α} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x := by
  simp_rw [smul_inter_ne_empty_iff, div_eq_mul_inv]
#align set.smul_inter_ne_empty_iff' Set.smul_inter_ne_empty_iff'

@[to_additive]
theorem op_smul_inter_ne_empty_iff {s t : Set α} {x : αᵐᵒᵖ} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = MulOpposite.unop x :=
  by
  rw [← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, H⟩
    have : MulOpposite.op (a⁻¹ * b) = x := congr_arg MulOpposite.op H
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩
#align set.op_smul_inter_ne_empty_iff Set.op_smul_inter_ne_empty_iff

@[simp, to_additive]
theorem Union_inv_smul : (⋃ g : α, g⁻¹ • s) = ⋃ g : α, g • s :=
  (Function.Surjective.supᵢ_congr _ inv_surjective) fun g => rfl
#align set.Union_inv_smul Set.Union_inv_smul

@[to_additive]
theorem Union_smul_eq_set_of_exists {s : Set β} : (⋃ g : α, g • s) = { a | ∃ g : α, g • a ∈ s } :=
  by simp_rw [← Union_set_of, ← Union_inv_smul, ← preimage_smul, preimage]
#align set.Union_smul_eq_set_of_exists Set.Union_smul_eq_set_of_exists

end Group

section GroupWithZero

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

@[simp]
theorem smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : a • x ∈ a • A ↔ x ∈ A :=
  show Units.mk0 a ha • _ ∈ _ ↔ _ from smul_mem_smul_set_iff
#align set.smul_mem_smul_set_iff₀ Set.smul_mem_smul_set_iff₀

theorem mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show _ ∈ Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem
#align set.mem_smul_set_iff_inv_smul_mem₀ Set.mem_smul_set_iff_inv_smul_mem₀

theorem mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff
#align set.mem_inv_smul_set_iff₀ Set.mem_inv_smul_set_iff₀

theorem preimage_smul₀ (ha : a ≠ 0) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  preimage_smul (Units.mk0 a ha) t
#align set.preimage_smul₀ Set.preimage_smul₀

theorem preimage_smul_inv₀ (ha : a ≠ 0) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (Units.mk0 a ha)⁻¹ t
#align set.preimage_smul_inv₀ Set.preimage_smul_inv₀

@[simp]
theorem set_smul_subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_set_smul_iff
#align set.set_smul_subset_set_smul_iff₀ Set.set_smul_subset_set_smul_iff₀

theorem set_smul_subset_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_iff
#align set.set_smul_subset_iff₀ Set.set_smul_subset_iff₀

theorem subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_set_smul_iff
#align set.subset_set_smul_iff₀ Set.subset_set_smul_iff₀

theorem smul_set_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  show Units.mk0 a ha • _ = _ from smul_set_inter
#align set.smul_set_inter₀ Set.smul_set_inter₀

theorem smul_set_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t :=
  image_diff (MulAction.injective₀ ha) _ _
#align set.smul_set_sdiff₀ Set.smul_set_sdiff₀

theorem smul_set_symm_diff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symm_diff (MulAction.injective₀ ha) _ _
#align set.smul_set_symm_diff₀ Set.smul_set_symm_diff₀

theorem smul_set_univ₀ (ha : a ≠ 0) : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective₀ ha
#align set.smul_set_univ₀ Set.smul_set_univ₀

theorem smul_univ₀ {s : Set α} (hs : ¬s ⊆ 0) : s • (univ : Set β) = univ :=
  let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul₀ ha₀ _⟩
#align set.smul_univ₀ Set.smul_univ₀

theorem smul_univ₀' {s : Set α} (hs : s.Nontrivial) : s • (univ : Set β) = univ :=
  smul_univ₀ hs.not_subset_singleton
#align set.smul_univ₀' Set.smul_univ₀'

end GroupWithZero

section Monoid

variable [Monoid α] [AddGroup β] [DistribMulAction α β] (a : α) (s : Set α) (t : Set β)

@[simp]
theorem smul_set_neg : a • -t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg, image_image, smul_neg]
#align set.smul_set_neg Set.smul_set_neg

@[simp]
protected theorem smul_neg : s • -t = -(s • t) :=
  by
  simp_rw [← image_neg]
  exact image_image2_right_comm smul_neg
#align set.smul_neg Set.smul_neg

end Monoid

section Ring

variable [Ring α] [AddCommGroup β] [Module α β] (a : α) (s : Set α) (t : Set β)

@[simp]
theorem neg_smul_set : -a • t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg, image_image, neg_smul]
#align set.neg_smul_set Set.neg_smul_set

@[simp]
protected theorem neg_smul : -s • t = -(s • t) :=
  by
  simp_rw [← image_neg]
  exact image2_image_left_comm neg_smul
#align set.neg_smul Set.neg_smul

end Ring

end Set

