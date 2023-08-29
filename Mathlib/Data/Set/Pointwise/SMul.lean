/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Set.Pairwise.Lattice
import Mathlib.Data.Set.Pointwise.Basic

#align_import data.set.pointwise.smul from "leanprover-community/mathlib"@"5e526d18cea33550268dcbbddcb822d5cde40654"

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
#align set.has_smul_set Set.smulSet
#align set.has_vadd_set Set.vaddSet

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
locale `Pointwise`. -/
@[to_additive
      "The pointwise scalar addition of sets `s +ᵥ t` is defined as
      `{x +ᵥ y | x ∈ s, y ∈ t}` in locale `Pointwise`."]
protected def smul [SMul α β] : SMul (Set α) (Set β) :=
  ⟨image2 (· • ·)⟩
#align set.has_smul Set.smul
#align set.has_vadd Set.vadd

scoped[Pointwise] attribute [instance] Set.smulSet Set.smul

scoped[Pointwise] attribute [instance] Set.vaddSet Set.vadd

section SMul

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

/- Porting note: Could `@[simp, to_additive]` be automatically changed to
`@[to_additive (attr := simp)]`?
-/
@[to_additive (attr := simp)]
theorem image2_smul : image2 SMul.smul s t = s • t :=
  rfl
#align set.image2_smul Set.image2_smul
#align set.image2_vadd Set.image2_vadd

-- @[to_additive add_image_prod] -- Porting note: bug in mathlib3
theorem image_smul_prod : (fun x : α × β ↦ x.fst • x.snd) '' s ×ˢ t = s • t :=
  image_prod _
#align set.image_smul_prod Set.image_smul_prod

@[to_additive]
theorem mem_smul : b ∈ s • t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x • y = b :=
  Iff.rfl
#align set.mem_smul Set.mem_smul
#align set.mem_vadd Set.mem_vadd

@[to_additive]
theorem smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t :=
  mem_image2_of_mem
#align set.smul_mem_smul Set.smul_mem_smul
#align set.vadd_mem_vadd Set.vadd_mem_vadd

@[to_additive (attr := simp)]
theorem empty_smul : (∅ : Set α) • t = ∅ :=
  image2_empty_left
#align set.empty_smul Set.empty_smul
#align set.empty_vadd Set.empty_vadd

@[to_additive (attr := simp)]
theorem smul_empty : s • (∅ : Set β) = ∅ :=
  image2_empty_right
#align set.smul_empty Set.smul_empty
#align set.vadd_empty Set.vadd_empty

@[to_additive (attr := simp)]
theorem smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.smul_eq_empty Set.smul_eq_empty
#align set.vadd_eq_empty Set.vadd_eq_empty

@[to_additive (attr := simp)]
theorem smul_nonempty : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.smul_nonempty Set.smul_nonempty
#align set.vadd_nonempty Set.vadd_nonempty

@[to_additive]
theorem Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty :=
  Nonempty.image2
#align set.nonempty.smul Set.Nonempty.smul
#align set.nonempty.vadd Set.Nonempty.vadd

@[to_additive]
theorem Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_smul_left Set.Nonempty.of_smul_left
#align set.nonempty.of_vadd_left Set.Nonempty.of_vadd_left

@[to_additive]
theorem Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_smul_right Set.Nonempty.of_smul_right
#align set.nonempty.of_vadd_right Set.Nonempty.of_vadd_right

@[to_additive (attr := simp low+1)]
theorem smul_singleton : s • ({b} : Set β) = (· • b) '' s :=
  image2_singleton_right
#align set.smul_singleton Set.smul_singleton
#align set.vadd_singleton Set.vadd_singleton

@[to_additive (attr := simp low+1)]
theorem singleton_smul : ({a} : Set α) • t = a • t :=
  image2_singleton_left
#align set.singleton_smul Set.singleton_smul
#align set.singleton_vadd Set.singleton_vadd

@[to_additive (attr := simp high)]
theorem singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b} :=
  image2_singleton
#align set.singleton_smul_singleton Set.singleton_smul_singleton
#align set.singleton_vadd_singleton Set.singleton_vadd_singleton

@[to_additive (attr := mono)]
theorem smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ :=
  image2_subset
#align set.smul_subset_smul Set.smul_subset_smul
#align set.vadd_subset_vadd Set.vadd_subset_vadd

@[to_additive]
theorem smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ :=
  image2_subset_left
#align set.smul_subset_smul_left Set.smul_subset_smul_left
#align set.vadd_subset_vadd_left Set.vadd_subset_vadd_left

@[to_additive]
theorem smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t :=
  image2_subset_right
#align set.smul_subset_smul_right Set.smul_subset_smul_right
#align set.vadd_subset_vadd_right Set.vadd_subset_vadd_right

@[to_additive]
theorem smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u :=
  image2_subset_iff
#align set.smul_subset_iff Set.smul_subset_iff
#align set.vadd_subset_iff Set.vadd_subset_iff


@[to_additive]
theorem union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
  image2_union_left
#align set.union_smul Set.union_smul
#align set.union_vadd Set.union_vadd

@[to_additive]
theorem smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ :=
  image2_union_right
#align set.smul_union Set.smul_union
#align set.vadd_union Set.vadd_union

@[to_additive]
theorem inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image2_inter_subset_left
#align set.inter_smul_subset Set.inter_smul_subset
#align set.inter_vadd_subset Set.inter_vadd_subset

@[to_additive]
theorem smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
  image2_inter_subset_right
#align set.smul_inter_subset Set.smul_inter_subset
#align set.vadd_inter_subset Set.vadd_inter_subset

@[to_additive]
theorem inter_smul_union_subset_union : (s₁ ∩ s₂) • (t₁ ∪ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image2_inter_union_subset_union
#align set.inter_smul_union_subset_union Set.inter_smul_union_subset_union
#align set.inter_vadd_union_subset_union Set.inter_vadd_union_subset_union

@[to_additive]
theorem union_smul_inter_subset_union : (s₁ ∪ s₂) • (t₁ ∩ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image2_union_inter_subset_union
#align set.union_smul_inter_subset_union Set.union_smul_inter_subset_union
#align set.union_vadd_inter_subset_union Set.union_vadd_inter_subset_union

@[to_additive]
theorem iUnion_smul_left_image : ⋃ a ∈ s, a • t = s • t :=
  iUnion_image_left _
#align set.Union_smul_left_image Set.iUnion_smul_left_image
#align set.Union_vadd_left_image Set.iUnion_vadd_left_image

@[to_additive]
theorem iUnion_smul_right_image : ⋃ a ∈ t, (· • a) '' s = s • t :=
  iUnion_image_right _
#align set.Union_smul_right_image Set.iUnion_smul_right_image
#align set.Union_vadd_right_image Set.iUnion_vadd_right_image

@[to_additive]
theorem iUnion_smul (s : ι → Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
  image2_iUnion_left _ _ _
#align set.Union_smul Set.iUnion_smul
#align set.Union_vadd Set.iUnion_vadd

@[to_additive]
theorem smul_iUnion (s : Set α) (t : ι → Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i :=
  image2_iUnion_right _ _ _
#align set.smul_Union Set.smul_iUnion
#align set.vadd_Union Set.vadd_iUnion

@[to_additive]
theorem iUnion₂_smul (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋃ (i) (j), s i j) • t = ⋃ (i) (j), s i j • t :=
  image2_iUnion₂_left _ _ _
#align set.Union₂_smul Set.iUnion₂_smul
#align set.Union₂_vadd Set.iUnion₂_vadd

@[to_additive]
theorem smul_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋃ (i) (j), t i j) = ⋃ (i) (j), s • t i j :=
  image2_iUnion₂_right _ _ _
#align set.smul_Union₂ Set.smul_iUnion₂
#align set.vadd_Union₂ Set.vadd_iUnion₂

@[to_additive]
theorem iInter_smul_subset (s : ι → Set α) (t : Set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
  image2_iInter_subset_left _ _ _
#align set.Inter_smul_subset Set.iInter_smul_subset
#align set.Inter_vadd_subset Set.iInter_vadd_subset

@[to_additive]
theorem smul_iInter_subset (s : Set α) (t : ι → Set β) : (s • ⋂ i, t i) ⊆ ⋂ i, s • t i :=
  image2_iInter_subset_right _ _ _
#align set.smul_Inter_subset Set.smul_iInter_subset
#align set.vadd_Inter_subset Set.vadd_iInter_subset

@[to_additive]
theorem iInter₂_smul_subset (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋂ (i) (j), s i j) • t ⊆ ⋂ (i) (j), s i j • t :=
  image2_iInter₂_subset_left _ _ _
#align set.Inter₂_smul_subset Set.iInter₂_smul_subset
#align set.Inter₂_vadd_subset Set.iInter₂_vadd_subset

@[to_additive]
theorem smul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s • t i j :=
  image2_iInter₂_subset_right _ _ _
#align set.smul_Inter₂_subset Set.smul_iInter₂_subset
#align set.vadd_Inter₂_subset Set.vadd_iInter₂_subset

@[to_additive]
theorem smul_set_subset_smul {s : Set α} : a ∈ s → a • t ⊆ s • t :=
  image_subset_image2_right
#align set.smul_set_subset_smul Set.smul_set_subset_smul
#align set.vadd_set_subset_vadd Set.vadd_set_subset_vadd

@[to_additive (attr := simp)]
theorem iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a ∈ s, a • t = s • t :=
  iUnion_image_left _
#align set.bUnion_smul_set Set.iUnion_smul_set
#align set.bUnion_vadd_set Set.iUnion_vadd_set

end SMul

section SMulSet

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

@[to_additive]
theorem image_smul : (fun x ↦ a • x) '' t = a • t :=
  rfl
#align set.image_smul Set.image_smul
#align set.image_vadd Set.image_vadd

scoped[Pointwise] attribute [simp] Set.image_smul Set.image_vadd

@[to_additive]
theorem mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x :=
  Iff.rfl
#align set.mem_smul_set Set.mem_smul_set
#align set.mem_vadd_set Set.mem_vadd_set

@[to_additive]
theorem smul_mem_smul_set : b ∈ s → a • b ∈ a • s :=
  mem_image_of_mem _
#align set.smul_mem_smul_set Set.smul_mem_smul_set
#align set.vadd_mem_vadd_set Set.vadd_mem_vadd_set

@[to_additive (attr := simp)]
theorem smul_set_empty : a • (∅ : Set β) = ∅ :=
  image_empty _
#align set.smul_set_empty Set.smul_set_empty
#align set.vadd_set_empty Set.vadd_set_empty

@[to_additive (attr := simp)]
theorem smul_set_eq_empty : a • s = ∅ ↔ s = ∅ :=
  image_eq_empty
#align set.smul_set_eq_empty Set.smul_set_eq_empty
#align set.vadd_set_eq_empty Set.vadd_set_eq_empty

@[to_additive (attr := simp)]
theorem smul_set_nonempty : (a • s).Nonempty ↔ s.Nonempty :=
  nonempty_image_iff
#align set.smul_set_nonempty Set.smul_set_nonempty
#align set.vadd_set_nonempty Set.vadd_set_nonempty

@[to_additive (attr := simp)]
theorem smul_set_singleton : a • ({b} : Set β) = {a • b} :=
  image_singleton
#align set.smul_set_singleton Set.smul_set_singleton
#align set.vadd_set_singleton Set.vadd_set_singleton

@[to_additive]
theorem smul_set_mono : s ⊆ t → a • s ⊆ a • t :=
  image_subset _
#align set.smul_set_mono Set.smul_set_mono
#align set.vadd_set_mono Set.vadd_set_mono

@[to_additive]
theorem smul_set_subset_iff : a • s ⊆ t ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ t :=
  image_subset_iff
#align set.smul_set_subset_iff Set.smul_set_subset_iff
#align set.vadd_set_subset_iff Set.vadd_set_subset_iff

@[to_additive]
theorem smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ :=
  image_union _ _ _
#align set.smul_set_union Set.smul_set_union
#align set.vadd_set_union Set.vadd_set_union

@[to_additive]
theorem smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ a • t₂ :=
  image_inter_subset _ _ _
#align set.smul_set_inter_subset Set.smul_set_inter_subset
#align set.vadd_set_inter_subset Set.vadd_set_inter_subset

@[to_additive]
theorem smul_set_Union (a : α) (s : ι → Set β) : (a • ⋃ i, s i) = ⋃ i, a • s i :=
  image_iUnion
#align set.smul_set_Union Set.smul_set_Union
#align set.vadd_set_Union Set.vadd_set_Union

@[to_additive]
theorem smul_set_iUnion₂ (a : α) (s : ∀ i, κ i → Set β) :
    (a • ⋃ (i) (j), s i j) = ⋃ (i) (j), a • s i j :=
  image_iUnion₂ _ _
#align set.smul_set_Union₂ Set.smul_set_iUnion₂
#align set.vadd_set_Union₂ Set.vadd_set_iUnion₂

@[to_additive]
theorem smul_set_iInter_subset (a : α) (t : ι → Set β) : (a • ⋂ i, t i) ⊆ ⋂ i, a • t i :=
  image_iInter_subset _ _
#align set.smul_set_Inter_subset Set.smul_set_iInter_subset
#align set.vadd_set_Inter_subset Set.vadd_set_iInter_subset

@[to_additive]
theorem smul_set_iInter₂_subset (a : α) (t : ∀ i, κ i → Set β) :
    (a • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), a • t i j :=
  image_iInter₂_subset _ _
#align set.smul_set_Inter₂_subset Set.smul_set_iInter₂_subset
#align set.vadd_set_Inter₂_subset Set.vadd_set_iInter₂_subset

@[to_additive]
theorem Nonempty.smul_set : s.Nonempty → (a • s).Nonempty :=
  Nonempty.image _
#align set.nonempty.smul_set Set.Nonempty.smul_set
#align set.nonempty.vadd_set Set.Nonempty.vadd_set

end SMulSet

section Mul

variable [Mul α] {s t u : Set α} {a : α}

@[to_additive]
theorem op_smul_set_subset_mul : a ∈ t → op a • s ⊆ s * t :=
  image_subset_image2_left
#align set.op_smul_set_subset_mul Set.op_smul_set_subset_mul
#align set.op_vadd_set_subset_add Set.op_vadd_set_subset_add

@[to_additive]
theorem image_op_smul : (op '' s) • t = t * s := by
  rw [← image2_smul, ← image2_mul, image2_image_left, image2_swap]
  -- ⊢ image2 (fun a b => SMul.smul (op b) a) t s = image2 (fun x x_1 => x * x_1) t s
  rfl
  -- 🎉 no goals

@[to_additive (attr := simp)]
theorem iUnion_op_smul_set (s t : Set α) : ⋃ a ∈ t, MulOpposite.op a • s = s * t :=
  iUnion_image_right _
#align set.bUnion_op_smul_set Set.iUnion_op_smul_set
#align set.bUnion_op_vadd_set Set.iUnion_op_vadd_set

@[to_additive]
theorem mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u :=
  image2_subset_iff_left
#align set.mul_subset_iff_left Set.mul_subset_iff_left
#align set.add_subset_iff_left Set.add_subset_iff_left

@[to_additive]
theorem mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
  image2_subset_iff_right
#align set.mul_subset_iff_right Set.mul_subset_iff_right
#align set.add_subset_iff_right Set.add_subset_iff_right

end Mul

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

@[to_additive]
theorem range_smul_range {ι κ : Type*} [SMul α β] (b : ι → α) (c : κ → β) :
    range b • range c = range fun p : ι × κ ↦ b p.1 • c p.2 :=
  ext fun _x ↦
    ⟨fun hx ↦
      let ⟨_p, _q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := Set.mem_smul.1 hx
      ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
      fun ⟨⟨i, j⟩, h⟩ ↦ Set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩
#align set.range_smul_range Set.range_smul_range
#align set.range_vadd_range Set.range_vadd_range

@[to_additive]
theorem smul_set_range [SMul α β] {ι : Sort*} {f : ι → β} :
    a • range f = range fun i ↦ a • f i :=
  (range_comp _ _).symm
#align set.smul_set_range Set.smul_set_range
#align set.vadd_set_range Set.vadd_set_range

@[to_additive]
instance smulCommClass_set [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Set γ) :=
  ⟨fun _ _ ↦ Commute.set_image <| smul_comm _ _⟩
#align set.smul_comm_class_set Set.smulCommClass_set
#align set.vadd_comm_class_set Set.vaddCommClass_set

@[to_additive]
instance smulCommClass_set' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image_image2_distrib_right <| smul_comm _⟩
#align set.smul_comm_class_set' Set.smulCommClass_set'
#align set.vadd_comm_class_set' Set.vaddCommClass_set'

@[to_additive]
instance smulCommClass_set'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) β (Set γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _
#align set.smul_comm_class_set'' Set.smulCommClass_set''
#align set.vadd_comm_class_set'' Set.vaddCommClass_set''

@[to_additive]
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image2_left_comm smul_comm⟩
#align set.smul_comm_class Set.smulCommClass
#align set.vadd_comm_class Set.vaddCommClass

@[to_additive vAddAssocClass]
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Set γ) where
  smul_assoc a b T := by simp only [← image_smul, image_image, smul_assoc]
                         -- 🎉 no goals
#align set.is_scalar_tower Set.isScalarTower
#align set.vadd_assoc_class Set.vAddAssocClass

@[to_additive vAddAssocClass']
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image2_image_left_comm <| smul_assoc _⟩
#align set.is_scalar_tower' Set.isScalarTower'
#align set.vadd_assoc_class' Set.vAddAssocClass'

@[to_additive vAddAssocClass'']
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Set α) (Set β) (Set γ) where
  smul_assoc _ _ _ := image2_assoc smul_assoc
#align set.is_scalar_tower'' Set.isScalarTower''
#align set.vadd_assoc_class'' Set.vAddAssocClass''

@[to_additive]
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Set β) :=
  ⟨fun _ S ↦ (congr_arg fun f ↦ f '' S) <| funext fun _ ↦ op_smul_eq_smul _ _⟩
#align set.is_central_scalar Set.isCentralScalar
#align set.is_central_vadd Set.isCentralVAdd

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `Set α`
on `Set β`. -/
@[to_additive
      "An additive action of an additive monoid `α` on a type `β` gives an additive action of
      `Set α` on `Set β`"]
protected def mulAction [Monoid α] [MulAction α β] : MulAction (Set α) (Set β) where
  mul_smul _ _ _ := image2_assoc mul_smul
  one_smul s := image2_singleton_left.trans <| by simp_rw [one_smul, image_id']
                                                  -- 🎉 no goals
#align set.mul_action Set.mulAction
#align set.add_action Set.addAction

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `Set β`. -/
@[to_additive
      "An additive action of an additive monoid on a type `β` gives an additive action on `Set β`."]
protected def mulActionSet [Monoid α] [MulAction α β] : MulAction α (Set β) where
  mul_smul := by
    intros
    -- ⊢ (x✝ * y✝) • b✝ = x✝ • y✝ • b✝
    simp only [← image_smul, image_image, ← mul_smul]
    -- 🎉 no goals
    -- ⊢ 1 • b✝ = b✝
  one_smul := by
    -- 🎉 no goals
    intros
    simp only [← image_smul, one_smul, image_id']
#align set.mul_action_set Set.mulActionSet
#align set.add_action_set Set.addActionSet

scoped[Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `Set β`. -/
protected def distribMulActionSet [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Set β) where
  smul_add _ _ _ := image_image2_distrib <| smul_add _
  smul_zero _ := image_singleton.trans <| by rw [smul_zero, singleton_zero]
                                             -- 🎉 no goals
#align set.distrib_mul_action_set Set.distribMulActionSet

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `Set β`. -/
protected def mulDistribMulActionSet [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Set β) where
  smul_mul _ _ _ := image_image2_distrib <| smul_mul' _
  smul_one _ := image_singleton.trans <| by rw [smul_one, singleton_one]
                                            -- 🎉 no goals
#align set.mul_distrib_mul_action_set Set.mulDistribMulActionSet

scoped[Pointwise] attribute [instance] Set.distribMulActionSet Set.mulDistribMulActionSet

instance [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors (Set α) (Set β) :=
  ⟨fun {s t} h ↦ by
    by_contra' H
    -- ⊢ False
    have hst : (s • t).Nonempty := h.symm.subst zero_nonempty
    -- ⊢ False
    rw [Ne.def, ← hst.of_smul_left.subset_zero_iff, Ne.def,
      ← hst.of_smul_right.subset_zero_iff] at H
    simp only [not_subset, mem_zero] at H
    -- ⊢ False
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    -- ⊢ False
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul hs ht).elim ha hb⟩
    -- 🎉 no goals

instance noZeroSMulDivisors_set [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors α (Set β) :=
  ⟨fun {a s} h ↦ by
    by_contra' H
    -- ⊢ False
    have hst : (a • s).Nonempty := h.symm.subst zero_nonempty
    -- ⊢ False
    rw [Ne.def, Ne.def, ← hst.of_image.subset_zero_iff, not_subset] at H
    -- ⊢ False
    obtain ⟨ha, b, ht, hb⟩ := H
    -- ⊢ False
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul_set ht).elim ha hb⟩
    -- 🎉 no goals
#align set.no_zero_smul_divisors_set Set.noZeroSMulDivisors_set

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Set α) :=
  ⟨fun h ↦ eq_zero_or_eq_zero_of_smul_eq_zero h⟩

end SMul

section VSub

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

instance vsub : VSub (Set α) (Set β) :=
  ⟨image2 (· -ᵥ ·)⟩
#align set.has_vsub Set.vsub

@[simp]
theorem image2_vsub : (image2 VSub.vsub s t : Set α) = s -ᵥ t :=
  rfl
#align set.image2_vsub Set.image2_vsub

theorem image_vsub_prod : (fun x : β × β ↦ x.fst -ᵥ x.snd) '' s ×ˢ t = s -ᵥ t :=
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
  Nonempty.image2
#align set.nonempty.vsub Set.Nonempty.vsub

theorem Nonempty.of_vsub_left : (s -ᵥ t : Set α).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_vsub_left Set.Nonempty.of_vsub_left

theorem Nonempty.of_vsub_right : (s -ᵥ t : Set α).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_vsub_right Set.Nonempty.of_vsub_right

@[simp low+1]
theorem vsub_singleton (s : Set β) (b : β) : s -ᵥ {b} = (· -ᵥ b) '' s :=
  image2_singleton_right
#align set.vsub_singleton Set.vsub_singleton

@[simp low+1]
theorem singleton_vsub (t : Set β) (b : β) : {b} -ᵥ t = (· -ᵥ ·) b '' t :=
  image2_singleton_left
#align set.singleton_vsub Set.singleton_vsub

@[simp high]
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

theorem inter_vsub_union_subset_union : s₁ ∩ s₂ -ᵥ (t₁ ∪ t₂) ⊆ s₁ -ᵥ t₁ ∪ (s₂ -ᵥ t₂) :=
  image2_inter_union_subset_union
#align set.inter_vsub_union_subset_union Set.inter_vsub_union_subset_union

theorem union_vsub_inter_subset_union : s₁ ∪ s₂ -ᵥ t₁ ∩ t₂ ⊆ s₁ -ᵥ t₁ ∪ (s₂ -ᵥ t₂) :=
  image2_union_inter_subset_union
#align set.union_vsub_inter_subset_union Set.union_vsub_inter_subset_union

theorem iUnion_vsub_left_image : ⋃ a ∈ s, (· -ᵥ ·) a '' t = s -ᵥ t :=
  iUnion_image_left _
#align set.Union_vsub_left_image Set.iUnion_vsub_left_image

theorem iUnion_vsub_right_image : ⋃ a ∈ t, (· -ᵥ a) '' s = s -ᵥ t :=
  iUnion_image_right _
#align set.Union_vsub_right_image Set.iUnion_vsub_right_image

theorem iUnion_vsub (s : ι → Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
  image2_iUnion_left _ _ _
#align set.Union_vsub Set.iUnion_vsub

theorem vsub_iUnion (s : Set β) (t : ι → Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i :=
  image2_iUnion_right _ _ _
#align set.vsub_Union Set.vsub_iUnion

theorem iUnion₂_vsub (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋃ (i) (j), s i j) -ᵥ t = ⋃ (i) (j), s i j -ᵥ t :=
  image2_iUnion₂_left _ _ _
#align set.Union₂_vsub Set.iUnion₂_vsub

theorem vsub_iUnion₂ (s : Set β) (t : ∀ i, κ i → Set β) :
    (s -ᵥ ⋃ (i) (j), t i j) = ⋃ (i) (j), s -ᵥ t i j :=
  image2_iUnion₂_right _ _ _
#align set.vsub_Union₂ Set.vsub_iUnion₂

theorem iInter_vsub_subset (s : ι → Set β) (t : Set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
  image2_iInter_subset_left _ _ _
#align set.Inter_vsub_subset Set.iInter_vsub_subset

theorem vsub_iInter_subset (s : Set β) (t : ι → Set β) : (s -ᵥ ⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
  image2_iInter_subset_right _ _ _
#align set.vsub_Inter_subset Set.vsub_iInter_subset

theorem iInter₂_vsub_subset (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋂ (i) (j), s i j) -ᵥ t ⊆ ⋂ (i) (j), s i j -ᵥ t :=
  image2_iInter₂_subset_left _ _ _
#align set.Inter₂_vsub_subset Set.iInter₂_vsub_subset

theorem vsub_iInter₂_subset (s : Set β) (t : ∀ i, κ i → Set β) :
    (s -ᵥ ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s -ᵥ t i j :=
  image2_iInter₂_subset_right _ _ _
#align set.vsub_Inter₂_subset Set.vsub_iInter₂_subset

end VSub

open Pointwise

@[to_additive]
theorem image_smul_comm [SMul α β] [SMul α γ] (f : β → γ) (a : α) (s : Set β) :
    (∀ b, f (a • b) = a • f b) → f '' (a • s) = a • f '' s :=
  image_comm
#align set.image_smul_comm Set.image_smul_comm
#align set.image_vadd_comm Set.image_vadd_comm

@[to_additive]
theorem image_smul_distrib [MulOneClass α] [MulOneClass β] [MonoidHomClass F α β] (f : F) (a : α)
    (s : Set α) : f '' (a • s) = f a • f '' s :=
  image_comm <| map_mul _ _
#align set.image_smul_distrib Set.image_smul_distrib
#align set.image_vadd_distrib Set.image_vadd_distrib

section SMul

variable [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

-- TODO: replace hypothesis and conclusion with a typeclass
@[to_additive]
theorem op_smul_set_smul_eq_smul_smul_set (a : α) (s : Set β) (t : Set γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext
  -- ⊢ x✝ ∈ (op a • s) • t ↔ x✝ ∈ s • a • t
  simp [mem_smul, mem_smul_set, h]
  -- 🎉 no goals
#align set.op_smul_set_smul_eq_smul_smul_set Set.op_smul_set_smul_eq_smul_smul_set
#align set.op_vadd_set_vadd_eq_vadd_vadd_set Set.op_vadd_set_vadd_eq_vadd_vadd_set

end SMul

section SMulWithZero

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

/-!
Note that we have neither `SMulWithZero α (Set β)` nor `SMulWithZero (Set α) (Set β)`
because `0 * ∅ ≠ 0`.
-/


theorem smul_zero_subset (s : Set α) : s • (0 : Set β) ⊆ 0 := by simp [subset_def, mem_smul]
                                                                 -- 🎉 no goals
#align set.smul_zero_subset Set.smul_zero_subset

theorem zero_smul_subset (t : Set β) : (0 : Set α) • t ⊆ 0 := by simp [subset_def, mem_smul]
                                                                 -- 🎉 no goals
#align set.zero_smul_subset Set.zero_smul_subset

theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using hs
                                    -- 🎉 no goals
#align set.nonempty.smul_zero Set.Nonempty.smul_zero

theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using ht
                                    -- 🎉 no goals
#align set.nonempty.zero_smul Set.Nonempty.zero_smul

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
theorem zero_smul_set {s : Set β} (h : s.Nonempty) : (0 : α) • s = (0 : Set β) := by
  simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]
  -- 🎉 no goals
#align set.zero_smul_set Set.zero_smul_set

theorem zero_smul_set_subset (s : Set β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ ↦ zero_smul α x
#align set.zero_smul_set_subset Set.zero_smul_set_subset

theorem subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton :=
  subsingleton_singleton.anti <| zero_smul_set_subset s
#align set.subsingleton_zero_smul_set Set.subsingleton_zero_smul_set

theorem zero_mem_smul_set {t : Set β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
  ⟨0, h, smul_zero _⟩
#align set.zero_mem_smul_set Set.zero_mem_smul_set

variable [NoZeroSMulDivisors α β] {a : α}

theorem zero_mem_smul_iff :
    (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.Nonempty ∨ (0 : β) ∈ t ∧ s.Nonempty := by
  constructor
  -- ⊢ 0 ∈ s • t → 0 ∈ s ∧ Set.Nonempty t ∨ 0 ∈ t ∧ Set.Nonempty s
  · rintro ⟨a, b, ha, hb, h⟩
    -- ⊢ 0 ∈ s ∧ Set.Nonempty t ∨ 0 ∈ t ∧ Set.Nonempty s
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h
    -- ⊢ 0 ∈ s ∧ Set.Nonempty t ∨ 0 ∈ t ∧ Set.Nonempty s
    · exact Or.inl ⟨ha, b, hb⟩
      -- 🎉 no goals
    · exact Or.inr ⟨hb, a, ha⟩
      -- 🎉 no goals
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    -- ⊢ 0 ∈ s • t
    · exact ⟨0, b, hs, hb, zero_smul _ _⟩
      -- 🎉 no goals
    · exact ⟨a, 0, ha, ht, smul_zero _⟩
      -- 🎉 no goals
#align set.zero_mem_smul_iff Set.zero_mem_smul_iff

theorem zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t := by
  refine' ⟨_, zero_mem_smul_set⟩
  -- ⊢ 0 ∈ a • t → 0 ∈ t
  rintro ⟨b, hb, h⟩
  -- ⊢ 0 ∈ t
  rwa [(eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha] at hb
  -- 🎉 no goals
#align set.zero_mem_smul_set_iff Set.zero_mem_smul_set_iff

end SMulWithZero

section Semigroup

variable [Semigroup α]

@[to_additive]
theorem op_smul_set_mul_eq_mul_smul_set (a : α) (s : Set α) (t : Set α) :
    op a • s * t = s * a • t :=
  op_smul_set_smul_eq_smul_smul_set _ _ _ fun _ _ _ => mul_assoc _ _ _
#align set.op_smul_set_mul_eq_mul_smul_set Set.op_smul_set_mul_eq_mul_smul_set
#align set.op_vadd_set_add_eq_add_vadd_set Set.op_vadd_set_add_eq_add_vadd_set

end Semigroup

section LeftCancelSemigroup

variable [LeftCancelSemigroup α] {s t : Set α}

@[to_additive]
theorem pairwiseDisjoint_smul_iff :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t).InjOn fun p ↦ p.1 * p.2 :=
  pairwiseDisjoint_image_right_iff fun _ _ ↦ mul_right_injective _
#align set.pairwise_disjoint_smul_iff Set.pairwiseDisjoint_smul_iff
#align set.pairwise_disjoint_vadd_iff Set.pairwiseDisjoint_vadd_iff

end LeftCancelSemigroup

section Group

variable [Group α] [MulAction α β] {s t A B : Set β} {a : α} {x : β}

@[to_additive (attr := simp)]
theorem smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s :=
  (MulAction.injective _).mem_set_image
#align set.smul_mem_smul_set_iff Set.smul_mem_smul_set_iff
#align set.vadd_mem_vadd_set_iff Set.vadd_mem_vadd_set_iff

@[to_additive]
theorem mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show x ∈ MulAction.toPerm a '' A ↔ _ from mem_image_equiv
#align set.mem_smul_set_iff_inv_smul_mem Set.mem_smul_set_iff_inv_smul_mem
#align set.mem_vadd_set_iff_neg_vadd_mem Set.mem_vadd_set_iff_neg_vadd_mem

@[to_additive]
theorem mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A := by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]
  -- 🎉 no goals
#align set.mem_inv_smul_set_iff Set.mem_inv_smul_set_iff
#align set.mem_neg_vadd_set_iff Set.mem_neg_vadd_set_iff

@[to_additive]
theorem preimage_smul (a : α) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).symm.image_eq_preimage _).symm
#align set.preimage_smul Set.preimage_smul
#align set.preimage_vadd Set.preimage_vadd

@[to_additive]
theorem preimage_smul_inv (a : α) (t : Set β) : (fun x ↦ a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (toUnits a)⁻¹ t
#align set.preimage_smul_inv Set.preimage_smul_inv
#align set.preimage_vadd_neg Set.preimage_vadd_neg

@[to_additive (attr := simp)]
theorem set_smul_subset_set_smul_iff : a • A ⊆ a • B ↔ A ⊆ B :=
  image_subset_image_iff <| MulAction.injective _
#align set.set_smul_subset_set_smul_iff Set.set_smul_subset_set_smul_iff
#align set.set_vadd_subset_set_vadd_iff Set.set_vadd_subset_set_vadd_iff

@[to_additive]
theorem set_smul_subset_iff : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  image_subset_iff.trans <|
    iff_of_eq <| congr_arg _ <| preimage_equiv_eq_image_symm _ <| MulAction.toPerm _
#align set.set_smul_subset_iff Set.set_smul_subset_iff
#align set.set_vadd_subset_iff Set.set_vadd_subset_iff

@[to_additive]
theorem subset_set_smul_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  Iff.symm <|
    image_subset_iff.trans <|
      Iff.symm <| iff_of_eq <| congr_arg _ <| image_equiv_eq_preimage_symm _ <| MulAction.toPerm _
#align set.subset_set_smul_iff Set.subset_set_smul_iff
#align set.subset_set_vadd_iff Set.subset_set_vadd_iff

@[to_additive]
theorem smul_set_inter : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter <| MulAction.injective a
#align set.smul_set_inter Set.smul_set_inter
#align set.vadd_set_inter Set.vadd_set_inter

@[to_additive]
theorem smul_set_sdiff : a • (s \ t) = a • s \ a • t :=
  image_diff (MulAction.injective a) _ _
#align set.smul_set_sdiff Set.smul_set_sdiff
#align set.vadd_set_sdiff Set.vadd_set_sdiff

@[to_additive]
theorem smul_set_symmDiff : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff (MulAction.injective a) _ _
#align set.smul_set_symm_diff Set.smul_set_symmDiff
#align set.vadd_set_symm_diff Set.vadd_set_symmDiff

@[to_additive (attr := simp)]
theorem smul_set_univ : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective a
#align set.smul_set_univ Set.smul_set_univ
#align set.vadd_set_univ Set.vadd_set_univ

@[to_additive (attr := simp)]
theorem smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set β) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b ↦ ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul _ _⟩
#align set.smul_univ Set.smul_univ
#align set.vadd_univ Set.vadd_univ

@[to_additive]
theorem smul_inter_ne_empty_iff {s t : Set α} {x : α} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x := by
  rw [← nonempty_iff_ne_empty]
  -- ⊢ Set.Nonempty (x • s ∩ t) ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x
  constructor
  -- ⊢ Set.Nonempty (x • s ∩ t) → ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x
  · rintro ⟨a, h, ha⟩
    -- ⊢ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    -- ⊢ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩
    -- 🎉 no goals
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    -- ⊢ Set.Nonempty ((a * b⁻¹) • s ∩ t)
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩
    -- 🎉 no goals
#align set.smul_inter_ne_empty_iff Set.smul_inter_ne_empty_iff
#align set.vadd_inter_ne_empty_iff Set.vadd_inter_ne_empty_iff

@[to_additive]
theorem smul_inter_ne_empty_iff' {s t : Set α} {x : α} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x := by
  simp_rw [smul_inter_ne_empty_iff, div_eq_mul_inv]
  -- 🎉 no goals
#align set.smul_inter_ne_empty_iff' Set.smul_inter_ne_empty_iff'
#align set.vadd_inter_ne_empty_iff' Set.vadd_inter_ne_empty_iff'

@[to_additive]
theorem op_smul_inter_ne_empty_iff {s t : Set α} {x : αᵐᵒᵖ} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = MulOpposite.unop x := by
  rw [← nonempty_iff_ne_empty]
  -- ⊢ Set.Nonempty (x • s ∩ t) ↔ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = unop x
  constructor
  -- ⊢ Set.Nonempty (x • s ∩ t) → ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = unop x
  · rintro ⟨a, h, ha⟩
    -- ⊢ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = unop x
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    -- ⊢ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = unop x
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩
    -- 🎉 no goals
  · rintro ⟨a, b, ⟨ha, hb⟩, H⟩
    -- ⊢ Set.Nonempty (x • s ∩ t)
    have : MulOpposite.op (a⁻¹ * b) = x := congr_arg MulOpposite.op H
    -- ⊢ Set.Nonempty (x • s ∩ t)
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩
    -- 🎉 no goals
#align set.op_smul_inter_ne_empty_iff Set.op_smul_inter_ne_empty_iff
#align set.op_vadd_inter_ne_empty_iff Set.op_vadd_inter_ne_empty_iff

@[to_additive (attr := simp)]
theorem iUnion_inv_smul : ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s :=
  (Function.Surjective.iSup_congr _ inv_surjective) fun _ ↦ rfl
#align set.Union_inv_smul Set.iUnion_inv_smul
#align set.Union_neg_vadd Set.iUnion_neg_vadd

@[to_additive]
theorem iUnion_smul_eq_setOf_exists {s : Set β} : ⋃ g : α, g • s = { a | ∃ g : α, g • a ∈ s } :=
  by simp_rw [← iUnion_setOf, ← iUnion_inv_smul, ← preimage_smul, preimage]
     -- 🎉 no goals
#align set.Union_smul_eq_set_of_exists Set.iUnion_smul_eq_setOf_exists
#align set.Union_vadd_eq_set_of_exists Set.iUnion_vadd_eq_setOf_exists

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

theorem preimage_smul₀ (ha : a ≠ 0) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t :=
  preimage_smul (Units.mk0 a ha) t
#align set.preimage_smul₀ Set.preimage_smul₀

theorem preimage_smul_inv₀ (ha : a ≠ 0) (t : Set β) : (fun x ↦ a⁻¹ • x) ⁻¹' t = a • t :=
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

theorem smul_set_symmDiff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff (MulAction.injective₀ ha) _ _
#align set.smul_set_symm_diff₀ Set.smul_set_symmDiff₀

theorem smul_set_univ₀ (ha : a ≠ 0) : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective₀ ha
#align set.smul_set_univ₀ Set.smul_set_univ₀

theorem smul_univ₀ {s : Set α} (hs : ¬s ⊆ 0) : s • (univ : Set β) = univ :=
  let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b ↦ ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul₀ ha₀ _⟩
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
  -- 🎉 no goals
#align set.smul_set_neg Set.smul_set_neg

@[simp]
protected theorem smul_neg : s • -t = -(s • t) := by
  simp_rw [← image_neg]
  -- ⊢ s • Neg.neg '' t = Neg.neg '' (s • t)
  exact image_image2_right_comm smul_neg
  -- 🎉 no goals
#align set.smul_neg Set.smul_neg

end Monoid

section Semiring

variable [Semiring α] [AddCommMonoid β] [Module α β]

-- porting note: new lemma
theorem add_smul_subset (a b : α) (s : Set β) : (a + b) • s ⊆ a • s + b • s := by
  rintro _ ⟨x, hx, rfl⟩
  -- ⊢ (fun x => (a + b) • x) x ∈ a • s + b • s
  simpa only [add_smul] using add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hx)
  -- 🎉 no goals

end Semiring

section Ring

variable [Ring α] [AddCommGroup β] [Module α β] (a : α) (s : Set α) (t : Set β)

@[simp]
theorem neg_smul_set : -a • t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg, image_image, neg_smul]
  -- 🎉 no goals
#align set.neg_smul_set Set.neg_smul_set

@[simp]
protected theorem neg_smul : -s • t = -(s • t) := by
  simp_rw [← image_neg]
  -- ⊢ Neg.neg '' s • t = Neg.neg '' (s • t)
  exact image2_image_left_comm neg_smul
  -- 🎉 no goals
#align set.neg_smul Set.neg_smul

end Ring

end Set
