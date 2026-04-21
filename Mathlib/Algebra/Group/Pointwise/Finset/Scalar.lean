/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.NAry
public import Mathlib.Algebra.Group.Pointwise.Set.Finite

/-!
# Pointwise operations of finsets

This file defines pointwise algebraic operations on finsets.

## Main declarations

For finsets `s` and `t`:

* `s +ᵥ t` (`Finset.vadd`): Scalar addition, finset of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s • t` (`Finset.smul`): Scalar multiplication, finset of all `x • y` where `x ∈ s` and
  `y ∈ t`.
* `s -ᵥ t` (`Finset.vsub`): Scalar subtraction, finset of all `x -ᵥ y` where `x ∈ s` and
  `y ∈ t`.
* `a • s` (`Finset.smulFinset`): Scaling, finset of all `a • x` where `x ∈ s`.
* `a +ᵥ s` (`Finset.vaddFinset`): Translation, finset of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `Finset α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

## Implementation notes

We put all instances in the scope `Pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the scope to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`).

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists Cardinal Finset.dens MonoidWithZero MulAction IsOrderedMonoid

open Function MulOpposite

open scoped Pointwise

variable {F α β γ : Type*}

namespace Finset

open Pointwise

/-! ### Scalar addition/multiplication of finsets -/

section SMul
variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

/-- The pointwise product of two finsets `s` and `t`: `s • t = {x • y | x ∈ s, y ∈ t}`. -/
@[to_additive (attr := implicit_reducible)
/-- The pointwise sum of two finsets `s` and `t`: `s +ᵥ t = {x +ᵥ y | x ∈ s, y ∈ t}`. -/]
protected def smul : SMul (Finset α) (Finset β) := ⟨image₂ (· • ·)⟩

scoped[Pointwise] attribute [instance] Finset.smul Finset.vadd

@[to_additive] lemma smul_def : s • t = (s ×ˢ t).image fun p : α × β => p.1 • p.2 := rfl

@[to_additive]
lemma image_smul_product : ((s ×ˢ t).image fun x : α × β => x.fst • x.snd) = s • t := rfl

@[to_additive] lemma mem_smul {x : β} : x ∈ s • t ↔ ∃ y ∈ s, ∃ z ∈ t, y • z = x := mem_image₂

@[to_additive (attr := simp, norm_cast)]
lemma coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s : Set α) • (t : Set β) := coe_image₂ ..

@[to_additive] lemma smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t := mem_image₂_of_mem

@[to_additive] lemma card_smul_le : #(s • t) ≤ #s * #t := card_image₂_le ..

@[to_additive (attr := simp)]
lemma empty_smul (t : Finset β) : (∅ : Finset α) • t = ∅ := image₂_empty_left

@[to_additive (attr := simp)]
lemma smul_empty (s : Finset α) : s • (∅ : Finset β) = ∅ := image₂_empty_right

@[to_additive (attr := simp)]
lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff

@[to_additive (attr := simp)]
lemma smul_nonempty_iff : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
lemma Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty := .image₂

@[to_additive] lemma Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty := .of_image₂_left
@[to_additive] lemma Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty := .of_image₂_right

@[to_additive]
lemma smul_singleton (b : β) : s • ({b} : Finset β) = s.image (· • b) := image₂_singleton_right

@[to_additive]
lemma singleton_smul_singleton (a : α) (b : β) : ({a} : Finset α) • ({b} : Finset β) = {a • b} :=
  image₂_singleton

@[to_additive (attr := mono, gcongr)]
lemma smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image₂_subset

@[to_additive] lemma smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ := image₂_subset_left
@[to_additive] lemma smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t := image₂_subset_right
@[to_additive] lemma smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u := image₂_subset_iff

@[to_additive]
lemma union_smul [DecidableEq α] : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t := image₂_union_left

@[to_additive]
lemma smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ := image₂_union_right

@[to_additive]
lemma inter_smul_subset [DecidableEq α] : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image₂_inter_subset_left

@[to_additive]
lemma smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ := image₂_inter_subset_right

@[to_additive]
lemma inter_smul_union_subset_union [DecidableEq α] : (s₁ ∩ s₂) • (t₁ ∪ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image₂_inter_union_subset_union

@[to_additive]
lemma union_smul_inter_subset_union [DecidableEq α] : (s₁ ∪ s₂) • (t₁ ∩ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image₂_union_inter_subset_union

/-- If a finset `u` is contained in the scalar product of two sets `s • t`, we can find two finsets
`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' • t'`. -/
@[to_additive
/-- If a finset `u` is contained in the scalar sum of two sets `s +ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' +ᵥ t'`. -/]
lemma subset_smul {s : Set α} {t : Set β} :
    ↑u ⊆ s • t → ∃ (s' : Finset α) (t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' • t' :=
  subset_set_image₂

end SMul

/-! ### Translation/scaling of finsets -/

section SMul
variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

/-- The scaling of a finset `s` by a scalar `a`: `a • s = {a • x | x ∈ s}`. -/
@[to_additive (attr := implicit_reducible)
  /-- The translation of a finset `s` by a vector `a`: `a +ᵥ s = {a +ᵥ x | x ∈ s}`. -/]
protected def smulFinset : SMul α (Finset β) where smul a := image <| (a • ·)

scoped[Pointwise] attribute [instance] Finset.smulFinset Finset.vaddFinset

@[to_additive] lemma smul_finset_def : a • s = s.image (a • ·) := rfl

@[to_additive] lemma image_smul : s.image (a • ·) = a • s := rfl

@[to_additive]
lemma mem_smul_finset {x : β} : x ∈ a • s ↔ ∃ y, y ∈ s ∧ a • y = x := by
  simp only [Finset.smul_finset_def, mem_image]

@[to_additive (attr := simp, norm_cast)]
lemma coe_smul_finset (a : α) (s : Finset β) : ↑(a • s) = a • (↑s : Set β) := coe_image

@[to_additive] lemma smul_mem_smul_finset : b ∈ s → a • b ∈ a • s := mem_image_of_mem _

@[to_additive] lemma card_smul_finset_le : #(a • s) ≤ #s := card_image_le
@[deprecated (since := "2026-04-16")] alias smul_finset_card_le := card_smul_finset_le
@[deprecated (since := "2026-04-16")] alias vadd_finset_card_le := card_vadd_finset_le

@[to_additive (attr := simp)]
lemma smul_finset_empty (a : α) : a • (∅ : Finset β) = ∅ := rfl

@[to_additive (attr := simp)]
lemma smul_finset_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty

@[to_additive (attr := simp)]
lemma smul_finset_nonempty : (a • s).Nonempty ↔ s.Nonempty := image_nonempty

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
lemma Nonempty.smul_finset (hs : s.Nonempty) : (a • s).Nonempty :=
  hs.image _

@[to_additive (attr := simp)]
lemma singleton_smul (a : α) : ({a} : Finset α) • t = a • t := image₂_singleton_left

@[to_additive (attr := mono, gcongr)]
lemma smul_finset_subset_smul_finset : s ⊆ t → a • s ⊆ a • t := image_subset_image

@[to_additive (attr := simp)]
lemma smul_finset_singleton (b : β) : a • ({b} : Finset β) = {a • b} := image_singleton ..

@[to_additive]
lemma smul_finset_union : a • (s₁ ∪ s₂) = a • s₁ ∪ a • s₂ := image_union _ _

@[to_additive]
lemma smul_finset_insert (a : α) (b : β) (s : Finset β) : a • insert b s = insert (a • b) (a • s) :=
  image_insert ..

@[to_additive]
lemma smul_finset_inter_subset : a • (s₁ ∩ s₂) ⊆ a • s₁ ∩ a • s₂ := image_inter_subset _ _ _

@[to_additive]
lemma smul_finset_subset_smul {s : Finset α} : a ∈ s → a • t ⊆ s • t := image_subset_image₂_right

@[to_additive (attr := simp)]
lemma biUnion_smul_finset (s : Finset α) (t : Finset β) : s.biUnion (· • t) = s • t :=
  biUnion_image_left

end SMul

open scoped Pointwise

/-! ### Instances -/

open Pointwise

/-! ### Scalar subtraction of finsets -/

section VSub

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

/-- The pointwise subtraction of two finsets `s` and `t`: `s -ᵥ t = {x -ᵥ y | x ∈ s, y ∈ t}`. -/
@[instance_reducible]
protected def vsub : VSub (Finset α) (Finset β) :=
  ⟨image₂ (· -ᵥ ·)⟩

scoped[Pointwise] attribute [instance] Finset.vsub

theorem vsub_def : s -ᵥ t = image₂ (· -ᵥ ·) s t :=
  rfl

@[simp]
theorem image_vsub_product : image₂ (· -ᵥ ·) s t = s -ᵥ t :=
  rfl

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ b ∈ s, ∃ c ∈ t, b -ᵥ c = a :=
  mem_image₂

@[simp, norm_cast]
theorem coe_vsub (s t : Finset β) : (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t :=
  coe_image₂ _ _ _

theorem vsub_mem_vsub : b ∈ s → c ∈ t → b -ᵥ c ∈ s -ᵥ t :=
  mem_image₂_of_mem

theorem vsub_card_le : #(s -ᵥ t : Finset α) ≤ #s * #t :=
  card_image₂_le _ _ _

@[simp]
theorem empty_vsub (t : Finset β) : (∅ : Finset β) -ᵥ t = ∅ :=
  image₂_empty_left

@[simp]
theorem vsub_empty (s : Finset β) : s -ᵥ (∅ : Finset β) = ∅ :=
  image₂_empty_right

@[simp]
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[simp]
theorem vsub_nonempty : (s -ᵥ t : Finset α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Finset α).Nonempty :=
  Nonempty.image₂

theorem Nonempty.of_vsub_left : (s -ᵥ t : Finset α).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left

theorem Nonempty.of_vsub_right : (s -ᵥ t : Finset α).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right

@[simp]
theorem vsub_singleton (b : β) : s -ᵥ ({b} : Finset β) = s.image (· -ᵥ b) :=
  image₂_singleton_right

theorem singleton_vsub (a : β) : ({a} : Finset β) -ᵥ t = t.image (a -ᵥ ·) :=
  image₂_singleton_left

theorem singleton_vsub_singleton (a b : β) : ({a} : Finset β) -ᵥ {b} = {a -ᵥ b} :=
  image₂_singleton

@[mono, gcongr]
theorem vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image₂_subset

theorem vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image₂_subset_left

theorem vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image₂_subset_right

theorem vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x -ᵥ y ∈ u :=
  image₂_subset_iff

section

variable [DecidableEq β]

theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image₂_union_left

theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image₂_union_right

theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image₂_inter_subset_left

theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image₂_inter_subset_right

end

/-- If a finset `u` is contained in the pointwise subtraction of two sets `s -ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' -ᵥ t'`. -/
theorem subset_vsub {s t : Set β} :
    ↑u ⊆ s -ᵥ t → ∃ s' t' : Finset β, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' -ᵥ t' :=
  subset_set_image₂

end VSub

section SMul

variable [DecidableEq β] [DecidableEq γ] [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

-- TODO: replace hypothesis and conclusion with a typeclass
@[to_additive]
theorem op_smul_finset_smul_eq_smul_smul_finset (a : α) (s : Finset β) (t : Finset γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext
  simp [mem_smul, mem_smul_finset, h]

end SMul

@[to_additive]
theorem image_smul_comm [DecidableEq β] [DecidableEq γ] [SMul α β] [SMul α γ] (f : β → γ) (a : α)
    (s : Finset β) : (∀ b, f (a • b) = a • f b) → (a • s).image f = a • s.image f :=
  image_comm

end Finset

open Pointwise

namespace Set

section SMul

variable [SMul α β] [DecidableEq β] {s : Set α} {t : Set β}

@[to_additive (attr := simp)]
theorem toFinset_smul (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s • t)] :
    (s • t).toFinset = s.toFinset • t.toFinset :=
  toFinset_image2 _ _ _

@[to_additive]
theorem Finite.toFinset_smul (hs : s.Finite) (ht : t.Finite) (hf := hs.smul ht) :
    hf.toFinset = hs.toFinset • ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end SMul

section SMul

variable [DecidableEq β] [SMul α β] {a : α} {s : Set β}

@[to_additive (attr := simp)]
theorem toFinset_smul_set (a : α) (s : Set β) [Fintype s] [Fintype ↑(a • s)] :
    (a • s).toFinset = a • s.toFinset :=
  toFinset_image _ _

@[to_additive]
theorem Finite.toFinset_smul_set (hs : s.Finite) (hf : (a • s).Finite := hs.smul_set) :
    hf.toFinset = a • hs.toFinset :=
  Finite.toFinset_image _ _ _

end SMul

section VSub

variable [DecidableEq α] [VSub α β] {s t : Set β}

@[simp]
theorem toFinset_vsub (s t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s -ᵥ t)] :
    (s -ᵥ t : Set α).toFinset = s.toFinset -ᵥ t.toFinset :=
  toFinset_image2 _ _ _

theorem Finite.toFinset_vsub (hs : s.Finite) (ht : t.Finite) (hf := hs.vsub ht) :
    hf.toFinset = hs.toFinset -ᵥ ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end VSub

end Set
