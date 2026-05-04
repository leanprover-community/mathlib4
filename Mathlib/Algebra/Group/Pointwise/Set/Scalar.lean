/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Data.Set.NAry
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Pointwise scalar operations of sets

This file defines pointwise scalar-flavored algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:

* `s • t`: Scalar multiplication, set of all `x • y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t`: Scalar addition, set of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s -ᵥ t`: Scalar subtraction, set of all `x -ᵥ y` where `x ∈ s` and `y ∈ t`.
* `a • s`: Scaling, set of all `a • x` where `x ∈ s`.
* `a +ᵥ s`: Translation, set of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `Set α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* The following expressions are considered in simp-normal form in a group:
  `(fun h ↦ h * g) ⁻¹' s`, `(fun h ↦ g * h) ⁻¹' s`, `(fun h ↦ h * g⁻¹) ⁻¹' s`,
  `(fun h ↦ g⁻¹ * h) ⁻¹' s`, `s * t`, `s⁻¹`, `(1 : Set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the scope `Pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the scope to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`).

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists Set.iUnion MulAction MonoidWithZero IsOrderedMonoid

open Function MulOpposite

variable {F α β γ : Type*}

namespace Set

/-! ### Translation/scaling of sets -/

section SMul

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in scope `Pointwise`. -/
@[to_additive (attr := implicit_reducible)
/-- The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in scope `Pointwise`. -/]
protected def smulSet [SMul α β] : SMul α (Set β) where smul a := image (a • ·)

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
scope `Pointwise`. -/
@[to_additive (attr := implicit_reducible)
/-- The pointwise scalar addition of sets `s +ᵥ t` is defined as `{x +ᵥ y | x ∈ s, y ∈ t}` in locale
`Pointwise`. -/]
protected def smul [SMul α β] : SMul (Set α) (Set β) where smul := image2 (· • ·)

scoped[Pointwise] attribute [instance] Set.smulSet Set.smul
scoped[Pointwise] attribute [instance] Set.vaddSet Set.vadd

open scoped Pointwise

section SMul
variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

@[to_additive (attr := simp)] lemma image2_smul : image2 (· • ·) s t = s • t := rfl

@[to_additive vadd_image_prod]
lemma image_smul_prod : (fun x : α × β ↦ x.fst • x.snd) '' s ×ˢ t = s • t := image_prod _

@[to_additive] lemma mem_smul : b ∈ s • t ↔ ∃ x ∈ s, ∃ y ∈ t, x • y = b := Iff.rfl

@[to_additive] lemma smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t := mem_image2_of_mem

@[to_additive (attr := simp)] lemma empty_smul : (∅ : Set α) • t = ∅ := image2_empty_left
@[to_additive (attr := simp)] lemma smul_empty : s • (∅ : Set β) = ∅ := image2_empty_right

@[to_additive (attr := simp)] lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff

@[to_additive (attr := simp)]
lemma smul_nonempty : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image2_nonempty_iff

@[to_additive] lemma Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty := .image2
@[to_additive] lemma Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty := .of_image2_left
@[to_additive] lemma Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty := .of_image2_right

@[to_additive (attr := simp low + 1)]
lemma smul_singleton : s • ({b} : Set β) = (· • b) '' s := image2_singleton_right

@[to_additive (attr := simp low + 1)]
lemma singleton_smul : ({a} : Set α) • t = a • t := image2_singleton_left

@[to_additive (attr := simp high)]
lemma singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b} := image2_singleton

@[to_additive (attr := mono, gcongr)]
lemma smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image2_subset

@[to_additive]
lemma smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ := image2_subset_left

@[to_additive]
lemma smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t := image2_subset_right

@[to_additive] lemma smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u := image2_subset_iff

@[to_additive] lemma union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t := image2_union_left
@[to_additive] lemma smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ := image2_union_right

@[to_additive]
lemma inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t := image2_inter_subset_left

@[to_additive]
lemma smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ := image2_inter_subset_right

@[to_additive]
lemma inter_smul_union_subset_union : (s₁ ∩ s₂) • (t₁ ∪ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image2_inter_union_subset_union

@[to_additive]
lemma union_smul_inter_subset_union : (s₁ ∪ s₂) • (t₁ ∩ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image2_union_inter_subset_union

@[to_additive]
lemma smul_set_subset_smul {s : Set α} : a ∈ s → a • t ⊆ s • t := image_subset_image2_right

end SMul

section SMulSet
variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

@[to_additive] lemma image_smul : (fun x ↦ a • x) '' t = a • t := rfl

scoped[Pointwise] attribute [simp] Set.image_smul Set.image_vadd

@[to_additive] lemma mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x := Iff.rfl

@[to_additive] lemma smul_mem_smul_set : b ∈ s → a • b ∈ a • s := mem_image_of_mem _

@[to_additive (attr := simp)] lemma smul_set_empty : a • (∅ : Set β) = ∅ := image_empty _
@[to_additive (attr := simp)] lemma smul_set_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty

@[to_additive (attr := simp)]
lemma smul_set_nonempty : (a • s).Nonempty ↔ s.Nonempty := image_nonempty

@[to_additive (attr := simp)]
lemma smul_set_singleton : a • ({b} : Set β) = {a • b} := image_singleton

@[to_additive (attr := gcongr)] lemma smul_set_mono : s ⊆ t → a • s ⊆ a • t := image_mono

@[to_additive]
lemma smul_set_subset_iff : a • s ⊆ t ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ t :=
  image_subset_iff

@[to_additive]
lemma smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ :=
  image_union ..

@[to_additive]
lemma smul_set_insert (a : α) (b : β) (s : Set β) : a • insert b s = insert (a • b) (a • s) :=
  image_insert_eq ..

@[to_additive]
lemma smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ a • t₂ :=
  image_inter_subset ..

@[to_additive] lemma Nonempty.smul_set : s.Nonempty → (a • s).Nonempty := Nonempty.image _

end SMulSet

section Pi

variable {M ι : Type*} {π : ι → Type*} [∀ i, SMul M (π i)]

@[to_additive]
theorem smul_set_pi_of_surjective (c : M) (I : Set ι) (s : ∀ i, Set (π i))
    (hsurj : ∀ i ∉ I, Function.Surjective (c • · : π i → π i)) : c • I.pi s = I.pi (c • s) :=
  piMap_image_pi hsurj s

@[to_additive]
theorem smul_set_univ_pi (c : M) (s : ∀ i, Set (π i)) : c • univ.pi s = univ.pi (c • s) :=
  piMap_image_univ_pi _ s

end Pi

variable {s : Set α} {t : Set β} {a : α} {b : β}

@[to_additive]
lemma range_smul_range {ι κ : Type*} [SMul α β] (b : ι → α) (c : κ → β) :
    range b • range c = range fun p : ι × κ ↦ b p.1 • c p.2 :=
  image2_range ..

@[to_additive]
lemma smul_set_range [SMul α β] {ι : Sort*} (a : α) (f : ι → β) :
    a • range f = range fun i ↦ a • f i :=
  (range_comp ..).symm

@[to_additive] lemma range_smul [SMul α β] {ι : Sort*} (a : α) (f : ι → β) :
    range (fun i ↦ a • f i) = a • range f := (smul_set_range ..).symm

end SMul

section SDiv
variable {ι : Sort*} {κ : ι → Sort*} [SDiv α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

@[to_additive]
instance sdiv : SDiv (Set α) (Set β) where sdiv := image2 (· /ₛ ·)

@[to_additive (attr := simp)]
lemma image2_sdiv : image2 (· /ₛ ·) s t = s /ₛ t := rfl

@[to_additive]
lemma image_sdiv_prod : (fun x : β × β ↦ x.fst /ₛ x.snd) '' s ×ˢ t = s /ₛ t := image_prod _

@[to_additive]
lemma mem_sdiv : a ∈ s /ₛ t ↔ ∃ x ∈ s, ∃ y ∈ t, x /ₛ y = a := Iff.rfl

@[to_additive]
lemma sdiv_mem_sdiv (hb : b ∈ s) (hc : c ∈ t) : b /ₛ c ∈ s /ₛ t := mem_image2_of_mem hb hc

@[to_additive (attr := simp)]
lemma empty_sdiv (t : Set β) : ∅ /ₛ t = ∅ := image2_empty_left

@[to_additive (attr := simp)]
lemma sdiv_empty (s : Set β) : s /ₛ ∅ = ∅ := image2_empty_right

@[to_additive (attr := simp)]
lemma sdiv_eq_empty : s /ₛ t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff

@[to_additive (attr := simp)]
lemma sdiv_nonempty : (s /ₛ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image2_nonempty_iff

@[to_additive]
lemma Nonempty.sdiv : s.Nonempty → t.Nonempty → (s /ₛ t : Set α).Nonempty := .image2

@[to_additive]
lemma Nonempty.of_sdiv_left : (s /ₛ t : Set α).Nonempty → s.Nonempty := .of_image2_left

@[to_additive]
lemma Nonempty.of_sdiv_right : (s /ₛ t : Set α).Nonempty → t.Nonempty := .of_image2_right

@[to_additive (attr := simp low + 1)]
lemma sdiv_singleton (s : Set β) (b : β) : s /ₛ {b} = (· /ₛ b) '' s := image2_singleton_right

@[to_additive (attr := simp low + 1)]
lemma singleton_sdiv (t : Set β) (b : β) : {b} /ₛ t = (b /ₛ ·) '' t := image2_singleton_left

@[to_additive (attr := simp high)]
lemma singleton_sdiv_singleton : ({b} : Set β) /ₛ {c} = {b /ₛ c} := image2_singleton

@[to_additive (attr := mono, gcongr)]
lemma sdiv_subset_sdiv : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ /ₛ t₁ ⊆ s₂ /ₛ t₂ := image2_subset

@[to_additive]
lemma sdiv_subset_sdiv_left : t₁ ⊆ t₂ → s /ₛ t₁ ⊆ s /ₛ t₂ := image2_subset_left

@[to_additive]
lemma sdiv_subset_sdiv_right : s₁ ⊆ s₂ → s₁ /ₛ t ⊆ s₂ /ₛ t := image2_subset_right

@[to_additive]
lemma sdiv_subset_iff : s /ₛ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x /ₛ y ∈ u := image2_subset_iff

@[to_additive]
lemma sdiv_self_mono (h : s ⊆ t) : s /ₛ s ⊆ t /ₛ t := sdiv_subset_sdiv h h

@[to_additive]
lemma union_sdiv : s₁ ∪ s₂ /ₛ t = s₁ /ₛ t ∪ (s₂ /ₛ t) := image2_union_left

@[to_additive]
lemma sdiv_union : s /ₛ (t₁ ∪ t₂) = s /ₛ t₁ ∪ (s /ₛ t₂) := image2_union_right

@[to_additive]
lemma inter_sdiv_subset : s₁ ∩ s₂ /ₛ t ⊆ (s₁ /ₛ t) ∩ (s₂ /ₛ t) := image2_inter_subset_left

@[to_additive]
lemma sdiv_inter_subset : s /ₛ t₁ ∩ t₂ ⊆ (s /ₛ t₁) ∩ (s /ₛ t₂) := image2_inter_subset_right

@[to_additive]
lemma inter_sdiv_union_subset_union : s₁ ∩ s₂ /ₛ (t₁ ∪ t₂) ⊆ s₁ /ₛ t₁ ∪ (s₂ /ₛ t₂) :=
  image2_inter_union_subset_union

@[to_additive]
lemma union_sdiv_inter_subset_union : s₁ ∪ s₂ /ₛ t₁ ∩ t₂ ⊆ s₁ /ₛ t₁ ∪ (s₂ /ₛ t₂) :=
  image2_union_inter_subset_union

end SDiv

open scoped Pointwise

@[to_additive]
lemma image_smul_comm [SMul α β] [SMul α γ] (f : β → γ) (a : α) (s : Set β) :
    (∀ b, f (a • b) = a • f b) → f '' (a • s) = a • f '' s := image_comm

section SMul
variable [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

-- TODO: replace hypothesis and conclusion with a typeclass
@[to_additive]
lemma op_smul_set_smul_eq_smul_smul_set (a : α) (s : Set β) (t : Set γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext; simp [mem_smul, mem_smul_set, h]

end SMul

end Set
