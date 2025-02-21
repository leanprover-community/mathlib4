/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn, Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Tactic.MinImports

/-!
# Pointwise operations of sets

This file defines pointwise algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:
* `s * t`: Multiplication, set of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s + t`: Addition, set of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s⁻¹`: Inversion, set of all `x⁻¹` where `x ∈ s`.
* `-s`: Negation, set of all `-x` where `x ∈ s`.
* `s / t`: Division, set of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s - t`: Subtraction, set of all `x - y` where `x ∈ s` and `y ∈ t`.
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
* We put all instances in the locale `Pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

assert_not_exists MonoidWithZero OrderedAddCommMonoid

library_note "pointwise nat action"/--
Pointwise monoids (`Set`, `Finset`, `Filter`) have derived pointwise actions of the form
`SMul α β → SMul α (Set β)`. When `α` is `ℕ` or `ℤ`, this action conflicts with the
nat or int action coming from `Set β` being a `Monoid` or `DivInvMonoid`. For example,
`2 • {a, b}` can both be `{2 • a, 2 • b}` (pointwise action, pointwise repeated addition,
`Set.smulSet`) and `{a + a, a + b, b + a, b + b}` (nat or int action, repeated pointwise
addition, `Set.NSMul`).

Because the pointwise action can easily be spelled out in such cases, we give higher priority to the
nat and int actions.
-/

open Function MulOpposite

variable {F α β γ : Type*}

namespace Set

/-! ### `0`/`1` as sets -/

section One

variable [One α] {s : Set α} {a : α}

/-- The set `1 : Set α` is defined as `{1}` in locale `Pointwise`. -/
@[to_additive "The set `0 : Set α` is defined as `{0}` in locale `Pointwise`."]
protected noncomputable def one : One (Set α) :=
  ⟨{1}⟩

scoped[Pointwise] attribute [instance] Set.one Set.zero

open Pointwise

-- TODO: This would be a good simp lemma scoped to `Pointwise`, but it seems `@[simp]` can't be
-- scoped
@[to_additive]
theorem singleton_one : ({1} : Set α) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem mem_one : a ∈ (1 : Set α) ↔ a = 1 :=
  Iff.rfl

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Set α) :=
  Eq.refl _

@[to_additive (attr := simp)]
theorem one_subset : 1 ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff

@[to_additive (attr := simp)]
theorem one_nonempty : (1 : Set α).Nonempty :=
  ⟨1, rfl⟩

@[to_additive (attr := simp)]
theorem image_one {f : α → β} : f '' 1 = {f 1} :=
  image_singleton

@[to_additive]
theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff_eq

@[to_additive]
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 :=
  h.subset_singleton_iff

/-- The singleton operation as a `OneHom`. -/
@[to_additive "The singleton operation as a `ZeroHom`."]
noncomputable def singletonOneHom : OneHom α (Set α) where
  toFun := singleton; map_one' := singleton_one

@[to_additive (attr := simp)]
theorem coe_singletonOneHom : (singletonOneHom : α → Set α) = singleton :=
  rfl

@[to_additive] lemma image_op_one : (1 : Set α).image op = 1 := image_singleton

@[to_additive (attr := simp)]
lemma one_prod_one [One β] : (1 ×ˢ 1 : Set (α × β)) = 1 := by ext; simp [Prod.ext_iff]

end One

/-! ### Set negation/inversion -/


section Inv

/-- The pointwise inversion of set `s⁻¹` is defined as `{x | x⁻¹ ∈ s}` in locale `Pointwise`. It is
equal to `{x⁻¹ | x ∈ s}`, see `Set.image_inv_eq_inv`. -/
@[to_additive
      "The pointwise negation of set `-s` is defined as `{x | -x ∈ s}` in locale `Pointwise`.
      It is equal to `{-x | x ∈ s}`, see `Set.image_neg_eq_neg`."]
protected def inv [Inv α] : Inv (Set α) :=
  ⟨preimage Inv.inv⟩

scoped[Pointwise] attribute [instance] Set.inv Set.neg

open Pointwise

section Inv

variable {ι : Sort*} [Inv α] {s t : Set α} {a : α}

@[to_additive (attr := simp)]
theorem mem_inv : a ∈ s⁻¹ ↔ a⁻¹ ∈ s :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem inv_preimage : Inv.inv ⁻¹' s = s⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem inv_empty : (∅ : Set α)⁻¹ = ∅ :=
  rfl

@[to_additive (attr := simp)]
theorem inv_univ : (univ : Set α)⁻¹ = univ :=
  rfl

@[to_additive (attr := simp)]
theorem inter_inv : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ :=
  preimage_inter

@[to_additive (attr := simp)]
theorem union_inv : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ :=
  preimage_union

@[to_additive (attr := simp)]
theorem iInter_inv (s : ι → Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ :=
  preimage_iInter

@[to_additive (attr := simp)]
theorem sInter_inv (S : Set (Set α)) : (⋂₀ S)⁻¹ = ⋂ s ∈ S, s⁻¹ :=
  preimage_sInter

@[to_additive (attr := simp)]
theorem iUnion_inv (s : ι → Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
  preimage_iUnion

@[to_additive (attr := simp)]
theorem sUnion_inv (S : Set (Set α)) : (⋃₀ S)⁻¹ = ⋃ s ∈ S, s⁻¹ :=
  preimage_sUnion

@[to_additive (attr := simp)]
theorem compl_inv : sᶜ⁻¹ = s⁻¹ᶜ :=
  preimage_compl

@[to_additive (attr := simp)]
lemma inv_prod [Inv β] (s : Set α) (t : Set β) : (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹ := rfl

end Inv

section InvolutiveInv

variable [InvolutiveInv α] {s t : Set α} {a : α}

@[to_additive]
theorem inv_mem_inv : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by simp only [mem_inv, inv_inv]

@[to_additive (attr := simp)]
theorem nonempty_inv : s⁻¹.Nonempty ↔ s.Nonempty :=
  inv_involutive.surjective.nonempty_preimage

@[to_additive]
theorem Nonempty.inv (h : s.Nonempty) : s⁻¹.Nonempty :=
  nonempty_inv.2 h

@[to_additive (attr := simp)]
theorem image_inv_eq_inv : (·⁻¹) '' s = s⁻¹ :=
  congr_fun (image_eq_preimage_of_inverse inv_involutive.leftInverse inv_involutive.rightInverse) _

@[to_additive (attr := simp)]
theorem inv_eq_empty : s⁻¹ = ∅ ↔ s = ∅ := by
  rw [← image_inv_eq_inv, image_eq_empty]

@[to_additive (attr := simp)]
noncomputable instance involutiveInv : InvolutiveInv (Set α) where
  inv := Inv.inv
  inv_inv s := by simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id']

@[to_additive (attr := simp)]
theorem inv_subset_inv : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
  (Equiv.inv α).surjective.preimage_subset_preimage_iff

@[to_additive]
theorem inv_subset : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by rw [← inv_subset_inv, inv_inv]

@[to_additive (attr := simp)]
theorem inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹} := by
  rw [← image_inv_eq_inv, image_singleton]

@[to_additive (attr := simp)]
theorem inv_insert (a : α) (s : Set α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ := by
  rw [insert_eq, union_inv, inv_singleton, insert_eq]

@[to_additive]
theorem inv_range {ι : Sort*} {f : ι → α} : (range f)⁻¹ = range fun i => (f i)⁻¹ := by
  rw [← image_inv_eq_inv]
  exact (range_comp ..).symm

open MulOpposite

@[to_additive]
theorem image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ := by
  simp_rw [← image_inv_eq_inv, Function.Semiconj.set_image op_inv s]

end InvolutiveInv

end Inv

open Pointwise

/-! ### Translation/scaling of sets -/

section SMul

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in locale `Pointwise`. -/
@[to_additive
"The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in locale `Pointwise`."]
protected def smulSet [SMul α β] : SMul α (Set β) where smul a := image (a • ·)

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
locale `Pointwise`. -/
@[to_additive
"The pointwise scalar addition of sets `s +ᵥ t` is defined as `{x +ᵥ y | x ∈ s, y ∈ t}` in locale
`Pointwise`."]
protected def smul [SMul α β] : SMul (Set α) (Set β) where smul := image2 (· • ·)

scoped[Pointwise] attribute [instance] Set.smulSet Set.smul
scoped[Pointwise] attribute [instance] Set.vaddSet Set.vadd

section SMul
variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

@[to_additive (attr := simp)] lemma image2_smul : image2 SMul.smul s t = s • t := rfl

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

@[to_additive (attr := simp low+1)]
lemma smul_singleton : s • ({b} : Set β) = (· • b) '' s := image2_singleton_right

@[to_additive (attr := simp low+1)]
lemma singleton_smul : ({a} : Set α) • t = a • t := image2_singleton_left

@[to_additive (attr := simp high)]
lemma singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b} := image2_singleton

@[to_additive (attr := mono, gcongr)]
lemma smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image2_subset

@[to_additive (attr := gcongr)]
lemma smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ := image2_subset_left

@[to_additive (attr := gcongr)]
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

@[to_additive] lemma iUnion_smul_left_image : ⋃ a ∈ s, a • t = s • t := iUnion_image_left _

@[to_additive]
lemma iUnion_smul_right_image : ⋃ a ∈ t, (· • a) '' s = s • t := iUnion_image_right _

@[to_additive]
lemma iUnion_smul (s : ι → Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
  image2_iUnion_left ..

@[to_additive]
lemma smul_iUnion (s : Set α) (t : ι → Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i :=
  image2_iUnion_right ..

@[to_additive]
lemma sUnion_smul (S : Set (Set α)) (t : Set β) : ⋃₀ S • t = ⋃ s ∈ S, s • t :=
  image2_sUnion_left ..

@[to_additive]
lemma smul_sUnion (s : Set α) (T : Set (Set β)) : s • ⋃₀ T = ⋃ t ∈ T, s • t :=
  image2_sUnion_right ..

@[to_additive]
lemma iUnion₂_smul (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋃ i, ⋃ j, s i j) • t = ⋃ i, ⋃ j, s i j • t := image2_iUnion₂_left ..

@[to_additive]
lemma smul_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋃ i, ⋃ j, t i j) = ⋃ i, ⋃ j, s • t i j := image2_iUnion₂_right ..

@[to_additive]
lemma iInter_smul_subset (s : ι → Set α) (t : Set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
  image2_iInter_subset_left ..

@[to_additive]
lemma smul_iInter_subset (s : Set α) (t : ι → Set β) : (s • ⋂ i, t i) ⊆ ⋂ i, s • t i :=
  image2_iInter_subset_right ..

@[to_additive]
lemma sInter_smul_subset (S : Set (Set α)) (t : Set β) : ⋂₀ S • t ⊆ ⋂ s ∈ S, s • t :=
  image2_sInter_left_subset S t (fun a x => a • x)

@[to_additive]
lemma smul_sInter_subset (s : Set α) (T : Set (Set β)) : s • ⋂₀ T ⊆ ⋂ t ∈ T, s • t :=
  image2_sInter_right_subset s T (fun a x => a • x)

@[to_additive]
lemma iInter₂_smul_subset (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋂ i, ⋂ j, s i j) • t ⊆ ⋂ i, ⋂ j, s i j • t := image2_iInter₂_subset_left ..

@[to_additive]
lemma smul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋂ i, ⋂ j, t i j) ⊆ ⋂ i, ⋂ j, s • t i j := image2_iInter₂_subset_right ..

@[to_additive]
lemma smul_set_subset_smul {s : Set α} : a ∈ s → a • t ⊆ s • t := image_subset_image2_right

@[to_additive (attr := simp)]
lemma iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a ∈ s, a • t = s • t := iUnion_image_left _

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

@[to_additive (attr := gcongr)] lemma smul_set_mono : s ⊆ t → a • s ⊆ a • t := image_subset _

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

@[to_additive]
lemma smul_set_iUnion (a : α) (s : ι → Set β) : a • ⋃ i, s i = ⋃ i, a • s i :=
  image_iUnion

@[to_additive]
lemma smul_set_iUnion₂ (a : α) (s : ∀ i, κ i → Set β) :
    a • ⋃ i, ⋃ j, s i j = ⋃ i, ⋃ j, a • s i j := image_iUnion₂ ..

@[to_additive]
lemma smul_set_sUnion (a : α) (S : Set (Set β)) : a • ⋃₀ S = ⋃ s ∈ S, a • s := by
  rw [sUnion_eq_biUnion, smul_set_iUnion₂]

@[to_additive]
lemma smul_set_iInter_subset (a : α) (t : ι → Set β) : a • ⋂ i, t i ⊆ ⋂ i, a • t i :=
  image_iInter_subset ..

@[to_additive]
lemma smul_set_sInter_subset (a : α) (S : Set (Set β)) :
    a • ⋂₀ S ⊆ ⋂ s ∈ S, a • s := image_sInter_subset ..

@[to_additive]
lemma smul_set_iInter₂_subset (a : α) (t : ∀ i, κ i → Set β) :
    a • ⋂ i, ⋂ j, t i j ⊆ ⋂ i, ⋂ j, a • t i j := image_iInter₂_subset ..

@[to_additive] lemma Nonempty.smul_set : s.Nonempty → (a • s).Nonempty := Nonempty.image _

end SMulSet

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

/-! ### Set addition/multiplication -/

open scoped Pointwise

section Mul

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-- The pointwise multiplication of sets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}` in
locale `Pointwise`. -/
@[to_additive
      "The pointwise addition of sets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in locale
      `Pointwise`."]
protected def mul : Mul (Set α) :=
  ⟨image2 (· * ·)⟩

scoped[Pointwise] attribute [instance] Set.mul Set.add

@[to_additive (attr := simp)]
theorem image2_mul : image2 (· * ·) s t = s * t :=
  rfl

@[to_additive]
theorem mem_mul : a ∈ s * t ↔ ∃ x ∈ s, ∃ y ∈ t, x * y = a :=
  Iff.rfl

@[to_additive]
theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t :=
  mem_image2_of_mem

@[to_additive add_image_prod]
theorem image_mul_prod : (fun x : α × α => x.fst * x.snd) '' s ×ˢ t = s * t :=
  image_prod _

@[to_additive (attr := simp)]
theorem empty_mul : ∅ * s = ∅ :=
  image2_empty_left

@[to_additive (attr := simp)]
theorem mul_empty : s * ∅ = ∅ :=
  image2_empty_right

@[to_additive (attr := simp)]
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[to_additive (attr := simp)]
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

@[to_additive]
theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  Nonempty.image2

@[to_additive]
theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left

@[to_additive]
theorem Nonempty.of_mul_right : (s * t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right

@[to_additive (attr := simp)]
theorem mul_singleton : s * {b} = (· * b) '' s :=
  image2_singleton_right

@[to_additive (attr := simp)]
theorem singleton_mul : {a} * t = (a * ·) '' t :=
  image2_singleton_left

@[to_additive] lemma smul_set_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image2_right

open scoped RightActions in
@[to_additive] lemma op_smul_set_subset_mul : a ∈ t → s <• a ⊆ s * t := image_subset_image2_left

@[to_additive]
lemma image_op_smul : (op '' s) • t = t * s := by
  rw [← image2_smul, ← image2_mul, image2_image_left, image2_swap]
  rfl

@[to_additive (attr := simp)]
lemma iUnion_op_smul_set (s t : Set α) : ⋃ a ∈ t, MulOpposite.op a • s = s * t :=
  iUnion_image_right _

@[to_additive]
lemma mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u := image2_subset_iff_left

@[to_additive]
lemma mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u := image2_subset_iff_right

@[to_additive]
theorem singleton_mul_singleton : ({a} : Set α) * {b} = {a * b} :=
  image2_singleton

@[to_additive (attr := mono, gcongr)]
theorem mul_subset_mul : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ * s₂ ⊆ t₁ * t₂ :=
  image2_subset

@[to_additive (attr := gcongr)]
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image2_subset_left

@[to_additive (attr := gcongr)]
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image2_subset_right

@[to_additive] instance : MulLeftMono (Set α) where elim _s _t₁ _t₂ := mul_subset_mul_left
@[to_additive] instance : MulRightMono (Set α) where elim _t _s₁ _s₂ := mul_subset_mul_right

@[to_additive]
theorem mul_subset_iff : s * t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x * y ∈ u :=
  image2_subset_iff

@[to_additive]
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image2_union_left

@[to_additive]
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image2_union_right

@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image2_inter_subset_left

@[to_additive]
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image2_inter_subset_right

@[to_additive]
theorem inter_mul_union_subset_union : s₁ ∩ s₂ * (t₁ ∪ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ :=
  image2_inter_union_subset_union

@[to_additive]
theorem union_mul_inter_subset_union : (s₁ ∪ s₂) * (t₁ ∩ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ :=
  image2_union_inter_subset_union

@[to_additive]
theorem iUnion_mul_left_image : ⋃ a ∈ s, (a * ·) '' t = s * t :=
  iUnion_image_left _

@[to_additive]
theorem iUnion_mul_right_image : ⋃ a ∈ t, (· * a) '' s = s * t :=
  iUnion_image_right _

@[to_additive]
theorem iUnion_mul (s : ι → Set α) (t : Set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
  image2_iUnion_left ..

@[to_additive]
theorem mul_iUnion (s : Set α) (t : ι → Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i :=
  image2_iUnion_right ..

@[to_additive]
theorem sUnion_mul (S : Set (Set α)) (t : Set α) : ⋃₀ S * t = ⋃ s ∈ S, s * t :=
  image2_sUnion_left ..

@[to_additive]
theorem mul_sUnion (s : Set α) (T : Set (Set α)) : s * ⋃₀ T = ⋃ t ∈ T, s * t :=
  image2_sUnion_right ..

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iUnion₂_mul (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t :=
  image2_iUnion₂_left ..

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋃ (i) (j), t i j) = ⋃ (i) (j), s * t i j :=
  image2_iUnion₂_right ..

@[to_additive]
theorem iInter_mul_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
  Set.image2_iInter_subset_left ..

@[to_additive]
theorem mul_iInter_subset (s : Set α) (t : ι → Set α) : (s * ⋂ i, t i) ⊆ ⋂ i, s * t i :=
  image2_iInter_subset_right ..

@[to_additive]
lemma mul_sInter_subset (s : Set α) (T : Set (Set α)) :
    s * ⋂₀ T ⊆ ⋂ t ∈ T, s * t := image2_sInter_right_subset s T (fun a b => a * b)

@[to_additive]
lemma sInter_mul_subset (S : Set (Set α)) (t : Set α) :
    ⋂₀ S * t ⊆ ⋂ s ∈ S, s * t := image2_sInter_left_subset S t (fun a b => a * b)

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iInter₂_mul_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) * t ⊆ ⋂ (i) (j), s i j * t :=
  image2_iInter₂_subset_left ..

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s * t i j :=
  image2_iInter₂_subset_right ..

@[to_additive] lemma pair_mul (a b : α) (s : Set α) : {a, b} * s = a • s ∪ b • s := by
  rw [insert_eq, union_mul, singleton_mul, singleton_mul]; rfl

open scoped RightActions
@[to_additive] lemma mul_pair (s : Set α) (a b : α) : s * {a, b} = s <• a ∪ s <• b := by
  rw [insert_eq, mul_union, mul_singleton, mul_singleton]; rfl

/-- The singleton operation as a `MulHom`. -/
@[to_additive "The singleton operation as an `AddHom`."]
noncomputable def singletonMulHom : α →ₙ* Set α where
  toFun := singleton
  map_mul' _ _ := singleton_mul_singleton.symm

@[to_additive (attr := simp)]
theorem coe_singletonMulHom : (singletonMulHom : α → Set α) = singleton :=
  rfl

@[to_additive (attr := simp)]
theorem singletonMulHom_apply (a : α) : singletonMulHom a = {a} :=
  rfl

@[to_additive] lemma range_mul {ι : Sort*} (a : α) (f : ι → α) :
    range (fun i ↦ a * f i) = a • range f := range_smul a f

open MulOpposite

@[to_additive (attr := simp)]
theorem image_op_mul : op '' (s * t) = op '' t * op '' s :=
  image_image2_antidistrib op_mul

@[to_additive (attr := simp)]
lemma prod_mul_prod_comm [Mul β] (s₁ s₂: Set α) (t₁ t₂ : Set β) :
   (s₁ ×ˢ t₁) * (s₂ ×ˢ t₂) = (s₁ * s₂) ×ˢ (t₁ * t₂) := by ext; simp [mem_mul]; aesop

end Mul

/-! ### Set subtraction/division -/


section Div

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-- The pointwise division of sets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`Pointwise`. -/
@[to_additive
      "The pointwise subtraction of sets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}` in locale
      `Pointwise`."]
protected def div : Div (Set α) :=
  ⟨image2 (· / ·)⟩

scoped[Pointwise] attribute [instance] Set.div Set.sub

@[to_additive (attr := simp)]
theorem image2_div : image2 Div.div s t = s / t :=
  rfl

@[to_additive]
theorem mem_div : a ∈ s / t ↔ ∃ x ∈ s, ∃ y ∈ t, x / y = a :=
  Iff.rfl

@[to_additive]
theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t :=
  mem_image2_of_mem

@[to_additive sub_image_prod]
theorem image_div_prod : (fun x : α × α => x.fst / x.snd) '' s ×ˢ t = s / t :=
  image_prod _

@[to_additive (attr := simp)]
theorem empty_div : ∅ / s = ∅ :=
  image2_empty_left

@[to_additive (attr := simp)]
theorem div_empty : s / ∅ = ∅ :=
  image2_empty_right

@[to_additive (attr := simp)]
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[to_additive (attr := simp)]
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

@[to_additive]
theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty :=
  Nonempty.image2

@[to_additive]
theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left

@[to_additive]
theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right

@[to_additive (attr := simp)]
theorem div_singleton : s / {b} = (· / b) '' s :=
  image2_singleton_right

@[to_additive (attr := simp)]
theorem singleton_div : {a} / t = (· / ·) a '' t :=
  image2_singleton_left

@[to_additive]
theorem singleton_div_singleton : ({a} : Set α) / {b} = {a / b} :=
  image2_singleton

@[to_additive (attr := mono, gcongr)]
theorem div_subset_div : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ / s₂ ⊆ t₁ / t₂ :=
  image2_subset

@[to_additive (attr := gcongr)]
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image2_subset_left

@[to_additive (attr := gcongr)]
theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t :=
  image2_subset_right

@[to_additive]
theorem div_subset_iff : s / t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x / y ∈ u :=
  image2_subset_iff

@[to_additive]
theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t :=
  image2_union_left

@[to_additive]
theorem div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ :=
  image2_union_right

@[to_additive]
theorem inter_div_subset : s₁ ∩ s₂ / t ⊆ s₁ / t ∩ (s₂ / t) :=
  image2_inter_subset_left

@[to_additive]
theorem div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
  image2_inter_subset_right

@[to_additive]
theorem inter_div_union_subset_union : s₁ ∩ s₂ / (t₁ ∪ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ :=
  image2_inter_union_subset_union

@[to_additive]
theorem union_div_inter_subset_union : (s₁ ∪ s₂) / (t₁ ∩ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ :=
  image2_union_inter_subset_union

@[to_additive]
theorem iUnion_div_left_image : ⋃ a ∈ s, (a / ·) '' t = s / t :=
  iUnion_image_left _

@[to_additive]
theorem iUnion_div_right_image : ⋃ a ∈ t, (· / a) '' s = s / t :=
  iUnion_image_right _

@[to_additive]
theorem iUnion_div (s : ι → Set α) (t : Set α) : (⋃ i, s i) / t = ⋃ i, s i / t :=
  image2_iUnion_left ..

@[to_additive]
theorem div_iUnion (s : Set α) (t : ι → Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i :=
  image2_iUnion_right ..

@[to_additive]
theorem sUnion_div (S : Set (Set α)) (t : Set α) : ⋃₀ S / t = ⋃ s ∈ S, s / t :=
  image2_sUnion_left ..

@[to_additive]
theorem div_sUnion (s : Set α) (T : Set (Set α)) : s / ⋃₀ T = ⋃ t ∈ T, s / t :=
  image2_sUnion_right ..

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iUnion₂_div (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) / t = ⋃ (i) (j), s i j / t :=
  image2_iUnion₂_left ..

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋃ (i) (j), t i j) = ⋃ (i) (j), s / t i j :=
  image2_iUnion₂_right ..

@[to_additive]
theorem iInter_div_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
  image2_iInter_subset_left ..

@[to_additive]
theorem div_iInter_subset (s : Set α) (t : ι → Set α) : (s / ⋂ i, t i) ⊆ ⋂ i, s / t i :=
  image2_iInter_subset_right ..

@[to_additive]
theorem sInter_div_subset (S : Set (Set α)) (t : Set α) : ⋂₀ S / t ⊆ ⋂ s ∈ S, s / t :=
  image2_sInter_subset_left ..

@[to_additive]
theorem div_sInter_subset (s : Set α) (T : Set (Set α)) : s / ⋂₀ T ⊆ ⋂ t ∈ T, s / t :=
  image2_sInter_subset_right ..

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iInter₂_div_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) / t ⊆ ⋂ (i) (j), s i j / t :=
  image2_iInter₂_subset_left ..

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s / t i j :=
  image2_iInter₂_subset_right ..

end Div

section VSub
variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

instance vsub : VSub (Set α) (Set β) where vsub := image2 (· -ᵥ ·)

@[simp] lemma image2_vsub : (image2 VSub.vsub s t : Set α) = s -ᵥ t := rfl

lemma image_vsub_prod : (fun x : β × β ↦ x.fst -ᵥ x.snd) '' s ×ˢ t = s -ᵥ t := image_prod _

lemma mem_vsub : a ∈ s -ᵥ t ↔ ∃ x ∈ s, ∃ y ∈ t, x -ᵥ y = a := Iff.rfl

lemma vsub_mem_vsub (hb : b ∈ s) (hc : c ∈ t) : b -ᵥ c ∈ s -ᵥ t := mem_image2_of_mem hb hc

@[simp] lemma empty_vsub (t : Set β) : ∅ -ᵥ t = ∅ := image2_empty_left
@[simp] lemma vsub_empty (s : Set β) : s -ᵥ ∅ = ∅ := image2_empty_right

@[simp] lemma vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff

@[simp]
lemma vsub_nonempty : (s -ᵥ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image2_nonempty_iff

lemma Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Set α).Nonempty := .image2
lemma Nonempty.of_vsub_left : (s -ᵥ t : Set α).Nonempty → s.Nonempty := .of_image2_left
lemma Nonempty.of_vsub_right : (s -ᵥ t : Set α).Nonempty → t.Nonempty := .of_image2_right

@[simp low+1]
lemma vsub_singleton (s : Set β) (b : β) : s -ᵥ {b} = (· -ᵥ b) '' s := image2_singleton_right

@[simp low+1]
lemma singleton_vsub (t : Set β) (b : β) : {b} -ᵥ t = (b -ᵥ ·) '' t := image2_singleton_left

@[simp high] lemma singleton_vsub_singleton : ({b} : Set β) -ᵥ {c} = {b -ᵥ c} := image2_singleton

@[mono, gcongr] lemma vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ := image2_subset

@[gcongr] lemma vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ := image2_subset_left
@[gcongr] lemma vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t := image2_subset_right

lemma vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x -ᵥ y ∈ u := image2_subset_iff

lemma vsub_self_mono (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t := vsub_subset_vsub h h

lemma union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) := image2_union_left
lemma vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) := image2_union_right

lemma inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) := image2_inter_subset_left
lemma vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) := image2_inter_subset_right

lemma inter_vsub_union_subset_union : s₁ ∩ s₂ -ᵥ (t₁ ∪ t₂) ⊆ s₁ -ᵥ t₁ ∪ (s₂ -ᵥ t₂) :=
  image2_inter_union_subset_union

lemma union_vsub_inter_subset_union : s₁ ∪ s₂ -ᵥ t₁ ∩ t₂ ⊆ s₁ -ᵥ t₁ ∪ (s₂ -ᵥ t₂) :=
  image2_union_inter_subset_union

lemma iUnion_vsub_left_image : ⋃ a ∈ s, (a -ᵥ ·) '' t = s -ᵥ t := iUnion_image_left _
lemma iUnion_vsub_right_image : ⋃ a ∈ t, (· -ᵥ a) '' s = s -ᵥ t := iUnion_image_right _

lemma iUnion_vsub (s : ι → Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
  image2_iUnion_left ..

lemma vsub_iUnion (s : Set β) (t : ι → Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i :=
  image2_iUnion_right ..

lemma sUnion_vsub (S : Set (Set β)) (t : Set β) : ⋃₀ S -ᵥ t = ⋃ s ∈ S, s -ᵥ t :=
  image2_sUnion_left ..

lemma vsub_sUnion (s : Set β) (T : Set (Set β)) : s -ᵥ ⋃₀ T = ⋃ t ∈ T, s -ᵥ t :=
  image2_sUnion_right ..

lemma iUnion₂_vsub (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋃ i, ⋃ j, s i j) -ᵥ t = ⋃ i, ⋃ j, s i j -ᵥ t := image2_iUnion₂_left ..

lemma vsub_iUnion₂ (s : Set β) (t : ∀ i, κ i → Set β) :
    (s -ᵥ ⋃ i, ⋃ j, t i j) = ⋃ i, ⋃ j, s -ᵥ t i j := image2_iUnion₂_right ..

lemma iInter_vsub_subset (s : ι → Set β) (t : Set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
  image2_iInter_subset_left ..

lemma vsub_iInter_subset (s : Set β) (t : ι → Set β) : (s -ᵥ ⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
  image2_iInter_subset_right ..

lemma sInter_vsub_subset (S : Set (Set β)) (t : Set β) : ⋂₀ S -ᵥ t ⊆ ⋂ s ∈ S, s -ᵥ t :=
  image2_sInter_subset_left ..

lemma vsub_sInter_subset (s : Set β) (T : Set (Set β)) : s -ᵥ ⋂₀ T ⊆ ⋂ t ∈ T, s -ᵥ t :=
  image2_sInter_subset_right ..

lemma iInter₂_vsub_subset (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋂ i, ⋂ j, s i j) -ᵥ t ⊆ ⋂ i, ⋂ j, s i j -ᵥ t := image2_iInter₂_subset_left ..

lemma vsub_iInter₂_subset (s : Set β) (t : ∀ i, κ i → Set β) :
    s -ᵥ ⋂ i, ⋂ j, t i j ⊆ ⋂ i, ⋂ j, s -ᵥ t i j := image2_iInter₂_subset_right ..

end VSub

@[to_additive]
lemma image_smul_comm [SMul α β] [SMul α γ] (f : β → γ) (a : α) (s : Set β) :
    (∀ b, f (a • b) = a • f b) → f '' (a • s) = a • f '' s := image_comm

@[to_additive]
lemma image_smul_distrib [MulOneClass α] [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β]
    (f : F) (a : α) (s : Set α) :
    f '' (a • s) = f a • f '' s :=
  image_comm <| map_mul _ _

open scoped RightActions in
@[to_additive]
lemma image_op_smul_distrib [MulOneClass α] [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β]
    (f : F) (a : α) (s : Set α) : f '' (s <• a) = f '' s <• f a := image_comm fun _ ↦ map_mul ..

section SMul
variable [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

-- TODO: replace hypothesis and conclusion with a typeclass
@[to_additive]
lemma op_smul_set_smul_eq_smul_smul_set (a : α) (s : Set β) (t : Set γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext; simp [mem_smul, mem_smul_set, h]

end SMul

section Semigroup
variable [Semigroup α]

@[to_additive]
lemma op_smul_set_mul_eq_mul_smul_set (a : α) (s : Set α) (t : Set α) :
    op a • s * t = s * a • t :=
  op_smul_set_smul_eq_smul_smul_set _ _ _ fun _ _ _ => mul_assoc _ _ _

end Semigroup

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `Set`. See
note [pointwise nat action]. -/
protected def NSMul [Zero α] [Add α] : SMul ℕ (Set α) :=
  ⟨nsmulRec⟩

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`Set`. See note [pointwise nat action]. -/
@[to_additive existing]
protected def NPow [One α] [Mul α] : Pow (Set α) ℕ :=
  ⟨fun s n => npowRec n s⟩

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `Set`. See note [pointwise nat action]. -/
protected def ZSMul [Zero α] [Add α] [Neg α] : SMul ℤ (Set α) :=
  ⟨zsmulRec⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `Set`. See note [pointwise nat action]. -/
@[to_additive existing]
protected def ZPow [One α] [Mul α] [Inv α] : Pow (Set α) ℤ :=
  ⟨fun s n => zpowRec npowRec n s⟩

scoped[Pointwise] attribute [instance] Set.NSMul Set.NPow Set.ZSMul Set.ZPow

/-- `Set α` is a `Semigroup` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddSemigroup` under pointwise operations if `α` is."]
protected noncomputable def semigroup [Semigroup α] : Semigroup (Set α) :=
  { Set.mul with mul_assoc := fun _ _ _ => image2_assoc mul_assoc }

section CommSemigroup

variable [CommSemigroup α] {s t : Set α}

/-- `Set α` is a `CommSemigroup` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddCommSemigroup` under pointwise operations if `α` is."]
protected noncomputable def commSemigroup : CommSemigroup (Set α) :=
  { Set.semigroup with mul_comm := fun _ _ => image2_comm mul_comm }

@[to_additive]
theorem inter_mul_union_subset : s ∩ t * (s ∪ t) ⊆ s * t :=
  image2_inter_union_subset mul_comm

@[to_additive]
theorem union_mul_inter_subset : (s ∪ t) * (s ∩ t) ⊆ s * t :=
  image2_union_inter_subset mul_comm

end CommSemigroup

section MulOneClass

variable [MulOneClass α]

/-- `Set α` is a `MulOneClass` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddZeroClass` under pointwise operations if `α` is."]
protected noncomputable def mulOneClass : MulOneClass (Set α) :=
  { Set.one, Set.mul with
    mul_one := image2_right_identity mul_one
    one_mul := image2_left_identity one_mul }

scoped[Pointwise]
  attribute [instance]
    Set.mulOneClass Set.addZeroClass Set.semigroup Set.addSemigroup Set.commSemigroup
    Set.addCommSemigroup

@[to_additive]
theorem subset_mul_left (s : Set α) {t : Set α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun x hx =>
  ⟨x, hx, 1, ht, mul_one _⟩

@[to_additive]
theorem subset_mul_right {s : Set α} (t : Set α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun x hx =>
  ⟨1, hs, x, hx, one_mul _⟩

/-- The singleton operation as a `MonoidHom`. -/
@[to_additive "The singleton operation as an `AddMonoidHom`."]
noncomputable def singletonMonoidHom : α →* Set α :=
  { singletonMulHom, singletonOneHom with }

@[to_additive (attr := simp)]
theorem coe_singletonMonoidHom : (singletonMonoidHom : α → Set α) = singleton :=
  rfl

@[to_additive (attr := simp)]
theorem singletonMonoidHom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl

end MulOneClass

section IsLeftCancelMul

variable [Mul α] [IsLeftCancelMul α] {s t : Set α}

@[to_additive]
theorem pairwiseDisjoint_smul_iff :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t).InjOn fun p ↦ p.1 * p.2 :=
  pairwiseDisjoint_image_right_iff fun _ _ ↦ mul_right_injective _

end IsLeftCancelMul

section Monoid

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

/-- `Set α` is a `Monoid` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddMonoid` under pointwise operations if `α` is."]
protected noncomputable def monoid : Monoid (Set α) :=
  { Set.semigroup, Set.mulOneClass, @Set.NPow α _ _ with }

scoped[Pointwise] attribute [instance] Set.monoid Set.addMonoid

-- `Set.pow_left_monotone` doesn't exist since it would syntactically be a special case of
-- `pow_left_mono`

@[to_additive]
protected lemma pow_right_monotone (hs : 1 ∈ s) : Monotone (s ^ ·) :=
  pow_right_monotone <| one_subset.2 hs

@[to_additive (attr := gcongr)]
lemma pow_subset_pow_left (hst : s ⊆ t) : s ^ n ⊆ t ^ n := pow_left_mono _ hst

@[to_additive (attr := gcongr)]
lemma pow_subset_pow_right (hs : 1 ∈ s) (hmn : m ≤ n) : s ^ m ⊆ s ^ n :=
  Set.pow_right_monotone hs hmn

@[to_additive (attr := gcongr)]
lemma pow_subset_pow (hst : s ⊆ t) (ht : 1 ∈ t) (hmn : m ≤ n) : s ^ m ⊆ t ^ n :=
  (pow_subset_pow_left hst).trans (pow_subset_pow_right ht hmn)

@[to_additive]
lemma subset_pow (hs : 1 ∈ s) (hn : n ≠ 0) : s ⊆ s ^ n := by
  simpa using pow_subset_pow_right hs <| Nat.one_le_iff_ne_zero.2 hn

@[deprecated (since := "2024-11-19")] alias pow_subset_pow_of_one_mem := pow_subset_pow_right

@[deprecated (since := "2024-11-19")]
alias nsmul_subset_nsmul_of_zero_mem := nsmul_subset_nsmul_right

@[to_additive]
lemma pow_subset_pow_mul_of_sq_subset_mul (hst : s ^ 2 ⊆ t * s) (hn : n ≠ 0) :
    s ^ n ⊆ t ^ (n - 1) * s := pow_le_pow_mul_of_sq_le_mul hst hn

@[to_additive (attr := simp) nsmul_empty]
lemma empty_pow (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ := match n with | n + 1 => by simp [pow_succ]

@[deprecated (since := "2024-10-21")] alias empty_nsmul := nsmul_empty

@[to_additive]
lemma Nonempty.pow (hs : s.Nonempty) : ∀ {n}, (s ^ n).Nonempty
  | 0 => by simp
  | n + 1 => by rw [pow_succ]; exact hs.pow.mul hs

set_option push_neg.use_distrib true in
@[to_additive (attr := simp)] lemma pow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n ≠ 0 := by
  constructor
  · contrapose!
    rintro (hs | rfl)
    · exact hs.pow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_pow hn

@[to_additive (attr := simp) nsmul_singleton]
lemma singleton_pow (a : α) : ∀ n, ({a} : Set α) ^ n = {a ^ n}
  | 0 => by simp [singleton_one]
  | n + 1 => by simp [pow_succ, singleton_pow _ n]

@[to_additive] lemma pow_mem_pow (ha : a ∈ s) : a ^ n ∈ s ^ n := by
  simpa using pow_subset_pow_left (singleton_subset_iff.2 ha)

@[to_additive] lemma one_mem_pow (hs : 1 ∈ s) : 1 ∈ s ^ n := by simpa using pow_mem_pow hs

@[to_additive]
lemma inter_pow_subset : (s ∩ t) ^ n ⊆ s ^ n ∩ t ^ n := by apply subset_inter <;> gcongr <;> simp

@[to_additive]
theorem mul_univ_of_one_mem (hs : (1 : α) ∈ s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩

@[to_additive]
theorem univ_mul_of_one_mem (ht : (1 : α) ∈ t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩

@[to_additive (attr := simp)]
theorem univ_mul_univ : (univ : Set α) * univ = univ :=
  mul_univ_of_one_mem <| mem_univ _

@[to_additive (attr := simp) nsmul_univ]
theorem univ_pow : ∀ {n : ℕ}, n ≠ 0 → (univ : Set α) ^ n = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => pow_one _
  | n + 2 => fun _ => by rw [pow_succ, univ_pow n.succ_ne_zero, univ_mul_univ]

@[to_additive]
protected theorem _root_.IsUnit.set : IsUnit a → IsUnit ({a} : Set α) :=
  IsUnit.map (singletonMonoidHom : α →* Set α)

@[to_additive nsmul_prod]
lemma prod_pow [Monoid β] (s : Set α) (t : Set β) : ∀ n, (s ×ˢ t) ^ n = (s ^ n) ×ˢ (t ^ n)
  | 0 => by simp
  | n + 1 => by simp [pow_succ, prod_pow _ _ n]

@[deprecated (since := "2025-02-17")] alias sum_nsmul := nsmul_prod

end Monoid

section IsLeftCancelMul
variable [Mul α] [IsLeftCancelMul α] {s t : Set α}

@[to_additive]
lemma Nontrivial.mul_left : t.Nontrivial → s.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, mul_mem_mul hc ha, c * b, mul_mem_mul hc hb, by simpa⟩

@[to_additive]
lemma Nontrivial.mul (hs : s.Nontrivial) (ht : t.Nontrivial) : (s * t).Nontrivial :=
  ht.mul_left hs.nonempty

end IsLeftCancelMul

section IsRightCancelMul
variable [Mul α] [IsRightCancelMul α] {s t : Set α}

@[to_additive]
lemma Nontrivial.mul_right : s.Nontrivial → t.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, mul_mem_mul ha hc, b * c, mul_mem_mul hb hc, by simpa⟩

end IsRightCancelMul

section CancelMonoid
variable [CancelMonoid α] {s t : Set α} {a : α} {n : ℕ}

@[to_additive]
lemma Nontrivial.pow (hs : s.Nontrivial) : ∀ {n}, n ≠ 0 → (s ^ n).Nontrivial
  | 1, _ => by simpa
  | n + 2, _ => by simpa [pow_succ] using (hs.pow n.succ_ne_zero).mul hs

end CancelMonoid

/-- `Set α` is a `CommMonoid` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddCommMonoid` under pointwise operations if `α` is."]
protected noncomputable def commMonoid [CommMonoid α] : CommMonoid (Set α) :=
  { Set.monoid, Set.commSemigroup with }

scoped[Pointwise] attribute [instance] Set.commMonoid Set.addCommMonoid

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Set α} {n : ℤ}

@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · have hst : (s * t).Nonempty := h.symm.subst one_nonempty
    obtain ⟨a, ha⟩ := hst.of_image2_left
    obtain ⟨b, hb⟩ := hst.of_image2_right
    have H : ∀ {a b}, a ∈ s → b ∈ t → a * b = (1 : α) := fun {a b} ha hb =>
      h.subset <| mem_image2_of_mem ha hb
    refine ⟨a, b, ?_, ?_, H ha hb⟩ <;> refine eq_singleton_iff_unique_mem.2 ⟨‹_›, fun x hx => ?_⟩
    · exact (eq_inv_of_mul_eq_one_left <| H hx hb).trans (inv_eq_of_mul_eq_one_left <| H ha hb)
    · exact (eq_inv_of_mul_eq_one_right <| H ha hx).trans (inv_eq_of_mul_eq_one_right <| H ha hb)
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [singleton_mul_singleton, h, singleton_one]

/-- `Set α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive
    "`Set α` is a subtraction monoid under pointwise operations if `α` is."]
protected noncomputable def divisionMonoid : DivisionMonoid (Set α) :=
  { Set.monoid, Set.involutiveInv, Set.div, @Set.ZPow α _ _ _ with
    mul_inv_rev := fun s t => by
      simp_rw [← image_inv_eq_inv]
      exact image_image2_antidistrib mul_inv_rev
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Set.mul_eq_one_iff.1 h
      rw [inv_singleton, inv_eq_of_mul_eq_one_right hab]
    div_eq_mul_inv := fun s t => by
      rw [← image_id (s / t), ← image_inv_eq_inv]
      exact image_image2_distrib_right div_eq_mul_inv }

scoped[Pointwise] attribute [instance] Set.divisionMonoid Set.subtractionMonoid

@[to_additive (attr := simp 500)]
theorem isUnit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Set.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, singleton_injective ?_⟩, rfl⟩
    rw [← singleton_mul_singleton, ← ha, ← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.set

@[to_additive (attr := simp)]
lemma univ_div_univ : (univ / univ : Set α) = univ := by simp [div_eq_mul_inv]

@[to_additive] lemma subset_div_left (ht : 1 ∈ t) : s ⊆ s / t := by
  rw [div_eq_mul_inv]; exact subset_mul_left _ <| by simpa

@[to_additive] lemma inv_subset_div_right (hs : 1 ∈ s) : t⁻¹ ⊆ s / t := by
  rw [div_eq_mul_inv]; exact subset_mul_right _ hs

@[to_additive (attr := simp) zsmul_empty]
lemma empty_zpow (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ := by cases n <;> aesop

@[to_additive]
lemma Nonempty.zpow (hs : s.Nonempty) : ∀ {n : ℤ}, (s ^ n).Nonempty
  | (n : ℕ) => hs.pow
  | .negSucc n => by simpa using hs.pow

set_option push_neg.use_distrib true in
@[to_additive (attr := simp)] lemma zpow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n ≠ 0 := by
  constructor
  · contrapose!
    rintro (hs | rfl)
    · exact hs.zpow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_zpow hn

@[to_additive (attr := simp) zsmul_singleton]
lemma singleton_zpow (a : α) (n : ℤ) : ({a} : Set α) ^ n = {a ^ n} := by cases n <;> simp

end DivisionMonoid

/-- `Set α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive subtractionCommMonoid
      "`Set α` is a commutative subtraction monoid under pointwise operations if `α` is."]
protected noncomputable def divisionCommMonoid [DivisionCommMonoid α] :
    DivisionCommMonoid (Set α) :=
  { Set.divisionMonoid, Set.commSemigroup with }

scoped[Pointwise] attribute [instance] Set.divisionCommMonoid Set.subtractionCommMonoid

section Group

variable [Group α] {s t : Set α} {a b : α}

/-! Note that `Set` is not a `Group` because `s / s ≠ 1` in general. -/


@[to_additive (attr := simp)]
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, Set.Nonempty]

@[to_additive (attr := simp)]
lemma one_mem_inv_mul_iff : (1 : α) ∈ t⁻¹ * s ↔ ¬Disjoint s t := by
  aesop (add simp [not_disjoint_iff_nonempty_inter, mem_mul, mul_eq_one_iff_eq_inv, Set.Nonempty])

@[to_additive]
theorem not_one_mem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left

@[to_additive]
lemma not_one_mem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t := one_mem_inv_mul_iff.not_left

alias ⟨_, _root_.Disjoint.one_not_mem_div_set⟩ := not_one_mem_div_iff

attribute [to_additive] Disjoint.one_not_mem_div_set

@[to_additive]
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

@[to_additive]
theorem isUnit_singleton (a : α) : IsUnit ({a} : Set α) :=
  (Group.isUnit a).set

@[to_additive (attr := simp)]
theorem isUnit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [isUnit_iff, Group.isUnit, and_true]

@[to_additive (attr := simp)]
theorem image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive (attr := simp)]
theorem image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive]
theorem image_mul_left' : (a⁻¹ * ·) '' t = (a * ·) ⁻¹' t := by simp

@[to_additive]
theorem image_mul_right' : (· * b⁻¹) '' t = (· * b) ⁻¹' t := by simp

@[to_additive (attr := simp)]
theorem preimage_mul_left_singleton : (a * ·) ⁻¹' {b} = {a⁻¹ * b} := by
  rw [← image_mul_left', image_singleton]

@[to_additive (attr := simp)]
theorem preimage_mul_right_singleton : (· * a) ⁻¹' {b} = {b * a⁻¹} := by
  rw [← image_mul_right', image_singleton]

@[to_additive (attr := simp)]
theorem preimage_mul_left_one : (a * ·) ⁻¹' 1 = {a⁻¹} := by
  rw [← image_mul_left', image_one, mul_one]

@[to_additive (attr := simp)]
theorem preimage_mul_right_one : (· * b) ⁻¹' 1 = {b⁻¹} := by
  rw [← image_mul_right', image_one, one_mul]

@[to_additive]
theorem preimage_mul_left_one' : (a⁻¹ * ·) ⁻¹' 1 = {a} := by simp

@[to_additive]
theorem preimage_mul_right_one' : (· * b⁻¹) ⁻¹' 1 = {b} := by simp

@[to_additive (attr := simp)]
theorem mul_univ (hs : s.Nonempty) : s * (univ : Set α) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ * b, trivial, mul_inv_cancel_left ..⟩

@[to_additive (attr := simp)]
theorem univ_mul (ht : t.Nonempty) : (univ : Set α) * t = univ :=
  let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, trivial, a, ha, inv_mul_cancel_right ..⟩

@[to_additive]
lemma image_inv [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β] (f : F) (s : Set α) :
    f '' s⁻¹ = (f '' s)⁻¹ := by
  rw [← image_inv_eq_inv, ← image_inv_eq_inv]; exact image_comm (map_inv _)

end Group

section Mul

variable [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β] (m : F) {s t : Set α}

@[to_additive]
theorem image_mul : m '' (s * t) = m '' s * m '' t :=
  image_image2_distrib <| map_mul m

@[to_additive]
lemma mul_subset_range {s t : Set β} (hs : s ⊆ range m) (ht : t ⊆ range m) : s * t ⊆ range m := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨a, rfl⟩ := hs ha
  obtain ⟨b, rfl⟩ := ht hb
  exact ⟨a * b, map_mul ..⟩

@[to_additive]
theorem preimage_mul_preimage_subset {s t : Set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_mul m ..).symm⟩

@[to_additive]
lemma preimage_mul (hm : Injective m) {s t : Set β} (hs : s ⊆ range m) (ht : t ⊆ range m) :
    m ⁻¹' (s * t) = m ⁻¹' s * m ⁻¹' t :=
  hm.image_injective <| by
    rw [image_mul, image_preimage_eq_iff.2 hs, image_preimage_eq_iff.2 ht,
      image_preimage_eq_iff.2 (mul_subset_range m hs ht)]

end Mul

section Monoid
variable [Monoid α] [Monoid β] [FunLike F α β]

@[to_additive]
lemma image_pow_of_ne_zero [MulHomClass F α β] :
    ∀ {n}, n ≠ 0 → ∀ (f : F) (s : Set α), f '' (s ^ n) = (f '' s) ^ n
  | 1, _ => by simp
  | n + 2, _ => by simp [image_mul, pow_succ _ n.succ, image_pow_of_ne_zero]

@[to_additive]
lemma image_pow [MonoidHomClass F α β] (f : F) (s : Set α) : ∀ n, f '' (s ^ n) = (f '' s) ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => image_pow_of_ne_zero n.succ_ne_zero ..

end Monoid

section Group

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β] (m : F) {s t : Set α}

@[to_additive]
theorem image_div : m '' (s / t) = m '' s / m '' t :=
  image_image2_distrib <| map_div m

@[to_additive]
lemma div_subset_range {s t : Set β} (hs : s ⊆ range m) (ht : t ⊆ range m) : s / t ⊆ range m := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨a, rfl⟩ := hs ha
  obtain ⟨b, rfl⟩ := ht hb
  exact ⟨a / b, map_div ..⟩

@[to_additive]
theorem preimage_div_preimage_subset {s t : Set β} : m ⁻¹' s / m ⁻¹' t ⊆ m ⁻¹' (s / t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_div m ..).symm⟩

@[to_additive]
lemma preimage_div (hm : Injective m) {s t : Set β} (hs : s ⊆ range m) (ht : t ⊆ range m) :
    m ⁻¹' (s / t) = m ⁻¹' s / m ⁻¹' t :=
  hm.image_injective <| by
    rw [image_div, image_preimage_eq_iff.2 hs, image_preimage_eq_iff.2 ht,
      image_preimage_eq_iff.2 (div_subset_range m hs ht)]

end Group

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
"An additive action of an additive monoid `α` on a type `β` gives an additive action of `Set α`
on `Set β`"]
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
theorem smul_set_subset_smul_set_iff : a • A ⊆ a • B ↔ A ⊆ B :=
  image_subset_image_iff <| MulAction.injective _

@[deprecated (since := "2024-12-28")]
alias set_smul_subset_set_smul_iff := smul_set_subset_smul_set_iff

@[to_additive]
theorem smul_set_subset_iff_subset_inv_smul_set : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  image_subset_iff.trans <|
    iff_of_eq <| congr_arg _ <| preimage_equiv_eq_image_symm _ <| MulAction.toPerm _

@[deprecated (since := "2024-12-28")]
alias set_smul_subset_iff := smul_set_subset_iff_subset_inv_smul_set

@[to_additive]
theorem subset_smul_set_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  Iff.symm <|
    image_subset_iff.trans <|
      Iff.symm <| iff_of_eq <| congr_arg _ <| image_equiv_eq_preimage_symm _ <| MulAction.toPerm _

@[deprecated (since := "2024-12-28")] alias subset_set_smul_iff := subset_smul_set_iff

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
  simpa only [smul_inv_smul a t] using disjoint_smul_set (a := a) (t := a⁻¹ • t)

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

section Pi

variable {ι : Type*} {α : ι → Type*} [∀ i, Inv (α i)]

@[to_additive (attr := simp)]
lemma inv_pi (s : Set ι) (t : ∀ i, Set (α i)) : (s.pi t)⁻¹ = s.pi fun i ↦ (t i)⁻¹ := by ext x; simp

end Pi

section Pointwise

open scoped Pointwise

@[to_additive]
lemma MapsTo.mul [Mul β] {A : Set α} {B₁ B₂ : Set β} {f₁ f₂ : α → β}
    (h₁ : MapsTo f₁ A B₁) (h₂ : MapsTo f₂ A B₂) : MapsTo (f₁ * f₂) A (B₁ * B₂) :=
  fun _ h => mul_mem_mul (h₁ h) (h₂ h)

@[to_additive]
lemma MapsTo.inv [DivisionCommMonoid β] {A : Set α} {B : Set β} {f : α → β} (h : MapsTo f A B) :
    MapsTo (f⁻¹) A (B⁻¹) :=
  fun _ ha => inv_mem_inv.2 (h ha)


@[to_additive]
lemma MapsTo.div [DivisionCommMonoid β] {A : Set α} {B₁ B₂ : Set β} {f₁ f₂ : α → β}
    (h₁ : MapsTo f₁ A B₁) (h₂ : MapsTo f₂ A B₂) : MapsTo (f₁ / f₂) A (B₁ / B₂) :=
  fun _ ha => div_mem_div (h₁ ha) (h₂ ha)

end Pointwise

end Set

set_option linter.style.longFile 2000
