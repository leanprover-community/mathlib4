/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Common

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


assert_not_exists OrderedAddCommMonoid

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


open Function

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

@[to_additive]
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

end One

/-! ### Set negation/inversion -/


section Inv

/-- The pointwise inversion of set `s⁻¹` is defined as `{x | x⁻¹ ∈ s}` in locale `Pointwise`. It is
equal to `{x⁻¹ | x ∈ s}`, see `Set.image_inv`. -/
@[to_additive
      "The pointwise negation of set `-s` is defined as `{x | -x ∈ s}` in locale `Pointwise`.
      It is equal to `{-x | x ∈ s}`, see `Set.image_neg`."]
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
theorem iUnion_inv (s : ι → Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
  preimage_iUnion

@[to_additive (attr := simp)]
theorem compl_inv : sᶜ⁻¹ = s⁻¹ᶜ :=
  preimage_compl

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
theorem image_inv : Inv.inv '' s = s⁻¹ :=
  congr_fun (image_eq_preimage_of_inverse inv_involutive.leftInverse inv_involutive.rightInverse) _

@[to_additive (attr := simp)]
theorem inv_eq_empty : s⁻¹ = ∅ ↔ s = ∅ := by
  rw [← image_inv, image_eq_empty]

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
theorem inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹} := by rw [← image_inv, image_singleton]

@[to_additive (attr := simp)]
theorem inv_insert (a : α) (s : Set α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ := by
  rw [insert_eq, union_inv, inv_singleton, insert_eq]

@[to_additive]
theorem inv_range {ι : Sort*} {f : ι → α} : (range f)⁻¹ = range fun i => (f i)⁻¹ := by
  rw [← image_inv]
  exact (range_comp _ _).symm

open MulOpposite

@[to_additive]
theorem image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ := by
  simp_rw [← image_inv, Function.Semiconj.set_image op_inv s]

end InvolutiveInv

end Inv

open Pointwise

/-! ### Set addition/multiplication -/


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

-- Porting note (#10618): simp can prove this
@[to_additive]
theorem singleton_mul_singleton : ({a} : Set α) * {b} = {a * b} :=
  image2_singleton

@[to_additive (attr := mono)]
theorem mul_subset_mul : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ * s₂ ⊆ t₁ * t₂ :=
  image2_subset

@[to_additive]
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image2_subset_left

@[to_additive]
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image2_subset_right

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
  image2_iUnion_left _ _ _

@[to_additive]
theorem mul_iUnion (s : Set α) (t : ι → Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i :=
  image2_iUnion_right _ _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iUnion₂_mul (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t :=
  image2_iUnion₂_left _ _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋃ (i) (j), t i j) = ⋃ (i) (j), s * t i j :=
  image2_iUnion₂_right _ _ _

@[to_additive]
theorem iInter_mul_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
  Set.image2_iInter_subset_left _ _ _

@[to_additive]
theorem mul_iInter_subset (s : Set α) (t : ι → Set α) : (s * ⋂ i, t i) ⊆ ⋂ i, s * t i :=
  image2_iInter_subset_right _ _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iInter₂_mul_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) * t ⊆ ⋂ (i) (j), s i j * t :=
  image2_iInter₂_subset_left _ _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s * t i j :=
  image2_iInter₂_subset_right _ _ _

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

open MulOpposite

@[to_additive (attr := simp)]
theorem image_op_mul : op '' (s * t) = op '' t * op '' s :=
  image_image2_antidistrib op_mul

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

-- Porting note (#10618): simp can prove this
@[to_additive]
theorem singleton_div_singleton : ({a} : Set α) / {b} = {a / b} :=
  image2_singleton

@[to_additive (attr := mono)]
theorem div_subset_div : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ / s₂ ⊆ t₁ / t₂ :=
  image2_subset

@[to_additive]
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image2_subset_left

@[to_additive]
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
  image2_iUnion_left _ _ _

@[to_additive]
theorem div_iUnion (s : Set α) (t : ι → Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i :=
  image2_iUnion_right _ _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iUnion₂_div (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) / t = ⋃ (i) (j), s i j / t :=
  image2_iUnion₂_left _ _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋃ (i) (j), t i j) = ⋃ (i) (j), s / t i j :=
  image2_iUnion₂_right _ _ _

@[to_additive]
theorem iInter_div_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
  image2_iInter_subset_left _ _ _

@[to_additive]
theorem div_iInter_subset (s : Set α) (t : ι → Set α) : (s / ⋂ i, t i) ⊆ ⋂ i, s / t i :=
  image2_iInter_subset_right _ _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iInter₂_div_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) / t ⊆ ⋂ (i) (j), s i j / t :=
  image2_iInter₂_subset_left _ _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s / t i j :=
  image2_iInter₂_subset_right _ _ _

end Div

open Pointwise

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

section Monoid

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

/-- `Set α` is a `Monoid` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddMonoid` under pointwise operations if `α` is."]
protected noncomputable def monoid : Monoid (Set α) :=
  { Set.semigroup, Set.mulOneClass, @Set.NPow α _ _ with }

scoped[Pointwise] attribute [instance] Set.monoid Set.addMonoid

@[to_additive]
theorem pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
  | 0 => by
    simp only [pow_zero, mem_one]
  | n + 1 => by
    simp only [pow_succ]
    exact mul_mem_mul (pow_mem_pow ha _) ha

@[to_additive]
theorem pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
  | 0 => by
    rw [pow_zero]
    exact Subset.rfl
  | n + 1 => by
    rw [pow_succ]
    exact mul_subset_mul (pow_subset_pow hst _) hst

@[to_additive]
theorem pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) (hn : m ≤ n) : s ^ m ⊆ s ^ n := by
  -- Porting note: `Nat.le_induction` didn't work as an induction principle in mathlib3, this was
  -- `refine Nat.le_induction ...`
  induction' n, hn using Nat.le_induction with _ _ ih
  · exact Subset.rfl
  · dsimp only
    rw [pow_succ']
    exact ih.trans (subset_mul_right _ hs)

@[to_additive (attr := simp)]
theorem empty_pow {n : ℕ} (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ := by
  match n with
  | n + 1 => rw [pow_succ', empty_mul]

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

end Monoid

/-- `Set α` is a `CommMonoid` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddCommMonoid` under pointwise operations if `α` is."]
protected noncomputable def commMonoid [CommMonoid α] : CommMonoid (Set α) :=
  { Set.monoid, Set.commSemigroup with }

scoped[Pointwise] attribute [instance] Set.commMonoid Set.addCommMonoid

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Set α}

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
      simp_rw [← image_inv]
      exact image_image2_antidistrib mul_inv_rev
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Set.mul_eq_one_iff.1 h
      rw [inv_singleton, inv_eq_of_mul_eq_one_right hab]
    div_eq_mul_inv := fun s t => by
      rw [← image_id (s / t), ← image_inv]
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

end DivisionMonoid

/-- `Set α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive subtractionCommMonoid
      "`Set α` is a commutative subtraction monoid under pointwise operations if `α` is."]
protected noncomputable def divisionCommMonoid [DivisionCommMonoid α] :
    DivisionCommMonoid (Set α) :=
  { Set.divisionMonoid, Set.commSemigroup with }

/-- `Set α` has distributive negation if `α` has. -/
protected noncomputable def hasDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Set α) :=
  { Set.involutiveNeg with
    neg_mul := fun _ _ => by
      simp_rw [← image_neg]
      exact image2_image_left_comm neg_mul
    mul_neg := fun _ _ => by
      simp_rw [← image_neg]
      exact image_image2_right_comm mul_neg }

scoped[Pointwise]
  attribute [instance] Set.divisionCommMonoid Set.subtractionCommMonoid Set.hasDistribNeg

section Distrib

variable [Distrib α] (s t u : Set α)

/-!
Note that `Set α` is not a `Distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.
-/


theorem mul_add_subset : s * (t + u) ⊆ s * t + s * u :=
  image2_distrib_subset_left mul_add

theorem add_mul_subset : (s + t) * u ⊆ s * u + t * u :=
  image2_distrib_subset_right add_mul

end Distrib

section MulZeroClass

variable [MulZeroClass α] {s t : Set α}

/-! Note that `Set` is not a `MulZeroClass` because `0 * ∅ ≠ 0`. -/


theorem mul_zero_subset (s : Set α) : s * 0 ⊆ 0 := by simp [subset_def, mem_mul]

theorem zero_mul_subset (s : Set α) : 0 * s ⊆ 0 := by simp [subset_def, mem_mul]

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by simpa [mem_mul] using hs

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by simpa [mem_mul] using hs

end MulZeroClass

section Group

variable [Group α] {s t : Set α} {a b : α}

/-! Note that `Set` is not a `Group` because `s / s ≠ 1` in general. -/


@[to_additive (attr := simp)]
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, Set.Nonempty]

@[to_additive]
theorem not_one_mem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left

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
  simp only [isUnit_iff, Group.isUnit, and_true_iff]

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
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ * b, trivial, mul_inv_cancel_left _ _⟩

@[to_additive (attr := simp)]
theorem univ_mul (ht : t.Nonempty) : (univ : Set α) * t = univ :=
  let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, trivial, a, ha, inv_mul_cancel_right _ _⟩

end Group

section GroupWithZero

variable [GroupWithZero α] {s t : Set α}

theorem div_zero_subset (s : Set α) : s / 0 ⊆ 0 := by simp [subset_def, mem_div]

theorem zero_div_subset (s : Set α) : 0 / s ⊆ 0 := by simp [subset_def, mem_div]

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by simpa [mem_div] using hs

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by simpa [mem_div] using hs

end GroupWithZero

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
  exact ⟨a * b, map_mul _ _ _⟩

@[to_additive]
theorem preimage_mul_preimage_subset {s t : Set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_mul m _ _).symm⟩

@[to_additive]
lemma preimage_mul (hm : Injective m) {s t : Set β} (hs : s ⊆ range m) (ht : t ⊆ range m) :
    m ⁻¹' (s * t) = m ⁻¹' s * m ⁻¹' t :=
  hm.image_injective <| by
    rw [image_mul, image_preimage_eq_iff.2 hs, image_preimage_eq_iff.2 ht,
      image_preimage_eq_iff.2 (mul_subset_range m hs ht)]

end Mul

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
  exact ⟨a / b, map_div _ _ _⟩

@[to_additive]
theorem preimage_div_preimage_subset {s t : Set β} : m ⁻¹' s / m ⁻¹' t ⊆ m ⁻¹' (s / t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_div m _ _).symm⟩

@[to_additive]
lemma preimage_div (hm : Injective m) {s t : Set β} (hs : s ⊆ range m) (ht : t ⊆ range m) :
    m ⁻¹' (s / t) = m ⁻¹' s / m ⁻¹' t :=
  hm.image_injective <| by
    rw [image_div, image_preimage_eq_iff.2 hs, image_preimage_eq_iff.2 ht,
      image_preimage_eq_iff.2 (div_subset_range m hs ht)]

end Group

end Set

/-! ### Miscellaneous -/


open Set

open Pointwise

namespace Group

@[to_additive]
theorem card_pow_eq_card_pow_card_univ_aux {f : ℕ → ℕ} (h1 : Monotone f) {B : ℕ} (h2 : ∀ n, f n ≤ B)
    (h3 : ∀ n, f n = f (n + 1) → f (n + 1) = f (n + 2)) : ∀ k, B ≤ k → f k = f B := by
  have key : ∃ n : ℕ, n ≤ B ∧ f n = f (n + 1) := by
    contrapose! h2
    suffices ∀ n : ℕ, n ≤ B + 1 → n ≤ f n by exact ⟨B + 1, this (B + 1) (le_refl (B + 1))⟩
    exact fun n =>
      Nat.rec (fun _ => Nat.zero_le (f 0))
        (fun n ih h =>
          lt_of_le_of_lt (ih (n.le_succ.trans h))
            (lt_of_le_of_ne (h1 n.le_succ) (h2 n (Nat.succ_le_succ_iff.mp h))))
        n
  obtain ⟨n, hn1, hn2⟩ := key
  replace key : ∀ k : ℕ, f (n + k) = f (n + k + 1) ∧ f (n + k) = f n := fun k =>
    Nat.rec ⟨hn2, rfl⟩ (fun k ih => ⟨h3 _ ih.1, ih.1.symm.trans ih.2⟩) k
  replace key : ∀ k : ℕ, n ≤ k → f k = f n := fun k hk =>
    (congr_arg f (Nat.add_sub_of_le hk)).symm.trans (key (k - n)).2
  exact fun k hk => (key k (hn1.trans hk)).trans (key B hn1).symm

end Group
