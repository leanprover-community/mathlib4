/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Algebra.Hom.Units
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Order.Basic

#align_import data.set.pointwise.basic from "leanprover-community/mathlib"@"5e526d18cea33550268dcbbddcb822d5cde40654"

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
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : Set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `Pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/


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
#align set.has_one Set.one
#align set.has_zero Set.zero

scoped[Pointwise] attribute [instance] Set.one Set.zero

open Pointwise

@[to_additive]
theorem singleton_one : ({1} : Set α) = 1 :=
  rfl
#align set.singleton_one Set.singleton_one
#align set.singleton_zero Set.singleton_zero

@[to_additive (attr := simp)]
theorem mem_one : a ∈ (1 : Set α) ↔ a = 1 :=
  Iff.rfl
#align set.mem_one Set.mem_one
#align set.mem_zero Set.mem_zero

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Set α) :=
  Eq.refl _
#align set.one_mem_one Set.one_mem_one
#align set.zero_mem_zero Set.zero_mem_zero

@[to_additive (attr := simp)]
theorem one_subset : 1 ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff
#align set.one_subset Set.one_subset
#align set.zero_subset Set.zero_subset

@[to_additive]
theorem one_nonempty : (1 : Set α).Nonempty :=
  ⟨1, rfl⟩
#align set.one_nonempty Set.one_nonempty
#align set.zero_nonempty Set.zero_nonempty

@[to_additive (attr := simp)]
theorem image_one {f : α → β} : f '' 1 = {f 1} :=
  image_singleton
#align set.image_one Set.image_one
#align set.image_zero Set.image_zero

@[to_additive]
theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff_eq
#align set.subset_one_iff_eq Set.subset_one_iff_eq
#align set.subset_zero_iff_eq Set.subset_zero_iff_eq

@[to_additive]
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 :=
  h.subset_singleton_iff
#align set.nonempty.subset_one_iff Set.Nonempty.subset_one_iff
#align set.nonempty.subset_zero_iff Set.Nonempty.subset_zero_iff

/-- The singleton operation as a `OneHom`. -/
@[to_additive "The singleton operation as a `ZeroHom`."]
noncomputable def singletonOneHom : OneHom α (Set α) :=
  ⟨singleton, singleton_one⟩
#align set.singleton_one_hom Set.singletonOneHom
#align set.singleton_zero_hom Set.singletonZeroHom

@[to_additive (attr := simp)]
theorem coe_singletonOneHom : (singletonOneHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_one_hom Set.coe_singletonOneHom
#align set.coe_singleton_zero_hom Set.coe_singletonZeroHom

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
#align set.has_inv Set.inv
#align set.has_neg Set.neg

scoped[Pointwise] attribute [instance] Set.inv Set.neg

open Pointwise

section Inv

variable {ι : Sort*} [Inv α] {s t : Set α} {a : α}

@[to_additive (attr := simp)]
theorem mem_inv : a ∈ s⁻¹ ↔ a⁻¹ ∈ s :=
  Iff.rfl
#align set.mem_inv Set.mem_inv
#align set.mem_neg Set.mem_neg

@[to_additive (attr := simp)]
theorem inv_preimage : Inv.inv ⁻¹' s = s⁻¹ :=
  rfl
#align set.inv_preimage Set.inv_preimage
#align set.neg_preimage Set.neg_preimage

@[to_additive (attr := simp)]
theorem inv_empty : (∅ : Set α)⁻¹ = ∅ :=
  rfl
#align set.inv_empty Set.inv_empty
#align set.neg_empty Set.neg_empty

@[to_additive (attr := simp)]
theorem inv_univ : (univ : Set α)⁻¹ = univ :=
  rfl
#align set.inv_univ Set.inv_univ
#align set.neg_univ Set.neg_univ

@[to_additive (attr := simp)]
theorem inter_inv : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ :=
  preimage_inter
#align set.inter_inv Set.inter_inv
#align set.inter_neg Set.inter_neg

@[to_additive (attr := simp)]
theorem union_inv : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ :=
  preimage_union
#align set.union_inv Set.union_inv
#align set.union_neg Set.union_neg

@[to_additive (attr := simp)]
theorem iInter_inv (s : ι → Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ :=
  preimage_iInter
#align set.Inter_inv Set.iInter_inv
#align set.Inter_neg Set.iInter_neg

@[to_additive (attr := simp)]
theorem iUnion_inv (s : ι → Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
  preimage_iUnion
#align set.Union_inv Set.iUnion_inv
#align set.Union_neg Set.iUnion_neg

@[to_additive (attr := simp)]
theorem compl_inv : sᶜ⁻¹ = s⁻¹ᶜ :=
  preimage_compl
#align set.compl_inv Set.compl_inv
#align set.compl_neg Set.compl_neg

end Inv

section InvolutiveInv

variable [InvolutiveInv α] {s t : Set α} {a : α}

@[to_additive]
theorem inv_mem_inv : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by simp only [mem_inv, inv_inv]
                                              -- 🎉 no goals
#align set.inv_mem_inv Set.inv_mem_inv
#align set.neg_mem_neg Set.neg_mem_neg

@[to_additive (attr := simp)]
theorem nonempty_inv : s⁻¹.Nonempty ↔ s.Nonempty :=
  inv_involutive.surjective.nonempty_preimage
#align set.nonempty_inv Set.nonempty_inv
#align set.nonempty_neg Set.nonempty_neg

@[to_additive]
theorem Nonempty.inv (h : s.Nonempty) : s⁻¹.Nonempty :=
  nonempty_inv.2 h
#align set.nonempty.inv Set.Nonempty.inv
#align set.nonempty.neg Set.Nonempty.neg

@[to_additive (attr := simp)]
theorem image_inv : Inv.inv '' s = s⁻¹ :=
  congr_fun (image_eq_preimage_of_inverse inv_involutive.leftInverse inv_involutive.rightInverse) _
#align set.image_inv Set.image_inv
#align set.image_neg Set.image_neg

@[to_additive (attr := simp)]
noncomputable instance involutiveInv : InvolutiveInv (Set α) where
  inv := Inv.inv
  inv_inv s := by simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id']
                  -- 🎉 no goals

@[to_additive (attr := simp)]
theorem inv_subset_inv : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
  (Equiv.inv α).surjective.preimage_subset_preimage_iff
#align set.inv_subset_inv Set.inv_subset_inv
#align set.neg_subset_neg Set.neg_subset_neg

@[to_additive]
theorem inv_subset : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by rw [← inv_subset_inv, inv_inv]
                                             -- 🎉 no goals
#align set.inv_subset Set.inv_subset
#align set.neg_subset Set.neg_subset

@[to_additive (attr := simp)]
theorem inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹} := by rw [← image_inv, image_singleton]
                                                              -- 🎉 no goals
#align set.inv_singleton Set.inv_singleton
#align set.neg_singleton Set.neg_singleton

@[to_additive (attr := simp)]
theorem inv_insert (a : α) (s : Set α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ := by
  rw [insert_eq, union_inv, inv_singleton, insert_eq]
  -- 🎉 no goals
#align set.inv_insert Set.inv_insert
#align set.neg_insert Set.neg_insert

@[to_additive]
theorem inv_range {ι : Sort*} {f : ι → α} : (range f)⁻¹ = range fun i => (f i)⁻¹ := by
  rw [← image_inv]
  -- ⊢ Inv.inv '' range f = range fun i => (f i)⁻¹
  exact (range_comp _ _).symm
  -- 🎉 no goals
#align set.inv_range Set.inv_range
#align set.neg_range Set.neg_range

open MulOpposite

@[to_additive]
theorem image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ := by
  simp_rw [← image_inv, Function.Semiconj.set_image op_inv s]
  -- 🎉 no goals
#align set.image_op_inv Set.image_op_inv
#align set.image_op_neg Set.image_op_neg

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
#align set.has_mul Set.mul
#align set.has_add Set.add

scoped[Pointwise] attribute [instance] Set.mul Set.add

@[to_additive (attr := simp)]
theorem image2_mul : image2 (· * ·) s t = s * t :=
  rfl
#align set.image2_mul Set.image2_mul
#align set.image2_add Set.image2_add

@[to_additive]
theorem mem_mul : a ∈ s * t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x * y = a :=
  Iff.rfl
#align set.mem_mul Set.mem_mul
#align set.mem_add Set.mem_add

@[to_additive]
theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t :=
  mem_image2_of_mem
#align set.mul_mem_mul Set.mul_mem_mul
#align set.add_mem_add Set.add_mem_add

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive add_image_prod]
theorem image_mul_prod : (fun x : α × α => x.fst * x.snd) '' s ×ˢ t = s * t :=
  image_prod _
#align set.image_mul_prod Set.image_mul_prod
#align set.add_image_prod Set.add_image_prod

@[to_additive (attr := simp)]
theorem empty_mul : ∅ * s = ∅ :=
  image2_empty_left
#align set.empty_mul Set.empty_mul
#align set.empty_add Set.empty_add

@[to_additive (attr := simp)]
theorem mul_empty : s * ∅ = ∅ :=
  image2_empty_right
#align set.mul_empty Set.mul_empty
#align set.add_empty Set.add_empty

@[to_additive (attr := simp)]
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.mul_eq_empty Set.mul_eq_empty
#align set.add_eq_empty Set.add_eq_empty

@[to_additive (attr := simp)]
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.mul_nonempty Set.mul_nonempty
#align set.add_nonempty Set.add_nonempty

@[to_additive]
theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  Nonempty.image2
#align set.nonempty.mul Set.Nonempty.mul
#align set.nonempty.add Set.Nonempty.add

@[to_additive]
theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_mul_left Set.Nonempty.of_mul_left
#align set.nonempty.of_add_left Set.Nonempty.of_add_left

@[to_additive]
theorem Nonempty.of_mul_right : (s * t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_mul_right Set.Nonempty.of_mul_right
#align set.nonempty.of_add_right Set.Nonempty.of_add_right

@[to_additive (attr := simp)]
theorem mul_singleton : s * {b} = (· * b) '' s :=
  image2_singleton_right
#align set.mul_singleton Set.mul_singleton
#align set.add_singleton Set.add_singleton

@[to_additive (attr := simp)]
theorem singleton_mul : {a} * t = (· * ·) a '' t :=
  image2_singleton_left
#align set.singleton_mul Set.singleton_mul
#align set.singleton_add Set.singleton_add

-- Porting note: simp can prove this
@[to_additive]
theorem singleton_mul_singleton : ({a} : Set α) * {b} = {a * b} :=
  image2_singleton
#align set.singleton_mul_singleton Set.singleton_mul_singleton
#align set.singleton_add_singleton Set.singleton_add_singleton

@[to_additive (attr := mono)]
theorem mul_subset_mul : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ * s₂ ⊆ t₁ * t₂ :=
  image2_subset
#align set.mul_subset_mul Set.mul_subset_mul
#align set.add_subset_add Set.add_subset_add

@[to_additive]
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image2_subset_left
#align set.mul_subset_mul_left Set.mul_subset_mul_left
#align set.add_subset_add_left Set.add_subset_add_left

@[to_additive]
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image2_subset_right
#align set.mul_subset_mul_right Set.mul_subset_mul_right
#align set.add_subset_add_right Set.add_subset_add_right

@[to_additive]
theorem mul_subset_iff : s * t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x * y ∈ u :=
  image2_subset_iff
#align set.mul_subset_iff Set.mul_subset_iff
#align set.add_subset_iff Set.add_subset_iff

@[to_additive]
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image2_union_left
#align set.union_mul Set.union_mul
#align set.union_add Set.union_add

@[to_additive]
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image2_union_right
#align set.mul_union Set.mul_union
#align set.add_union Set.add_union

@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image2_inter_subset_left
#align set.inter_mul_subset Set.inter_mul_subset
#align set.inter_add_subset Set.inter_add_subset

@[to_additive]
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image2_inter_subset_right
#align set.mul_inter_subset Set.mul_inter_subset
#align set.add_inter_subset Set.add_inter_subset

@[to_additive]
theorem inter_mul_union_subset_union : s₁ ∩ s₂ * (t₁ ∪ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ :=
  image2_inter_union_subset_union
#align set.inter_mul_union_subset_union Set.inter_mul_union_subset_union
#align set.inter_add_union_subset_union Set.inter_add_union_subset_union

@[to_additive]
theorem union_mul_inter_subset_union : (s₁ ∪ s₂) * (t₁ ∩ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ :=
  image2_union_inter_subset_union
#align set.union_mul_inter_subset_union Set.union_mul_inter_subset_union
#align set.union_add_inter_subset_union Set.union_add_inter_subset_union

@[to_additive]
theorem iUnion_mul_left_image : ⋃ a ∈ s, (· * ·) a '' t = s * t :=
  iUnion_image_left _
#align set.Union_mul_left_image Set.iUnion_mul_left_image
#align set.Union_add_left_image Set.iUnion_add_left_image

@[to_additive]
theorem iUnion_mul_right_image : ⋃ a ∈ t, (· * a) '' s = s * t :=
  iUnion_image_right _
#align set.Union_mul_right_image Set.iUnion_mul_right_image
#align set.Union_add_right_image Set.iUnion_add_right_image

@[to_additive]
theorem iUnion_mul (s : ι → Set α) (t : Set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
  image2_iUnion_left _ _ _
#align set.Union_mul Set.iUnion_mul
#align set.Union_add Set.iUnion_add

@[to_additive]
theorem mul_iUnion (s : Set α) (t : ι → Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i :=
  image2_iUnion_right _ _ _
#align set.mul_Union Set.mul_iUnion
#align set.add_Union Set.add_iUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iUnion₂_mul (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t :=
  image2_iUnion₂_left _ _ _
#align set.Union₂_mul Set.iUnion₂_mul
#align set.Union₂_add Set.iUnion₂_add

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋃ (i) (j), t i j) = ⋃ (i) (j), s * t i j :=
  image2_iUnion₂_right _ _ _
#align set.mul_Union₂ Set.mul_iUnion₂
#align set.add_Union₂ Set.add_iUnion₂

@[to_additive]
theorem iInter_mul_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
  image2_iInter_subset_left _ _ _
#align set.Inter_mul_subset Set.iInter_mul_subset
#align set.Inter_add_subset Set.iInter_add_subset

@[to_additive]
theorem mul_iInter_subset (s : Set α) (t : ι → Set α) : (s * ⋂ i, t i) ⊆ ⋂ i, s * t i :=
  image2_iInter_subset_right _ _ _
#align set.mul_Inter_subset Set.mul_iInter_subset
#align set.add_Inter_subset Set.add_iInter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iInter₂_mul_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) * t ⊆ ⋂ (i) (j), s i j * t :=
  image2_iInter₂_subset_left _ _ _
#align set.Inter₂_mul_subset Set.iInter₂_mul_subset
#align set.Inter₂_add_subset Set.iInter₂_add_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s * t i j :=
  image2_iInter₂_subset_right _ _ _
#align set.mul_Inter₂_subset Set.mul_iInter₂_subset
#align set.add_Inter₂_subset Set.add_iInter₂_subset

/-- The singleton operation as a `MulHom`. -/
@[to_additive "The singleton operation as an `AddHom`."]
noncomputable def singletonMulHom : α →ₙ* Set α :=
  ⟨singleton, fun _ _ => singleton_mul_singleton.symm⟩
#align set.singleton_mul_hom Set.singletonMulHom
#align set.singleton_add_hom Set.singletonAddHom

@[to_additive (attr := simp)]
theorem coe_singletonMulHom : (singletonMulHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_mul_hom Set.coe_singletonMulHom
#align set.coe_singleton_add_hom Set.coe_singletonAddHom

@[to_additive (attr := simp)]
theorem singletonMulHom_apply (a : α) : singletonMulHom a = {a} :=
  rfl
#align set.singleton_mul_hom_apply Set.singletonMulHom_apply
#align set.singleton_add_hom_apply Set.singletonAddHom_apply

open MulOpposite

@[to_additive (attr := simp)]
theorem image_op_mul : op '' (s * t) = op '' t * op '' s :=
  image_image2_antidistrib op_mul
#align set.image_op_mul Set.image_op_mul
#align set.image_op_add Set.image_op_add

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
#align set.has_div Set.div
#align set.has_sub Set.sub

scoped[Pointwise] attribute [instance] Set.div Set.sub

@[to_additive (attr := simp)]
theorem image2_div : image2 Div.div s t = s / t :=
  rfl
#align set.image2_div Set.image2_div
#align set.image2_sub Set.image2_sub

@[to_additive]
theorem mem_div : a ∈ s / t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x / y = a :=
  Iff.rfl
#align set.mem_div Set.mem_div
#align set.mem_sub Set.mem_sub

@[to_additive]
theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t :=
  mem_image2_of_mem
#align set.div_mem_div Set.div_mem_div
#align set.sub_mem_sub Set.sub_mem_sub

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive sub_image_prod]
theorem image_div_prod : (fun x : α × α => x.fst / x.snd) '' s ×ˢ t = s / t :=
  image_prod _
#align set.image_div_prod Set.image_div_prod
#align set.sub_image_prod Set.sub_image_prod

@[to_additive (attr := simp)]
theorem empty_div : ∅ / s = ∅ :=
  image2_empty_left
#align set.empty_div Set.empty_div
#align set.empty_sub Set.empty_sub

@[to_additive (attr := simp)]
theorem div_empty : s / ∅ = ∅ :=
  image2_empty_right
#align set.div_empty Set.div_empty
#align set.sub_empty Set.sub_empty

@[to_additive (attr := simp)]
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.div_eq_empty Set.div_eq_empty
#align set.sub_eq_empty Set.sub_eq_empty

@[to_additive (attr := simp)]
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.div_nonempty Set.div_nonempty
#align set.sub_nonempty Set.sub_nonempty

@[to_additive]
theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty :=
  Nonempty.image2
#align set.nonempty.div Set.Nonempty.div
#align set.nonempty.sub Set.Nonempty.sub

@[to_additive]
theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_div_left Set.Nonempty.of_div_left
#align set.nonempty.of_sub_left Set.Nonempty.of_sub_left

@[to_additive]
theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_div_right Set.Nonempty.of_div_right
#align set.nonempty.of_sub_right Set.Nonempty.of_sub_right

@[to_additive (attr := simp)]
theorem div_singleton : s / {b} = (· / b) '' s :=
  image2_singleton_right
#align set.div_singleton Set.div_singleton
#align set.sub_singleton Set.sub_singleton

@[to_additive (attr := simp)]
theorem singleton_div : {a} / t = (· / ·) a '' t :=
  image2_singleton_left
#align set.singleton_div Set.singleton_div
#align set.singleton_sub Set.singleton_sub

-- Porting note: simp can prove this
@[to_additive]
theorem singleton_div_singleton : ({a} : Set α) / {b} = {a / b} :=
  image2_singleton
#align set.singleton_div_singleton Set.singleton_div_singleton
#align set.singleton_sub_singleton Set.singleton_sub_singleton

@[to_additive (attr := mono)]
theorem div_subset_div : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ / s₂ ⊆ t₁ / t₂ :=
  image2_subset
#align set.div_subset_div Set.div_subset_div
#align set.sub_subset_sub Set.sub_subset_sub

@[to_additive]
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image2_subset_left
#align set.div_subset_div_left Set.div_subset_div_left
#align set.sub_subset_sub_left Set.sub_subset_sub_left

@[to_additive]
theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t :=
  image2_subset_right
#align set.div_subset_div_right Set.div_subset_div_right
#align set.sub_subset_sub_right Set.sub_subset_sub_right

@[to_additive]
theorem div_subset_iff : s / t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x / y ∈ u :=
  image2_subset_iff
#align set.div_subset_iff Set.div_subset_iff
#align set.sub_subset_iff Set.sub_subset_iff

@[to_additive]
theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t :=
  image2_union_left
#align set.union_div Set.union_div
#align set.union_sub Set.union_sub

@[to_additive]
theorem div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ :=
  image2_union_right
#align set.div_union Set.div_union
#align set.sub_union Set.sub_union

@[to_additive]
theorem inter_div_subset : s₁ ∩ s₂ / t ⊆ s₁ / t ∩ (s₂ / t) :=
  image2_inter_subset_left
#align set.inter_div_subset Set.inter_div_subset
#align set.inter_sub_subset Set.inter_sub_subset

@[to_additive]
theorem div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
  image2_inter_subset_right
#align set.div_inter_subset Set.div_inter_subset
#align set.sub_inter_subset Set.sub_inter_subset

@[to_additive]
theorem inter_div_union_subset_union : s₁ ∩ s₂ / (t₁ ∪ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ :=
  image2_inter_union_subset_union
#align set.inter_div_union_subset_union Set.inter_div_union_subset_union
#align set.inter_sub_union_subset_union Set.inter_sub_union_subset_union

@[to_additive]
theorem union_div_inter_subset_union : (s₁ ∪ s₂) / (t₁ ∩ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ :=
  image2_union_inter_subset_union
#align set.union_div_inter_subset_union Set.union_div_inter_subset_union
#align set.union_sub_inter_subset_union Set.union_sub_inter_subset_union

@[to_additive]
theorem iUnion_div_left_image : ⋃ a ∈ s, (· / ·) a '' t = s / t :=
  iUnion_image_left _
#align set.Union_div_left_image Set.iUnion_div_left_image
#align set.Union_sub_left_image Set.iUnion_sub_left_image

@[to_additive]
theorem iUnion_div_right_image : ⋃ a ∈ t, (· / a) '' s = s / t :=
  iUnion_image_right _
#align set.Union_div_right_image Set.iUnion_div_right_image
#align set.Union_sub_right_image Set.iUnion_sub_right_image

@[to_additive]
theorem iUnion_div (s : ι → Set α) (t : Set α) : (⋃ i, s i) / t = ⋃ i, s i / t :=
  image2_iUnion_left _ _ _
#align set.Union_div Set.iUnion_div
#align set.Union_sub Set.iUnion_sub

@[to_additive]
theorem div_iUnion (s : Set α) (t : ι → Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i :=
  image2_iUnion_right _ _ _
#align set.div_Union Set.div_iUnion
#align set.sub_Union Set.sub_iUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iUnion₂_div (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) / t = ⋃ (i) (j), s i j / t :=
  image2_iUnion₂_left _ _ _
#align set.Union₂_div Set.iUnion₂_div
#align set.Union₂_sub Set.iUnion₂_sub

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋃ (i) (j), t i j) = ⋃ (i) (j), s / t i j :=
  image2_iUnion₂_right _ _ _
#align set.div_Union₂ Set.div_iUnion₂
#align set.sub_Union₂ Set.sub_iUnion₂

@[to_additive]
theorem iInter_div_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
  image2_iInter_subset_left _ _ _
#align set.Inter_div_subset Set.iInter_div_subset
#align set.Inter_sub_subset Set.iInter_sub_subset

@[to_additive]
theorem div_iInter_subset (s : Set α) (t : ι → Set α) : (s / ⋂ i, t i) ⊆ ⋂ i, s / t i :=
  image2_iInter_subset_right _ _ _
#align set.div_Inter_subset Set.div_iInter_subset
#align set.sub_Inter_subset Set.sub_iInter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem iInter₂_div_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) / t ⊆ ⋂ (i) (j), s i j / t :=
  image2_iInter₂_subset_left _ _ _
#align set.Inter₂_div_subset Set.iInter₂_div_subset
#align set.Inter₂_sub_subset Set.iInter₂_sub_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s / t i j :=
  image2_iInter₂_subset_right _ _ _
#align set.div_Inter₂_subset Set.div_iInter₂_subset
#align set.sub_Inter₂_subset Set.sub_iInter₂_subset

end Div

open Pointwise

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `Set`. See
note [pointwise nat action].-/
protected def NSMul [Zero α] [Add α] : SMul ℕ (Set α) :=
  ⟨nsmulRec⟩
#align set.has_nsmul Set.NSMul

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`Set`. See note [pointwise nat action]. -/
@[to_additive existing]
protected def NPow [One α] [Mul α] : Pow (Set α) ℕ :=
  ⟨fun s n => npowRec n s⟩
#align set.has_npow Set.NPow

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `Set`. See note [pointwise nat action]. -/
protected def ZSMul [Zero α] [Add α] [Neg α] : SMul ℤ (Set α) :=
  ⟨zsmulRec⟩
#align set.has_zsmul Set.ZSMul

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `Set`. See note [pointwise nat action]. -/
@[to_additive existing]
protected def ZPow [One α] [Mul α] [Inv α] : Pow (Set α) ℤ :=
  ⟨fun s n => zpowRec n s⟩
#align set.has_zpow Set.ZPow

scoped[Pointwise] attribute [instance] Set.NSMul Set.NPow Set.ZSMul Set.ZPow

/-- `Set α` is a `Semigroup` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddSemigroup` under pointwise operations if `α` is."]
protected noncomputable def semigroup [Semigroup α] : Semigroup (Set α) :=
  { Set.mul with mul_assoc := fun _ _ _ => image2_assoc mul_assoc }
#align set.semigroup Set.semigroup
#align set.add_semigroup Set.addSemigroup

section CommSemigroup

variable [CommSemigroup α] {s t : Set α}

/-- `Set α` is a `CommSemigroup` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddCommSemigroup` under pointwise operations if `α` is."]
protected noncomputable def commSemigroup : CommSemigroup (Set α) :=
  { Set.semigroup with mul_comm := fun _ _ => image2_comm mul_comm }
#align set.comm_semigroup Set.commSemigroup
#align set.add_comm_semigroup Set.addCommSemigroup

@[to_additive]
theorem inter_mul_union_subset : s ∩ t * (s ∪ t) ⊆ s * t :=
  image2_inter_union_subset mul_comm
#align set.inter_mul_union_subset Set.inter_mul_union_subset
#align set.inter_add_union_subset Set.inter_add_union_subset

@[to_additive]
theorem union_mul_inter_subset : (s ∪ t) * (s ∩ t) ⊆ s * t :=
  image2_union_inter_subset mul_comm
#align set.union_mul_inter_subset Set.union_mul_inter_subset
#align set.union_add_inter_subset Set.union_add_inter_subset

end CommSemigroup

section MulOneClass

variable [MulOneClass α]

/-- `Set α` is a `MulOneClass` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddZeroClass` under pointwise operations if `α` is."]
protected noncomputable def mulOneClass : MulOneClass (Set α) :=
  { Set.one, Set.mul with
    mul_one := image2_right_identity mul_one
    one_mul := image2_left_identity one_mul }
#align set.mul_one_class Set.mulOneClass
#align set.add_zero_class Set.addZeroClass

scoped[Pointwise]
  attribute [instance]
    Set.mulOneClass Set.addZeroClass Set.semigroup Set.addSemigroup Set.commSemigroup
    Set.addCommSemigroup

@[to_additive]
theorem subset_mul_left (s : Set α) {t : Set α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun x hx =>
  ⟨x, 1, hx, ht, mul_one _⟩
#align set.subset_mul_left Set.subset_mul_left
#align set.subset_add_left Set.subset_add_left

@[to_additive]
theorem subset_mul_right {s : Set α} (t : Set α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun x hx =>
  ⟨1, x, hs, hx, one_mul _⟩
#align set.subset_mul_right Set.subset_mul_right
#align set.subset_add_right Set.subset_add_right

/-- The singleton operation as a `MonoidHom`. -/
@[to_additive "The singleton operation as an `AddMonoidHom`."]
noncomputable def singletonMonoidHom : α →* Set α :=
  { singletonMulHom, singletonOneHom with }
#align set.singleton_monoid_hom Set.singletonMonoidHom
#align set.singleton_add_monoid_hom Set.singletonAddMonoidHom

@[to_additive (attr := simp)]
theorem coe_singletonMonoidHom : (singletonMonoidHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_monoid_hom Set.coe_singletonMonoidHom
#align set.coe_singleton_add_monoid_hom Set.coe_singletonAddMonoidHom

@[to_additive (attr := simp)]
theorem singletonMonoidHom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl
#align set.singleton_monoid_hom_apply Set.singletonMonoidHom_apply
#align set.singleton_add_monoid_hom_apply Set.singletonAddMonoidHom_apply

end MulOneClass

section Monoid

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

/-- `Set α` is a `Monoid` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddMonoid` under pointwise operations if `α` is."]
protected noncomputable def monoid : Monoid (Set α) :=
  { Set.semigroup, Set.mulOneClass, @Set.NPow α _ _ with }
#align set.monoid Set.monoid
#align set.add_monoid Set.addMonoid

scoped[Pointwise] attribute [instance] Set.monoid Set.addMonoid

@[to_additive]
theorem pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
  | 0 => by
    rw [pow_zero]
    -- ⊢ 1 ∈ s ^ 0
    exact one_mem_one
    -- 🎉 no goals
  | n + 1 => by
    rw [pow_succ]
    -- ⊢ a * a ^ n ∈ s ^ (n + 1)
    exact mul_mem_mul ha (pow_mem_pow ha _)
    -- 🎉 no goals
#align set.pow_mem_pow Set.pow_mem_pow
#align set.nsmul_mem_nsmul Set.nsmul_mem_nsmul

@[to_additive]
theorem pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
  | 0 => by
    rw [pow_zero]
    -- ⊢ 1 ⊆ t ^ 0
    exact Subset.rfl
    -- 🎉 no goals
  | n + 1 => by
    rw [pow_succ]
    -- ⊢ s * s ^ n ⊆ t ^ (n + 1)
    exact mul_subset_mul hst (pow_subset_pow hst _)
    -- 🎉 no goals
#align set.pow_subset_pow Set.pow_subset_pow
#align set.nsmul_subset_nsmul Set.nsmul_subset_nsmul

@[to_additive]
theorem pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) (hn : m ≤ n) : s ^ m ⊆ s ^ n := by
  -- Porting note: `Nat.le_induction` didn't work as an induction principle in mathlib3, this was
  -- `refine Nat.le_induction ...`
  induction' n, hn using Nat.le_induction with _ _ ih
  -- ⊢ s ^ m ⊆ s ^ m
  · exact Subset.rfl
    -- 🎉 no goals
  · dsimp only
    -- ⊢ s ^ m ⊆ s ^ (n✝ + 1)
    rw [pow_succ]
    -- ⊢ s ^ m ⊆ s * s ^ n✝
    exact ih.trans (subset_mul_right _ hs)
    -- 🎉 no goals
#align set.pow_subset_pow_of_one_mem Set.pow_subset_pow_of_one_mem
#align set.nsmul_subset_nsmul_of_zero_mem Set.nsmul_subset_nsmul_of_zero_mem

@[to_additive (attr := simp)]
theorem empty_pow {n : ℕ} (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ := by
  rw [← tsub_add_cancel_of_le (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn), pow_succ, empty_mul]
  -- 🎉 no goals
#align set.empty_pow Set.empty_pow
#align set.empty_nsmul Set.empty_nsmul

@[to_additive]
theorem mul_univ_of_one_mem (hs : (1 : α) ∈ s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, _, hs, mem_univ _, one_mul _⟩
#align set.mul_univ_of_one_mem Set.mul_univ_of_one_mem
#align set.add_univ_of_zero_mem Set.add_univ_of_zero_mem

@[to_additive]
theorem univ_mul_of_one_mem (ht : (1 : α) ∈ t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, _, mem_univ _, ht, mul_one _⟩
#align set.univ_mul_of_one_mem Set.univ_mul_of_one_mem
#align set.univ_add_of_zero_mem Set.univ_add_of_zero_mem

@[to_additive (attr := simp)]
theorem univ_mul_univ : (univ : Set α) * univ = univ :=
  mul_univ_of_one_mem <| mem_univ _
#align set.univ_mul_univ Set.univ_mul_univ
#align set.univ_add_univ Set.univ_add_univ

--TODO: `to_additive` trips up on the `1 : ℕ` used in the pattern-matching.
@[simp]
theorem nsmul_univ {α : Type*} [AddMonoid α] : ∀ {n : ℕ}, n ≠ 0 → n • (univ : Set α) = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => one_nsmul _
  | n + 2 => fun _ => by rw [succ_nsmul, nsmul_univ n.succ_ne_zero, univ_add_univ]
                         -- 🎉 no goals
#align set.nsmul_univ Set.nsmul_univ

@[to_additive existing (attr := simp) nsmul_univ]
theorem univ_pow : ∀ {n : ℕ}, n ≠ 0 → (univ : Set α) ^ n = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => pow_one _
  | n + 2 => fun _ => by rw [pow_succ, univ_pow n.succ_ne_zero, univ_mul_univ]
                         -- 🎉 no goals
#align set.univ_pow Set.univ_pow

@[to_additive]
protected theorem _root_.IsUnit.set : IsUnit a → IsUnit ({a} : Set α) :=
  IsUnit.map (singletonMonoidHom : α →* Set α)
#align is_unit.set IsUnit.set
#align is_add_unit.set IsAddUnit.set

end Monoid

/-- `Set α` is a `CommMonoid` under pointwise operations if `α` is. -/
@[to_additive "`Set α` is an `AddCommMonoid` under pointwise operations if `α` is."]
protected noncomputable def commMonoid [CommMonoid α] : CommMonoid (Set α) :=
  { Set.monoid, Set.commSemigroup with }
#align set.comm_monoid Set.commMonoid
#align set.add_comm_monoid Set.addCommMonoid

scoped[Pointwise] attribute [instance] Set.commMonoid Set.addCommMonoid

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Set α}

@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  refine' ⟨fun h => _, _⟩
  -- ⊢ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1
  · have hst : (s * t).Nonempty := h.symm.subst one_nonempty
    -- ⊢ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1
    obtain ⟨a, ha⟩ := hst.of_image2_left
    -- ⊢ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1
    obtain ⟨b, hb⟩ := hst.of_image2_right
    -- ⊢ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1
    have H : ∀ {a b}, a ∈ s → b ∈ t → a * b = (1 : α) := fun {a b} ha hb =>
      h.subset <| mem_image2_of_mem ha hb
    refine' ⟨a, b, _, _, H ha hb⟩ <;> refine' eq_singleton_iff_unique_mem.2 ⟨‹_›, fun x hx => _⟩
    -- ⊢ s = {a}
                                      -- ⊢ x = a
                                      -- ⊢ x = b
    · exact (eq_inv_of_mul_eq_one_left <| H hx hb).trans (inv_eq_of_mul_eq_one_left <| H ha hb)
      -- 🎉 no goals
    · exact (eq_inv_of_mul_eq_one_right <| H ha hx).trans (inv_eq_of_mul_eq_one_right <| H ha hb)
      -- 🎉 no goals
  · rintro ⟨b, c, rfl, rfl, h⟩
    -- ⊢ {b} * {c} = 1
    rw [singleton_mul_singleton, h, singleton_one]
    -- 🎉 no goals
#align set.mul_eq_one_iff Set.mul_eq_one_iff
#align set.add_eq_zero_iff Set.add_eq_zero_iff

/-- `Set α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive subtractionMonoid
    "`Set α` is a subtraction monoid under pointwise operations if `α` is."]
protected noncomputable def divisionMonoid : DivisionMonoid (Set α) :=
  { Set.monoid, Set.involutiveInv, Set.div, @Set.ZPow α _ _ _ with
    mul_inv_rev := fun s t => by
      simp_rw [← image_inv]
      -- ⊢ Inv.inv '' (s * t) = Inv.inv '' t * Inv.inv '' s
      exact image_image2_antidistrib mul_inv_rev
      -- 🎉 no goals
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Set.mul_eq_one_iff.1 h
      -- ⊢ {a}⁻¹ = {b}
      -- ⊢ id '' (s / t) = s * Inv.inv '' t
      rw [inv_singleton, inv_eq_of_mul_eq_one_right hab]
      -- 🎉 no goals
      -- 🎉 no goals
    div_eq_mul_inv := fun s t => by
      rw [← image_id (s / t), ← image_inv]
      exact image_image2_distrib_right div_eq_mul_inv }
#align set.division_monoid Set.divisionMonoid
#align set.subtraction_monoid Set.subtractionMonoid

@[to_additive (attr := simp 500)]
theorem isUnit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a := by
  constructor
  -- ⊢ IsUnit s → ∃ a, s = {a} ∧ IsUnit a
  · rintro ⟨u, rfl⟩
    -- ⊢ ∃ a, ↑u = {a} ∧ IsUnit a
    obtain ⟨a, b, ha, hb, h⟩ := Set.mul_eq_one_iff.1 u.mul_inv
    -- ⊢ ∃ a, ↑u = {a} ∧ IsUnit a
    refine' ⟨a, ha, ⟨a, b, h, singleton_injective _⟩, rfl⟩
    -- ⊢ {b * a} = {1}
    rw [← singleton_mul_singleton, ← ha, ← hb]
    -- ⊢ ↑u⁻¹ * ↑u = {1}
    exact u.inv_mul
    -- 🎉 no goals
  · rintro ⟨a, rfl, ha⟩
    -- ⊢ IsUnit {a}
    exact ha.set
    -- 🎉 no goals
#align set.is_unit_iff Set.isUnit_iff
#align set.is_add_unit_iff Set.isAddUnit_iff

end DivisionMonoid

/-- `Set α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive subtractionCommMonoid
      "`Set α` is a commutative subtraction monoid under pointwise operations if `α` is."]
protected noncomputable def divisionCommMonoid [DivisionCommMonoid α] :
    DivisionCommMonoid (Set α) :=
  { Set.divisionMonoid, Set.commSemigroup with }
#align set.division_comm_monoid Set.divisionCommMonoid
#align set.subtraction_comm_monoid Set.subtractionCommMonoid

/-- `Set α` has distributive negation if `α` has. -/
protected noncomputable def hasDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Set α) :=
  { Set.involutiveNeg with
    neg_mul := fun _ _ => by
      simp_rw [← image_neg]
      -- ⊢ Neg.neg '' x✝¹ * x✝ = Neg.neg '' (x✝¹ * x✝)
      exact image2_image_left_comm neg_mul
      -- 🎉 no goals
    mul_neg := fun _ _ => by
      simp_rw [← image_neg]
      -- ⊢ x✝¹ * Neg.neg '' x✝ = Neg.neg '' (x✝¹ * x✝)
      exact image_image2_right_comm mul_neg }
      -- 🎉 no goals
#align set.has_distrib_neg Set.hasDistribNeg

scoped[Pointwise]
  attribute [instance]
    Set.divisionMonoid Set.subtractionMonoid Set.divisionCommMonoid Set.subtractionCommMonoid
    Set.hasDistribNeg

section Distrib

variable [Distrib α] (s t u : Set α)

/-!
Note that `Set α` is not a `Distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.
-/


theorem mul_add_subset : s * (t + u) ⊆ s * t + s * u :=
  image2_distrib_subset_left mul_add
#align set.mul_add_subset Set.mul_add_subset

theorem add_mul_subset : (s + t) * u ⊆ s * u + t * u :=
  image2_distrib_subset_right add_mul
#align set.add_mul_subset Set.add_mul_subset

end Distrib

section MulZeroClass

variable [MulZeroClass α] {s t : Set α}

/-! Note that `Set` is not a `MulZeroClass` because `0 * ∅ ≠ 0`. -/


theorem mul_zero_subset (s : Set α) : s * 0 ⊆ 0 := by simp [subset_def, mem_mul]
                                                      -- 🎉 no goals
#align set.mul_zero_subset Set.mul_zero_subset

theorem zero_mul_subset (s : Set α) : 0 * s ⊆ 0 := by simp [subset_def, mem_mul]
                                                      -- 🎉 no goals
#align set.zero_mul_subset Set.zero_mul_subset

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by simpa [mem_mul] using hs
                                   -- 🎉 no goals
#align set.nonempty.mul_zero Set.Nonempty.mul_zero

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by simpa [mem_mul] using hs
                                   -- 🎉 no goals
#align set.nonempty.zero_mul Set.Nonempty.zero_mul

end MulZeroClass

section Group

variable [Group α] {s t : Set α} {a b : α}

/-! Note that `Set` is not a `Group` because `s / s ≠ 1` in general. -/


@[to_additive (attr := simp)]
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, Set.Nonempty]
  -- 🎉 no goals
#align set.one_mem_div_iff Set.one_mem_div_iff
#align set.zero_mem_sub_iff Set.zero_mem_sub_iff

@[to_additive]
theorem not_one_mem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left
#align set.not_one_mem_div_iff Set.not_one_mem_div_iff
#align set.not_zero_mem_sub_iff Set.not_zero_mem_sub_iff

alias ⟨_, _root_.Disjoint.one_not_mem_div_set⟩ := not_one_mem_div_iff
#align disjoint.one_not_mem_div_set Disjoint.one_not_mem_div_set

attribute [to_additive] Disjoint.one_not_mem_div_set
#align disjoint.zero_not_mem_sub_set Disjoint.zero_not_mem_sub_set

@[to_additive]
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, a, ha, ha, div_self' _⟩
#align set.nonempty.one_mem_div Set.Nonempty.one_mem_div
#align set.nonempty.zero_mem_sub Set.Nonempty.zero_mem_sub

@[to_additive]
theorem isUnit_singleton (a : α) : IsUnit ({a} : Set α) :=
  (Group.isUnit a).set
#align set.is_unit_singleton Set.isUnit_singleton
#align set.is_add_unit_singleton Set.isAddUnit_singleton

@[to_additive (attr := simp)]
theorem isUnit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [isUnit_iff, Group.isUnit, and_true_iff]
  -- 🎉 no goals
#align set.is_unit_iff_singleton Set.isUnit_iff_singleton
#align set.is_add_unit_iff_singleton Set.isAddUnit_iff_singleton

@[to_additive (attr := simp)]
theorem image_mul_left : (· * ·) a '' t = (· * ·) a⁻¹ ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp
  -- ⊢ LeftInverse ((fun x x_1 => x * x_1) a⁻¹) ((fun x x_1 => x * x_1) a)
                                        -- ⊢ (fun x x_1 => x * x_1) a⁻¹ ((fun x x_1 => x * x_1) a c) = c
                                        -- ⊢ (fun x x_1 => x * x_1) a ((fun x x_1 => x * x_1) a⁻¹ c) = c
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align set.image_mul_left Set.image_mul_left
#align set.image_add_left Set.image_add_left

@[to_additive (attr := simp)]
theorem image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp
  -- ⊢ LeftInverse (fun x => x * b⁻¹) fun x => x * b
                                        -- ⊢ (fun x => x * b⁻¹) ((fun x => x * b) c) = c
                                        -- ⊢ (fun x => x * b) ((fun x => x * b⁻¹) c) = c
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align set.image_mul_right Set.image_mul_right
#align set.image_add_right Set.image_add_right

@[to_additive]
theorem image_mul_left' : (fun b => a⁻¹ * b) '' t = (fun b => a * b) ⁻¹' t := by simp
                                                                                 -- 🎉 no goals
#align set.image_mul_left' Set.image_mul_left'
#align set.image_add_left' Set.image_add_left'

@[to_additive]
theorem image_mul_right' : (· * b⁻¹) '' t = (· * b) ⁻¹' t := by simp
                                                                -- 🎉 no goals
#align set.image_mul_right' Set.image_mul_right'
#align set.image_add_right' Set.image_add_right'

@[to_additive (attr := simp)]
theorem preimage_mul_left_singleton : (· * ·) a ⁻¹' {b} = {a⁻¹ * b} := by
  rw [← image_mul_left', image_singleton]
  -- 🎉 no goals
#align set.preimage_mul_left_singleton Set.preimage_mul_left_singleton
#align set.preimage_add_left_singleton Set.preimage_add_left_singleton

@[to_additive (attr := simp)]
theorem preimage_mul_right_singleton : (· * a) ⁻¹' {b} = {b * a⁻¹} := by
  rw [← image_mul_right', image_singleton]
  -- 🎉 no goals
#align set.preimage_mul_right_singleton Set.preimage_mul_right_singleton
#align set.preimage_add_right_singleton Set.preimage_add_right_singleton

@[to_additive (attr := simp)]
theorem preimage_mul_left_one : (· * ·) a ⁻¹' 1 = {a⁻¹} := by
  rw [← image_mul_left', image_one, mul_one]
  -- 🎉 no goals
#align set.preimage_mul_left_one Set.preimage_mul_left_one
#align set.preimage_add_left_zero Set.preimage_add_left_zero

@[to_additive (attr := simp)]
theorem preimage_mul_right_one : (· * b) ⁻¹' 1 = {b⁻¹} := by
  rw [← image_mul_right', image_one, one_mul]
  -- 🎉 no goals
#align set.preimage_mul_right_one Set.preimage_mul_right_one
#align set.preimage_add_right_zero Set.preimage_add_right_zero

@[to_additive]
theorem preimage_mul_left_one' : (fun b => a⁻¹ * b) ⁻¹' 1 = {a} := by simp
                                                                      -- 🎉 no goals
#align set.preimage_mul_left_one' Set.preimage_mul_left_one'
#align set.preimage_add_left_zero' Set.preimage_add_left_zero'

@[to_additive]
theorem preimage_mul_right_one' : (· * b⁻¹) ⁻¹' 1 = {b} := by simp
                                                              -- 🎉 no goals
#align set.preimage_mul_right_one' Set.preimage_mul_right_one'
#align set.preimage_add_right_zero' Set.preimage_add_right_zero'

@[to_additive (attr := simp)]
theorem mul_univ (hs : s.Nonempty) : s * (univ : Set α) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ * b, ha, trivial, mul_inv_cancel_left _ _⟩
#align set.mul_univ Set.mul_univ
#align set.add_univ Set.add_univ

@[to_additive (attr := simp)]
theorem univ_mul (ht : t.Nonempty) : (univ : Set α) * t = univ :=
  let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, a, trivial, ha, inv_mul_cancel_right _ _⟩
#align set.univ_mul Set.univ_mul
#align set.univ_add Set.univ_add

end Group

section GroupWithZero

variable [GroupWithZero α] {s t : Set α}

theorem div_zero_subset (s : Set α) : s / 0 ⊆ 0 := by simp [subset_def, mem_div]
                                                      -- 🎉 no goals
#align set.div_zero_subset Set.div_zero_subset

theorem zero_div_subset (s : Set α) : 0 / s ⊆ 0 := by simp [subset_def, mem_div]
                                                      -- 🎉 no goals
#align set.zero_div_subset Set.zero_div_subset

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by simpa [mem_div] using hs
                                   -- 🎉 no goals
#align set.nonempty.div_zero Set.Nonempty.div_zero

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by simpa [mem_div] using hs
                                   -- 🎉 no goals
#align set.nonempty.zero_div Set.Nonempty.zero_div

end GroupWithZero

section Mul

variable [Mul α] [Mul β] [MulHomClass F α β] (m : F) {s t : Set α}

@[to_additive]
theorem image_mul : m '' (s * t) = m '' s * m '' t :=
  image_image2_distrib <| map_mul m
#align set.image_mul Set.image_mul
#align set.image_add Set.image_add

@[to_additive]
theorem preimage_mul_preimage_subset {s t : Set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  -- ⊢ (fun x x_1 => x * x_1) w✝¹ w✝ ∈ ↑m ⁻¹' (s * t)
  exact ⟨_, _, ‹_›, ‹_›, (map_mul m _ _).symm⟩
  -- 🎉 no goals
#align set.preimage_mul_preimage_subset Set.preimage_mul_preimage_subset
#align set.preimage_add_preimage_subset Set.preimage_add_preimage_subset

end Mul

section Group

variable [Group α] [DivisionMonoid β] [MonoidHomClass F α β] (m : F) {s t : Set α}

@[to_additive]
theorem image_div : m '' (s / t) = m '' s / m '' t :=
  image_image2_distrib <| map_div m
#align set.image_div Set.image_div
#align set.image_sub Set.image_sub

@[to_additive]
theorem preimage_div_preimage_subset {s t : Set β} : m ⁻¹' s / m ⁻¹' t ⊆ m ⁻¹' (s / t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  -- ⊢ (fun x x_1 => x / x_1) w✝¹ w✝ ∈ ↑m ⁻¹' (s / t)
  exact ⟨_, _, ‹_›, ‹_›, (map_div m _ _).symm⟩
  -- 🎉 no goals
#align set.preimage_div_preimage_subset Set.preimage_div_preimage_subset
#align set.preimage_sub_preimage_subset Set.preimage_sub_preimage_subset

end Group

@[to_additive]
theorem bddAbove_mul [OrderedCommMonoid α] {A B : Set α} :
    BddAbove A → BddAbove B → BddAbove (A * B) := by
  rintro ⟨bA, hbA⟩ ⟨bB, hbB⟩
  -- ⊢ BddAbove (A * B)
  use bA * bB
  -- ⊢ bA * bB ∈ upperBounds (A * B)
  rintro x ⟨xa, xb, hxa, hxb, rfl⟩
  -- ⊢ (fun x x_1 => x * x_1) xa xb ≤ bA * bB
  exact mul_le_mul' (hbA hxa) (hbB hxb)
  -- 🎉 no goals
#align set.bdd_above_mul Set.bddAbove_mul
#align set.bdd_above_add Set.bddAbove_add

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
  · obtain ⟨n, hn1, hn2⟩ := key
    -- ⊢ ∀ (k : ℕ), B ≤ k → f k = f B
    replace key : ∀ k : ℕ, f (n + k) = f (n + k + 1) ∧ f (n + k) = f n := fun k =>
      Nat.rec ⟨hn2, rfl⟩ (fun k ih => ⟨h3 _ ih.1, ih.1.symm.trans ih.2⟩) k
    replace key : ∀ k : ℕ, n ≤ k → f k = f n := fun k hk =>
      (congr_arg f (add_tsub_cancel_of_le hk)).symm.trans (key (k - n)).2
    exact fun k hk => (key k (hn1.trans hk)).trans (key B hn1).symm
    -- 🎉 no goals
#align group.card_pow_eq_card_pow_card_univ_aux Group.card_pow_eq_card_pow_card_univ_aux
#align add_group.card_nsmul_eq_card_nsmul_card_univ_aux AddGroup.card_nsmul_eq_card_nsmul_card_univ_aux

end Group
