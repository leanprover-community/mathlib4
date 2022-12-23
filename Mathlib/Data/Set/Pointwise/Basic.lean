/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn

! This file was ported from Lean 3 source module data.set.pointwise.basic
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Hom.Units
import Mathbin.Data.Set.Lattice
import Mathbin.Data.Nat.Order.Basic

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

For `α` a semigroup/monoid, `set α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/


library_note "pointwise nat action"/--
Pointwise monoids (`set`, `finset`, `filter`) have derived pointwise actions of the form
`has_smul α β → has_smul α (set β)`. When `α` is `ℕ` or `ℤ`, this action conflicts with the
nat or int action coming from `set β` being a `monoid` or `div_inv_monoid`. For example,
`2 • {a, b}` can both be `{2 • a, 2 • b}` (pointwise action, pointwise repeated addition,
`set.has_smul_set`) and `{a + a, a + b, b + a, b + b}` (nat or int action, repeated pointwise
addition, `set.has_nsmul`).

Because the pointwise action can easily be spelled out in such cases, we give higher priority to the
nat and int actions.
-/


open Function

variable {F α β γ : Type _}

namespace Set

/-! ### `0`/`1` as sets -/


section One

variable [One α] {s : Set α} {a : α}

/-- The set `1 : set α` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The set `0 : set α` is defined as `{0}` in locale `pointwise`."]
protected def hasOne : One (Set α) :=
  ⟨{1}⟩
#align set.has_one Set.hasOne

scoped[Pointwise] attribute [instance] Set.hasOne Set.hasZero

@[to_additive]
theorem singleton_one : ({1} : Set α) = 1 :=
  rfl
#align set.singleton_one Set.singleton_one

@[simp, to_additive]
theorem mem_one : a ∈ (1 : Set α) ↔ a = 1 :=
  Iff.rfl
#align set.mem_one Set.mem_one

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Set α) :=
  Eq.refl _
#align set.one_mem_one Set.one_mem_one

@[simp, to_additive]
theorem one_subset : 1 ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff
#align set.one_subset Set.one_subset

@[to_additive]
theorem one_nonempty : (1 : Set α).Nonempty :=
  ⟨1, rfl⟩
#align set.one_nonempty Set.one_nonempty

@[simp, to_additive]
theorem image_one {f : α → β} : f '' 1 = {f 1} :=
  image_singleton
#align set.image_one Set.image_one

@[to_additive]
theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff_eq
#align set.subset_one_iff_eq Set.subset_one_iff_eq

@[to_additive]
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 :=
  h.subset_singleton_iff
#align set.nonempty.subset_one_iff Set.Nonempty.subset_one_iff

/-- The singleton operation as a `one_hom`. -/
@[to_additive "The singleton operation as a `zero_hom`."]
def singletonOneHom : OneHom α (Set α) :=
  ⟨singleton, singleton_one⟩
#align set.singleton_one_hom Set.singletonOneHom

@[simp, to_additive]
theorem coe_singleton_one_hom : (singletonOneHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_one_hom Set.coe_singleton_one_hom

end One

/-! ### Set negation/inversion -/


section Inv

/-- The pointwise inversion of set `s⁻¹` is defined as `{x | x⁻¹ ∈ s}` in locale `pointwise`. It i
equal to `{x⁻¹ | x ∈ s}`, see `set.image_inv`. -/
@[to_additive
      "The pointwise negation of set `-s` is defined as `{x | -x ∈ s}` in locale\n`pointwise`. It is equal to `{-x | x ∈ s}`, see `set.image_neg`."]
protected def hasInv [Inv α] : Inv (Set α) :=
  ⟨preimage Inv.inv⟩
#align set.has_inv Set.hasInv

scoped[Pointwise] attribute [instance] Set.hasInv Set.hasNeg

section Inv

variable {ι : Sort _} [Inv α] {s t : Set α} {a : α}

@[simp, to_additive]
theorem mem_inv : a ∈ s⁻¹ ↔ a⁻¹ ∈ s :=
  Iff.rfl
#align set.mem_inv Set.mem_inv

@[simp, to_additive]
theorem inv_preimage : Inv.inv ⁻¹' s = s⁻¹ :=
  rfl
#align set.inv_preimage Set.inv_preimage

@[simp, to_additive]
theorem inv_empty : (∅ : Set α)⁻¹ = ∅ :=
  rfl
#align set.inv_empty Set.inv_empty

@[simp, to_additive]
theorem inv_univ : (univ : Set α)⁻¹ = univ :=
  rfl
#align set.inv_univ Set.inv_univ

@[simp, to_additive]
theorem inter_inv : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ :=
  preimage_inter
#align set.inter_inv Set.inter_inv

@[simp, to_additive]
theorem union_inv : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ :=
  preimage_union
#align set.union_inv Set.union_inv

@[simp, to_additive]
theorem Inter_inv (s : ι → Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ :=
  preimage_Inter
#align set.Inter_inv Set.Inter_inv

@[simp, to_additive]
theorem Union_inv (s : ι → Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
  preimage_Union
#align set.Union_inv Set.Union_inv

@[simp, to_additive]
theorem compl_inv : (sᶜ)⁻¹ = s⁻¹ᶜ :=
  preimage_compl
#align set.compl_inv Set.compl_inv

end Inv

section InvolutiveInv

variable [InvolutiveInv α] {s t : Set α} {a : α}

@[to_additive]
theorem inv_mem_inv : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by simp only [mem_inv, inv_inv]
#align set.inv_mem_inv Set.inv_mem_inv

@[simp, to_additive]
theorem nonempty_inv : s⁻¹.Nonempty ↔ s.Nonempty :=
  inv_involutive.Surjective.nonempty_preimage
#align set.nonempty_inv Set.nonempty_inv

@[to_additive]
theorem Nonempty.inv (h : s.Nonempty) : s⁻¹.Nonempty :=
  nonempty_inv.2 h
#align set.nonempty.inv Set.Nonempty.inv

@[simp, to_additive]
theorem image_inv : Inv.inv '' s = s⁻¹ :=
  congr_fun (image_eq_preimage_of_inverse inv_involutive.LeftInverse inv_involutive.RightInverse) _
#align set.image_inv Set.image_inv

@[simp, to_additive]
instance : InvolutiveInv (Set α) where 
  inv := Inv.inv
  inv_inv s := by simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id']

@[simp, to_additive]
theorem inv_subset_inv : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
  (Equiv.inv α).Surjective.preimage_subset_preimage_iff
#align set.inv_subset_inv Set.inv_subset_inv

@[to_additive]
theorem inv_subset : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by rw [← inv_subset_inv, inv_inv]
#align set.inv_subset Set.inv_subset

@[simp, to_additive]
theorem inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹} := by rw [← image_inv, image_singleton]
#align set.inv_singleton Set.inv_singleton

@[simp, to_additive]
theorem inv_insert (a : α) (s : Set α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ := by
  rw [insert_eq, union_inv, inv_singleton, insert_eq]
#align set.inv_insert Set.inv_insert

@[to_additive]
theorem inv_range {ι : Sort _} {f : ι → α} : (range f)⁻¹ = range fun i => (f i)⁻¹ := by
  rw [← image_inv]
  exact (range_comp _ _).symm
#align set.inv_range Set.inv_range

open MulOpposite

@[to_additive]
theorem image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ := by
  simp_rw [← image_inv, Function.Semiconj.set_image op_inv s]
#align set.image_op_inv Set.image_op_inv

end InvolutiveInv

end Inv

open Pointwise

/-! ### Set addition/multiplication -/


section Mul

variable {ι : Sort _} {κ : ι → Sort _} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-- The pointwise multiplication of sets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive
      "The pointwise addition of sets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in\nlocale `pointwise`."]
protected def hasMul : Mul (Set α) :=
  ⟨image2 (· * ·)⟩
#align set.has_mul Set.hasMul

scoped[Pointwise] attribute [instance] Set.hasMul Set.hasAdd

@[simp, to_additive]
theorem image2_mul : image2 Mul.mul s t = s * t :=
  rfl
#align set.image2_mul Set.image2_mul

@[to_additive]
theorem mem_mul : a ∈ s * t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x * y = a :=
  Iff.rfl
#align set.mem_mul Set.mem_mul

@[to_additive]
theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t :=
  mem_image2_of_mem
#align set.mul_mem_mul Set.mul_mem_mul

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive add_image_prod]
theorem image_mul_prod : (fun x : α × α => x.fst * x.snd) '' s ×ˢ t = s * t :=
  image_prod _
#align set.image_mul_prod Set.image_mul_prod

@[simp, to_additive]
theorem empty_mul : ∅ * s = ∅ :=
  image2_empty_left
#align set.empty_mul Set.empty_mul

@[simp, to_additive]
theorem mul_empty : s * ∅ = ∅ :=
  image2_empty_right
#align set.mul_empty Set.mul_empty

@[simp, to_additive]
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.mul_eq_empty Set.mul_eq_empty

@[simp, to_additive]
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.mul_nonempty Set.mul_nonempty

@[to_additive]
theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  nonempty.image2
#align set.nonempty.mul Set.Nonempty.mul

@[to_additive]
theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty :=
  nonempty.of_image2_left
#align set.nonempty.of_mul_left Set.Nonempty.of_mul_left

@[to_additive]
theorem Nonempty.of_mul_right : (s * t).Nonempty → t.Nonempty :=
  nonempty.of_image2_right
#align set.nonempty.of_mul_right Set.Nonempty.of_mul_right

@[simp, to_additive]
theorem mul_singleton : s * {b} = (· * b) '' s :=
  image2_singleton_right
#align set.mul_singleton Set.mul_singleton

@[simp, to_additive]
theorem singleton_mul : {a} * t = (· * ·) a '' t :=
  image2_singleton_left
#align set.singleton_mul Set.singleton_mul

@[simp, to_additive]
theorem singleton_mul_singleton : ({a} : Set α) * {b} = {a * b} :=
  image2_singleton
#align set.singleton_mul_singleton Set.singleton_mul_singleton

@[to_additive, mono]
theorem mul_subset_mul : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ * s₂ ⊆ t₁ * t₂ :=
  image2_subset
#align set.mul_subset_mul Set.mul_subset_mul

@[to_additive]
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image2_subset_left
#align set.mul_subset_mul_left Set.mul_subset_mul_left

@[to_additive]
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image2_subset_right
#align set.mul_subset_mul_right Set.mul_subset_mul_right

@[to_additive]
theorem mul_subset_iff : s * t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x * y ∈ u :=
  image2_subset_iff
#align set.mul_subset_iff Set.mul_subset_iff

attribute [mono] add_subset_add

@[to_additive]
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image2_union_left
#align set.union_mul Set.union_mul

@[to_additive]
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image2_union_right
#align set.mul_union Set.mul_union

@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image2_inter_subset_left
#align set.inter_mul_subset Set.inter_mul_subset

@[to_additive]
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image2_inter_subset_right
#align set.mul_inter_subset Set.mul_inter_subset

@[to_additive]
theorem Union_mul_left_image : (⋃ a ∈ s, (· * ·) a '' t) = s * t :=
  Union_image_left _
#align set.Union_mul_left_image Set.Union_mul_left_image

@[to_additive]
theorem Union_mul_right_image : (⋃ a ∈ t, (· * a) '' s) = s * t :=
  Union_image_right _
#align set.Union_mul_right_image Set.Union_mul_right_image

@[to_additive]
theorem Union_mul (s : ι → Set α) (t : Set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
  image2_Union_left _ _ _
#align set.Union_mul Set.Union_mul

@[to_additive]
theorem mul_Union (s : Set α) (t : ι → Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i :=
  image2_Union_right _ _ _
#align set.mul_Union Set.mul_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Union₂_mul (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t :=
  image2_Union₂_left _ _ _
#align set.Union₂_mul Set.Union₂_mul

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_Union₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋃ (i) (j), t i j) = ⋃ (i) (j), s * t i j :=
  image2_Union₂_right _ _ _
#align set.mul_Union₂ Set.mul_Union₂

@[to_additive]
theorem Inter_mul_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
  image2_Inter_subset_left _ _ _
#align set.Inter_mul_subset Set.Inter_mul_subset

@[to_additive]
theorem mul_Inter_subset (s : Set α) (t : ι → Set α) : (s * ⋂ i, t i) ⊆ ⋂ i, s * t i :=
  image2_Inter_subset_right _ _ _
#align set.mul_Inter_subset Set.mul_Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Inter₂_mul_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) * t ⊆ ⋂ (i) (j), s i j * t :=
  image2_Inter₂_subset_left _ _ _
#align set.Inter₂_mul_subset Set.Inter₂_mul_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_Inter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s * t i j :=
  image2_Inter₂_subset_right _ _ _
#align set.mul_Inter₂_subset Set.mul_Inter₂_subset

/-- The singleton operation as a `mul_hom`. -/
@[to_additive "The singleton operation as an `add_hom`."]
def singletonMulHom : α →ₙ* Set α :=
  ⟨singleton, fun a b => singleton_mul_singleton.symm⟩
#align set.singleton_mul_hom Set.singletonMulHom

@[simp, to_additive]
theorem coe_singleton_mul_hom : (singletonMulHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_mul_hom Set.coe_singleton_mul_hom

@[simp, to_additive]
theorem singleton_mul_hom_apply (a : α) : singletonMulHom a = {a} :=
  rfl
#align set.singleton_mul_hom_apply Set.singleton_mul_hom_apply

open MulOpposite

@[simp, to_additive]
theorem image_op_mul : op '' (s * t) = op '' t * op '' s :=
  image_image2_antidistrib op_mul
#align set.image_op_mul Set.image_op_mul

end Mul

/-! ### Set subtraction/division -/


section Div

variable {ι : Sort _} {κ : ι → Sort _} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-- The pointwise division of sets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`pointwise`. -/
@[to_additive
      "The pointwise subtraction of sets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}` in\nlocale `pointwise`."]
protected def hasDiv : Div (Set α) :=
  ⟨image2 (· / ·)⟩
#align set.has_div Set.hasDiv

scoped[Pointwise] attribute [instance] Set.hasDiv Set.hasSub

@[simp, to_additive]
theorem image2_div : image2 Div.div s t = s / t :=
  rfl
#align set.image2_div Set.image2_div

@[to_additive]
theorem mem_div : a ∈ s / t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x / y = a :=
  Iff.rfl
#align set.mem_div Set.mem_div

@[to_additive]
theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t :=
  mem_image2_of_mem
#align set.div_mem_div Set.div_mem_div

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive add_image_prod]
theorem image_div_prod : (fun x : α × α => x.fst / x.snd) '' s ×ˢ t = s / t :=
  image_prod _
#align set.image_div_prod Set.image_div_prod

@[simp, to_additive]
theorem empty_div : ∅ / s = ∅ :=
  image2_empty_left
#align set.empty_div Set.empty_div

@[simp, to_additive]
theorem div_empty : s / ∅ = ∅ :=
  image2_empty_right
#align set.div_empty Set.div_empty

@[simp, to_additive]
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.div_eq_empty Set.div_eq_empty

@[simp, to_additive]
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.div_nonempty Set.div_nonempty

@[to_additive]
theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty :=
  nonempty.image2
#align set.nonempty.div Set.Nonempty.div

@[to_additive]
theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty :=
  nonempty.of_image2_left
#align set.nonempty.of_div_left Set.Nonempty.of_div_left

@[to_additive]
theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty :=
  nonempty.of_image2_right
#align set.nonempty.of_div_right Set.Nonempty.of_div_right

@[simp, to_additive]
theorem div_singleton : s / {b} = (· / b) '' s :=
  image2_singleton_right
#align set.div_singleton Set.div_singleton

@[simp, to_additive]
theorem singleton_div : {a} / t = (· / ·) a '' t :=
  image2_singleton_left
#align set.singleton_div Set.singleton_div

@[simp, to_additive]
theorem singleton_div_singleton : ({a} : Set α) / {b} = {a / b} :=
  image2_singleton
#align set.singleton_div_singleton Set.singleton_div_singleton

@[to_additive, mono]
theorem div_subset_div : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ / s₂ ⊆ t₁ / t₂ :=
  image2_subset
#align set.div_subset_div Set.div_subset_div

@[to_additive]
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image2_subset_left
#align set.div_subset_div_left Set.div_subset_div_left

@[to_additive]
theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t :=
  image2_subset_right
#align set.div_subset_div_right Set.div_subset_div_right

@[to_additive]
theorem div_subset_iff : s / t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x / y ∈ u :=
  image2_subset_iff
#align set.div_subset_iff Set.div_subset_iff

attribute [mono] sub_subset_sub

@[to_additive]
theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t :=
  image2_union_left
#align set.union_div Set.union_div

@[to_additive]
theorem div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ :=
  image2_union_right
#align set.div_union Set.div_union

@[to_additive]
theorem inter_div_subset : s₁ ∩ s₂ / t ⊆ s₁ / t ∩ (s₂ / t) :=
  image2_inter_subset_left
#align set.inter_div_subset Set.inter_div_subset

@[to_additive]
theorem div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
  image2_inter_subset_right
#align set.div_inter_subset Set.div_inter_subset

@[to_additive]
theorem Union_div_left_image : (⋃ a ∈ s, (· / ·) a '' t) = s / t :=
  Union_image_left _
#align set.Union_div_left_image Set.Union_div_left_image

@[to_additive]
theorem Union_div_right_image : (⋃ a ∈ t, (· / a) '' s) = s / t :=
  Union_image_right _
#align set.Union_div_right_image Set.Union_div_right_image

@[to_additive]
theorem Union_div (s : ι → Set α) (t : Set α) : (⋃ i, s i) / t = ⋃ i, s i / t :=
  image2_Union_left _ _ _
#align set.Union_div Set.Union_div

@[to_additive]
theorem div_Union (s : Set α) (t : ι → Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i :=
  image2_Union_right _ _ _
#align set.div_Union Set.div_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Union₂_div (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) / t = ⋃ (i) (j), s i j / t :=
  image2_Union₂_left _ _ _
#align set.Union₂_div Set.Union₂_div

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_Union₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋃ (i) (j), t i j) = ⋃ (i) (j), s / t i j :=
  image2_Union₂_right _ _ _
#align set.div_Union₂ Set.div_Union₂

@[to_additive]
theorem Inter_div_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
  image2_Inter_subset_left _ _ _
#align set.Inter_div_subset Set.Inter_div_subset

@[to_additive]
theorem div_Inter_subset (s : Set α) (t : ι → Set α) : (s / ⋂ i, t i) ⊆ ⋂ i, s / t i :=
  image2_Inter_subset_right _ _ _
#align set.div_Inter_subset Set.div_Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem Inter₂_div_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) / t ⊆ ⋂ (i) (j), s i j / t :=
  image2_Inter₂_subset_left _ _ _
#align set.Inter₂_div_subset Set.Inter₂_div_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_Inter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s / t i j :=
  image2_Inter₂_subset_right _ _ _
#align set.div_Inter₂_subset Set.div_Inter₂_subset

end Div

open Pointwise

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `finset`. See
note [pointwise nat action].-/
protected def hasNsmul [Zero α] [Add α] : HasSmul ℕ (Set α) :=
  ⟨nsmulRec⟩
#align set.has_nsmul Set.hasNsmul

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`set`. See note [pointwise nat action]. -/
@[to_additive]
protected def hasNpow [One α] [Mul α] : Pow (Set α) ℕ :=
  ⟨fun s n => npowRec n s⟩
#align set.has_npow Set.hasNpow

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `set`. See note [pointwise nat action]. -/
protected def hasZsmul [Zero α] [Add α] [Neg α] : HasSmul ℤ (Set α) :=
  ⟨zsmulRec⟩
#align set.has_zsmul Set.hasZsmul

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `set`. See note [pointwise nat action]. -/
@[to_additive]
protected def hasZpow [One α] [Mul α] [Inv α] : Pow (Set α) ℤ :=
  ⟨fun s n => zpowRec n s⟩
#align set.has_zpow Set.hasZpow

scoped[Pointwise] attribute [instance] Set.hasNsmul Set.hasNpow Set.hasZsmul Set.hasZpow

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_semigroup` under pointwise operations if `α` is."]
protected def semigroup [Semigroup α] : Semigroup (Set α) :=
  { Set.hasMul with mul_assoc := fun _ _ _ => image2_assoc mul_assoc }
#align set.semigroup Set.semigroup

/-- `set α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_semigroup` under pointwise operations if `α` is."]
protected def commSemigroup [CommSemigroup α] : CommSemigroup (Set α) :=
  { Set.semigroup with mul_comm := fun s t => image2_comm mul_comm }
#align set.comm_semigroup Set.commSemigroup

section MulOneClass

variable [MulOneClass α]

/-- `set α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mulOneClass : MulOneClass (Set α) :=
  { Set.hasOne, Set.hasMul with
    mul_one := fun s => by simp only [← singleton_one, mul_singleton, mul_one, image_id']
    one_mul := fun s => by simp only [← singleton_one, singleton_mul, one_mul, image_id'] }
#align set.mul_one_class Set.mulOneClass

scoped[Pointwise]
  attribute [instance]
    Set.mulOneClass Set.addZeroClass Set.semigroup Set.addSemigroup Set.commSemigroup Set.addCommSemigroup

@[to_additive]
theorem subset_mul_left (s : Set α) {t : Set α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun x hx =>
  ⟨x, 1, hx, ht, mul_one _⟩
#align set.subset_mul_left Set.subset_mul_left

@[to_additive]
theorem subset_mul_right {s : Set α} (t : Set α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun x hx =>
  ⟨1, x, hs, hx, one_mul _⟩
#align set.subset_mul_right Set.subset_mul_right

/-- The singleton operation as a `monoid_hom`. -/
@[to_additive "The singleton operation as an `add_monoid_hom`."]
def singletonMonoidHom : α →* Set α :=
  { singletonMulHom, singletonOneHom with }
#align set.singleton_monoid_hom Set.singletonMonoidHom

@[simp, to_additive]
theorem coe_singleton_monoid_hom : (singletonMonoidHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_monoid_hom Set.coe_singleton_monoid_hom

@[simp, to_additive]
theorem singleton_monoid_hom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl
#align set.singleton_monoid_hom_apply Set.singleton_monoid_hom_apply

end MulOneClass

section Monoid

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_monoid` under pointwise operations if `α` is."]
protected def monoid : Monoid (Set α) :=
  { Set.semigroup, Set.mulOneClass, Set.hasNpow with }
#align set.monoid Set.monoid

scoped[Pointwise] attribute [instance] Set.monoid Set.addMonoid

@[to_additive]
theorem pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
  | 0 => by 
    rw [pow_zero]
    exact one_mem_one
  | n + 1 => by 
    rw [pow_succ]
    exact mul_mem_mul ha (pow_mem_pow _)
#align set.pow_mem_pow Set.pow_mem_pow

@[to_additive]
theorem pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
  | 0 => by 
    rw [pow_zero]
    exact subset.rfl
  | n + 1 => by 
    rw [pow_succ]
    exact mul_subset_mul hst (pow_subset_pow _)
#align set.pow_subset_pow Set.pow_subset_pow

@[to_additive]
theorem pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) : m ≤ n → s ^ m ⊆ s ^ n := by
  refine' Nat.le_induction _ (fun n h ih => _) _
  · exact subset.rfl
  · rw [pow_succ]
    exact ih.trans (subset_mul_right _ hs)
#align set.pow_subset_pow_of_one_mem Set.pow_subset_pow_of_one_mem

@[simp, to_additive]
theorem empty_pow {n : ℕ} (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ := by
  rw [← tsub_add_cancel_of_le (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn), pow_succ, empty_mul]
#align set.empty_pow Set.empty_pow

@[to_additive]
theorem mul_univ_of_one_mem (hs : (1 : α) ∈ s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, hs, mem_univ _, one_mul _⟩
#align set.mul_univ_of_one_mem Set.mul_univ_of_one_mem

@[to_additive]
theorem univ_mul_of_one_mem (ht : (1 : α) ∈ t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, mem_univ _, ht, mul_one _⟩
#align set.univ_mul_of_one_mem Set.univ_mul_of_one_mem

@[simp, to_additive]
theorem univ_mul_univ : (univ : Set α) * univ = univ :=
  mul_univ_of_one_mem <| mem_univ _
#align set.univ_mul_univ Set.univ_mul_univ

--TODO: `to_additive` trips up on the `1 : ℕ` used in the pattern-matching.
@[simp]
theorem nsmul_univ {α : Type _} [AddMonoid α] : ∀ {n : ℕ}, n ≠ 0 → n • (univ : Set α) = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => one_nsmul _
  | n + 2 => fun _ => by rw [succ_nsmul, nsmul_univ n.succ_ne_zero, univ_add_univ]
#align set.nsmul_univ Set.nsmul_univ

@[simp, to_additive nsmul_univ]
theorem univ_pow : ∀ {n : ℕ}, n ≠ 0 → (univ : Set α) ^ n = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => pow_one _
  | n + 2 => fun _ => by rw [pow_succ, univ_pow n.succ_ne_zero, univ_mul_univ]
#align set.univ_pow Set.univ_pow

@[to_additive]
protected theorem IsUnit.set : IsUnit a → IsUnit ({a} : Set α) :=
  IsUnit.map (singletonMonoidHom : α →* Set α)
#align is_unit.set IsUnit.set

end Monoid

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_monoid` under pointwise operations if `α` is."]
protected def commMonoid [CommMonoid α] : CommMonoid (Set α) :=
  { Set.monoid, Set.commSemigroup with }
#align set.comm_monoid Set.commMonoid

scoped[Pointwise] attribute [instance] Set.commMonoid Set.addCommMonoid

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Set α}

@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  refine' ⟨fun h => _, _⟩
  · have hst : (s * t).Nonempty := h.symm.subst one_nonempty
    obtain ⟨a, ha⟩ := hst.of_image2_left
    obtain ⟨b, hb⟩ := hst.of_image2_right
    have H : ∀ {a b}, a ∈ s → b ∈ t → a * b = (1 : α) := fun a b ha hb =>
      h.subset <| mem_image2_of_mem ha hb
    refine' ⟨a, b, _, _, H ha hb⟩ <;> refine' eq_singleton_iff_unique_mem.2 ⟨‹_›, fun x hx => _⟩
    · exact (eq_inv_of_mul_eq_one_left <| H hx hb).trans (inv_eq_of_mul_eq_one_left <| H ha hb)
    · exact (eq_inv_of_mul_eq_one_right <| H ha hx).trans (inv_eq_of_mul_eq_one_right <| H ha hb)
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [singleton_mul_singleton, h, singleton_one]
#align set.mul_eq_one_iff Set.mul_eq_one_iff

/-- `set α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive "`set α` is a subtraction monoid under pointwise operations if `α` is."]
protected def divisionMonoid : DivisionMonoid (Set α) :=
  { Set.monoid, Set.hasInvolutiveInv, Set.hasDiv, Set.hasZpow with
    mul_inv_rev := fun s t => by 
      simp_rw [← image_inv]
      exact image_image2_antidistrib mul_inv_rev
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Set.mul_eq_one_iff.1 h
      rw [inv_singleton, inv_eq_of_mul_eq_one_right hab]
    div_eq_mul_inv := fun s t => by
      rw [← image_id (s / t), ← image_inv]
      exact image_image2_distrib_right div_eq_mul_inv }
#align set.division_monoid Set.divisionMonoid

@[simp, to_additive]
theorem is_unit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Set.mul_eq_one_iff.1 u.mul_inv
    refine' ⟨a, ha, ⟨a, b, h, singleton_injective _⟩, rfl⟩
    rw [← singleton_mul_singleton, ← ha, ← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.set
#align set.is_unit_iff Set.is_unit_iff

end DivisionMonoid

/-- `set α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive SubtractionCommMonoid
      "`set α` is a commutative subtraction monoid under pointwise\noperations if `α` is."]
protected def divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (Set α) :=
  { Set.divisionMonoid, Set.commSemigroup with }
#align set.division_comm_monoid Set.divisionCommMonoid

/-- `set α` has distributive negation if `α` has. -/
protected def hasDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Set α) :=
  { Set.hasInvolutiveNeg with
    neg_mul := fun _ _ => by 
      simp_rw [← image_neg]
      exact image2_image_left_comm neg_mul
    mul_neg := fun _ _ => by 
      simp_rw [← image_neg]
      exact image_image2_right_comm mul_neg }
#align set.has_distrib_neg Set.hasDistribNeg

scoped[Pointwise]
  attribute [instance]
    Set.divisionMonoid Set.subtractionMonoid Set.divisionCommMonoid Set.subtractionCommMonoid Set.hasDistribNeg

section Distrib

variable [Distrib α] (s t u : Set α)

/-!
Note that `set α` is not a `distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
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

/-! Note that `set` is not a `mul_zero_class` because `0 * ∅ ≠ 0`. -/


theorem mul_zero_subset (s : Set α) : s * 0 ⊆ 0 := by simp [subset_def, mem_mul]
#align set.mul_zero_subset Set.mul_zero_subset

theorem zero_mul_subset (s : Set α) : 0 * s ⊆ 0 := by simp [subset_def, mem_mul]
#align set.zero_mul_subset Set.zero_mul_subset

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by simpa [mem_mul] using hs
#align set.nonempty.mul_zero Set.Nonempty.mul_zero

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by simpa [mem_mul] using hs
#align set.nonempty.zero_mul Set.Nonempty.zero_mul

end MulZeroClass

section Group

variable [Group α] {s t : Set α} {a b : α}

/-! Note that `set` is not a `group` because `s / s ≠ 1` in general. -/


@[simp, to_additive]
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, Set.Nonempty]
#align set.one_mem_div_iff Set.one_mem_div_iff

@[to_additive]
theorem not_one_mem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left
#align set.not_one_mem_div_iff Set.not_one_mem_div_iff

alias not_one_mem_div_iff ↔ _ _root_.disjoint.one_not_mem_div_set

attribute [to_additive] Disjoint.one_not_mem_div_set

@[to_additive]
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, a, ha, ha, div_self' _⟩
#align set.nonempty.one_mem_div Set.Nonempty.one_mem_div

@[to_additive]
theorem is_unit_singleton (a : α) : IsUnit ({a} : Set α) :=
  (Group.isUnit a).Set
#align set.is_unit_singleton Set.is_unit_singleton

@[simp, to_additive]
theorem is_unit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [is_unit_iff, Group.isUnit, and_true_iff]
#align set.is_unit_iff_singleton Set.is_unit_iff_singleton

@[simp, to_additive]
theorem image_mul_left : (· * ·) a '' t = (· * ·) a⁻¹ ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp
#align set.image_mul_left Set.image_mul_left

@[simp, to_additive]
theorem image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp
#align set.image_mul_right Set.image_mul_right

@[to_additive]
theorem image_mul_left' : (fun b => a⁻¹ * b) '' t = (fun b => a * b) ⁻¹' t := by simp
#align set.image_mul_left' Set.image_mul_left'

@[to_additive]
theorem image_mul_right' : (· * b⁻¹) '' t = (· * b) ⁻¹' t := by simp
#align set.image_mul_right' Set.image_mul_right'

@[simp, to_additive]
theorem preimage_mul_left_singleton : (· * ·) a ⁻¹' {b} = {a⁻¹ * b} := by
  rw [← image_mul_left', image_singleton]
#align set.preimage_mul_left_singleton Set.preimage_mul_left_singleton

@[simp, to_additive]
theorem preimage_mul_right_singleton : (· * a) ⁻¹' {b} = {b * a⁻¹} := by
  rw [← image_mul_right', image_singleton]
#align set.preimage_mul_right_singleton Set.preimage_mul_right_singleton

@[simp, to_additive]
theorem preimage_mul_left_one : (· * ·) a ⁻¹' 1 = {a⁻¹} := by
  rw [← image_mul_left', image_one, mul_one]
#align set.preimage_mul_left_one Set.preimage_mul_left_one

@[simp, to_additive]
theorem preimage_mul_right_one : (· * b) ⁻¹' 1 = {b⁻¹} := by
  rw [← image_mul_right', image_one, one_mul]
#align set.preimage_mul_right_one Set.preimage_mul_right_one

@[to_additive]
theorem preimage_mul_left_one' : (fun b => a⁻¹ * b) ⁻¹' 1 = {a} := by simp
#align set.preimage_mul_left_one' Set.preimage_mul_left_one'

@[to_additive]
theorem preimage_mul_right_one' : (· * b⁻¹) ⁻¹' 1 = {b} := by simp
#align set.preimage_mul_right_one' Set.preimage_mul_right_one'

@[simp, to_additive]
theorem mul_univ (hs : s.Nonempty) : s * (univ : Set α) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ * b, ha, trivial, mul_inv_cancel_left _ _⟩
#align set.mul_univ Set.mul_univ

@[simp, to_additive]
theorem univ_mul (ht : t.Nonempty) : (univ : Set α) * t = univ :=
  let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, a, trivial, ha, inv_mul_cancel_right _ _⟩
#align set.univ_mul Set.univ_mul

end Group

section GroupWithZero

variable [GroupWithZero α] {s t : Set α}

theorem div_zero_subset (s : Set α) : s / 0 ⊆ 0 := by simp [subset_def, mem_div]
#align set.div_zero_subset Set.div_zero_subset

theorem zero_div_subset (s : Set α) : 0 / s ⊆ 0 := by simp [subset_def, mem_div]
#align set.zero_div_subset Set.zero_div_subset

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by simpa [mem_div] using hs
#align set.nonempty.div_zero Set.Nonempty.div_zero

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by simpa [mem_div] using hs
#align set.nonempty.zero_div Set.Nonempty.zero_div

end GroupWithZero

section Mul

variable [Mul α] [Mul β] [MulHomClass F α β] (m : F) {s t : Set α}

include α β

@[to_additive]
theorem image_mul : m '' (s * t) = m '' s * m '' t :=
  image_image2_distrib <| map_mul m
#align set.image_mul Set.image_mul

@[to_additive]
theorem preimage_mul_preimage_subset {s t : Set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, _, ‹_›, ‹_›, (map_mul m _ _).symm⟩
#align set.preimage_mul_preimage_subset Set.preimage_mul_preimage_subset

end Mul

section Group

variable [Group α] [DivisionMonoid β] [MonoidHomClass F α β] (m : F) {s t : Set α}

include α β

@[to_additive]
theorem image_div : m '' (s / t) = m '' s / m '' t :=
  image_image2_distrib <| map_div m
#align set.image_div Set.image_div

@[to_additive]
theorem preimage_div_preimage_subset {s t : Set β} : m ⁻¹' s / m ⁻¹' t ⊆ m ⁻¹' (s / t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, _, ‹_›, ‹_›, (map_div m _ _).symm⟩
#align set.preimage_div_preimage_subset Set.preimage_div_preimage_subset

end Group

@[to_additive]
theorem bdd_above_mul [OrderedCommMonoid α] {A B : Set α} :
    BddAbove A → BddAbove B → BddAbove (A * B) := by
  rintro ⟨bA, hbA⟩ ⟨bB, hbB⟩
  use bA * bB
  rintro x ⟨xa, xb, hxa, hxb, rfl⟩
  exact mul_le_mul' (hbA hxa) (hbB hxb)
#align set.bdd_above_mul Set.bdd_above_mul

end Set

/-! ### Miscellaneous -/


open Set

open Pointwise

namespace Group

theorem card_pow_eq_card_pow_card_univ_aux {f : ℕ → ℕ} (h1 : Monotone f) {B : ℕ} (h2 : ∀ n, f n ≤ B)
    (h3 : ∀ n, f n = f (n + 1) → f (n + 1) = f (n + 2)) : ∀ k, B ≤ k → f k = f B := by
  have key : ∃ n : ℕ, n ≤ B ∧ f n = f (n + 1) := by
    contrapose! h2
    suffices ∀ n : ℕ, n ≤ B + 1 → n ≤ f n by exact ⟨B + 1, this (B + 1) (le_refl (B + 1))⟩
    exact fun n =>
      Nat.rec (fun h => Nat.zero_le (f 0))
        (fun n ih h =>
          lt_of_le_of_lt (ih (n.le_succ.trans h))
            (lt_of_le_of_ne (h1 n.le_succ) (h2 n (nat.succ_le_succ_iff.mp h))))
        n
  · obtain ⟨n, hn1, hn2⟩ := key
    replace key : ∀ k : ℕ, f (n + k) = f (n + k + 1) ∧ f (n + k) = f n := fun k =>
      Nat.rec ⟨hn2, rfl⟩ (fun k ih => ⟨h3 _ ih.1, ih.1.symm.trans ih.2⟩) k
    replace key : ∀ k : ℕ, n ≤ k → f k = f n := fun k hk =>
      (congr_arg f (add_tsub_cancel_of_le hk)).symm.trans (key (k - n)).2
    exact fun k hk => (key k (hn1.trans hk)).trans (key B hn1).symm
#align group.card_pow_eq_card_pow_card_univ_aux Group.card_pow_eq_card_pow_card_univ_aux

end Group

