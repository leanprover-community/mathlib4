/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Set.Pointwise.Finite
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Data.Set.Pointwise.ListOfFn
import Mathlib.GroupTheory.GroupAction.Pi
import Mathlib.SetTheory.Cardinal.Finite

#align_import data.finset.pointwise from "leanprover-community/mathlib"@"eba7871095e834365616b5e43c8c7bb0b37058d0"

/-!
# Pointwise operations of finsets

This file defines pointwise algebraic operations on finsets.

## Main declarations

For finsets `s` and `t`:
* `0` (`Finset.zero`): The singleton `{0}`.
* `1` (`Finset.one`): The singleton `{1}`.
* `-s` (`Finset.neg`): Negation, finset of all `-x` where `x ∈ s`.
* `s⁻¹` (`Finset.inv`): Inversion, finset of all `x⁻¹` where `x ∈ s`.
* `s + t` (`Finset.add`): Addition, finset of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s * t` (`Finset.mul`): Multiplication, finset of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s - t` (`Finset.sub`): Subtraction, finset of all `x - y` where `x ∈ s` and `y ∈ t`.
* `s / t` (`Finset.div`): Division, finset of all `x / y` where `x ∈ s` and `y ∈ t`.
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

We put all instances in the locale `Pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the locale to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`.

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/


open Function MulOpposite

open scoped Pointwise

variable {F α β γ : Type*}

namespace Finset

/-! ### `0`/`1` as finsets -/

section One

variable [One α] {s : Finset α} {a : α}

/-- The finset `1 : Finset α` is defined as `{1}` in locale `Pointwise`. -/
@[to_additive "The finset `0 : Finset α` is defined as `{0}` in locale `Pointwise`."]
protected def one : One (Finset α) :=
  ⟨{1}⟩
#align finset.has_one Finset.one
#align finset.has_zero Finset.zero

scoped[Pointwise] attribute [instance] Finset.one Finset.zero

@[to_additive (attr := simp)]
theorem mem_one : a ∈ (1 : Finset α) ↔ a = 1 :=
  mem_singleton
#align finset.mem_one Finset.mem_one
#align finset.mem_zero Finset.mem_zero

@[to_additive (attr := simp, norm_cast)]
theorem coe_one : ↑(1 : Finset α) = (1 : Set α) :=
  coe_singleton 1
#align finset.coe_one Finset.coe_one
#align finset.coe_zero Finset.coe_zero

@[to_additive (attr := simp, norm_cast)]
lemma coe_eq_one : (s : Set α) = 1 ↔ s = 1 := coe_eq_singleton

@[to_additive (attr := simp)]
theorem one_subset : (1 : Finset α) ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff
#align finset.one_subset Finset.one_subset
#align finset.zero_subset Finset.zero_subset

@[to_additive]
theorem singleton_one : ({1} : Finset α) = 1 :=
  rfl
#align finset.singleton_one Finset.singleton_one
#align finset.singleton_zero Finset.singleton_zero

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Finset α) :=
  mem_singleton_self _
#align finset.one_mem_one Finset.one_mem_one
#align finset.zero_mem_zero Finset.zero_mem_zero

@[to_additive (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]
theorem one_nonempty : (1 : Finset α).Nonempty :=
  ⟨1, one_mem_one⟩
#align finset.one_nonempty Finset.one_nonempty
#align finset.zero_nonempty Finset.zero_nonempty

@[to_additive (attr := simp)]
protected theorem map_one {f : α ↪ β} : map f 1 = {f 1} :=
  map_singleton f 1
#align finset.map_one Finset.map_one
#align finset.map_zero Finset.map_zero

@[to_additive (attr := simp)]
theorem image_one [DecidableEq β] {f : α → β} : image f 1 = {f 1} :=
  image_singleton _ _
#align finset.image_one Finset.image_one
#align finset.image_zero Finset.image_zero

@[to_additive]
theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff
#align finset.subset_one_iff_eq Finset.subset_one_iff_eq
#align finset.subset_zero_iff_eq Finset.subset_zero_iff_eq

@[to_additive]
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 :=
  h.subset_singleton_iff
#align finset.nonempty.subset_one_iff Finset.Nonempty.subset_one_iff
#align finset.nonempty.subset_zero_iff Finset.Nonempty.subset_zero_iff

@[to_additive (attr := simp)]
theorem card_one : (1 : Finset α).card = 1 :=
  card_singleton _
#align finset.card_one Finset.card_one
#align finset.card_zero Finset.card_zero

/-- The singleton operation as a `OneHom`. -/
@[to_additive "The singleton operation as a `ZeroHom`."]
def singletonOneHom : OneHom α (Finset α) where
  toFun := singleton; map_one' := singleton_one
#align finset.singleton_one_hom Finset.singletonOneHom
#align finset.singleton_zero_hom Finset.singletonZeroHom

@[to_additive (attr := simp)]
theorem coe_singletonOneHom : (singletonOneHom : α → Finset α) = singleton :=
  rfl
#align finset.coe_singleton_one_hom Finset.coe_singletonOneHom
#align finset.coe_singleton_zero_hom Finset.coe_singletonZeroHom

@[to_additive (attr := simp)]
theorem singletonOneHom_apply (a : α) : singletonOneHom a = {a} :=
  rfl
#align finset.singleton_one_hom_apply Finset.singletonOneHom_apply
#align finset.singleton_zero_hom_apply Finset.singletonZeroHom_apply

/-- Lift a `OneHom` to `Finset` via `image`. -/
@[to_additive (attr := simps) "Lift a `ZeroHom` to `Finset` via `image`"]
def imageOneHom [DecidableEq β] [One β] [FunLike F α β] [OneHomClass F α β] (f : F) :
    OneHom (Finset α) (Finset β) where
  toFun := Finset.image f
  map_one' := by rw [image_one, map_one, singleton_one]
#align finset.image_one_hom Finset.imageOneHom
#align finset.image_zero_hom Finset.imageZeroHom

@[to_additive (attr := simp)]
lemma sup_one [SemilatticeSup β] [OrderBot β] (f : α → β) : sup 1 f = f 1 := sup_singleton

@[to_additive (attr := simp)]
lemma sup'_one [SemilatticeSup β] (f : α → β) : sup' 1 one_nonempty f = f 1 := rfl

@[to_additive (attr := simp)]
lemma inf_one [SemilatticeInf β] [OrderTop β] (f : α → β) : inf 1 f = f 1 := inf_singleton

@[to_additive (attr := simp)]
lemma inf'_one [SemilatticeInf β] (f : α → β) : inf' 1 one_nonempty f = f 1 := rfl

@[to_additive (attr := simp)]
lemma max_one [LinearOrder α] : (1 : Finset α).max = 1 := rfl

@[to_additive (attr := simp)]
lemma min_one [LinearOrder α] : (1 : Finset α).min = 1 := rfl

@[to_additive (attr := simp)]
lemma max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty = 1 := rfl

@[to_additive (attr := simp)]
lemma min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty = 1 := rfl

end One

/-! ### Finset negation/inversion -/

section Inv

variable [DecidableEq α] [Inv α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise inversion of finset `s⁻¹` is defined as `{x⁻¹ | x ∈ s}` in locale `Pointwise`. -/
@[to_additive
      "The pointwise negation of finset `-s` is defined as `{-x | x ∈ s}` in locale `Pointwise`."]
protected def inv : Inv (Finset α) :=
  ⟨image Inv.inv⟩
#align finset.has_inv Finset.inv
#align finset.has_neg Finset.neg

scoped[Pointwise] attribute [instance] Finset.inv Finset.neg

@[to_additive]
theorem inv_def : s⁻¹ = s.image fun x => x⁻¹ :=
  rfl
#align finset.inv_def Finset.inv_def
#align finset.neg_def Finset.neg_def

@[to_additive]
theorem image_inv : (s.image fun x => x⁻¹) = s⁻¹ :=
  rfl
#align finset.image_inv Finset.image_inv
#align finset.image_neg Finset.image_neg

@[to_additive]
theorem mem_inv {x : α} : x ∈ s⁻¹ ↔ ∃ y ∈ s, y⁻¹ = x :=
  mem_image
#align finset.mem_inv Finset.mem_inv
#align finset.mem_neg Finset.mem_neg

@[to_additive]
theorem inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ :=
  mem_image_of_mem _ ha
#align finset.inv_mem_inv Finset.inv_mem_inv
#align finset.neg_mem_neg Finset.neg_mem_neg

@[to_additive]
theorem card_inv_le : s⁻¹.card ≤ s.card :=
  card_image_le
#align finset.card_inv_le Finset.card_inv_le
#align finset.card_neg_le Finset.card_neg_le

@[to_additive (attr := simp)]
theorem inv_empty : (∅ : Finset α)⁻¹ = ∅ :=
  image_empty _
#align finset.inv_empty Finset.inv_empty
#align finset.neg_empty Finset.neg_empty

@[to_additive (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]
theorem inv_nonempty_iff : s⁻¹.Nonempty ↔ s.Nonempty := image_nonempty
#align finset.inv_nonempty_iff Finset.inv_nonempty_iff
#align finset.neg_nonempty_iff Finset.neg_nonempty_iff

alias ⟨Nonempty.of_inv, Nonempty.inv⟩ := inv_nonempty_iff
#align finset.nonempty.of_inv Finset.Nonempty.of_inv
#align finset.nonempty.inv Finset.Nonempty.inv

attribute [to_additive] Nonempty.inv Nonempty.of_inv

@[to_additive (attr := simp)]
theorem inv_eq_empty : s⁻¹ = ∅ ↔ s = ∅ := image_eq_empty

@[to_additive (attr := mono)]
theorem inv_subset_inv (h : s ⊆ t) : s⁻¹ ⊆ t⁻¹ :=
  image_subset_image h
#align finset.inv_subset_inv Finset.inv_subset_inv
#align finset.neg_subset_neg Finset.neg_subset_neg

@[to_additive (attr := simp)]
theorem inv_singleton (a : α) : ({a} : Finset α)⁻¹ = {a⁻¹} :=
  image_singleton _ _
#align finset.inv_singleton Finset.inv_singleton
#align finset.neg_singleton Finset.neg_singleton

@[to_additive (attr := simp)]
theorem inv_insert (a : α) (s : Finset α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ :=
  image_insert _ _ _
#align finset.inv_insert Finset.inv_insert
#align finset.neg_insert Finset.neg_insert

@[to_additive (attr := simp)]
lemma sup_inv [SemilatticeSup β] [OrderBot β] (s : Finset α) (f : α → β) :
    sup s⁻¹ f = sup s (f ·⁻¹) :=
  sup_image ..

@[to_additive (attr := simp)]
lemma sup'_inv [SemilatticeSup β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α → β) :
    sup' s⁻¹ hs f = sup' s hs.of_inv (f ·⁻¹) :=
  sup'_image ..

@[to_additive (attr := simp)]
lemma inf_inv [SemilatticeInf β] [OrderTop β] (s : Finset α) (f : α → β) :
    inf s⁻¹ f = inf s (f ·⁻¹) :=
  inf_image ..

@[to_additive (attr := simp)]
lemma inf'_inv [SemilatticeInf β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α → β) :
    inf' s⁻¹ hs f = inf' s hs.of_inv (f ·⁻¹) :=
  inf'_image ..

@[to_additive] lemma image_op_inv (s : Finset α) : s⁻¹.image op = (s.image op)⁻¹ :=
  image_comm op_inv

end Inv

open Pointwise

section InvolutiveInv
variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

@[to_additive (attr := simp)]
lemma mem_inv' : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := by simp [mem_inv, inv_eq_iff_eq_inv]

@[to_additive (attr := simp, norm_cast)]
theorem coe_inv (s : Finset α) : ↑s⁻¹ = (s : Set α)⁻¹ := coe_image.trans Set.image_inv
#align finset.coe_inv Finset.coe_inv
#align finset.coe_neg Finset.coe_neg

@[to_additive (attr := simp)]
theorem card_inv (s : Finset α) : s⁻¹.card = s.card := card_image_of_injective _ inv_injective
#align finset.card_inv Finset.card_inv
#align finset.card_neg Finset.card_neg

@[to_additive (attr := simp)]
theorem preimage_inv (s : Finset α) : s.preimage (·⁻¹) (inv_injective.injOn _) = s⁻¹ :=
  coe_injective <| by rw [coe_preimage, Set.inv_preimage, coe_inv]
#align finset.preimage_inv Finset.preimage_inv
#align finset.preimage_neg Finset.preimage_neg

@[to_additive (attr := simp)]
lemma inv_univ [Fintype α] : (univ : Finset α)⁻¹ = univ := by ext; simp

@[to_additive (attr := simp)]
lemma inv_inter (s t : Finset α) : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ := coe_injective <| by simp

end InvolutiveInv

/-! ### Finset addition/multiplication -/


section Mul

variable [DecidableEq α] [DecidableEq β] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise multiplication of finsets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}`
in locale `Pointwise`. -/
@[to_additive
      "The pointwise addition of finsets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in
      locale `Pointwise`."]
protected def mul : Mul (Finset α) :=
  ⟨image₂ (· * ·)⟩
#align finset.has_mul Finset.mul
#align finset.has_add Finset.add

scoped[Pointwise] attribute [instance] Finset.mul Finset.add

@[to_additive]
theorem mul_def : s * t = (s ×ˢ t).image fun p : α × α => p.1 * p.2 :=
  rfl
#align finset.mul_def Finset.mul_def
#align finset.add_def Finset.add_def

@[to_additive]
theorem image_mul_product : ((s ×ˢ t).image fun x : α × α => x.fst * x.snd) = s * t :=
  rfl
#align finset.image_mul_product Finset.image_mul_product
#align finset.image_add_product Finset.image_add_product

@[to_additive]
theorem mem_mul {x : α} : x ∈ s * t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := mem_image₂
#align finset.mem_mul Finset.mem_mul
#align finset.mem_add Finset.mem_add

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t :=
  coe_image₂ _ _ _
#align finset.coe_mul Finset.coe_mul
#align finset.coe_add Finset.coe_add

@[to_additive]
theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t :=
  mem_image₂_of_mem
#align finset.mul_mem_mul Finset.mul_mem_mul
#align finset.add_mem_add Finset.add_mem_add

@[to_additive]
theorem card_mul_le : (s * t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.card_mul_le Finset.card_mul_le
#align finset.card_add_le Finset.card_add_le

@[to_additive]
theorem card_mul_iff :
    (s * t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 :=
  card_image₂_iff
#align finset.card_mul_iff Finset.card_mul_iff
#align finset.card_add_iff Finset.card_add_iff

@[to_additive (attr := simp)]
theorem empty_mul (s : Finset α) : ∅ * s = ∅ :=
  image₂_empty_left
#align finset.empty_mul Finset.empty_mul
#align finset.empty_add Finset.empty_add

@[to_additive (attr := simp)]
theorem mul_empty (s : Finset α) : s * ∅ = ∅ :=
  image₂_empty_right
#align finset.mul_empty Finset.mul_empty
#align finset.add_empty Finset.add_empty

@[to_additive (attr := simp)]
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.mul_eq_empty Finset.mul_eq_empty
#align finset.add_eq_empty Finset.add_eq_empty

@[to_additive (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.mul_nonempty Finset.mul_nonempty
#align finset.add_nonempty Finset.add_nonempty

@[to_additive]
theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.mul Finset.Nonempty.mul
#align finset.nonempty.add Finset.Nonempty.add

@[to_additive]
theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_mul_left Finset.Nonempty.of_mul_left
#align finset.nonempty.of_add_left Finset.Nonempty.of_add_left

@[to_additive]
theorem Nonempty.of_mul_right : (s * t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_mul_right Finset.Nonempty.of_mul_right
#align finset.nonempty.of_add_right Finset.Nonempty.of_add_right

@[to_additive]
theorem mul_singleton (a : α) : s * {a} = s.image (· * a) :=
  image₂_singleton_right
#align finset.mul_singleton Finset.mul_singleton
#align finset.add_singleton Finset.add_singleton

@[to_additive]
theorem singleton_mul (a : α) : {a} * s = s.image (a * ·) :=
  image₂_singleton_left
#align finset.singleton_mul Finset.singleton_mul
#align finset.singleton_add Finset.singleton_add

@[to_additive (attr := simp)]
theorem singleton_mul_singleton (a b : α) : ({a} : Finset α) * {b} = {a * b} :=
  image₂_singleton
#align finset.singleton_mul_singleton Finset.singleton_mul_singleton
#align finset.singleton_add_singleton Finset.singleton_add_singleton

@[to_additive (attr := mono)]
theorem mul_subset_mul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ * t₁ ⊆ s₂ * t₂ :=
  image₂_subset
#align finset.mul_subset_mul Finset.mul_subset_mul
#align finset.add_subset_add Finset.add_subset_add

@[to_additive]
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image₂_subset_left
#align finset.mul_subset_mul_left Finset.mul_subset_mul_left
#align finset.add_subset_add_left Finset.add_subset_add_left

@[to_additive]
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image₂_subset_right
#align finset.mul_subset_mul_right Finset.mul_subset_mul_right
#align finset.add_subset_add_right Finset.add_subset_add_right

@[to_additive]
theorem mul_subset_iff : s * t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x * y ∈ u :=
  image₂_subset_iff
#align finset.mul_subset_iff Finset.mul_subset_iff
#align finset.add_subset_iff Finset.add_subset_iff

@[to_additive]
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image₂_union_left
#align finset.union_mul Finset.union_mul
#align finset.union_add Finset.union_add

@[to_additive]
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image₂_union_right
#align finset.mul_union Finset.mul_union
#align finset.add_union Finset.add_union

@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image₂_inter_subset_left
#align finset.inter_mul_subset Finset.inter_mul_subset
#align finset.inter_add_subset Finset.inter_add_subset

@[to_additive]
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image₂_inter_subset_right
#align finset.mul_inter_subset Finset.mul_inter_subset
#align finset.add_inter_subset Finset.add_inter_subset

@[to_additive]
theorem inter_mul_union_subset_union : s₁ ∩ s₂ * (t₁ ∪ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ :=
  image₂_inter_union_subset_union
#align finset.inter_mul_union_subset_union Finset.inter_mul_union_subset_union
#align finset.inter_add_union_subset_union Finset.inter_add_union_subset_union

@[to_additive]
theorem union_mul_inter_subset_union : (s₁ ∪ s₂) * (t₁ ∩ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ :=
  image₂_union_inter_subset_union
#align finset.union_mul_inter_subset_union Finset.union_mul_inter_subset_union
#align finset.union_add_inter_subset_union Finset.union_add_inter_subset_union

/-- If a finset `u` is contained in the product of two sets `s * t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' * t'`. -/
@[to_additive
      "If a finset `u` is contained in the sum of two sets `s + t`, we can find two finsets
      `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' + t'`."]
theorem subset_mul {s t : Set α} :
    ↑u ⊆ s * t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' * t' :=
  subset_image₂
#align finset.subset_mul Finset.subset_mul
#align finset.subset_add Finset.subset_add

@[to_additive]
theorem image_mul : (s * t).image (f : α → β) = s.image f * t.image f :=
  image_image₂_distrib <| map_mul f
#align finset.image_mul Finset.image_mul
#align finset.image_add Finset.image_add

/-- The singleton operation as a `MulHom`. -/
@[to_additive "The singleton operation as an `AddHom`."]
def singletonMulHom : α →ₙ* Finset α where
  toFun := singleton; map_mul' _ _ := (singleton_mul_singleton _ _).symm
#align finset.singleton_mul_hom Finset.singletonMulHom
#align finset.singleton_add_hom Finset.singletonAddHom

@[to_additive (attr := simp)]
theorem coe_singletonMulHom : (singletonMulHom : α → Finset α) = singleton :=
  rfl
#align finset.coe_singleton_mul_hom Finset.coe_singletonMulHom
#align finset.coe_singleton_add_hom Finset.coe_singletonAddHom

@[to_additive (attr := simp)]
theorem singletonMulHom_apply (a : α) : singletonMulHom a = {a} :=
  rfl
#align finset.singleton_mul_hom_apply Finset.singletonMulHom_apply
#align finset.singleton_add_hom_apply Finset.singletonAddHom_apply

/-- Lift a `MulHom` to `Finset` via `image`. -/
@[to_additive (attr := simps) "Lift an `AddHom` to `Finset` via `image`"]
def imageMulHom : Finset α →ₙ* Finset β where
  toFun := Finset.image f
  map_mul' _ _ := image_mul _
#align finset.image_mul_hom Finset.imageMulHom
#align finset.image_add_hom Finset.imageAddHom

@[to_additive (attr := simp (default + 1))]
lemma sup_mul_le [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α → β} {a : β} :
    sup (s * t) f ≤ a ↔ ∀ x ∈ s, ∀ y ∈ t, f (x * y) ≤ a :=
  sup_image₂_le

@[to_additive]
lemma sup_mul_left [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s * t) f = sup s fun x ↦ sup t (f <| x * ·) :=
  sup_image₂_left ..

@[to_additive]
lemma sup_mul_right [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s * t) f = sup t fun y ↦ sup s (f <| · * y) :=
  sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]
lemma le_inf_mul [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α → β} {a : β} :
    a ≤ inf (s * t) f ↔ ∀ x ∈ s, ∀ y ∈ t, a ≤ f (x * y) :=
  le_inf_image₂

@[to_additive]
lemma inf_mul_left [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s * t) f = inf s fun x ↦ inf t (f <| x * ·) :=
  inf_image₂_left ..

@[to_additive]
lemma inf_mul_right [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s * t) f = inf t fun y ↦ inf s (f <| · * y) :=
  inf_image₂_right ..

end Mul

/-! ### Finset subtraction/division -/

section Div

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise division of finsets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`Pointwise`. -/
@[to_additive
      "The pointwise subtraction of finsets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}`
      in locale `Pointwise`."]
protected def div : Div (Finset α) :=
  ⟨image₂ (· / ·)⟩
#align finset.has_div Finset.div
#align finset.has_sub Finset.sub

scoped[Pointwise] attribute [instance] Finset.div Finset.sub

@[to_additive]
theorem div_def : s / t = (s ×ˢ t).image fun p : α × α => p.1 / p.2 :=
  rfl
#align finset.div_def Finset.div_def
#align finset.sub_def Finset.sub_def

@[to_additive]
theorem image_div_product : ((s ×ˢ t).image fun x : α × α => x.fst / x.snd) = s / t :=
  rfl
#align finset.image_div_prod Finset.image_div_product
#align finset.add_image_prod Finset.image_sub_product

@[to_additive]
theorem mem_div : a ∈ s / t ↔ ∃ b ∈ s, ∃ c ∈ t, b / c = a :=
  mem_image₂
#align finset.mem_div Finset.mem_div
#align finset.mem_sub Finset.mem_sub

@[to_additive (attr := simp, norm_cast)]
theorem coe_div (s t : Finset α) : (↑(s / t) : Set α) = ↑s / ↑t :=
  coe_image₂ _ _ _
#align finset.coe_div Finset.coe_div
#align finset.coe_sub Finset.coe_sub

@[to_additive]
theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t :=
  mem_image₂_of_mem
#align finset.div_mem_div Finset.div_mem_div
#align finset.sub_mem_sub Finset.sub_mem_sub

@[to_additive]
theorem div_card_le : (s / t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.div_card_le Finset.div_card_le
#align finset.sub_card_le Finset.sub_card_le

@[to_additive (attr := simp)]
theorem empty_div (s : Finset α) : ∅ / s = ∅ :=
  image₂_empty_left
#align finset.empty_div Finset.empty_div
#align finset.empty_sub Finset.empty_sub

@[to_additive (attr := simp)]
theorem div_empty (s : Finset α) : s / ∅ = ∅ :=
  image₂_empty_right
#align finset.div_empty Finset.div_empty
#align finset.sub_empty Finset.sub_empty

@[to_additive (attr := simp)]
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.div_eq_empty Finset.div_eq_empty
#align finset.sub_eq_empty Finset.sub_eq_empty

@[to_additive (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.div_nonempty Finset.div_nonempty
#align finset.sub_nonempty Finset.sub_nonempty

@[to_additive]
theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.div Finset.Nonempty.div
#align finset.nonempty.sub Finset.Nonempty.sub

@[to_additive]
theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_div_left Finset.Nonempty.of_div_left
#align finset.nonempty.of_sub_left Finset.Nonempty.of_sub_left

@[to_additive]
theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_div_right Finset.Nonempty.of_div_right
#align finset.nonempty.of_sub_right Finset.Nonempty.of_sub_right

@[to_additive (attr := simp)]
theorem div_singleton (a : α) : s / {a} = s.image (· / a) :=
  image₂_singleton_right
#align finset.div_singleton Finset.div_singleton
#align finset.sub_singleton Finset.sub_singleton

@[to_additive (attr := simp)]
theorem singleton_div (a : α) : {a} / s = s.image (a / ·) :=
  image₂_singleton_left
#align finset.singleton_div Finset.singleton_div
#align finset.singleton_sub Finset.singleton_sub

-- @[to_additive (attr := simp)]
-- Porting note (#10618): simp can prove this & the additive version
@[to_additive]
theorem singleton_div_singleton (a b : α) : ({a} : Finset α) / {b} = {a / b} :=
  image₂_singleton
#align finset.singleton_div_singleton Finset.singleton_div_singleton
#align finset.singleton_sub_singleton Finset.singleton_sub_singleton

@[to_additive (attr := mono)]
theorem div_subset_div : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ / t₁ ⊆ s₂ / t₂ :=
  image₂_subset
#align finset.div_subset_div Finset.div_subset_div
#align finset.sub_subset_sub Finset.sub_subset_sub

@[to_additive]
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image₂_subset_left
#align finset.div_subset_div_left Finset.div_subset_div_left
#align finset.sub_subset_sub_left Finset.sub_subset_sub_left

@[to_additive]
theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t :=
  image₂_subset_right
#align finset.div_subset_div_right Finset.div_subset_div_right
#align finset.sub_subset_sub_right Finset.sub_subset_sub_right

@[to_additive]
theorem div_subset_iff : s / t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x / y ∈ u :=
  image₂_subset_iff
#align finset.div_subset_iff Finset.div_subset_iff
#align finset.sub_subset_iff Finset.sub_subset_iff

@[to_additive]
theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t :=
  image₂_union_left
#align finset.union_div Finset.union_div
#align finset.union_sub Finset.union_sub

@[to_additive]
theorem div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ :=
  image₂_union_right
#align finset.div_union Finset.div_union
#align finset.sub_union Finset.sub_union

@[to_additive]
theorem inter_div_subset : s₁ ∩ s₂ / t ⊆ s₁ / t ∩ (s₂ / t) :=
  image₂_inter_subset_left
#align finset.inter_div_subset Finset.inter_div_subset
#align finset.inter_sub_subset Finset.inter_sub_subset

@[to_additive]
theorem div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
  image₂_inter_subset_right
#align finset.div_inter_subset Finset.div_inter_subset
#align finset.sub_inter_subset Finset.sub_inter_subset

@[to_additive]
theorem inter_div_union_subset_union : s₁ ∩ s₂ / (t₁ ∪ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ :=
  image₂_inter_union_subset_union
#align finset.inter_div_union_subset_union Finset.inter_div_union_subset_union
#align finset.inter_sub_union_subset_union Finset.inter_sub_union_subset_union

@[to_additive]
theorem union_div_inter_subset_union : (s₁ ∪ s₂) / (t₁ ∩ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ :=
  image₂_union_inter_subset_union
#align finset.union_div_inter_subset_union Finset.union_div_inter_subset_union
#align finset.union_sub_inter_subset_union Finset.union_sub_inter_subset_union

/-- If a finset `u` is contained in the product of two sets `s / t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' / t'`. -/
@[to_additive
      "If a finset `u` is contained in the sum of two sets `s - t`, we can find two finsets
      `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' - t'`."]
theorem subset_div {s t : Set α} :
    ↑u ⊆ s / t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' / t' :=
  subset_image₂
#align finset.subset_div Finset.subset_div
#align finset.subset_sub Finset.subset_sub

@[to_additive (attr := simp (default + 1))]
lemma sup_div_le [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α → β} {a : β} :
    sup (s / t) f ≤ a ↔ ∀ x ∈ s, ∀ y ∈ t, f (x /  y) ≤ a :=
  sup_image₂_le

@[to_additive]
lemma sup_div_left [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s / t) f = sup s fun x ↦ sup t (f <| x / ·) :=
  sup_image₂_left ..

@[to_additive]
lemma sup_div_right [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s / t) f = sup t fun y ↦ sup s (f <| · / y) :=
  sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]
lemma le_inf_div [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α → β} {a : β} :
    a ≤ inf (s / t) f ↔ ∀ x ∈ s, ∀ y ∈ t, a ≤ f (x / y) :=
  le_inf_image₂

@[to_additive]
lemma inf_div_left [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s / t) f = inf s fun x ↦ inf t (f <| x / ·) :=
  inf_image₂_left ..

@[to_additive]
lemma inf_div_right [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s / t) f = inf t fun y ↦ inf s (f <| · / y) :=
  inf_image₂_right ..

end Div

/-! ### Instances -/


open Pointwise

section Instances

variable [DecidableEq α] [DecidableEq β]

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `Finset`. See
note [pointwise nat action]. -/
protected def nsmul [Zero α] [Add α] : SMul ℕ (Finset α) :=
  ⟨nsmulRec⟩
#align finset.has_nsmul Finset.nsmul

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`Finset`. See note [pointwise nat action]. -/
protected def npow [One α] [Mul α] : Pow (Finset α) ℕ :=
  ⟨fun s n => npowRec n s⟩
#align finset.has_npow Finset.npow

attribute [to_additive existing] Finset.npow


/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `Finset`. See note [pointwise nat action]. -/
protected def zsmul [Zero α] [Add α] [Neg α] : SMul ℤ (Finset α) :=
  ⟨zsmulRec⟩
#align finset.has_zsmul Finset.zsmul

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `Finset`. See note [pointwise nat action]. -/
@[to_additive existing]
protected def zpow [One α] [Mul α] [Inv α] : Pow (Finset α) ℤ :=
  ⟨fun s n => zpowRec npowRec n s⟩
#align finset.has_zpow Finset.zpow

scoped[Pointwise] attribute [instance] Finset.nsmul Finset.npow Finset.zsmul Finset.zpow

/-- `Finset α` is a `Semigroup` under pointwise operations if `α` is. -/
@[to_additive "`Finset α` is an `AddSemigroup` under pointwise operations if `α` is. "]
protected def semigroup [Semigroup α] : Semigroup (Finset α) :=
  coe_injective.semigroup _ coe_mul
#align finset.semigroup Finset.semigroup
#align finset.add_semigroup Finset.addSemigroup

section CommSemigroup

variable [CommSemigroup α] {s t : Finset α}

/-- `Finset α` is a `CommSemigroup` under pointwise operations if `α` is. -/
@[to_additive "`Finset α` is an `AddCommSemigroup` under pointwise operations if `α` is. "]
protected def commSemigroup : CommSemigroup (Finset α) :=
  coe_injective.commSemigroup _ coe_mul
#align finset.comm_semigroup Finset.commSemigroup
#align finset.add_comm_semigroup Finset.addCommSemigroup

@[to_additive]
theorem inter_mul_union_subset : s ∩ t * (s ∪ t) ⊆ s * t :=
  image₂_inter_union_subset mul_comm
#align finset.inter_mul_union_subset Finset.inter_mul_union_subset
#align finset.inter_add_union_subset Finset.inter_add_union_subset

@[to_additive]
theorem union_mul_inter_subset : (s ∪ t) * (s ∩ t) ⊆ s * t :=
  image₂_union_inter_subset mul_comm
#align finset.union_mul_inter_subset Finset.union_mul_inter_subset
#align finset.union_add_inter_subset Finset.union_add_inter_subset

end CommSemigroup

section MulOneClass

variable [MulOneClass α]

/-- `Finset α` is a `MulOneClass` under pointwise operations if `α` is. -/
@[to_additive "`Finset α` is an `AddZeroClass` under pointwise operations if `α` is."]
protected def mulOneClass : MulOneClass (Finset α) :=
  coe_injective.mulOneClass _ (coe_singleton 1) coe_mul
#align finset.mul_one_class Finset.mulOneClass
#align finset.add_zero_class Finset.addZeroClass

scoped[Pointwise] attribute [instance] Finset.semigroup Finset.addSemigroup Finset.commSemigroup
  Finset.addCommSemigroup Finset.mulOneClass Finset.addZeroClass

@[to_additive]
theorem subset_mul_left (s : Finset α) {t : Finset α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun a ha =>
  mem_mul.2 ⟨a, ha, 1, ht, mul_one _⟩
#align finset.subset_mul_left Finset.subset_mul_left
#align finset.subset_add_left Finset.subset_add_left

@[to_additive]
theorem subset_mul_right {s : Finset α} (t : Finset α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun a ha =>
  mem_mul.2 ⟨1, hs, a, ha, one_mul _⟩
#align finset.subset_mul_right Finset.subset_mul_right
#align finset.subset_add_right Finset.subset_add_right

/-- The singleton operation as a `MonoidHom`. -/
@[to_additive "The singleton operation as an `AddMonoidHom`."]
def singletonMonoidHom : α →* Finset α :=
  { singletonMulHom, singletonOneHom with }
#align finset.singleton_monoid_hom Finset.singletonMonoidHom
#align finset.singleton_add_monoid_hom Finset.singletonAddMonoidHom

@[to_additive (attr := simp)]
theorem coe_singletonMonoidHom : (singletonMonoidHom : α → Finset α) = singleton :=
  rfl
#align finset.coe_singleton_monoid_hom Finset.coe_singletonMonoidHom
#align finset.coe_singleton_add_monoid_hom Finset.coe_singletonAddMonoidHom

@[to_additive (attr := simp)]
theorem singletonMonoidHom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl
#align finset.singleton_monoid_hom_apply Finset.singletonMonoidHom_apply
#align finset.singleton_add_monoid_hom_apply Finset.singletonAddMonoidHom_apply

/-- The coercion from `Finset` to `Set` as a `MonoidHom`. -/
@[to_additive "The coercion from `Finset` to `set` as an `AddMonoidHom`."]
noncomputable def coeMonoidHom : Finset α →* Set α where
  toFun := CoeTC.coe
  map_one' := coe_one
  map_mul' := coe_mul
#align finset.coe_monoid_hom Finset.coeMonoidHom
#align finset.coe_add_monoid_hom Finset.coeAddMonoidHom

@[to_additive (attr := simp)]
theorem coe_coeMonoidHom : (coeMonoidHom : Finset α → Set α) = CoeTC.coe :=
  rfl
#align finset.coe_coe_monoid_hom Finset.coe_coeMonoidHom
#align finset.coe_coe_add_monoid_hom Finset.coe_coeAddMonoidHom

@[to_additive (attr := simp)]
theorem coeMonoidHom_apply (s : Finset α) : coeMonoidHom s = s :=
  rfl
#align finset.coe_monoid_hom_apply Finset.coeMonoidHom_apply
#align finset.coe_add_monoid_hom_apply Finset.coeAddMonoidHom_apply

/-- Lift a `MonoidHom` to `Finset` via `image`. -/
@[to_additive (attr := simps) "Lift an `add_monoid_hom` to `Finset` via `image`"]
def imageMonoidHom [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β] (f : F) :
    Finset α →* Finset β :=
  { imageMulHom f, imageOneHom f with }
#align finset.image_monoid_hom Finset.imageMonoidHom
#align finset.image_add_monoid_hom Finset.imageAddMonoidHom

end MulOneClass

section Monoid

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

@[to_additive (attr := simp, norm_cast)]
theorem coe_pow (s : Finset α) (n : ℕ) : ↑(s ^ n) = (s : Set α) ^ n := by
  change ↑(npowRec n s) = (s: Set α) ^ n
  induction' n with n ih
  · rw [npowRec, pow_zero, coe_one]
  · rw [npowRec, pow_succ, coe_mul, ih]
#align finset.coe_pow Finset.coe_pow

/-- `Finset α` is a `Monoid` under pointwise operations if `α` is. -/
@[to_additive "`Finset α` is an `AddMonoid` under pointwise operations if `α` is. "]
protected def monoid : Monoid (Finset α) :=
  coe_injective.monoid _ coe_one coe_mul coe_pow
#align finset.monoid Finset.monoid
#align finset.add_monoid Finset.addMonoid

scoped[Pointwise] attribute [instance] Finset.monoid Finset.addMonoid

@[to_additive]
theorem pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
  | 0 => by
    rw [pow_zero]
    exact one_mem_one
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem_mul (pow_mem_pow ha n) ha
#align finset.pow_mem_pow Finset.pow_mem_pow
#align finset.nsmul_mem_nsmul Finset.nsmul_mem_nsmul

@[to_additive]
theorem pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
  | 0 => by
    simp [pow_zero]
  | n + 1 => by
    rw [pow_succ]
    exact mul_subset_mul (pow_subset_pow hst n) hst
#align finset.pow_subset_pow Finset.pow_subset_pow
#align finset.nsmul_subset_nsmul Finset.nsmul_subset_nsmul

@[to_additive]
theorem pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) : m ≤ n → s ^ m ⊆ s ^ n := by
  apply Nat.le_induction
  · exact fun _ hn => hn
  · intro n _ hmn
    rw [pow_succ]
    exact hmn.trans (subset_mul_left (s ^ n) hs)
#align finset.pow_subset_pow_of_one_mem Finset.pow_subset_pow_of_one_mem
#align finset.nsmul_subset_nsmul_of_zero_mem Finset.nsmul_subset_nsmul_of_zero_mem

@[to_additive (attr := simp, norm_cast)]
theorem coe_list_prod (s : List (Finset α)) : (↑s.prod : Set α) = (s.map (↑)).prod :=
  map_list_prod (coeMonoidHom : Finset α →* Set α) _
#align finset.coe_list_prod Finset.coe_list_prod
#align finset.coe_list_sum Finset.coe_list_sum

@[to_additive]
theorem mem_prod_list_ofFn {a : α} {s : Fin n → Finset α} :
    a ∈ (List.ofFn s).prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i => (f i : α)).prod = a := by
  rw [← mem_coe, coe_list_prod, List.map_ofFn, Set.mem_prod_list_ofFn]
  rfl
#align finset.mem_prod_list_of_fn Finset.mem_prod_list_ofFn
#align finset.mem_sum_list_of_fn Finset.mem_sum_list_ofFn

@[to_additive]
theorem mem_pow {a : α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ f : Fin n → s, (List.ofFn fun i => ↑(f i)).prod = a := by
  set_option tactic.skipAssignedInstances false in
  simp [← mem_coe, coe_pow, Set.mem_pow]
#align finset.mem_pow Finset.mem_pow
#align finset.mem_nsmul Finset.mem_nsmul

@[to_additive (attr := simp)]
theorem empty_pow (hn : n ≠ 0) : (∅ : Finset α) ^ n = ∅ := by
  rw [← tsub_add_cancel_of_le (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn), pow_succ', empty_mul]
#align finset.empty_pow Finset.empty_pow
#align finset.empty_nsmul Finset.empty_nsmul

@[to_additive]
theorem mul_univ_of_one_mem [Fintype α] (hs : (1 : α) ∈ s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩
#align finset.mul_univ_of_one_mem Finset.mul_univ_of_one_mem
#align finset.add_univ_of_zero_mem Finset.add_univ_of_zero_mem

@[to_additive]
theorem univ_mul_of_one_mem [Fintype α] (ht : (1 : α) ∈ t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩
#align finset.univ_mul_of_one_mem Finset.univ_mul_of_one_mem
#align finset.univ_add_of_zero_mem Finset.univ_add_of_zero_mem

@[to_additive (attr := simp)]
theorem univ_mul_univ [Fintype α] : (univ : Finset α) * univ = univ :=
  mul_univ_of_one_mem <| mem_univ _
#align finset.univ_mul_univ Finset.univ_mul_univ
#align finset.univ_add_univ Finset.univ_add_univ

@[to_additive (attr := simp) nsmul_univ]
theorem univ_pow [Fintype α] (hn : n ≠ 0) : (univ : Finset α) ^ n = univ :=
  coe_injective <| by rw [coe_pow, coe_univ, Set.univ_pow hn]
#align finset.univ_pow Finset.univ_pow
#align finset.nsmul_univ Finset.nsmul_univ

@[to_additive]
protected theorem _root_.IsUnit.finset : IsUnit a → IsUnit ({a} : Finset α) :=
  IsUnit.map (singletonMonoidHom : α →* Finset α)
#align is_unit.finset IsUnit.finset
#align is_add_unit.finset IsAddUnit.finset

end Monoid

section CommMonoid

variable [CommMonoid α]

/-- `Finset α` is a `CommMonoid` under pointwise operations if `α` is. -/
@[to_additive "`Finset α` is an `AddCommMonoid` under pointwise operations if `α` is. "]
protected def commMonoid : CommMonoid (Finset α) :=
  coe_injective.commMonoid _ coe_one coe_mul coe_pow
#align finset.comm_monoid Finset.commMonoid
#align finset.add_comm_monoid Finset.addCommMonoid

scoped[Pointwise] attribute [instance] Finset.commMonoid Finset.addCommMonoid

@[to_additive (attr := simp, norm_cast)]
theorem coe_prod {ι : Type*} (s : Finset ι) (f : ι → Finset α) :
    ↑(∏ i ∈ s, f i) = ∏ i ∈ s, (f i : Set α) :=
  map_prod ((coeMonoidHom) : Finset α →* Set α) _ _
#align finset.coe_prod Finset.coe_prod
#align finset.coe_sum Finset.coe_sum

end CommMonoid

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Finset α}

@[to_additive (attr := simp)]
theorem coe_zpow (s : Finset α) : ∀ n : ℤ, ↑(s ^ n) = (s : Set α) ^ n
  | Int.ofNat n => coe_pow _ _
  | Int.negSucc n => by
    refine (coe_inv _).trans ?_
    exact congr_arg Inv.inv (coe_pow _ _)
#align finset.coe_zpow Finset.coe_zpow
#align finset.coe_zsmul Finset.coe_zsmul

@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  simp_rw [← coe_inj, coe_mul, coe_one, Set.mul_eq_one_iff, coe_singleton]
#align finset.mul_eq_one_iff Finset.mul_eq_one_iff
#align finset.add_eq_zero_iff Finset.add_eq_zero_iff

/-- `Finset α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive subtractionMonoid
  "`Finset α` is a subtraction monoid under pointwise operations if `α` is."]
protected def divisionMonoid : DivisionMonoid (Finset α) :=
  coe_injective.divisionMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow
#align finset.division_monoid Finset.divisionMonoid
#align finset.subtraction_monoid Finset.subtractionMonoid

scoped[Pointwise] attribute [instance] Finset.divisionMonoid Finset.subtractionMonoid

@[to_additive (attr := simp)]
theorem isUnit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Finset.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, singleton_injective ?_⟩, rfl⟩
    rw [← singleton_mul_singleton, ← ha, ← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.finset
#align finset.is_unit_iff Finset.isUnit_iff
#align finset.is_add_unit_iff Finset.isAddUnit_iff

@[to_additive (attr := simp)]
theorem isUnit_coe : IsUnit (s : Set α) ↔ IsUnit s := by
  simp_rw [isUnit_iff, Set.isUnit_iff, coe_eq_singleton]
#align finset.is_unit_coe Finset.isUnit_coe
#align finset.is_add_unit_coe Finset.isAddUnit_coe

@[to_additive (attr := simp)]
lemma univ_div_univ [Fintype α] : (univ / univ : Finset α) = univ := by simp [div_eq_mul_inv]

end DivisionMonoid

/-- `Finset α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive subtractionCommMonoid
      "`Finset α` is a commutative subtraction monoid under pointwise operations if `α` is."]
protected def divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (Finset α) :=
  coe_injective.divisionCommMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow
#align finset.division_comm_monoid Finset.divisionCommMonoid
#align finset.subtraction_comm_monoid Finset.subtractionCommMonoid

/-- `Finset α` has distributive negation if `α` has. -/
protected def distribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Finset α) :=
  coe_injective.hasDistribNeg _ coe_neg coe_mul
#align finset.has_distrib_neg Finset.distribNeg

scoped[Pointwise]
  attribute [instance] Finset.divisionCommMonoid Finset.subtractionCommMonoid Finset.distribNeg

section Distrib

variable [Distrib α] (s t u : Finset α)

/-!
Note that `Finset α` is not a `Distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.

```lean
-- {10, 16, 18, 20, 8, 9}
#eval {1, 2} * ({3, 4} + {5, 6} : Finset ℕ)

-- {10, 11, 12, 13, 14, 15, 16, 18, 20, 8, 9}
#eval ({1, 2} : Finset ℕ) * {3, 4} + {1, 2} * {5, 6}
```
-/


theorem mul_add_subset : s * (t + u) ⊆ s * t + s * u :=
  image₂_distrib_subset_left mul_add
#align finset.mul_add_subset Finset.mul_add_subset

theorem add_mul_subset : (s + t) * u ⊆ s * u + t * u :=
  image₂_distrib_subset_right add_mul
#align finset.add_mul_subset Finset.add_mul_subset

end Distrib

section MulZeroClass

variable [MulZeroClass α] {s t : Finset α}

/-! Note that `Finset` is not a `MulZeroClass` because `0 * ∅ ≠ 0`. -/


theorem mul_zero_subset (s : Finset α) : s * 0 ⊆ 0 := by simp [subset_iff, mem_mul]
#align finset.mul_zero_subset Finset.mul_zero_subset

theorem zero_mul_subset (s : Finset α) : 0 * s ⊆ 0 := by simp [subset_iff, mem_mul]
#align finset.zero_mul_subset Finset.zero_mul_subset

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by simpa [mem_mul] using hs
#align finset.nonempty.mul_zero Finset.Nonempty.mul_zero

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by simpa [mem_mul] using hs
#align finset.nonempty.zero_mul Finset.Nonempty.zero_mul

end MulZeroClass

section Group

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]
variable (f : F) {s t : Finset α} {a b : α}

/-! Note that `Finset` is not a `Group` because `s / s ≠ 1` in general. -/


@[to_additive (attr := simp)]
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  rw [← mem_coe, ← disjoint_coe, coe_div, Set.one_mem_div_iff]
#align finset.one_mem_div_iff Finset.one_mem_div_iff
#align finset.zero_mem_sub_iff Finset.zero_mem_sub_iff

@[to_additive]
theorem not_one_mem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left
#align finset.not_one_mem_div_iff Finset.not_one_mem_div_iff
#align finset.not_zero_mem_sub_iff Finset.not_zero_mem_sub_iff

@[to_additive]
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, ha, a, ha, div_self' _⟩
#align finset.nonempty.one_mem_div Finset.Nonempty.one_mem_div
#align finset.nonempty.zero_mem_sub Finset.Nonempty.zero_mem_sub

@[to_additive]
theorem isUnit_singleton (a : α) : IsUnit ({a} : Finset α) :=
  (Group.isUnit a).finset
#align finset.is_unit_singleton Finset.isUnit_singleton
#align finset.is_add_unit_singleton Finset.isAddUnit_singleton

/- Porting note: not in simp nf; Added non-simpable part as `isUnit_iff_singleton_aux` below
Left-hand side simplifies from
  IsUnit s
to
  ∃ a, s = {a} ∧ IsUnit a -/
-- @[simp]
theorem isUnit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [isUnit_iff, Group.isUnit, and_true_iff]
#align finset.is_unit_iff_singleton Finset.isUnit_iff_singleton

@[simp]
theorem isUnit_iff_singleton_aux : (∃ a, s = {a} ∧ IsUnit a) ↔ ∃ a, s = {a} := by
  simp only [Group.isUnit, and_true_iff]

@[to_additive (attr := simp)]
theorem image_mul_left :
    image (fun b => a * b) t = preimage t (fun b => a⁻¹ * b) ((mul_right_injective _).injOn _) :=
  coe_injective <| by simp
#align finset.image_mul_left Finset.image_mul_left
#align finset.image_add_left Finset.image_add_left

@[to_additive (attr := simp)]
theorem image_mul_right : image (· * b) t = preimage t (· * b⁻¹) ((mul_left_injective _).injOn _) :=
  coe_injective <| by simp
#align finset.image_mul_right Finset.image_mul_right
#align finset.image_add_right Finset.image_add_right

@[to_additive]
theorem image_mul_left' :
    image (fun b => a⁻¹ * b) t = preimage t (fun b => a * b) ((mul_right_injective _).injOn _) := by
  simp
#align finset.image_mul_left' Finset.image_mul_left'
#align finset.image_add_left' Finset.image_add_left'

@[to_additive]
theorem image_mul_right' :
    image (· * b⁻¹) t = preimage t (· * b) ((mul_left_injective _).injOn _) := by simp
#align finset.image_mul_right' Finset.image_mul_right'
#align finset.image_add_right' Finset.image_add_right'

theorem image_div : (s / t).image (f : α → β) = s.image f / t.image f :=
  image_image₂_distrib <| map_div f
#align finset.image_div Finset.image_div

end Group

section GroupWithZero

variable [GroupWithZero α] {s t : Finset α}

theorem div_zero_subset (s : Finset α) : s / 0 ⊆ 0 := by simp [subset_iff, mem_div]
#align finset.div_zero_subset Finset.div_zero_subset

theorem zero_div_subset (s : Finset α) : 0 / s ⊆ 0 := by simp [subset_iff, mem_div]
#align finset.zero_div_subset Finset.zero_div_subset

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by simpa [mem_div] using hs
#align finset.nonempty.div_zero Finset.Nonempty.div_zero

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by simpa [mem_div] using hs
#align finset.nonempty.zero_div Finset.Nonempty.zero_div

end GroupWithZero

end Instances

section Group

variable [Group α] {s t : Finset α} {a b : α}

@[to_additive (attr := simp)]
theorem preimage_mul_left_singleton :
    preimage {b} (a * ·) ((mul_right_injective _).injOn _) = {a⁻¹ * b} := by
  classical rw [← image_mul_left', image_singleton]
#align finset.preimage_mul_left_singleton Finset.preimage_mul_left_singleton
#align finset.preimage_add_left_singleton Finset.preimage_add_left_singleton

@[to_additive (attr := simp)]
theorem preimage_mul_right_singleton :
    preimage {b} (· * a) ((mul_left_injective _).injOn _) = {b * a⁻¹} := by
  classical rw [← image_mul_right', image_singleton]
#align finset.preimage_mul_right_singleton Finset.preimage_mul_right_singleton
#align finset.preimage_add_right_singleton Finset.preimage_add_right_singleton

@[to_additive (attr := simp)]
theorem preimage_mul_left_one : preimage 1 (a * ·) ((mul_right_injective _).injOn _) = {a⁻¹} := by
  classical rw [← image_mul_left', image_one, mul_one]
#align finset.preimage_mul_left_one Finset.preimage_mul_left_one
#align finset.preimage_add_left_zero Finset.preimage_add_left_zero

@[to_additive (attr := simp)]
theorem preimage_mul_right_one : preimage 1 (· * b) ((mul_left_injective _).injOn _) = {b⁻¹} := by
  classical rw [← image_mul_right', image_one, one_mul]
#align finset.preimage_mul_right_one Finset.preimage_mul_right_one
#align finset.preimage_add_right_zero Finset.preimage_add_right_zero

@[to_additive]
theorem preimage_mul_left_one' : preimage 1 (a⁻¹ * ·) ((mul_right_injective _).injOn _) = {a} := by
  rw [preimage_mul_left_one, inv_inv]
#align finset.preimage_mul_left_one' Finset.preimage_mul_left_one'
#align finset.preimage_add_left_zero' Finset.preimage_add_left_zero'

@[to_additive]
theorem preimage_mul_right_one' : preimage 1 (· * b⁻¹) ((mul_left_injective _).injOn _) = {b} := by
  rw [preimage_mul_right_one, inv_inv]
#align finset.preimage_mul_right_one' Finset.preimage_mul_right_one'
#align finset.preimage_add_right_zero' Finset.preimage_add_right_zero'

end Group

/-! ### Scalar addition/multiplication of finsets -/


section SMul

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

/-- The pointwise product of two finsets `s` and `t`: `s • t = {x • y | x ∈ s, y ∈ t}`. -/
@[to_additive "The pointwise sum of two finsets `s` and `t`: `s +ᵥ t = {x +ᵥ y | x ∈ s, y ∈ t}`."]
protected def smul : SMul (Finset α) (Finset β) :=
  ⟨image₂ (· • ·)⟩
#align finset.has_smul Finset.smul
#align finset.has_vadd Finset.vadd

scoped[Pointwise] attribute [instance] Finset.smul Finset.vadd

@[to_additive]
theorem smul_def : s • t = (s ×ˢ t).image fun p : α × β => p.1 • p.2 :=
  rfl
#align finset.smul_def Finset.smul_def
#align finset.vadd_def Finset.vadd_def

@[to_additive]
theorem image_smul_product : ((s ×ˢ t).image fun x : α × β => x.fst • x.snd) = s • t :=
  rfl
#align finset.image_smul_product Finset.image_smul_product
#align finset.image_vadd_product Finset.image_vadd_product

@[to_additive]
theorem mem_smul {x : β} : x ∈ s • t ↔ ∃ y ∈ s, ∃ z ∈ t, y • z = x :=
  mem_image₂
#align finset.mem_smul Finset.mem_smul
#align finset.mem_vadd Finset.mem_vadd

@[to_additive (attr := simp, norm_cast)]
theorem coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s : Set α) • (t : Set β) :=
  coe_image₂ _ _ _
#align finset.coe_smul Finset.coe_smul
#align finset.coe_vadd Finset.coe_vadd

@[to_additive]
theorem smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t :=
  mem_image₂_of_mem
#align finset.smul_mem_smul Finset.smul_mem_smul
#align finset.vadd_mem_vadd Finset.vadd_mem_vadd

@[to_additive]
theorem smul_card_le : (s • t).card ≤ s.card • t.card :=
  card_image₂_le _ _ _
#align finset.smul_card_le Finset.smul_card_le
#align finset.vadd_card_le Finset.vadd_card_le

@[to_additive (attr := simp)]
theorem empty_smul (t : Finset β) : (∅ : Finset α) • t = ∅ :=
  image₂_empty_left
#align finset.empty_smul Finset.empty_smul
#align finset.empty_vadd Finset.empty_vadd

@[to_additive (attr := simp)]
theorem smul_empty (s : Finset α) : s • (∅ : Finset β) = ∅ :=
  image₂_empty_right
#align finset.smul_empty Finset.smul_empty
#align finset.vadd_empty Finset.vadd_empty

@[to_additive (attr := simp)]
theorem smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.smul_eq_empty Finset.smul_eq_empty
#align finset.vadd_eq_empty Finset.vadd_eq_empty

@[to_additive (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]
theorem smul_nonempty_iff : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.smul_nonempty_iff Finset.smul_nonempty_iff
#align finset.vadd_nonempty_iff Finset.vadd_nonempty_iff

@[to_additive]
theorem Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.smul Finset.Nonempty.smul
#align finset.nonempty.vadd Finset.Nonempty.vadd

@[to_additive]
theorem Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_smul_left Finset.Nonempty.of_smul_left
#align finset.nonempty.of_vadd_left Finset.Nonempty.of_vadd_left

@[to_additive]
theorem Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_smul_right Finset.Nonempty.of_smul_right
#align finset.nonempty.of_vadd_right Finset.Nonempty.of_vadd_right

@[to_additive]
theorem smul_singleton (b : β) : s • ({b} : Finset β) = s.image (· • b) :=
  image₂_singleton_right
#align finset.smul_singleton Finset.smul_singleton
#align finset.vadd_singleton Finset.vadd_singleton

@[to_additive]
theorem singleton_smul_singleton (a : α) (b : β) : ({a} : Finset α) • ({b} : Finset β) = {a • b} :=
  image₂_singleton
#align finset.singleton_smul_singleton Finset.singleton_smul_singleton
#align finset.singleton_vadd_singleton Finset.singleton_vadd_singleton

@[to_additive (attr := mono)]
theorem smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ :=
  image₂_subset
#align finset.smul_subset_smul Finset.smul_subset_smul
#align finset.vadd_subset_vadd Finset.vadd_subset_vadd

@[to_additive]
theorem smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ :=
  image₂_subset_left
#align finset.smul_subset_smul_left Finset.smul_subset_smul_left
#align finset.vadd_subset_vadd_left Finset.vadd_subset_vadd_left

@[to_additive]
theorem smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t :=
  image₂_subset_right
#align finset.smul_subset_smul_right Finset.smul_subset_smul_right
#align finset.vadd_subset_vadd_right Finset.vadd_subset_vadd_right

@[to_additive]
theorem smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u :=
  image₂_subset_iff
#align finset.smul_subset_iff Finset.smul_subset_iff
#align finset.vadd_subset_iff Finset.vadd_subset_iff

@[to_additive]
theorem union_smul [DecidableEq α] : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
  image₂_union_left
#align finset.union_smul Finset.union_smul
#align finset.union_vadd Finset.union_vadd

@[to_additive]
theorem smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ :=
  image₂_union_right
#align finset.smul_union Finset.smul_union
#align finset.vadd_union Finset.vadd_union

@[to_additive]
theorem inter_smul_subset [DecidableEq α] : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image₂_inter_subset_left
#align finset.inter_smul_subset Finset.inter_smul_subset
#align finset.inter_vadd_subset Finset.inter_vadd_subset

@[to_additive]
theorem smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
  image₂_inter_subset_right
#align finset.smul_inter_subset Finset.smul_inter_subset
#align finset.vadd_inter_subset Finset.vadd_inter_subset

@[to_additive]
theorem inter_smul_union_subset_union [DecidableEq α] : (s₁ ∩ s₂) • (t₁ ∪ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image₂_inter_union_subset_union
#align finset.inter_smul_union_subset_union Finset.inter_smul_union_subset_union
#align finset.inter_vadd_union_subset_union Finset.inter_vadd_union_subset_union

@[to_additive]
theorem union_smul_inter_subset_union [DecidableEq α] : (s₁ ∪ s₂) • (t₁ ∩ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image₂_union_inter_subset_union
#align finset.union_smul_inter_subset_union Finset.union_smul_inter_subset_union
#align finset.union_vadd_inter_subset_union Finset.union_vadd_inter_subset_union

/-- If a finset `u` is contained in the scalar product of two sets `s • t`, we can find two finsets
`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' • t'`. -/
@[to_additive
      "If a finset `u` is contained in the scalar sum of two sets `s +ᵥ t`, we can find two
      finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' +ᵥ t'`."]
theorem subset_smul {s : Set α} {t : Set β} :
    ↑u ⊆ s • t → ∃ (s' : Finset α) (t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' • t' :=
  subset_image₂
#align finset.subset_smul Finset.subset_smul
#align finset.subset_vadd Finset.subset_vadd

end SMul

/-! ### Scalar subtraction of finsets -/


section VSub

-- Porting note: Reordered [VSub α β] and [DecidableEq α] to make vsub less dangerous. Bad?
variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

/-- The pointwise subtraction of two finsets `s` and `t`: `s -ᵥ t = {x -ᵥ y | x ∈ s, y ∈ t}`. -/
protected def vsub : VSub (Finset α) (Finset β) :=
  ⟨image₂ (· -ᵥ ·)⟩
#align finset.has_vsub Finset.vsub

scoped[Pointwise] attribute [instance] Finset.vsub

theorem vsub_def : s -ᵥ t = image₂ (· -ᵥ ·) s t :=
  rfl
#align finset.vsub_def Finset.vsub_def

@[simp]
theorem image_vsub_product : image₂ (· -ᵥ ·) s t = s -ᵥ t :=
  rfl
#align finset.image_vsub_product Finset.image_vsub_product

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ b ∈ s, ∃ c ∈ t, b -ᵥ c = a :=
  mem_image₂
#align finset.mem_vsub Finset.mem_vsub

@[simp, norm_cast]
theorem coe_vsub (s t : Finset β) : (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t :=
  coe_image₂ _ _ _
#align finset.coe_vsub Finset.coe_vsub

theorem vsub_mem_vsub : b ∈ s → c ∈ t → b -ᵥ c ∈ s -ᵥ t :=
  mem_image₂_of_mem
#align finset.vsub_mem_vsub Finset.vsub_mem_vsub

theorem vsub_card_le : (s -ᵥ t : Finset α).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.vsub_card_le Finset.vsub_card_le

@[simp]
theorem empty_vsub (t : Finset β) : (∅ : Finset β) -ᵥ t = ∅ :=
  image₂_empty_left
#align finset.empty_vsub Finset.empty_vsub

@[simp]
theorem vsub_empty (s : Finset β) : s -ᵥ (∅ : Finset β) = ∅ :=
  image₂_empty_right
#align finset.vsub_empty Finset.vsub_empty

@[simp]
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.vsub_eq_empty Finset.vsub_eq_empty

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem vsub_nonempty : (s -ᵥ t : Finset α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.vsub_nonempty Finset.vsub_nonempty

theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Finset α).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.vsub Finset.Nonempty.vsub

theorem Nonempty.of_vsub_left : (s -ᵥ t : Finset α).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_vsub_left Finset.Nonempty.of_vsub_left

theorem Nonempty.of_vsub_right : (s -ᵥ t : Finset α).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_vsub_right Finset.Nonempty.of_vsub_right

@[simp]
theorem vsub_singleton (b : β) : s -ᵥ ({b} : Finset β) = s.image (· -ᵥ b) :=
  image₂_singleton_right
#align finset.vsub_singleton Finset.vsub_singleton

theorem singleton_vsub (a : β) : ({a} : Finset β) -ᵥ t = t.image (a -ᵥ ·) :=
  image₂_singleton_left
#align finset.singleton_vsub Finset.singleton_vsub

-- @[simp] -- Porting note (#10618): simp can prove this
theorem singleton_vsub_singleton (a b : β) : ({a} : Finset β) -ᵥ {b} = {a -ᵥ b} :=
  image₂_singleton
#align finset.singleton_vsub_singleton Finset.singleton_vsub_singleton

@[mono]
theorem vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image₂_subset
#align finset.vsub_subset_vsub Finset.vsub_subset_vsub

theorem vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image₂_subset_left
#align finset.vsub_subset_vsub_left Finset.vsub_subset_vsub_left

theorem vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image₂_subset_right
#align finset.vsub_subset_vsub_right Finset.vsub_subset_vsub_right

theorem vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x -ᵥ y ∈ u :=
  image₂_subset_iff
#align finset.vsub_subset_iff Finset.vsub_subset_iff

section

variable [DecidableEq β]

theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image₂_union_left
#align finset.union_vsub Finset.union_vsub

theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image₂_union_right
#align finset.vsub_union Finset.vsub_union

theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image₂_inter_subset_left
#align finset.inter_vsub_subset Finset.inter_vsub_subset

theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image₂_inter_subset_right
#align finset.vsub_inter_subset Finset.vsub_inter_subset

end

/-- If a finset `u` is contained in the pointwise subtraction of two sets `s -ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' -ᵥ t'`. -/
theorem subset_vsub {s t : Set β} :
    ↑u ⊆ s -ᵥ t → ∃ s' t' : Finset β, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' -ᵥ t' :=
  subset_image₂
#align finset.subset_vsub Finset.subset_vsub

end VSub

open Pointwise

/-! ### Translation/scaling of finsets -/


section SMul

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t u : Finset β} {a : α} {b : β}

/-- The scaling of a finset `s` by a scalar `a`: `a • s = {a • x | x ∈ s}`. -/
@[to_additive "The translation of a finset `s` by a vector `a`: `a +ᵥ s = {a +ᵥ x | x ∈ s}`."]
protected def smulFinset : SMul α (Finset β) :=
  ⟨fun a => image <| (a • ·)⟩
#align finset.has_smul_finset Finset.smulFinset
#align finset.has_vadd_finset Finset.vaddFinset

scoped[Pointwise] attribute [instance] Finset.smulFinset Finset.vaddFinset

@[to_additive]
theorem smul_finset_def : a • s = s.image (a • ·) :=
  rfl
#align finset.smul_finset_def Finset.smul_finset_def
#align finset.vadd_finset_def Finset.vadd_finset_def

@[to_additive]
theorem image_smul : (s.image fun x => a • x) = a • s :=
  rfl
#align finset.image_smul Finset.image_smul
#align finset.image_vadd Finset.image_vadd

@[to_additive]
theorem mem_smul_finset {x : β} : x ∈ a • s ↔ ∃ y, y ∈ s ∧ a • y = x := by
  simp only [Finset.smul_finset_def, and_assoc, mem_image, exists_prop, Prod.exists, mem_product]
#align finset.mem_smul_finset Finset.mem_smul_finset
#align finset.mem_vadd_finset Finset.mem_vadd_finset

@[to_additive (attr := simp, norm_cast)]
theorem coe_smul_finset (a : α) (s : Finset β) : ↑(a • s) = a • (↑s : Set β) :=
  coe_image
#align finset.coe_smul_finset Finset.coe_smul_finset
#align finset.coe_vadd_finset Finset.coe_vadd_finset

@[to_additive]
theorem smul_mem_smul_finset : b ∈ s → a • b ∈ a • s :=
  mem_image_of_mem _
#align finset.smul_mem_smul_finset Finset.smul_mem_smul_finset
#align finset.vadd_mem_vadd_finset Finset.vadd_mem_vadd_finset

@[to_additive]
theorem smul_finset_card_le : (a • s).card ≤ s.card :=
  card_image_le
#align finset.smul_finset_card_le Finset.smul_finset_card_le
#align finset.vadd_finset_card_le Finset.vadd_finset_card_le

@[to_additive (attr := simp)]
theorem smul_finset_empty (a : α) : a • (∅ : Finset β) = ∅ :=
  image_empty _
#align finset.smul_finset_empty Finset.smul_finset_empty
#align finset.vadd_finset_empty Finset.vadd_finset_empty

@[to_additive (attr := simp)]
theorem smul_finset_eq_empty : a • s = ∅ ↔ s = ∅ :=
  image_eq_empty
#align finset.smul_finset_eq_empty Finset.smul_finset_eq_empty
#align finset.vadd_finset_eq_empty Finset.vadd_finset_eq_empty

@[to_additive (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]
theorem smul_finset_nonempty : (a • s).Nonempty ↔ s.Nonempty :=
  image_nonempty
#align finset.smul_finset_nonempty Finset.smul_finset_nonempty
#align finset.vadd_finset_nonempty Finset.vadd_finset_nonempty

@[to_additive]
theorem Nonempty.smul_finset (hs : s.Nonempty) : (a • s).Nonempty :=
  hs.image _
#align finset.nonempty.smul_finset Finset.Nonempty.smul_finset
#align finset.nonempty.vadd_finset Finset.Nonempty.vadd_finset

@[to_additive (attr := simp)]
theorem singleton_smul (a : α) : ({a} : Finset α) • t = a • t :=
  image₂_singleton_left
#align finset.singleton_smul Finset.singleton_smul
#align finset.singleton_vadd Finset.singleton_vadd

@[to_additive (attr := mono)]
theorem smul_finset_subset_smul_finset : s ⊆ t → a • s ⊆ a • t :=
  image_subset_image
#align finset.smul_finset_subset_smul_finset Finset.smul_finset_subset_smul_finset
#align finset.vadd_finset_subset_vadd_finset Finset.vadd_finset_subset_vadd_finset

@[to_additive (attr := simp)]
theorem smul_finset_singleton (b : β) : a • ({b} : Finset β) = {a • b} :=
  image_singleton _ _
#align finset.smul_finset_singleton Finset.smul_finset_singleton
#align finset.vadd_finset_singleton Finset.vadd_finset_singleton

@[to_additive]
theorem smul_finset_union : a • (s₁ ∪ s₂) = a • s₁ ∪ a • s₂ :=
  image_union _ _
#align finset.smul_finset_union Finset.smul_finset_union
#align finset.vadd_finset_union Finset.vadd_finset_union

@[to_additive]
theorem smul_finset_inter_subset : a • (s₁ ∩ s₂) ⊆ a • s₁ ∩ a • s₂ :=
  image_inter_subset _ _ _
#align finset.smul_finset_inter_subset Finset.smul_finset_inter_subset
#align finset.vadd_finset_inter_subset Finset.vadd_finset_inter_subset

@[to_additive]
theorem smul_finset_subset_smul {s : Finset α} : a ∈ s → a • t ⊆ s • t :=
  image_subset_image₂_right
#align finset.smul_finset_subset_smul Finset.smul_finset_subset_smul
#align finset.vadd_finset_subset_vadd Finset.vadd_finset_subset_vadd

@[to_additive (attr := simp)]
theorem biUnion_smul_finset (s : Finset α) (t : Finset β) : s.biUnion (· • t) = s • t :=
  biUnion_image_left
#align finset.bUnion_smul_finset Finset.biUnion_smul_finset
#align finset.bUnion_vadd_finset Finset.biUnion_vadd_finset

end SMul

open Pointwise

section Instances

variable [DecidableEq γ]

@[to_additive]
instance smulCommClass_finset [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Finset γ) :=
  ⟨fun _ _ => Commute.finset_image <| smul_comm _ _⟩
#align finset.smul_comm_class_finset Finset.smulCommClass_finset
#align finset.vadd_comm_class_finset Finset.vaddCommClass_finset

@[to_additive]
instance smulCommClass_finset' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_comm]⟩
#align finset.smul_comm_class_finset' Finset.smulCommClass_finset'
#align finset.vadd_comm_class_finset' Finset.vaddCommClass_finset'

@[to_additive]
instance smulCommClass_finset'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) β (Finset γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _
#align finset.smul_comm_class_finset'' Finset.smulCommClass_finset''
#align finset.vadd_comm_class_finset'' Finset.vaddCommClass_finset''

@[to_additive]
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) (Finset β) (Finset γ) :=
  ⟨fun s t u => coe_injective <| by simp_rw [coe_smul, smul_comm]⟩
#align finset.smul_comm_class Finset.smulCommClass
#align finset.vadd_comm_class Finset.vaddCommClass

@[to_additive vaddAssocClass]
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Finset γ) :=
  ⟨fun a b s => by simp only [← image_smul, image_image, smul_assoc, Function.comp]⟩
#align finset.is_scalar_tower Finset.isScalarTower
#align finset.vadd_assoc_class Finset.vaddAssocClass

variable [DecidableEq β]

@[to_additive vaddAssocClass']
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩
#align finset.is_scalar_tower' Finset.isScalarTower'
#align finset.vadd_assoc_class' Finset.vaddAssocClass'

@[to_additive vaddAssocClass'']
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Finset α) (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩
#align finset.is_scalar_tower'' Finset.isScalarTower''
#align finset.vadd_assoc_class'' Finset.vaddAssocClass''

@[to_additive]
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Finset β) :=
  ⟨fun a s => coe_injective <| by simp only [coe_smul_finset, coe_smul, op_smul_eq_smul]⟩
#align finset.is_central_scalar Finset.isCentralScalar
#align finset.is_central_vadd Finset.isCentralVAdd

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of
`Finset α` on `Finset β`. -/
@[to_additive
      "An additive action of an additive monoid `α` on a type `β` gives an additive action
      of `Finset α` on `Finset β`"]
protected def mulAction [DecidableEq α] [Monoid α] [MulAction α β] :
    MulAction (Finset α) (Finset β) where
  mul_smul _ _ _ := image₂_assoc mul_smul
  one_smul s := image₂_singleton_left.trans <| by simp_rw [one_smul, image_id']
#align finset.mul_action Finset.mulAction
#align finset.add_action Finset.addAction

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `Finset β`.
-/
@[to_additive
      "An additive action of an additive monoid on a type `β` gives an additive action
      on `Finset β`."]
protected def mulActionFinset [Monoid α] [MulAction α β] : MulAction α (Finset β) :=
  coe_injective.mulAction _ coe_smul_finset
#align finset.mul_action_finset Finset.mulActionFinset
#align finset.add_action_finset Finset.addActionFinset

scoped[Pointwise]
  attribute [instance]
    Finset.mulActionFinset Finset.addActionFinset Finset.mulAction Finset.addAction

/-- If scalar multiplication by elements of `α` sends `(0 : β)` to zero,
then the same is true for `(0 : Finset β)`. -/
protected def smulZeroClassFinset [Zero β] [SMulZeroClass α β] :
    SMulZeroClass α (Finset β) :=
  coe_injective.smulZeroClass ⟨(↑), coe_zero⟩ coe_smul_finset

scoped[Pointwise] attribute [instance] Finset.smulZeroClassFinset

/-- If the scalar multiplication `(· • ·) : α → β → β` is distributive,
then so is `(· • ·) : α → Finset β → Finset β`. -/
protected def distribSMulFinset [AddZeroClass β] [DistribSMul α β] :
    DistribSMul α (Finset β) :=
  coe_injective.distribSMul coeAddMonoidHom coe_smul_finset

scoped[Pointwise] attribute [instance] Finset.distribSMulFinset

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `Finset β`. -/
protected def distribMulActionFinset [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Finset β) :=
  Function.Injective.distribMulAction coeAddMonoidHom coe_injective coe_smul_finset
#align finset.distrib_mul_action_finset Finset.distribMulActionFinset

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `Set β`. -/
protected def mulDistribMulActionFinset [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Finset β) :=
  Function.Injective.mulDistribMulAction coeMonoidHom coe_injective coe_smul_finset
#align finset.mul_distrib_mul_action_finset Finset.mulDistribMulActionFinset

scoped[Pointwise]
  attribute [instance] Finset.distribMulActionFinset Finset.mulDistribMulActionFinset

instance [DecidableEq α] [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Finset α) :=
  Function.Injective.noZeroDivisors (↑) coe_injective coe_zero coe_mul

instance noZeroSMulDivisors [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors (Finset α) (Finset β) where
  eq_zero_or_eq_zero_of_smul_eq_zero {s t} := by
    exact_mod_cast eq_zero_or_eq_zero_of_smul_eq_zero (c := s.toSet) (x := t.toSet)

instance noZeroSMulDivisors_finset [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors α (Finset β) :=
  Function.Injective.noZeroSMulDivisors (↑) coe_injective coe_zero coe_smul_finset
#align finset.no_zero_smul_divisors_finset Finset.noZeroSMulDivisors_finset

end Instances

section SMul

variable [DecidableEq β] [DecidableEq γ] [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

-- TODO: replace hypothesis and conclusion with a typeclass
@[to_additive]
theorem op_smul_finset_smul_eq_smul_smul_finset (a : α) (s : Finset β) (t : Finset γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext
  simp [mem_smul, mem_smul_finset, h]
#align finset.op_smul_finset_smul_eq_smul_smul_finset Finset.op_smul_finset_smul_eq_smul_smul_finset
#align finset.op_vadd_finset_vadd_eq_vadd_vadd_finset Finset.op_vadd_finset_vadd_eq_vadd_vadd_finset

end SMul

section Mul

variable [Mul α] [DecidableEq α] {s t u : Finset α} {a : α}

@[to_additive]
theorem op_smul_finset_subset_mul : a ∈ t → op a • s ⊆ s * t :=
  image_subset_image₂_left
#align finset.op_smul_finset_subset_mul Finset.op_smul_finset_subset_mul
#align finset.op_vadd_finset_subset_add Finset.op_vadd_finset_subset_add

@[to_additive (attr := simp)]
theorem biUnion_op_smul_finset (s t : Finset α) : (t.biUnion fun a => op a • s) = s * t :=
  biUnion_image_right
#align finset.bUnion_op_smul_finset Finset.biUnion_op_smul_finset
#align finset.bUnion_op_vadd_finset Finset.biUnion_op_vadd_finset

@[to_additive]
theorem mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u :=
  image₂_subset_iff_left
#align finset.mul_subset_iff_left Finset.mul_subset_iff_left
#align finset.add_subset_iff_left Finset.add_subset_iff_left

@[to_additive]
theorem mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
  image₂_subset_iff_right
#align finset.mul_subset_iff_right Finset.mul_subset_iff_right
#align finset.add_subset_iff_right Finset.add_subset_iff_right

end Mul

section Semigroup

variable [Semigroup α] [DecidableEq α]

@[to_additive]
theorem op_smul_finset_mul_eq_mul_smul_finset (a : α) (s : Finset α) (t : Finset α) :
    op a • s * t = s * a • t :=
  op_smul_finset_smul_eq_smul_smul_finset _ _ _ fun _ _ _ => mul_assoc _ _ _
#align finset.op_smul_finset_mul_eq_mul_smul_finset Finset.op_smul_finset_mul_eq_mul_smul_finset
#align finset.op_vadd_finset_add_eq_add_vadd_finset Finset.op_vadd_finset_add_eq_add_vadd_finset

end Semigroup

section IsLeftCancelMul

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] (s t : Finset α) (a : α)

@[to_additive]
theorem pairwiseDisjoint_smul_iff {s : Set α} {t : Finset α} :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 := by
  simp_rw [← pairwiseDisjoint_coe, coe_smul_finset, Set.pairwiseDisjoint_smul_iff]
#align finset.pairwise_disjoint_smul_iff Finset.pairwiseDisjoint_smul_iff
#align finset.pairwise_disjoint_vadd_iff Finset.pairwiseDisjoint_vadd_iff

@[to_additive (attr := simp)]
theorem card_singleton_mul : ({a} * t).card = t.card :=
  card_image₂_singleton_left _ <| mul_right_injective _
#align finset.card_singleton_mul Finset.card_singleton_mul
#align finset.card_singleton_add Finset.card_singleton_add

@[to_additive]
theorem singleton_mul_inter : {a} * (s ∩ t) = {a} * s ∩ ({a} * t) :=
  image₂_singleton_inter _ _ <| mul_right_injective _
#align finset.singleton_mul_inter Finset.singleton_mul_inter
#align finset.singleton_add_inter Finset.singleton_add_inter

@[to_additive]
theorem card_le_card_mul_left {s : Finset α} (hs : s.Nonempty) : t.card ≤ (s * t).card :=
  card_le_card_image₂_left _ hs mul_right_injective
#align finset.card_le_card_mul_left Finset.card_le_card_mul_left
#align finset.card_le_card_add_left Finset.card_le_card_add_left

end IsLeftCancelMul

section

variable [Mul α] [IsRightCancelMul α] [DecidableEq α] (s t : Finset α) (a : α)

@[to_additive (attr := simp)]
theorem card_mul_singleton : (s * {a}).card = s.card :=
  card_image₂_singleton_right _ <| mul_left_injective _
#align finset.card_mul_singleton Finset.card_mul_singleton
#align finset.card_add_singleton Finset.card_add_singleton

@[to_additive]
theorem inter_mul_singleton : s ∩ t * {a} = s * {a} ∩ (t * {a}) :=
  image₂_inter_singleton _ _ <| mul_left_injective _
#align finset.inter_mul_singleton Finset.inter_mul_singleton
#align finset.inter_add_singleton Finset.inter_add_singleton

@[to_additive]
theorem card_le_card_mul_right {t : Finset α} (ht : t.Nonempty) : s.card ≤ (s * t).card :=
  card_le_card_image₂_right _ ht mul_left_injective
#align finset.card_le_card_mul_right Finset.card_le_card_mul_right
#align finset.card_le_card_add_right Finset.card_le_card_add_right

end

section Group
variable [Group α] [DecidableEq α] {s t : Finset α}

@[to_additive] lemma card_le_card_div_left (hs : s.Nonempty) : t.card ≤ (s / t).card :=
  card_le_card_image₂_left _ hs fun _ ↦ div_right_injective

@[to_additive] lemma card_le_card_div_right (ht : t.Nonempty) : s.card ≤ (s / t).card :=
  card_le_card_image₂_right _ ht fun _ ↦ div_left_injective

end Group

open Pointwise

@[to_additive]
theorem image_smul_comm [DecidableEq β] [DecidableEq γ] [SMul α β] [SMul α γ] (f : β → γ) (a : α)
    (s : Finset β) : (∀ b, f (a • b) = a • f b) → (a • s).image f = a • s.image f :=
  image_comm
#align finset.image_smul_comm Finset.image_smul_comm
#align finset.image_vadd_comm Finset.image_vadd_comm

@[to_additive]
theorem image_smul_distrib [DecidableEq α] [DecidableEq β] [Monoid α] [Monoid β] [FunLike F α β]
    [MonoidHomClass F α β] (f : F) (a : α) (s : Finset α) : (a • s).image f = f a • s.image f :=
  image_comm <| map_mul _ _
#align finset.image_smul_distrib Finset.image_smul_distrib
#align finset.image_vadd_distrib Finset.image_vadd_distrib

section Group

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

@[to_additive (attr := simp)]
theorem smul_mem_smul_finset_iff (a : α) : a • b ∈ a • s ↔ b ∈ s :=
  (MulAction.injective _).mem_finset_image
#align finset.smul_mem_smul_finset_iff Finset.smul_mem_smul_finset_iff
#align finset.vadd_mem_vadd_finset_iff Finset.vadd_mem_vadd_finset_iff

@[to_additive]
theorem inv_smul_mem_iff : a⁻¹ • b ∈ s ↔ b ∈ a • s := by
  rw [← smul_mem_smul_finset_iff a, smul_inv_smul]
#align finset.inv_smul_mem_iff Finset.inv_smul_mem_iff
#align finset.neg_vadd_mem_iff Finset.neg_vadd_mem_iff

@[to_additive]
theorem mem_inv_smul_finset_iff : b ∈ a⁻¹ • s ↔ a • b ∈ s := by
  rw [← smul_mem_smul_finset_iff a, smul_inv_smul]
#align finset.mem_inv_smul_finset_iff Finset.mem_inv_smul_finset_iff
#align finset.mem_neg_vadd_finset_iff Finset.mem_neg_vadd_finset_iff

@[to_additive (attr := simp)]
theorem smul_finset_subset_smul_finset_iff : a • s ⊆ a • t ↔ s ⊆ t :=
  image_subset_image_iff <| MulAction.injective _
#align finset.smul_finset_subset_smul_finset_iff Finset.smul_finset_subset_smul_finset_iff
#align finset.vadd_finset_subset_vadd_finset_iff Finset.vadd_finset_subset_vadd_finset_iff

@[to_additive]
theorem smul_finset_subset_iff : a • s ⊆ t ↔ s ⊆ a⁻¹ • t := by
  simp_rw [← coe_subset]
  push_cast
  exact Set.set_smul_subset_iff
#align finset.smul_finset_subset_iff Finset.smul_finset_subset_iff
#align finset.vadd_finset_subset_iff Finset.vadd_finset_subset_iff

@[to_additive]
theorem subset_smul_finset_iff : s ⊆ a • t ↔ a⁻¹ • s ⊆ t := by
  simp_rw [← coe_subset]
  push_cast
  exact Set.subset_set_smul_iff
#align finset.subset_smul_finset_iff Finset.subset_smul_finset_iff
#align finset.subset_vadd_finset_iff Finset.subset_vadd_finset_iff

@[to_additive]
theorem smul_finset_inter : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter _ _ <| MulAction.injective a
#align finset.smul_finset_inter Finset.smul_finset_inter
#align finset.vadd_finset_inter Finset.vadd_finset_inter

@[to_additive]
theorem smul_finset_sdiff : a • (s \ t) = a • s \ a • t :=
  image_sdiff _ _ <| MulAction.injective a
#align finset.smul_finset_sdiff Finset.smul_finset_sdiff
#align finset.vadd_finset_sdiff Finset.vadd_finset_sdiff

open scoped symmDiff in
@[to_additive]
theorem smul_finset_symmDiff : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff _ _ <| MulAction.injective a
#align finset.smul_finset_symm_diff Finset.smul_finset_symmDiff
#align finset.vadd_finset_symm_diff Finset.vadd_finset_symmDiff

@[to_additive (attr := simp)]
theorem smul_finset_univ [Fintype β] : a • (univ : Finset β) = univ :=
  image_univ_of_surjective <| MulAction.surjective a
#align finset.smul_finset_univ Finset.smul_finset_univ
#align finset.vadd_finset_univ Finset.vadd_finset_univ

@[to_additive (attr := simp)]
theorem smul_univ [Fintype β] {s : Finset α} (hs : s.Nonempty) : s • (univ : Finset β) = univ :=
  coe_injective <| by
    push_cast
    exact Set.smul_univ hs
#align finset.smul_univ Finset.smul_univ
#align finset.vadd_univ Finset.vadd_univ

@[to_additive (attr := simp)]
theorem card_smul_finset (a : α) (s : Finset β) : (a • s).card = s.card :=
  card_image_of_injective _ <| MulAction.injective _
#align finset.card_smul_finset Finset.card_smul_finset
#align finset.card_vadd_finset Finset.card_vadd_finset

/-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily distinct!), then
the size of `t` divides the size of `s • t`. -/
@[to_additive "If the left cosets of `t` by elements of `s` are disjoint (but not necessarily
distinct!), then the size of `t` divides the size of `s +ᵥ t`."]
theorem card_dvd_card_smul_right {s : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id → t.card ∣ (s • t).card :=
  card_dvd_card_image₂_right fun _ _ => MulAction.injective _
#align finset.card_dvd_card_smul_right Finset.card_dvd_card_smul_right
#align finset.card_dvd_card_vadd_right Finset.card_dvd_card_vadd_right

variable [DecidableEq α]

/-- If the right cosets of `s` by elements of `t` are disjoint (but not necessarily distinct!), then
the size of `s` divides the size of `s * t`. -/
@[to_additive "If the right cosets of `s` by elements of `t` are disjoint (but not necessarily
distinct!), then the size of `s` divides the size of `s + t`."]
theorem card_dvd_card_mul_left {s t : Finset α} :
    ((fun b => s.image fun a => a * b) '' (t : Set α)).PairwiseDisjoint id →
      s.card ∣ (s * t).card :=
  card_dvd_card_image₂_left fun _ _ => mul_left_injective _
#align finset.card_dvd_card_mul_left Finset.card_dvd_card_mul_left
#align finset.card_dvd_card_add_left Finset.card_dvd_card_add_left

/-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily distinct!), then
the size of `t` divides the size of `s * t`. -/
@[to_additive "If the left cosets of `t` by elements of `s` are disjoint (but not necessarily
distinct!), then the size of `t` divides the size of `s + t`."]
theorem card_dvd_card_mul_right {s t : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id → t.card ∣ (s * t).card :=
  card_dvd_card_image₂_right fun _ _ => mul_right_injective _

@[to_additive (attr := simp)]
lemma inv_smul_finset_distrib (a : α) (s : Finset α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  ext; simp [← inv_smul_mem_iff]

@[to_additive (attr := simp)]
lemma inv_op_smul_finset_distrib (a : α) (s : Finset α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  ext; simp [← inv_smul_mem_iff]

end Group

section SMulZeroClass

variable [Zero β] [SMulZeroClass α β] [DecidableEq β] {s : Finset α} {t : Finset β} {a : α}

theorem smul_zero_subset (s : Finset α) : s • (0 : Finset β) ⊆ 0 := by simp [subset_iff, mem_smul]
#align finset.smul_zero_subset Finset.smul_zero_subset

theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Finset β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using hs
#align finset.nonempty.smul_zero Finset.Nonempty.smul_zero

theorem zero_mem_smul_finset (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
  mem_smul_finset.2 ⟨0, h, smul_zero _⟩
#align finset.zero_mem_smul_finset Finset.zero_mem_smul_finset

variable [Zero α] [NoZeroSMulDivisors α β]

theorem zero_mem_smul_finset_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t := by
  rw [← mem_coe, coe_smul_finset, Set.zero_mem_smul_set_iff ha, mem_coe]
#align finset.zero_mem_smul_finset_iff Finset.zero_mem_smul_finset_iff

end SMulZeroClass

section SMulWithZero

variable [Zero α] [Zero β] [SMulWithZero α β] [DecidableEq β] {s : Finset α} {t : Finset β}

/-!
Note that we have neither `SMulWithZero α (Finset β)` nor `SMulWithZero (Finset α) (Finset β)`
because `0 • ∅ ≠ 0`.
-/

lemma zero_smul_subset (t : Finset β) : (0 : Finset α) • t ⊆ 0 := by simp [subset_iff, mem_smul]
#align finset.zero_smul_subset Finset.zero_smul_subset

lemma Nonempty.zero_smul (ht : t.Nonempty) : (0 : Finset α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using ht
#align finset.nonempty.zero_smul Finset.Nonempty.zero_smul

/-- A nonempty set is scaled by zero to the singleton set containing zero. -/
@[simp] lemma zero_smul_finset {s : Finset β} (h : s.Nonempty) : (0 : α) • s = (0 : Finset β) :=
  coe_injective <| by simpa using @Set.zero_smul_set α _ _ _ _ _ h
#align finset.zero_smul_finset Finset.zero_smul_finset

lemma zero_smul_finset_subset (s : Finset β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ ↦ mem_zero.2 <| zero_smul α x
#align finset.zero_smul_finset_subset Finset.zero_smul_finset_subset

variable [NoZeroSMulDivisors α β] {a : α}

lemma zero_mem_smul_iff :
    (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.Nonempty ∨ (0 : β) ∈ t ∧ s.Nonempty := by
  rw [← mem_coe, coe_smul, Set.zero_mem_smul_iff]; rfl
#align finset.zero_mem_smul_iff Finset.zero_mem_smul_iff

end SMulWithZero

section GroupWithZero

variable [DecidableEq β] [GroupWithZero α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

@[simp]
theorem smul_mem_smul_finset_iff₀ (ha : a ≠ 0) : a • b ∈ a • s ↔ b ∈ s :=
  smul_mem_smul_finset_iff (Units.mk0 a ha)
#align finset.smul_mem_smul_finset_iff₀ Finset.smul_mem_smul_finset_iff₀

theorem inv_smul_mem_iff₀ (ha : a ≠ 0) : a⁻¹ • b ∈ s ↔ b ∈ a • s :=
  show _ ↔ _ ∈ Units.mk0 a ha • _ from inv_smul_mem_iff
#align finset.inv_smul_mem_iff₀ Finset.inv_smul_mem_iff₀

theorem mem_inv_smul_finset_iff₀ (ha : a ≠ 0) : b ∈ a⁻¹ • s ↔ a • b ∈ s :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_finset_iff
#align finset.mem_inv_smul_finset_iff₀ Finset.mem_inv_smul_finset_iff₀

@[simp]
theorem smul_finset_subset_smul_finset_iff₀ (ha : a ≠ 0) : a • s ⊆ a • t ↔ s ⊆ t :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_finset_subset_smul_finset_iff
#align finset.smul_finset_subset_smul_finset_iff₀ Finset.smul_finset_subset_smul_finset_iff₀

theorem smul_finset_subset_iff₀ (ha : a ≠ 0) : a • s ⊆ t ↔ s ⊆ a⁻¹ • t :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_finset_subset_iff
#align finset.smul_finset_subset_iff₀ Finset.smul_finset_subset_iff₀

theorem subset_smul_finset_iff₀ (ha : a ≠ 0) : s ⊆ a • t ↔ a⁻¹ • s ⊆ t :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_smul_finset_iff
#align finset.subset_smul_finset_iff₀ Finset.subset_smul_finset_iff₀

theorem smul_finset_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter _ _ <| MulAction.injective₀ ha
#align finset.smul_finset_inter₀ Finset.smul_finset_inter₀

theorem smul_finset_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t :=
  image_sdiff _ _ <| MulAction.injective₀ ha
#align finset.smul_finset_sdiff₀ Finset.smul_finset_sdiff₀

open scoped symmDiff in
theorem smul_finset_symmDiff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff _ _ <| MulAction.injective₀ ha
#align finset.smul_finset_symm_diff₀ Finset.smul_finset_symmDiff₀

lemma smul_finset_univ₀ [Fintype β] (ha : a ≠ 0) : a • (univ : Finset β) = univ :=
  coe_injective <| by push_cast; exact Set.smul_set_univ₀ ha
#align finset.smul_finset_univ₀ Finset.smul_finset_univ₀

theorem smul_univ₀ [Fintype β] {s : Finset α} (hs : ¬s ⊆ 0) : s • (univ : Finset β) = univ :=
  coe_injective <| by
    rw [← coe_subset] at hs
    push_cast at hs ⊢
    exact Set.smul_univ₀ hs
#align finset.smul_univ₀ Finset.smul_univ₀

lemma smul_univ₀' [Fintype β] {s : Finset α} (hs : s.Nontrivial) : s • (univ : Finset β) = univ :=
  coe_injective <| by push_cast; exact Set.smul_univ₀' hs

variable [DecidableEq α]

@[simp] protected lemma inv_zero : (0 : Finset α)⁻¹ = 0 := by ext; simp

@[simp] lemma inv_smul_finset_distrib₀ (a : α) (s : Finset α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [← inv_smul_mem_iff₀, *]

@[simp] lemma inv_op_smul_finset_distrib₀ (a : α) (s : Finset α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [← inv_smul_mem_iff₀, *]

end GroupWithZero

section Monoid

variable [Monoid α] [AddGroup β] [DistribMulAction α β] [DecidableEq β] (a : α) (s : Finset α)
  (t : Finset β)

@[simp]
theorem smul_finset_neg : a • -t = -(a • t) := by
  simp only [← image_smul, ← image_neg, Function.comp, image_image, smul_neg]
#align finset.smul_finset_neg Finset.smul_finset_neg

@[simp]
protected theorem smul_neg : s • -t = -(s • t) := by
  simp_rw [← image_neg]
  exact image_image₂_right_comm smul_neg
#align finset.smul_neg Finset.smul_neg

end Monoid

section Ring

variable [Ring α] [AddCommGroup β] [Module α β] [DecidableEq β] {s : Finset α} {t : Finset β}
  {a : α}

@[simp]
theorem neg_smul_finset : -a • t = -(a • t) := by
  simp only [← image_smul, ← image_neg, image_image, neg_smul, Function.comp]
#align finset.neg_smul_finset Finset.neg_smul_finset

@[simp]
protected theorem neg_smul [DecidableEq α] : -s • t = -(s • t) := by
  simp_rw [← image_neg]
  exact image₂_image_left_comm neg_smul
#align finset.neg_smul Finset.neg_smul

end Ring

section BigOps
section CommMonoid
variable [CommMonoid α] {ι : Type*} [DecidableEq ι]

@[to_additive (attr := simp)] lemma prod_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι → α) :
    ∏ i ∈ s⁻¹, f i = ∏ i ∈ s, f i⁻¹ := prod_image <| inv_injective.injOn _

@[to_additive existing, simp] lemma prod_neg_index [InvolutiveNeg ι] (s : Finset ι) (f : ι → α) :
    ∏ i ∈ -s, f i = ∏ i ∈ s, f (-i) := prod_image <| neg_injective.injOn _

end CommMonoid

section AddCommMonoid
variable [AddCommMonoid α] {ι : Type*} [DecidableEq ι]

@[to_additive existing, simp] lemma sum_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι → α) :
    ∑ i ∈ s⁻¹, f i = ∑ i ∈ s, f i⁻¹ := sum_image <| inv_injective.injOn _

end AddCommMonoid
end BigOps
end Finset

namespace Fintype
variable {ι : Type*} {α β : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (α i)]
  [∀ i, DecidableEq (β i)]

@[to_additive]
lemma piFinset_mul [∀ i, Mul (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ s i * t i) = piFinset s * piFinset t := piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_div [∀ i, Div (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ s i / t i) = piFinset s / piFinset t := piFinset_image₂ _ _ _

@[to_additive (attr := simp)]
lemma piFinset_inv [∀ i, Inv (α i)] (s : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ (s i)⁻¹) = (piFinset s)⁻¹ := piFinset_image _ _

@[to_additive]
lemma piFinset_smul [∀ i, SMul (α i) (β i)] (s : ∀ i, Finset (α i)) (t : ∀ i, Finset (β i)) :
    piFinset (fun i ↦ s i • t i) = piFinset s • piFinset t := piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_smul_finset [∀ i, SMul (α i) (β i)] (a : ∀ i, α i) (s : ∀ i, Finset (β i)) :
    piFinset (fun i ↦ a i • s i) = a • piFinset s := piFinset_image _ _

-- Note: We don't currently state `piFinset_vsub` because there's no
-- `[∀ i, VSub (β i) (α i)] → VSub (∀ i, β i) (∀ i, α i)` instance

end Fintype

open Pointwise

namespace Set

section One

variable [One α]

@[to_additive (attr := simp)]
theorem toFinset_one : (1 : Set α).toFinset = 1 :=
  rfl
#align set.to_finset_one Set.toFinset_one
#align set.to_finset_zero Set.toFinset_zero

-- Porting note: should take priority over `Finite.toFinset_singleton`
@[to_additive (attr := simp high)]
theorem Finite.toFinset_one (h : (1 : Set α).Finite := finite_one) : h.toFinset = 1 :=
  Finite.toFinset_singleton _
#align set.finite.to_finset_one Set.Finite.toFinset_one
#align set.finite.to_finset_zero Set.Finite.toFinset_zero

end One

section Mul

variable [DecidableEq α] [Mul α] {s t : Set α}

@[to_additive (attr := simp)]
theorem toFinset_mul (s t : Set α) [Fintype s] [Fintype t] [Fintype ↑(s * t)] :
    (s * t).toFinset = s.toFinset * t.toFinset :=
  toFinset_image2 _ _ _
#align set.to_finset_mul Set.toFinset_mul
#align set.to_finset_add Set.toFinset_add

@[to_additive]
theorem Finite.toFinset_mul (hs : s.Finite) (ht : t.Finite) (hf := hs.mul ht) :
    hf.toFinset = hs.toFinset * ht.toFinset :=
  Finite.toFinset_image2 _ _ _
#align set.finite.to_finset_mul Set.Finite.toFinset_mul
#align set.finite.to_finset_add Set.Finite.toFinset_add

end Mul

section SMul

variable [SMul α β] [DecidableEq β] {a : α} {s : Set α} {t : Set β}

@[to_additive (attr := simp)]
theorem toFinset_smul (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s • t)] :
    (s • t).toFinset = s.toFinset • t.toFinset :=
  toFinset_image2 _ _ _
#align set.to_finset_smul Set.toFinset_smul
#align set.to_finset_vadd Set.toFinset_vadd

@[to_additive]
theorem Finite.toFinset_smul (hs : s.Finite) (ht : t.Finite) (hf := hs.smul ht) :
    hf.toFinset = hs.toFinset • ht.toFinset :=
  Finite.toFinset_image2 _ _ _
#align set.finite.to_finset_smul Set.Finite.toFinset_smul
#align set.finite.to_finset_vadd Set.Finite.toFinset_vadd

end SMul

section SMul

variable [DecidableEq β] [SMul α β] {a : α} {s : Set β}

@[to_additive (attr := simp)]
theorem toFinset_smul_set (a : α) (s : Set β) [Fintype s] [Fintype ↑(a • s)] :
    (a • s).toFinset = a • s.toFinset :=
  toFinset_image _ _
#align set.to_finset_smul_set Set.toFinset_smul_set
#align set.to_finset_vadd_set Set.toFinset_vadd_set

@[to_additive]
theorem Finite.toFinset_smul_set (hs : s.Finite) (hf : (a • s).Finite := hs.smul_set) :
    hf.toFinset = a • hs.toFinset :=
  Finite.toFinset_image _ _ _
#align set.finite.to_finset_smul_set Set.Finite.toFinset_smul_set
#align set.finite.to_finset_vadd_set Set.Finite.toFinset_vadd_set

end SMul

section VSub

variable [DecidableEq α] [VSub α β] {s t : Set β}

@[simp]
theorem toFinset_vsub (s t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s -ᵥ t)] :
    (s -ᵥ t : Set α).toFinset = s.toFinset -ᵥ t.toFinset :=
  toFinset_image2 _ _ _
#align set.to_finset_vsub Set.toFinset_vsub

theorem Finite.toFinset_vsub (hs : s.Finite) (ht : t.Finite) (hf := hs.vsub ht) :
    hf.toFinset = hs.toFinset -ᵥ ht.toFinset :=
  Finite.toFinset_image2 _ _ _
#align set.finite.to_finset_vsub Set.Finite.toFinset_vsub

end VSub

section MulAction
variable [Group α] [MulAction α β]

@[to_additive (attr := simp)]
lemma card_smul_set (a : α) (s : Set β) : Nat.card ↥(a • s) = Nat.card s :=
  Nat.card_image_of_injective (MulAction.injective a) _

end MulAction

section IsCancelMul
variable [Mul α] [IsCancelMul α] {s t : Set α}

@[to_additive]
lemma card_mul_le : Nat.card (s * t) ≤ Nat.card s * Nat.card t := by
  classical
  obtain h | h := (s * t).infinite_or_finite
  · simp [Set.Infinite.card_eq_zero h]
  obtain ⟨hs, ht⟩ | rfl | rfl := finite_mul.1 h
  · lift s to Finset α using hs
    lift t to Finset α using ht
    rw [← Finset.coe_mul]
    simpa [-Finset.coe_mul] using Finset.card_mul_le
  all_goals simp

end IsCancelMul

section InvolutiveInv
variable [InvolutiveInv α] {s t : Set α}

@[to_additive (attr := simp)]
lemma card_inv (s : Set α) : Nat.card ↥(s⁻¹) = Nat.card s := by
  rw [← image_inv, Nat.card_image_of_injective inv_injective]

end InvolutiveInv

section Group
variable [Group α] {s t : Set α}

@[to_additive]
lemma card_div_le : Nat.card (s / t) ≤ Nat.card s * Nat.card t := by
  rw [div_eq_mul_inv, ← card_inv t]; exact card_mul_le

end Group
end Set

instance Nat.decidablePred_mem_vadd_set {s : Set ℕ} [DecidablePred (· ∈ s)] (a : ℕ) :
    DecidablePred (· ∈ a +ᵥ s) :=
  fun n ↦ decidable_of_iff' (a ≤ n ∧ n - a ∈ s) <| by
    simp only [Set.mem_vadd_set, vadd_eq_add]; aesop
