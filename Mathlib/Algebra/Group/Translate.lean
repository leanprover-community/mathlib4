/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Translation operator

This file defines the translation of a function from a group by an element of that group.

## Notation

`τ a f` is notation for `translate a f`.

## See also

Generally, translation is the same as acting on the domain by subtraction. This setting is
abstracted by `DomAddAct` in such a way that `τ a f = DomAddAct.mk (-a) +ᵥ f` (see
`translate_eq_domAddActMk_vadd`). Using `DomAddAct` is irritating in applications because of this
negation appearing inside `DomAddAct.mk`. Although mathematically equivalent, the pen and paper
convention is that translating is an action by subtraction, not by addition.
-/

open Function Set
open scoped Pointwise

variable {ι α β M G H : Type*} [AddCommGroup G]

/-- Translation of a function in a group by an element of that group.
`τ a f` is defined as `x ↦ f (x - a)`. -/
def translate (a : G) (f : G → α) : G → α := fun x ↦ f (x - a)

@[inherit_doc] scoped[translate] notation "τ " => translate

open scoped translate

@[simp] lemma translate_apply (a : G) (f : G → α) (x : G) : τ a f x = f (x - a) := rfl
@[simp] lemma translate_zero (f : G → α) : τ 0 f = f := by ext; simp

lemma translate_translate (a b : G) (f : G → α) : τ a (τ b f) = τ (a + b) f := by
  ext; simp [sub_sub]

lemma translate_add (a b : G) (f : G → α) : τ (a + b) f = τ a (τ b f) := by ext; simp [sub_sub]

/-- See `translate_add` -/
lemma translate_add' (a b : G) (f : G → α) : τ (a + b) f = τ b (τ a f) := by
  rw [add_comm, translate_add]

lemma translate_comm (a b : G) (f : G → α) : τ a (τ b f) = τ b (τ a f) := by
  rw [← translate_add, translate_add']

-- We make `simp` push the `τ` outside
@[simp] lemma comp_translate (a : G) (f : G → α) (g : α → β) : g ∘ τ a f = τ a (g ∘ f) := rfl

lemma translate_eq_domAddActMk_vadd (a : G) (f : G → α) : τ a f = DomAddAct.mk (-a) +ᵥ f := by
  ext; simp [DomAddAct.vadd_apply, sub_eq_neg_add]

@[simp]
lemma translate_smul_right [SMul H α] (a : G) (f : G → α) (c : H) : τ a (c • f) = c • τ a f := rfl

@[simp] lemma translate_zero_right [Zero α] (a : G) : τ a (0 : G → α) = 0 := rfl
lemma translate_add_right [Add α] (a : G) (f g : G → α) : τ a (f + g) = τ a f + τ a g := rfl
lemma translate_sub_right [Sub α] (a : G) (f g : G → α) : τ a (f - g) = τ a f - τ a g := rfl
lemma translate_neg_right [Neg α] (a : G) (f : G → α) : τ a (-f) = -τ a f := rfl

section AddCommMonoid
variable [AddCommMonoid M]

lemma translate_sum_right (a : G) (f : ι → G → M) (s : Finset ι) :
    τ a (∑ i ∈ s, f i) = ∑ i ∈ s, τ a (f i) := by ext; simp

lemma sum_translate [Fintype G] (a : G) (f : G → M) : ∑ b, τ a f b = ∑ b, f b :=
  Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup H]

@[simp] lemma support_translate (a : G) (f : G → H) : support (τ a f) = a +ᵥ support f := by
  ext; simp [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]

end AddCommGroup

variable [CommMonoid M]

lemma translate_prod_right (a : G) (f : ι → G → M) (s : Finset ι) :
    τ a (∏ i ∈ s, f i) = ∏ i ∈ s, τ a (f i) := by ext; simp
