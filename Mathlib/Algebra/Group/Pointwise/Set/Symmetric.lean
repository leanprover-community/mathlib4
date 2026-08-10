/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Lattice

/-!
# Symmetric sets

This file defines symmetric sets, i.e. sets that are closed under inversion (negation).

## Main declarations

* `Set.IsMulSymmetric s`: The set `s` is closed under inversion.
* `Set.IsAddSymmetric s`: The set `s` is closed under negation.

-/

@[expose] public section

open scoped Pointwise

namespace Set

variable {α : Type*}

section Inv

variable [Inv α] {s t : Set α} {a : α}

/-- A set `s` is *multiplicatively symmetric* if it is closed under inversion.
This is equivalent to `s⁻¹ = s`, see `Set.isMulSymmetric_iff_inv_eq_self`. -/
@[to_additive /-- A set `s` is *symmetric* if it is closed under negation.
This is equivalent to `-s = s`, see `Set.isAddSymmetric_iff_neg_eq_self`. -/]
def IsMulSymmetric (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → x⁻¹ ∈ s

@[to_additive]
lemma IsMulSymmetric.inv_mem (h : s.IsMulSymmetric) (ha : a ∈ s) : a⁻¹ ∈ s := h ha

@[to_additive]
lemma isMulSymmetric_iff_subset_inv : s.IsMulSymmetric ↔ s ⊆ s⁻¹ := Iff.rfl

@[to_additive]
lemma isMulSymmetric_empty : (∅ : Set α).IsMulSymmetric := fun _ h ↦ False.elim h

@[to_additive]
lemma isMulSymmetric_univ : (univ : Set α).IsMulSymmetric := fun _ _ ↦ mem_univ _

@[to_additive (attr := simp)]
lemma isMulSymmetric_singleton_iff {a : α} : ({a} : Set α).IsMulSymmetric ↔ a⁻¹ = a := by
  simp [IsMulSymmetric, mem_singleton_iff]

@[to_additive]
lemma IsMulSymmetric.inter (hs : s.IsMulSymmetric) (ht : t.IsMulSymmetric) :
    (s ∩ t).IsMulSymmetric := fun _ hx ↦ ⟨hs hx.1, ht hx.2⟩

@[to_additive]
lemma IsMulSymmetric.union (hs : s.IsMulSymmetric) (ht : t.IsMulSymmetric) :
    (s ∪ t).IsMulSymmetric := fun _ hx ↦ hx.imp (hs ·) (ht ·)

@[to_additive]
lemma isMulSymmetric_iUnion {ι : Sort*} {s : ι → Set α} (h : ∀ i, (s i).IsMulSymmetric) :
    (⋃ i, s i).IsMulSymmetric := by
  intro x hx
  rw [mem_iUnion] at hx ⊢
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, h i hi⟩

@[to_additive]
lemma isMulSymmetric_iInter {ι : Sort*} {s : ι → Set α} (h : ∀ i, (s i).IsMulSymmetric) :
    (⋂ i, s i).IsMulSymmetric := by
  intro x hx
  rw [mem_iInter] at hx ⊢
  exact fun i ↦ h i (hx i)

@[to_additive]
lemma isMulSymmetric_sUnion {S : Set (Set α)} (h : ∀ s ∈ S, s.IsMulSymmetric) :
    (⋃₀ S).IsMulSymmetric := by
  rw [sUnion_eq_iUnion]
  exact isMulSymmetric_iUnion fun s ↦ h s s.2

@[to_additive]
lemma isMulSymmetric_sInter {S : Set (Set α)} (h : ∀ s ∈ S, s.IsMulSymmetric) :
    (⋂₀ S).IsMulSymmetric := by
  rw [sInter_eq_iInter]
  exact isMulSymmetric_iInter fun s ↦ h s s.2

end Inv

section InvolutiveInv

variable [InvolutiveInv α] {s t : Set α}

@[to_additive]
lemma isMulSymmetric_iff_inv_subset : s.IsMulSymmetric ↔ s⁻¹ ⊆ s :=
  isMulSymmetric_iff_subset_inv.trans inv_subset.symm

@[to_additive]
lemma isMulSymmetric_iff_inv_eq_self : s.IsMulSymmetric ↔ s⁻¹ = s :=
  isMulSymmetric_iff_inv_subset.trans inv_eq_self_iff_inv_subset.symm

@[to_additive]
alias ⟨IsMulSymmetric.inv_eq_self, _⟩ := isMulSymmetric_iff_inv_eq_self

@[to_additive (attr := simp)]
lemma isMulSymmetric_inv : s⁻¹.IsMulSymmetric ↔ s.IsMulSymmetric := by
  simp only [isMulSymmetric_iff_inv_eq_self, inv_inv, eq_comm]

@[to_additive (attr := simp)]
lemma isMulSymmetric_compl : sᶜ.IsMulSymmetric ↔ s.IsMulSymmetric := by
  simp only [isMulSymmetric_iff_inv_eq_self, compl_inv, compl_inj_iff]

@[to_additive]
lemma IsMulSymmetric.diff (hs : s.IsMulSymmetric) (ht : t.IsMulSymmetric) :
    (s \ t).IsMulSymmetric := by
  rw [sdiff_eq]; exact hs.inter (isMulSymmetric_compl.mpr ht)

end InvolutiveInv

end Set
