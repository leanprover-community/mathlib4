/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Lattice

/-!
# Inverse-closed sets

This file defines inverse-closed sets.

## Main declarations

* `Set.IsInvClosed s`: The set `s` is closed under inversion.
* `Set.IsNegClosed s`: The set `s` is closed under negation.

-/

@[expose] public section

open scoped Pointwise

namespace Set

variable {α β : Type*}

section Inv

variable [Inv α] [Inv β] {s t : Set α}

/-- A set `s` is *inverse-closed* if `x⁻¹ ∈ s` whenever `x ∈ s`.
This is equivalent to `s⁻¹ = s`, see `Set.isInvClosed_iff_inv_eq_self`. -/
@[to_additive /-- A set `s` is *negation-closed* if `-x ∈ s` whenever `x ∈ s`.
This is equivalent to `-s = s`, see `Set.isNegClosed_iff_neg_eq_self`. -/]
def IsInvClosed (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → x⁻¹ ∈ s

@[to_additive]
lemma IsInvClosed.inv_mem (h : s.IsInvClosed) {a : α} (ha : a ∈ s) : a⁻¹ ∈ s := h ha

@[to_additive]
lemma isInvClosed_iff_subset_inv : s.IsInvClosed ↔ s ⊆ s⁻¹ := Iff.rfl

@[to_additive (attr := simp)]
lemma IsInvClosed.empty : (∅ : Set α).IsInvClosed := fun _ h ↦ False.elim h

@[to_additive (attr := simp)]
lemma IsInvClosed.univ : (univ : Set α).IsInvClosed := fun _ _ ↦ mem_univ _

@[to_additive (attr := simp)]
lemma isInvClosed_singleton_iff {a : α} : ({a} : Set α).IsInvClosed ↔ a⁻¹ = a := by
  simp [IsInvClosed, mem_singleton_iff]

@[to_additive]
lemma IsInvClosed.inter (hs : s.IsInvClosed) (ht : t.IsInvClosed) :
    (s ∩ t).IsInvClosed := fun _ hx ↦ ⟨hs hx.1, ht hx.2⟩

@[to_additive]
lemma IsInvClosed.union (hs : s.IsInvClosed) (ht : t.IsInvClosed) :
    (s ∪ t).IsInvClosed := fun _ hx ↦ hx.imp (hs ·) (ht ·)

@[to_additive]
lemma isInvClosed_iUnion {ι : Sort*} {s : ι → Set α} (h : ∀ i, (s i).IsInvClosed) :
    (⋃ i, s i).IsInvClosed := by
  intro x hx
  rw [mem_iUnion] at hx ⊢
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, h i hi⟩

@[to_additive]
lemma isInvClosed_iInter {ι : Sort*} {s : ι → Set α} (h : ∀ i, (s i).IsInvClosed) :
    (⋂ i, s i).IsInvClosed := by
  intro x hx
  rw [mem_iInter] at hx ⊢
  exact fun i ↦ h i (hx i)

@[to_additive]
lemma isInvClosed_sUnion {S : Set (Set α)} (h : ∀ s ∈ S, s.IsInvClosed) :
    (⋃₀ S).IsInvClosed := by
  rw [sUnion_eq_iUnion]
  exact isInvClosed_iUnion fun s ↦ h s s.2

@[to_additive]
lemma isInvClosed_sInter {S : Set (Set α)} (h : ∀ s ∈ S, s.IsInvClosed) :
    (⋂₀ S).IsInvClosed := by
  rw [sInter_eq_iInter]
  exact isInvClosed_iInter fun s ↦ h s s.2

lemma IsInvClosed.prod (hs : s.IsInvClosed) {t : Set β} (ht : t.IsInvClosed) :
    (s ×ˢ t).IsInvClosed := fun _ h ↦ ⟨hs h.1, ht h.2⟩

end Inv

section InvolutiveInv

variable [InvolutiveInv α] {s t : Set α}

@[to_additive]
lemma isInvClosed_iff_inv_subset : s.IsInvClosed ↔ s⁻¹ ⊆ s :=
  isInvClosed_iff_subset_inv.trans inv_subset.symm

@[to_additive]
lemma isInvClosed_iff_inv_eq_self : s.IsInvClosed ↔ s⁻¹ = s :=
  isInvClosed_iff_inv_subset.trans inv_eq_self_iff_inv_subset.symm

@[to_additive]
alias ⟨IsInvClosed.inv_eq_self, _⟩ := isInvClosed_iff_inv_eq_self

@[to_additive (attr := simp)]
lemma isInvClosed_inv : s⁻¹.IsInvClosed ↔ s.IsInvClosed := by
  simp only [isInvClosed_iff_inv_eq_self, inv_inv, eq_comm]

@[to_additive (attr := simp)]
lemma isInvClosed_compl : sᶜ.IsInvClosed ↔ s.IsInvClosed := by
  simp only [isInvClosed_iff_inv_eq_self, compl_inv, compl_inj_iff]

@[to_additive]
lemma IsInvClosed.diff (hs : s.IsInvClosed) (ht : t.IsInvClosed) :
    (s \ t).IsInvClosed := by
  rw [sdiff_eq]; exact hs.inter (isInvClosed_compl.mpr ht)

end InvolutiveInv

section DivisionCommMonoid

variable [DivisionCommMonoid α] {s t : Set α}

lemma IsInvClosed.mul (hs : s.IsInvClosed) (ht : t.IsInvClosed) :
    (s * t).IsInvClosed := by
  rintro x ⟨_, h₁, _, h₂, rfl⟩
  exact ⟨_, hs h₁, _, ht h₂, by simp only [mul_inv]⟩

end DivisionCommMonoid

end Set
