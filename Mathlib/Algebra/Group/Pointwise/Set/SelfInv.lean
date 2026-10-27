/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Group.SelfInv
public import Mathlib.Algebra.Group.Pointwise.Set.Lattice

/-!
# Self-inverse sets

This file specialises `IsSelfInv` to sets equipped with the pointwise inversion.

-/

public section

open Set
open scoped Pointwise

variable {α β : Type*}

section Inv

variable [Inv α] [Inv β] {s t : Set α}

@[to_additive]
lemma isSelfInv_iff_forall_inv_mem_iff : IsSelfInv s ↔ ∀ x, x⁻¹ ∈ s ↔ x ∈ s := by
  simp only [isSelfInv_iff, Set.ext_iff, mem_inv]

@[to_additive (attr := simp)]
protected lemma IsSelfInv.empty : IsSelfInv (∅ : Set α) := inv_empty

@[to_additive (attr := simp)]
protected lemma IsSelfInv.univ : IsSelfInv (univ : Set α) := inv_univ

@[to_additive]
protected lemma IsSelfInv.inter (hs : IsSelfInv s) (ht : IsSelfInv t) :
    IsSelfInv (s ∩ t) := by
  rw [isSelfInv_iff, inter_inv, hs, ht]

@[to_additive]
protected lemma IsSelfInv.union (hs : IsSelfInv s) (ht : IsSelfInv t) :
    IsSelfInv (s ∪ t) := by
  rw [isSelfInv_iff, union_inv, hs, ht]

@[to_additive]
protected lemma IsSelfInv.iUnion {ι : Sort*} {s : ι → Set α}
    (h : ∀ i, IsSelfInv (s i)) : IsSelfInv (⋃ i, s i) := by
  simpa only [isSelfInv_iff, iUnion_inv] using iUnion_congr h

@[to_additive]
protected lemma IsSelfInv.iInter {ι : Sort*} {s : ι → Set α}
    (h : ∀ i, IsSelfInv (s i)) : IsSelfInv (⋂ i, s i) := by
  simpa only [isSelfInv_iff, iInter_inv] using iInter_congr h

@[to_additive]
protected lemma IsSelfInv.sUnion {S : Set (Set α)} (h : ∀ s ∈ S, IsSelfInv s) :
    IsSelfInv (⋃₀ S) :=
  sUnion_eq_iUnion ▸ .iUnion fun s ↦ h s s.2

@[to_additive]
protected lemma IsSelfInv.sInter {S : Set (Set α)} (h : ∀ s ∈ S, IsSelfInv s) :
    IsSelfInv (⋂₀ S) :=
  sInter_eq_iInter ▸ .iInter fun s ↦ h s s.2

@[to_additive]
protected lemma IsSelfInv.prod {t : Set β} (hs : IsSelfInv s) (ht : IsSelfInv t) :
    IsSelfInv (s ×ˢ t) := by
  rw [isSelfInv_iff, inv_prod, hs, ht]

@[to_additive (attr := simp)]
lemma isSelfInv_compl_iff : IsSelfInv sᶜ ↔ IsSelfInv s := by
  simp only [isSelfInv_iff, compl_inv, compl_inj_iff]

@[to_additive]
protected alias ⟨IsSelfInv.of_compl, IsSelfInv.compl⟩ := isSelfInv_compl_iff

end Inv

section InvolutiveInv

variable [InvolutiveInv α] {s t : Set α}

@[to_additive (attr := simp)]
lemma isSelfInv_singleton_iff {a : α} : IsSelfInv ({a} : Set α) ↔ IsSelfInv a := by
  rw [isSelfInv_iff, inv_singleton, isSelfInv_iff, singleton_eq_singleton_iff]

@[to_additive]
lemma isSelfInv_iff_subset_inv : IsSelfInv s ↔ s ⊆ s⁻¹ :=
  inv_eq_self_iff_inv_subset.trans inv_subset

@[to_additive]
protected alias ⟨IsSelfInv.subset_inv, IsSelfInv.of_subset_inv⟩ := isSelfInv_iff_subset_inv

@[to_additive]
lemma isSelfInv_iff_inv_subset : IsSelfInv s ↔ s⁻¹ ⊆ s :=
  inv_eq_self_iff_inv_subset

@[to_additive]
protected alias ⟨IsSelfInv.inv_subset, IsSelfInv.of_inv_subset⟩ := isSelfInv_iff_inv_subset

@[to_additive]
lemma isSelfInv_iff_forall_inv_mem : IsSelfInv s ↔ ∀ ⦃x⦄, x ∈ s → x⁻¹ ∈ s := by
  rw [isSelfInv_iff_forall_inv_mem_iff]
  exact ⟨fun h x hx ↦ (h x).2 hx, fun h x ↦ ⟨fun hx ↦ inv_inv x ▸ h hx, @h x⟩⟩

@[to_additive]
protected lemma IsSelfInv.inv_mem (h : IsSelfInv s) {x : α} (hx : x ∈ s) : x⁻¹ ∈ s :=
  isSelfInv_iff_forall_inv_mem.mp h hx

@[to_additive]
protected lemma IsSelfInv.diff (hs : IsSelfInv s) (ht : IsSelfInv t) : IsSelfInv (s \ t) := by
  simpa only [sdiff_eq] using hs.inter ht.compl

end InvolutiveInv
