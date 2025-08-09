/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Indicator
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Support of a function in an order

This file relates the support of a function to order constructions.
-/

assert_not_exists MonoidWithZero

open Set

variable {ι : Sort*} {α M : Type*}

namespace Function
variable [One M]

@[to_additive]
lemma mulSupport_sup [SemilatticeSup M] (f g : α → M) :
    mulSupport (fun x ↦ f x ⊔ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊔ ·) (sup_idem _) f g

@[to_additive]
lemma mulSupport_inf [SemilatticeInf M] (f g : α → M) :
    mulSupport (fun x ↦ f x ⊓ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊓ ·) (inf_idem _) f g

@[to_additive]
lemma mulSupport_max [LinearOrder M] (f g : α → M) :
    mulSupport (fun x ↦ max (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := mulSupport_sup f g

@[to_additive]
lemma mulSupport_min [LinearOrder M] (f g : α → M) :
    mulSupport (fun x ↦ min (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := mulSupport_inf f g

@[to_additive]
lemma mulSupport_iSup [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    mulSupport (fun x ↦ ⨆ i, f i x) ⊆ ⋃ i, mulSupport (f i) := by
  simp only [mulSupport_subset_iff', mem_iUnion, not_exists, notMem_mulSupport]
  intro x hx
  simp only [hx, ciSup_const]

@[to_additive]
lemma mulSupport_iInf [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    mulSupport (fun x ↦ ⨅ i, f i x) ⊆ ⋃ i, mulSupport (f i) := mulSupport_iSup (M := Mᵒᵈ) f

end Function

namespace Set

section LE
variable [LE M] [One M] {s : Set α} {f g : α → M} {a : α} {y : M}

@[to_additive]
lemma mulIndicator_apply_le' (hfg : a ∈ s → f a ≤ y) (hg : a ∉ s → 1 ≤ y) :
    mulIndicator s f a ≤ y := by
  by_cases ha : a ∈ s
  · simpa [ha] using hfg ha
  · simpa [ha] using hg ha

@[to_additive]
lemma mulIndicator_le' (hfg : ∀ a ∈ s, f a ≤ g a) (hg : ∀ a, a ∉ s → 1 ≤ g a) :
    mulIndicator s f ≤ g := fun _ ↦ mulIndicator_apply_le' (hfg _) (hg _)

@[to_additive]
lemma le_mulIndicator_apply (hfg : a ∈ s → y ≤ g a) (hf : a ∉ s → y ≤ 1) :
    y ≤ mulIndicator s g a := mulIndicator_apply_le' (M := Mᵒᵈ) hfg hf

@[to_additive]
lemma le_mulIndicator (hfg : ∀ a ∈ s, f a ≤ g a) (hf : ∀ a ∉ s, f a ≤ 1) :
    f ≤ mulIndicator s g := fun _ ↦ le_mulIndicator_apply (hfg _) (hf _)

end LE

section Preorder
variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α}

@[to_additive indicator_apply_nonneg]
lemma one_le_mulIndicator_apply (h : a ∈ s → 1 ≤ f a) : 1 ≤ mulIndicator s f a :=
  le_mulIndicator_apply h fun _ ↦ le_rfl

@[to_additive indicator_nonneg]
lemma one_le_mulIndicator (h : ∀ a ∈ s, 1 ≤ f a) (a : α) : 1 ≤ mulIndicator s f a :=
  one_le_mulIndicator_apply (h a)

@[to_additive]
lemma mulIndicator_apply_le_one (h : a ∈ s → f a ≤ 1) : mulIndicator s f a ≤ 1 :=
  mulIndicator_apply_le' h fun _ ↦ le_rfl

@[to_additive]
lemma mulIndicator_le_one (h : ∀ a ∈ s, f a ≤ 1) (a : α) : mulIndicator s f a ≤ 1 :=
  mulIndicator_apply_le_one (h a)

@[to_additive]
lemma mulIndicator_le_mulIndicator' (h : a ∈ s → f a ≤ g a) :
    mulIndicator s f a ≤ mulIndicator s g a :=
  mulIndicator_rel_mulIndicator le_rfl h

@[to_additive (attr := mono, gcongr)]
lemma mulIndicator_le_mulIndicator (h : f a ≤ g a) : mulIndicator s f a ≤ mulIndicator s g a :=
  mulIndicator_rel_mulIndicator le_rfl fun _ ↦ h

@[to_additive (attr := gcongr)]
lemma mulIndicator_mono (h : f ≤ g) : s.mulIndicator f ≤ s.mulIndicator g :=
  fun _ ↦ mulIndicator_le_mulIndicator (h _)

@[to_additive]
lemma mulIndicator_le_mulIndicator_apply_of_subset (h : s ⊆ t) (hf : 1 ≤ f a) :
    mulIndicator s f a ≤ mulIndicator t f a :=
  mulIndicator_apply_le'
    (fun ha ↦ le_mulIndicator_apply (fun _ ↦ le_rfl) fun hat ↦ (hat <| h ha).elim) fun _ ↦
    one_le_mulIndicator_apply fun _ ↦ hf

@[to_additive]
lemma mulIndicator_le_mulIndicator_of_subset (h : s ⊆ t) (hf : 1 ≤ f) :
    mulIndicator s f ≤ mulIndicator t f :=
  fun _ ↦ mulIndicator_le_mulIndicator_apply_of_subset h (hf _)

@[to_additive]
lemma mulIndicator_le_self' (hf : ∀ x ∉ s, 1 ≤ f x) : mulIndicator s f ≤ f :=
  mulIndicator_le' (fun _ _ ↦ le_rfl) hf

end Preorder

section LinearOrder
variable [Zero M] [LinearOrder M]

lemma indicator_le_indicator_nonneg (s : Set α) (f : α → M) :
    s.indicator f ≤ {a | 0 ≤ f a}.indicator f := by
  intro a
  classical
  simp_rw [indicator_apply]
  split_ifs
  exacts [le_rfl, (not_le.1 ‹_›).le, ‹_›, le_rfl]

lemma indicator_nonpos_le_indicator (s : Set α) (f : α → M) :
    {a | f a ≤ 0}.indicator f ≤ s.indicator f :=
  indicator_le_indicator_nonneg (M := Mᵒᵈ) _ _

end LinearOrder

section CompleteLattice
variable [CompleteLattice M] [One M]

@[to_additive]
lemma mulIndicator_iUnion_apply (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋃ i, s i) f x = ⨆ i, mulIndicator (s i) f x := by
  by_cases hx : x ∈ ⋃ i, s i
  · rw [mulIndicator_of_mem hx]
    rw [mem_iUnion] at hx
    refine le_antisymm ?_ (iSup_le fun i ↦ mulIndicator_le_self' (fun x _ ↦ h1 ▸ bot_le) x)
    rcases hx with ⟨i, hi⟩
    exact le_iSup_of_le i (ge_of_eq <| mulIndicator_of_mem hi _)
  · rw [mulIndicator_of_notMem hx]
    simp only [mem_iUnion, not_exists] at hx
    simp [hx, ← h1]

variable [Nonempty ι]

@[to_additive]
lemma mulIndicator_iInter_apply (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋂ i, s i) f x = ⨅ i, mulIndicator (s i) f x := by
  by_cases hx : x ∈ ⋂ i, s i
  · simp_all
  · rw [mulIndicator_of_notMem hx]
    simp only [mem_iInter, not_forall] at hx
    rcases hx with ⟨j, hj⟩
    refine le_antisymm (by simp only [← h1, le_iInf_iff, bot_le, forall_const]) ?_
    simpa [mulIndicator_of_notMem hj] using (iInf_le (fun i ↦ (s i).mulIndicator f) j) x

@[to_additive]
lemma iSup_mulIndicator {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {f : ι → α → M}
    {s : ι → Set α} (h1 : (⊥ : M) = 1) (hf : Monotone f) (hs : Monotone s) :
    ⨆ i, (s i).mulIndicator (f i) = (⋃ i, s i).mulIndicator (⨆ i, f i) := by
  simp only [le_antisymm_iff, iSup_le_iff]
  refine ⟨fun i ↦ (mulIndicator_mono (le_iSup _ _)).trans (mulIndicator_le_mulIndicator_of_subset
    (subset_iUnion _ _) (fun _ ↦ by simp [← h1])), fun a ↦ ?_⟩
  by_cases ha : a ∈ ⋃ i, s i
  · obtain ⟨i, hi⟩ : ∃ i, a ∈ s i := by simpa using ha
    rw [mulIndicator_of_mem ha, iSup_apply, iSup_apply]
    refine iSup_le fun j ↦ ?_
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine le_iSup_of_le k <| (hf hjk _).trans_eq ?_
    rw [mulIndicator_of_mem (hs hik hi)]
  · rw [mulIndicator_of_notMem ha, ← h1]
    exact bot_le

end CompleteLattice

section CanonicallyOrderedMul

variable [Monoid M] [PartialOrder M] [CanonicallyOrderedMul M]

@[to_additive]
lemma mulIndicator_le_self (s : Set α) (f : α → M) : mulIndicator s f ≤ f :=
  mulIndicator_le_self' fun _ _ ↦ one_le _

@[to_additive]
lemma mulIndicator_apply_le {a : α} {s : Set α} {f g : α → M} (hfg : a ∈ s → f a ≤ g a) :
    mulIndicator s f a ≤ g a :=
  mulIndicator_apply_le' hfg fun _ ↦ one_le _

@[to_additive]
lemma mulIndicator_le {s : Set α} {f g : α → M} (hfg : ∀ a ∈ s, f a ≤ g a) :
    mulIndicator s f ≤ g :=
  mulIndicator_le' hfg fun _ _ ↦ one_le _

end CanonicallyOrderedMul

section LatticeOrderedCommGroup
variable [CommGroup M] [Lattice M]

open scoped symmDiff

@[to_additive]
lemma mabs_mulIndicator_symmDiff (s t : Set α) (f : α → M) (x : α) :
    |mulIndicator (s ∆ t) f x|ₘ = |mulIndicator s f x / mulIndicator t f x|ₘ :=
  apply_mulIndicator_symmDiff mabs_inv s t f x

end LatticeOrderedCommGroup
end Set
