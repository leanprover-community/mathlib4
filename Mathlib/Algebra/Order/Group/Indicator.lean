/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Support of a function in an order

This file relates the support of a function to order constructions.
-/

assert_not_exists MonoidWithZero

open Set

variable {ι : Sort*} {α β M : Type*}

namespace Function
variable [One M]

@[to_additive]
lemma mulSupport_sup [SemilatticeSup M] (f g : α → M) :
    mulSupport (fun x ↦ f x ⊔ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊔ ·) (sup_idem _) f g
#align function.mul_support_sup Function.mulSupport_sup
#align function.support_sup Function.support_sup

@[to_additive]
lemma mulSupport_inf [SemilatticeInf M] (f g : α → M) :
    mulSupport (fun x ↦ f x ⊓ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊓ ·) (inf_idem _) f g
#align function.mul_support_inf Function.mulSupport_inf
#align function.support_inf Function.support_inf

@[to_additive]
lemma mulSupport_max [LinearOrder M] (f g : α → M) :
    mulSupport (fun x ↦ max (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := mulSupport_sup f g
#align function.mul_support_max Function.mulSupport_max
#align function.support_max Function.support_max

@[to_additive]
lemma mulSupport_min [LinearOrder M] (f g : α → M) :
    mulSupport (fun x ↦ min (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := mulSupport_inf f g
#align function.mul_support_min Function.mulSupport_min
#align function.support_min Function.support_min

@[to_additive]
lemma mulSupport_iSup [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    mulSupport (fun x ↦ ⨆ i, f i x) ⊆ ⋃ i, mulSupport (f i) := by
  simp only [mulSupport_subset_iff', mem_iUnion, not_exists, nmem_mulSupport]
  intro x hx
  simp only [hx, ciSup_const]
#align function.mul_support_supr Function.mulSupport_iSup
#align function.support_supr Function.support_iSup

@[to_additive]
lemma mulSupport_iInf [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    mulSupport (fun x ↦ ⨅ i, f i x) ⊆ ⋃ i, mulSupport (f i) := mulSupport_iSup (M := Mᵒᵈ) f
#align function.mul_support_infi Function.mulSupport_iInf
#align function.support_infi Function.support_iInf

end Function

namespace Set

section LE
variable [LE M] [One M] {s t : Set α} {f g : α → M} {a : α} {y : M}

@[to_additive]
lemma mulIndicator_apply_le' (hfg : a ∈ s → f a ≤ y) (hg : a ∉ s → 1 ≤ y) :
    mulIndicator s f a ≤ y := by
  by_cases ha : a ∈ s
  · simpa [ha] using hfg ha
  · simpa [ha] using hg ha
#align set.mul_indicator_apply_le' Set.mulIndicator_apply_le'
#align set.indicator_apply_le' Set.indicator_apply_le'

@[to_additive]
lemma mulIndicator_le' (hfg : ∀ a ∈ s, f a ≤ g a) (hg : ∀ a, a ∉ s → 1 ≤ g a) :
    mulIndicator s f ≤ g := fun _ ↦ mulIndicator_apply_le' (hfg _) (hg _)
#align set.mul_indicator_le' Set.mulIndicator_le'
#align set.indicator_le' Set.indicator_le'

@[to_additive]
lemma le_mulIndicator_apply (hfg : a ∈ s → y ≤ g a) (hf : a ∉ s → y ≤ 1) :
    y ≤ mulIndicator s g a := mulIndicator_apply_le' (M := Mᵒᵈ) hfg hf
#align set.le_mul_indicator_apply Set.le_mulIndicator_apply
#align set.le_indicator_apply Set.le_indicator_apply

@[to_additive]
lemma le_mulIndicator (hfg : ∀ a ∈ s, f a ≤ g a) (hf : ∀ a ∉ s, f a ≤ 1) :
    f ≤ mulIndicator s g := fun _ ↦ le_mulIndicator_apply (hfg _) (hf _)
#align set.le_mul_indicator Set.le_mulIndicator
#align set.le_indicator Set.le_indicator

end LE

section Preorder
variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α} {y : M}

@[to_additive indicator_apply_nonneg]
lemma one_le_mulIndicator_apply (h : a ∈ s → 1 ≤ f a) : 1 ≤ mulIndicator s f a :=
  le_mulIndicator_apply h fun _ ↦ le_rfl
#align set.one_le_mul_indicator_apply Set.one_le_mulIndicator_apply
#align set.indicator_apply_nonneg Set.indicator_apply_nonneg

@[to_additive indicator_nonneg]
lemma one_le_mulIndicator (h : ∀ a ∈ s, 1 ≤ f a) (a : α) : 1 ≤ mulIndicator s f a :=
  one_le_mulIndicator_apply (h a)
#align set.one_le_mul_indicator Set.one_le_mulIndicator
#align set.indicator_nonneg Set.indicator_nonneg

@[to_additive]
lemma mulIndicator_apply_le_one (h : a ∈ s → f a ≤ 1) : mulIndicator s f a ≤ 1 :=
  mulIndicator_apply_le' h fun _ ↦ le_rfl
#align set.mul_indicator_apply_le_one Set.mulIndicator_apply_le_one
#align set.indicator_apply_nonpos Set.indicator_apply_nonpos

@[to_additive]
lemma mulIndicator_le_one (h : ∀ a ∈ s, f a ≤ 1) (a : α) : mulIndicator s f a ≤ 1 :=
  mulIndicator_apply_le_one (h a)
#align set.mul_indicator_le_one Set.mulIndicator_le_one
#align set.indicator_nonpos Set.indicator_nonpos

@[to_additive]
lemma mulIndicator_le_mulIndicator (h : f a ≤ g a) : mulIndicator s f a ≤ mulIndicator s g a :=
  mulIndicator_rel_mulIndicator le_rfl fun _ ↦ h
#align set.mul_indicator_le_mul_indicator Set.mulIndicator_le_mulIndicator
#align set.indicator_le_indicator Set.indicator_le_indicator

attribute [mono] mulIndicator_le_mulIndicator indicator_le_indicator

@[to_additive]
lemma mulIndicator_le_mulIndicator_of_subset (h : s ⊆ t) (hf : ∀ a, 1 ≤ f a) (a : α) :
    mulIndicator s f a ≤ mulIndicator t f a :=
  mulIndicator_apply_le'
    (fun ha ↦ le_mulIndicator_apply (fun _ ↦ le_rfl) fun hat ↦ (hat <| h ha).elim) fun _ ↦
    one_le_mulIndicator_apply fun _ ↦ hf _
#align set.mul_indicator_le_mul_indicator_of_subset Set.mulIndicator_le_mulIndicator_of_subset
#align set.indicator_le_indicator_of_subset Set.indicator_le_indicator_of_subset

@[to_additive]
lemma mulIndicator_le_self' (hf : ∀ x ∉ s, 1 ≤ f x) : mulIndicator s f ≤ f :=
  mulIndicator_le' (fun _ _ ↦ le_rfl) hf
#align set.mul_indicator_le_self' Set.mulIndicator_le_self'
#align set.indicator_le_self' Set.indicator_le_self'

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
#align set.indicator_le_indicator_nonneg Set.indicator_le_indicator_nonneg

lemma indicator_nonpos_le_indicator (s : Set α) (f : α → M) :
    {a | f a ≤ 0}.indicator f ≤ s.indicator f :=
  indicator_le_indicator_nonneg (M := Mᵒᵈ) _ _
#align set.indicator_nonpos_le_indicator Set.indicator_nonpos_le_indicator

end LinearOrder

section CompleteLattice
variable [CompleteLattice M] [One M] {s t : Set α} {f g : α → M} {a : α} {y : M}

@[to_additive]
lemma mulIndicator_iUnion_apply (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋃ i, s i) f x = ⨆ i, mulIndicator (s i) f x := by
  by_cases hx : x ∈ ⋃ i, s i
  · rw [mulIndicator_of_mem hx]
    rw [mem_iUnion] at hx
    refine le_antisymm ?_ (iSup_le fun i ↦ mulIndicator_le_self' (fun x _ ↦ h1 ▸ bot_le) x)
    rcases hx with ⟨i, hi⟩
    exact le_iSup_of_le i (ge_of_eq <| mulIndicator_of_mem hi _)
  · rw [mulIndicator_of_not_mem hx]
    simp only [mem_iUnion, not_exists] at hx
    simp [hx, ← h1]
#align set.mul_indicator_Union_apply Set.mulIndicator_iUnion_apply
#align set.indicator_Union_apply Set.indicator_iUnion_apply

variable [Nonempty ι]

@[to_additive]
lemma mulIndicator_iInter_apply (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋂ i, s i) f x = ⨅ i, mulIndicator (s i) f x := by
  by_cases hx : x ∈ ⋂ i, s i
  · rw [mulIndicator_of_mem hx]
    rw [mem_iInter] at hx
    refine le_antisymm ?_ (by simp only [mulIndicator_of_mem (hx _), ciInf_const, le_refl])
    exact le_iInf (fun j ↦ by simp only [mulIndicator_of_mem (hx j), le_refl])
  · rw [mulIndicator_of_not_mem hx]
    simp only [mem_iInter, not_exists, not_forall] at hx
    rcases hx with ⟨j, hj⟩
    refine le_antisymm (by simp only [← h1, le_iInf_iff, bot_le, forall_const]) ?_
    simpa [mulIndicator_of_not_mem hj] using (iInf_le (fun i ↦ (s i).mulIndicator f) j) x

end CompleteLattice

section CanonicallyOrderedCommMonoid

variable [CanonicallyOrderedCommMonoid M]

@[to_additive]
lemma mulIndicator_le_self (s : Set α) (f : α → M) : mulIndicator s f ≤ f :=
  mulIndicator_le_self' fun _ _ ↦ one_le _
#align set.mul_indicator_le_self Set.mulIndicator_le_self
#align set.indicator_le_self Set.indicator_le_self

@[to_additive]
lemma mulIndicator_apply_le {a : α} {s : Set α} {f g : α → M} (hfg : a ∈ s → f a ≤ g a) :
    mulIndicator s f a ≤ g a :=
  mulIndicator_apply_le' hfg fun _ ↦ one_le _
#align set.mul_indicator_apply_le Set.mulIndicator_apply_le
#align set.indicator_apply_le Set.indicator_apply_le

@[to_additive]
lemma mulIndicator_le {s : Set α} {f g : α → M} (hfg : ∀ a ∈ s, f a ≤ g a) :
    mulIndicator s f ≤ g :=
  mulIndicator_le' hfg fun _ _ ↦ one_le _
#align set.mul_indicator_le Set.mulIndicator_le
#align set.indicator_le Set.indicator_le

end CanonicallyOrderedCommMonoid

section LinearOrderedCommGroup
variable [LinearOrderedCommGroup M]

open scoped symmDiff

@[to_additive]
lemma mabs_mulIndicator_symmDiff (s t : Set α) (f : α → M) (x : α) :
    |mulIndicator (s ∆ t) f x|ₘ = |mulIndicator s f x / mulIndicator t f x|ₘ :=
  apply_mulIndicator_symmDiff mabs_inv s t f x

end LinearOrderedCommGroup
end Set
