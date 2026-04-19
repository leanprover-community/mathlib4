/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Order.SupClosed

import Mathlib.Data.Nat.Pairing

/-!
# Sets closed under countable join/meet

This file defines predicates for sets closed under countable supremum and dually for countable
infimum.

## Main declarations

* `CountableSupClosed`: Predicate for a set to be closed under countable supremum.
* `CountableInfClosed`: Predicate for a set to be closed under countable infimum.
* `countableSupClosure`: countable Sup-closure. Smallest countable sup-closed set containing
  a given set.
* `countableInfClosure`: countable Inf-closure. Smallest countable inf-closed set containing
  a given set.

## Implementation notes

The list of properties in this file is copied and adapted from the file about `SupClosed`.
We should keep these files in sync.

-/

@[expose] public section

variable {ι : Sort*} {α β : Type*} {S : Set (Set α)} {s t : Set α} {a b : α}

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β]

section Set
open Set

/-- A set `s` is closed under countable supremum if `⨆ n, A n ∈ s` for all `A : ι → α`
with `ι` nonempty countable and `A n ∈ s` for all `n`.

The definition uses `ι = ℕ`.
See `CountableSupClosed.iSup_mem` for a supremum over any nonempty countable type. -/
structure CountableSupClosed [CompleteLattice α] (s : Set α) : Prop where
  iSup_nat_mem : ∀ ⦃A : ℕ → α⦄ (_hA : ∀ n, A n ∈ s), ⨆ n, A n ∈ s

/-- A set `s` is closed under countable infimum if `⨅ n, A n ∈ s` for all `A : ι → α`
with `ι` nonempty countable and `A n ∈ s` for all `n`.

The definition uses `ι = ℕ`.
See `CountableInfClosed.iInf_mem` for an infimum over any nonempty countable type. -/
@[to_dual existing]
structure CountableInfClosed (s : Set α) : Prop where
  iInf_nat_mem : ∀ ⦃A : ℕ → α⦄, (∀ n, A n ∈ s) → ⨅ n, A n ∈ s

attribute [to_dual existing] CountableSupClosed

@[to_dual]
lemma CountableSupClosed.iSup_mem [hι : Countable ι] [Nonempty ι]
    (hs : CountableSupClosed s) {A : ι → α} (hA : ∀ n, A n ∈ s) :
    ⨆ n, A n ∈ s := by
  obtain ⟨g, hg⟩ := countable_iff_exists_surjective.mp hι
  have : ⨆ i, A i = ⨆ n, A (g n) := by rw [Function.Surjective.iSup_comp hg]
  rw [this]
  exact hs.iSup_nat_mem (fun n ↦ hA (g n))

@[to_dual]
lemma CountableSupClosed.sSup_mem (hs : CountableSupClosed s)
    (A : Set α) [Countable A] [Nonempty A] (hA : ∀ a ∈ A, a ∈ s) :
    sSup A ∈ s := by
  rw [sSup_eq_iSup']
  exact hs.iSup_mem fun a ↦ hA a a.2

@[to_dual]
lemma CountableSupClosed.supClosed (hs : CountableSupClosed s) : SupClosed s := by
  intro a ha b hb
  simpa using  hs.sSup_mem (A := {a, b}) (by grind)

@[to_dual (attr := simp)] lemma countableSupClosed_singleton_bot :
    CountableSupClosed ({⊥} : Set α) where
  iSup_nat_mem A hA := by simpa using hA

@[to_dual (attr := simp)] lemma CountableSupClosed.univ : CountableSupClosed (univ : Set α) where
  iSup_nat_mem A hA := by simp

@[to_dual]
lemma CountableSupClosed.inter (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s ∩ t) where
  iSup_nat_mem _ hA := ⟨hs.iSup_nat_mem (fun n ↦ (hA n).1), ht.iSup_nat_mem (fun n ↦ (hA n).2)⟩

@[to_dual]
lemma CountableSupClosed.sInter (hS : ∀ s ∈ S, CountableSupClosed s) :
    CountableSupClosed (⋂₀ S) where
  iSup_nat_mem _ hA := fun _s hs ↦ (hS _ hs).iSup_mem fun n ↦ hA n _ hs

@[to_dual]
lemma CountableSupClosed.iInter {f : ι → Set α} (hf : ∀ i, CountableSupClosed (f i)) :
    CountableSupClosed (⋂ i, f i) :=
  CountableSupClosed.sInter <| forall_mem_range.2 hf

lemma CountableSupClosed.directedOn (hs : CountableSupClosed s) : DirectedOn (· ≤ ·) s :=
  hs.supClosed.directedOn

@[to_dual]
lemma CountableSupClosed.prod {t : Set β} (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s ×ˢ t) where
  iSup_nat_mem _ hA := ⟨by rw [Prod.fst_iSup]; exact hs.iSup_nat_mem (fun n ↦ (hA n).1),
    by rw [Prod.snd_iSup]; exact ht.iSup_nat_mem (fun n ↦ (hA n).2)⟩

end Set

section Finset
variable {ι : Type*} {f : ι → α} {t : Finset ι}

@[to_dual]
lemma CountableSupClosed.finsetSup'_mem (hs : CountableSupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup' ht f ∈ s :=
  hs.supClosed.finsetSup'_mem ht

@[to_dual]
lemma CountableSupClosed.finsetSup_mem (hs : CountableSupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup f ∈ s :=
  Finset.sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

end Finset

open OrderDual

@[simp] lemma countableSupClosed_preimage_toDual {s : Set αᵒᵈ} :
    CountableSupClosed (toDual ⁻¹' s) ↔ CountableInfClosed s :=
  ⟨fun h ↦ ⟨h.iSup_nat_mem⟩, fun h ↦ ⟨h.iInf_nat_mem⟩⟩

@[simp] lemma countableInfClosed_preimage_toDual {s : Set αᵒᵈ} :
    CountableInfClosed (toDual ⁻¹' s) ↔ CountableSupClosed s :=
  ⟨fun h ↦ ⟨h.iInf_nat_mem⟩, fun h ↦ ⟨h.iSup_nat_mem⟩⟩

@[simp] lemma countableSupClosed_preimage_ofDual {s : Set α} :
    CountableSupClosed (ofDual ⁻¹' s) ↔ CountableInfClosed s :=
  ⟨fun h ↦ ⟨h.iSup_nat_mem⟩, fun h ↦ ⟨h.iInf_nat_mem⟩⟩

@[simp] lemma countableInfClosed_preimage_ofDual {s : Set α} :
    CountableInfClosed (ofDual ⁻¹' s) ↔ CountableSupClosed s :=
  ⟨fun h ↦ ⟨h.iInf_nat_mem⟩, fun h ↦ ⟨h.iSup_nat_mem⟩⟩

alias ⟨_, CountableInfClosed.dual⟩ := countableSupClosed_preimage_ofDual
alias ⟨_, CountableSupClosed.dual⟩ := countableInfClosed_preimage_ofDual

/-! ## Closure -/

/-- Every set generates a set closed under countable supremum. -/
@[simps! isClosed]
def countableSupClosure : ClosureOperator (Set α) := .ofPred
  (fun s ↦ {a | ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a})
  CountableSupClosed
  (fun s a ha ↦ ⟨fun _ ↦ a, by simpa, by rw [ciSup_const]⟩)
  (by
    refine fun x ↦ ⟨fun A hA ↦ ?_⟩
    choose B hB hB_eq using hA
    refine ⟨fun n ↦ B (Nat.unpair n).1 (Nat.unpair n).2, fun _ ↦ hB _ _, ?_⟩
    simp [iSup_unpair, ← hB_eq])
  (by
    rintro s₁ s₂ hs h₂ _ ⟨t, ht, rfl⟩
    exact h₂.iSup_mem fun n ↦ hs (ht n))

lemma mem_countableSupClosure_iff :
    a ∈ countableSupClosure s ↔ ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a := Iff.rfl

@[simp] lemma subset_countableSupClosure {s : Set α} : s ⊆ countableSupClosure s :=
  countableSupClosure.le_closure _

@[simp] lemma countableSupClosed_countableSupClosure : CountableSupClosed (countableSupClosure s) :=
  countableSupClosure.isClosed_closure _

@[simp] lemma supClosed_countableSupClosure : SupClosed (countableSupClosure s) :=
  countableSupClosed_countableSupClosure.supClosed

lemma countableSupClosure_mono : Monotone (countableSupClosure : Set α → Set α) :=
  countableSupClosure.monotone

@[simp] lemma countableSupClosure_eq_self : countableSupClosure s = s ↔ CountableSupClosed s :=
  countableSupClosure.isClosed_iff.symm

alias ⟨_, CountableSupClosed.countableSupClosure_eq⟩ := countableSupClosure_eq_self

lemma countableSupClosure_idem (s : Set α) : countableSupClosure (countableSupClosure s) =
    countableSupClosure s :=
  countableSupClosure.idempotent _

@[simp] lemma countableSupClosure_singleton_bot : countableSupClosure {(⊥ : α)} = {⊥} := by simp
@[simp] lemma countableSupClosure_univ : countableSupClosure (Set.univ : Set α) = Set.univ := by
  simp

@[simp] lemma upperBounds_countableSupClosure (s : Set α) :
    upperBounds (countableSupClosure s) = upperBounds s :=
  (upperBounds_mono_set subset_countableSupClosure).antisymm <| by
    rintro a ha _ ⟨t, ht, rfl⟩
    exact iSup_le fun n ↦ ha (ht n)

@[simp] lemma isLUB_countableSupClosure : IsLUB (countableSupClosure s) a ↔ IsLUB s a := by
  simp [IsLUB]

lemma sup_mem_countableSupClosure (ha : a ∈ s) (hb : b ∈ s) : a ⊔ b ∈ countableSupClosure s :=
  supClosed_countableSupClosure (subset_countableSupClosure ha) (subset_countableSupClosure hb)

lemma iSup_mem_countableSupClosure [Countable ι] [Nonempty ι] {A : ι → α} (hA : ∀ n, A n ∈ s) :
    (⨆ n, A n) ∈ countableSupClosure s :=
  countableSupClosed_countableSupClosure.iSup_mem (fun n ↦ subset_countableSupClosure (hA n))

lemma finsetSup'_mem_countableSupClosure {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.sup' ht f ∈ countableSupClosure s :=
  supClosed_countableSupClosure.finsetSup'_mem _ fun _i hi ↦ subset_countableSupClosure <| hf _ hi

lemma countableSupClosure_min : s ⊆ t → CountableSupClosed t → countableSupClosure s ⊆ t :=
  countableSupClosure.closure_min

@[simp] lemma countableSupClosure_prod (s : Set α) (t : Set β) :
    countableSupClosure (s ×ˢ t) = countableSupClosure s ×ˢ countableSupClosure t :=
  le_antisymm (countableSupClosure_min
    (Set.prod_mono subset_countableSupClosure subset_countableSupClosure) <|
    countableSupClosed_countableSupClosure.prod countableSupClosed_countableSupClosure) <| by
      rintro ⟨_, _⟩ ⟨⟨u, hu, rfl⟩, v, hv, rfl⟩
      exact ⟨fun n ↦ (u n, v n), fun n ↦ ⟨hu n, hv n⟩, by rw [Prod.iSup_mk]⟩

/-- Every set generates a set closed under countable infimum. -/
@[simps! isClosed]
def countableInfClosure : ClosureOperator (Set α) := ClosureOperator.ofPred
  (fun s ↦ {a | ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨅ n, t n = a})
  CountableInfClosed
  (fun s a ha ↦ ⟨fun _ ↦ a, by simpa, by rw [ciInf_const]⟩)
  (by
    refine fun x ↦ ⟨fun A hA ↦ ?_⟩
    choose B hB hB_eq using hA
    refine ⟨fun n ↦ B (Nat.unpair n).1 (Nat.unpair n).2, fun _ ↦ hB _ _, ?_⟩
    simp [iInf_unpair, ← hB_eq])
  (by
    rintro s₁ s₂ hs h₂ _ ⟨t, ht, rfl⟩
    exact h₂.iInf_mem fun n ↦ hs (ht n))

lemma mem_countableInfClosure_iff :
    a ∈ countableInfClosure s ↔ ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨅ n, t n = a := Iff.rfl

@[simp] lemma subset_countableInfClosure {s : Set α} : s ⊆ countableInfClosure s :=
  countableInfClosure.le_closure _

@[simp] lemma countableInfClosed_countableInfClosure : CountableInfClosed (countableInfClosure s) :=
  countableInfClosure.isClosed_closure _

@[simp] lemma infClosed_countableInfClosure : InfClosed (countableInfClosure s) :=
  countableInfClosed_countableInfClosure.infClosed

lemma countableInfClosure_mono : Monotone (countableInfClosure : Set α → Set α) :=
  countableInfClosure.monotone

@[simp] lemma countableInfClosure_eq_self : countableInfClosure s = s ↔ CountableInfClosed s :=
  countableInfClosure.isClosed_iff.symm

alias ⟨_, CountableInfClosed.countableInfClosure_eq⟩ := countableInfClosure_eq_self

lemma countableInfClosure_idem (s : Set α) :
    countableInfClosure (countableInfClosure s) = countableInfClosure s :=
  countableInfClosure.idempotent _

@[simp] lemma countableInfClosure_singleton_top : countableInfClosure {(⊤ : α)} = {⊤} := by simp
@[simp] lemma countableInfClosure_univ : countableInfClosure (Set.univ : Set α) = Set.univ := by
  simp

@[simp] lemma lowerBounds_countableInfClosure (s : Set α) :
    lowerBounds (countableInfClosure s) = lowerBounds s :=
  (lowerBounds_mono_set subset_countableInfClosure).antisymm <| by
    rintro a ha _ ⟨t, ht, rfl⟩
    exact le_iInf fun n ↦ ha (ht n)

@[simp] lemma isGLB_countableInfClosure : IsGLB (countableInfClosure s) a ↔ IsGLB s a := by
  simp [IsGLB]

lemma inf_mem_countableInfClosure (ha : a ∈ s) (hb : b ∈ s) : a ⊓ b ∈ countableInfClosure s :=
  infClosed_countableInfClosure (subset_countableInfClosure ha) (subset_countableInfClosure hb)

lemma iInf_mem_countableInfClosure [Countable ι] [Nonempty ι] {A : ι → α} (hA : ∀ n, A n ∈ s) :
    (⨅ n, A n) ∈ countableInfClosure s :=
  countableInfClosed_countableInfClosure.iInf_mem (fun n ↦ subset_countableInfClosure (hA n))

lemma finsetInf'_mem_countableInfClosure {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.inf' ht f ∈ countableInfClosure s :=
  infClosed_countableInfClosure.finsetInf'_mem _ fun _i hi ↦ subset_countableInfClosure <| hf _ hi

lemma countableInfClosure_min : s ⊆ t → CountableInfClosed t → countableInfClosure s ⊆ t :=
  countableInfClosure.closure_min

@[simp] lemma countableInfClosure_prod (s : Set α) (t : Set β) :
    countableInfClosure (s ×ˢ t) = countableInfClosure s ×ˢ countableInfClosure t :=
  le_antisymm (countableInfClosure_min
    (Set.prod_mono subset_countableInfClosure subset_countableInfClosure) <|
    countableInfClosed_countableInfClosure.prod countableInfClosed_countableInfClosure) <| by
      rintro ⟨_, _⟩ ⟨⟨u, hu, rfl⟩, v, hv, rfl⟩
      exact ⟨fun n ↦ (u n, v n), fun n ↦ ⟨hu n, hv n⟩, by rw [Prod.iInf_mk]⟩

end CompleteLattice

section Frame

/-- If a set is closed under binary suprema, then its countable infimum closure is also closed under
binary suprema. -/
protected lemma SupClosed.countableInfClosure [Order.Coframe α] (hs : SupClosed s) :
    SupClosed (countableInfClosure s) := by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [iInf_sup_iInf]
  refine ⟨fun n ↦ t (Nat.unpair n).1 ⊔ u (Nat.unpair n).2, fun n ↦ ?_, ?_⟩
  · simp only
    exact hs (ht (Nat.unpair n).1) (hu (Nat.unpair n).2)
  · rw [iInf_unpair (f := (fun n m ↦ t n ⊔ u m)), iInf_prod']

/-- If a set is closed under binary infima, then its countable supremum closure is also closed under
binary infima. -/
protected lemma InfClosed.countableSupClosure [Order.Frame α] (hs : InfClosed s) :
    InfClosed (countableSupClosure s) := by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [iSup_inf_iSup]
  refine ⟨fun n ↦ t (Nat.unpair n).1 ⊓ u (Nat.unpair n).2, fun n ↦ ?_, ?_⟩
  · simp only
    exact hs (ht (Nat.unpair n).1) (hu (Nat.unpair n).2)
  · rw [iSup_unpair (f := (fun n m ↦ t n ⊓ u m)), iSup_prod']

end Frame
