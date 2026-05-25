/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Set.Countable
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
structure CountableSupClosed (s : Set α) : Prop where
  exists_isLUB : ∀ t ⊆ s, t.Nonempty → t.Countable → ∃ x ∈ s, IsLUB t x

/-- A set `s` is closed under countable infimum if `⨅ n, A n ∈ s` for all `A : ι → α`
with `ι` nonempty countable and `A n ∈ s` for all `n`.

The definition uses `ι = ℕ`.
See `CountableInfClosed.iInf_mem` for an infimum over any nonempty countable type. -/
@[to_dual existing]
structure CountableInfClosed (s : Set α) : Prop where
  exists_isGLB : ∀ t ⊆ s, t.Nonempty → t.Countable → ∃ x ∈ s, IsGLB t x

attribute [to_dual existing] CountableSupClosed

@[to_dual]
lemma CountableSupClosed.iSup_mem [hι : Countable ι] [Nonempty ι]
    (hs : CountableSupClosed s) {A : ι → α} (hA : ∀ n, A n ∈ s) :
    ⨆ n, A n ∈ s := by
  let i₀ := Nonempty.some (α := ι) inferInstance
  obtain ⟨x, hxs, hx_lub⟩ := hs.exists_isLUB (range A) (by simp [range]; grind) ⟨A i₀, by simp⟩
    (countable_range A)
  rwa [hx_lub.iSup_eq]

@[to_dual]
lemma CountableSupClosed.of_iSup_mem (hs : ∀ A : ℕ → α, (∀ n, A n ∈ s) → ⨆ n, A n ∈ s) :
    CountableSupClosed s where
  exists_isLUB A hAs hA_ne hAc := by
    obtain ⟨f, rfl⟩ := hAc.exists_eq_range hA_ne
    specialize hs f (fun _ ↦ by grind)
    exact ⟨⨆ n, f n, hs, isLUB_iSup⟩

@[to_dual]
lemma CountableSupClosed.sSup_mem (hs : CountableSupClosed s)
    (A : Set α) [Countable A] [Nonempty A] (hA : ∀ a ∈ A, a ∈ s) :
    sSup A ∈ s := by
  rw [sSup_eq_iSup']
  exact hs.iSup_mem fun a ↦ hA a a.2

@[to_dual]
lemma CountableSupClosed.supClosed (hs : CountableSupClosed s) : SupClosed s := by
  intro a ha b hb
  simpa using hs.sSup_mem (A := {a, b}) (by grind)

@[to_dual (attr := simp)] lemma countableSupClosed_singleton_bot :
    CountableSupClosed ({⊥} : Set α) where
  exists_isLUB _ _ _ _ := by simp [IsLUB, upperBounds]; grind

@[to_dual (attr := simp)] lemma CountableSupClosed.univ : CountableSupClosed (univ : Set α) where
  exists_isLUB A hA _ _ := ⟨sSup A, by simp, isLUB_sSup A⟩

@[to_dual]
lemma CountableSupClosed.inter (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s ∩ t) where
  exists_isLUB A hAst hA_ne hAc := by
    obtain ⟨x, hxs, hx_lub⟩ := hs.exists_isLUB A (by grind) hA_ne hAc
    obtain ⟨y, hyt, hy_glb⟩ := ht.exists_isLUB A (by grind) hA_ne hAc
    have hxy : x = y := IsLUB.unique hx_lub hy_glb
    subst hxy
    exact ⟨x, ⟨hxs, hyt⟩, hx_lub⟩

@[to_dual]
lemma CountableSupClosed.sInter (hS : ∀ s ∈ S, CountableSupClosed s) :
    CountableSupClosed (⋂₀ S) where
  exists_isLUB A hAS hA_ne hAc := by
    rcases Set.eq_empty_or_nonempty S with rfl | hS_nonempty
    · simp only [sInter_empty, mem_univ, true_and]
      exact ⟨sSup A, isLUB_sSup A⟩
    obtain ⟨s₀, hs₀⟩ := hS_nonempty
    simp only [subset_sInter_iff] at hAS
    have h t' (ht' : t' ∈ S) : ∃ x ∈ t', IsLUB A x :=
      (hS t' ht').exists_isLUB A (hAS t' ht') hA_ne hAc
    choose x hx using h
    have h_eq t' (ht' : t' ∈ S) : x t' ht' = x s₀ hs₀ :=
      IsLUB.unique (hx t' ht').2 (hx s₀ hs₀).2
    refine ⟨x s₀ hs₀, ?_, (hx s₀ hs₀).2⟩
    simp only [mem_sInter]
    intro t' ht'
    rw [← h_eq t' ht']
    exact (hx t' ht').1

@[to_dual]
lemma CountableSupClosed.iInter {f : ι → Set α} (hf : ∀ i, CountableSupClosed (f i)) :
    CountableSupClosed (⋂ i, f i) :=
  .sInter <| forall_mem_range.2 hf

lemma CountableSupClosed.directedOn (hs : CountableSupClosed s) : DirectedOn (· ≤ ·) s :=
  hs.supClosed.directedOn

@[to_dual]
lemma CountableSupClosed.prod {t : Set β} (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s ×ˢ t) where
  exists_isLUB A hAst hA_ne hAc := by
    obtain ⟨x, hxs, hx_lub⟩ := hs.exists_isLUB (Prod.fst '' A) (by grind) (by simpa)
      (hAc.image Prod.fst)
    obtain ⟨y, hyt, hy_lub⟩ := ht.exists_isLUB (Prod.snd '' A) (by grind) (by simpa)
      (hAc.image Prod.snd)
    refine ⟨(x, y), ⟨hxs, hyt⟩, ?_⟩
    simp [IsLUB, lowerBounds, upperBounds, IsLeast] at hx_lub hy_lub ⊢
    grind

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
  ⟨fun h ↦ ⟨h.exists_isLUB⟩, fun h ↦ ⟨h.exists_isGLB⟩⟩

@[simp] lemma countableInfClosed_preimage_toDual {s : Set αᵒᵈ} :
    CountableInfClosed (toDual ⁻¹' s) ↔ CountableSupClosed s :=
  ⟨fun h ↦ ⟨h.exists_isGLB⟩, fun h ↦ ⟨h.exists_isLUB⟩⟩

@[simp] lemma countableSupClosed_preimage_ofDual {s : Set α} :
    CountableSupClosed (ofDual ⁻¹' s) ↔ CountableInfClosed s :=
  ⟨fun h ↦ ⟨h.exists_isLUB⟩, fun h ↦ ⟨h.exists_isGLB⟩⟩

@[simp] lemma countableInfClosed_preimage_ofDual {s : Set α} :
    CountableInfClosed (ofDual ⁻¹' s) ↔ CountableSupClosed s :=
  ⟨fun h ↦ ⟨h.exists_isGLB⟩, fun h ↦ ⟨h.exists_isLUB⟩⟩

alias ⟨_, CountableInfClosed.dual⟩ := countableSupClosed_preimage_ofDual
alias ⟨_, CountableSupClosed.dual⟩ := countableInfClosed_preimage_ofDual

/-! ## Closure -/

/-- Every set generates a set closed under countable supremum. -/
def countableSupClosure (s : Set α) : Set α := ⋂₀ {t | s ⊆ t ∧ CountableSupClosed t}

/-- Every set generates a set closed under countable infimum. -/
def countableInfClosure (s : Set α) : Set α := ⋂₀ {t | s ⊆ t ∧ CountableInfClosed t}

attribute [to_dual existing] countableSupClosure

lemma mem_countableSupClosure_iff :
    a ∈ countableSupClosure s ↔ ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a := by
  simp only [countableSupClosure, Set.mem_sInter, Set.mem_setOf_eq, and_imp]
  refine ⟨fun h ↦ ?_, fun h t hts ht ↦ ?_⟩
  · have h_csc : CountableSupClosed {a | ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a} := by
      refine .of_iSup_mem fun A hA ↦ ?_
      choose B hB hB_eq using hA
      refine ⟨fun n ↦ B (Nat.unpair n).1 (Nat.unpair n).2, fun _ ↦ hB _ _, ?_⟩
      simp [iSup_unpair, ← hB_eq]
    refine h {a | ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a} ?_ h_csc
    exact fun a ha ↦ ⟨fun _ ↦ a, by simp [ha]⟩
  · obtain ⟨u, hus, rfl⟩ := h
    exact ht.iSup_mem fun n ↦ hts (hus n)

lemma mem_countableInfClosure_iff :
    a ∈ countableInfClosure s ↔ ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨅ n, t n = a := by
  simp only [countableInfClosure, Set.mem_sInter, Set.mem_setOf_eq, and_imp]
  refine ⟨fun h ↦ ?_, fun h t hts ht ↦ ?_⟩
  · have h_cic : CountableInfClosed {a | ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨅ n, t n = a} := by
      refine .of_iInf_mem fun A hA ↦ ?_
      choose B hB hB_eq using hA
      refine ⟨fun n ↦ B (Nat.unpair n).1 (Nat.unpair n).2, fun _ ↦ hB _ _, ?_⟩
      simp [iInf_unpair, ← hB_eq]
    refine h {a | ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨅ n, t n = a} ?_ h_cic
    exact fun a ha ↦ ⟨fun _ ↦ a, by simp [ha]⟩
  · obtain ⟨u, hus, rfl⟩ := h
    exact ht.iInf_mem fun n ↦ hts (hus n)

attribute [to_dual existing] mem_countableSupClosure_iff

@[to_dual (attr := simp)] lemma subset_countableSupClosure {s : Set α} :
    s ⊆ countableSupClosure s := by simp [countableSupClosure]; grind

@[to_dual (attr := simp)] lemma countableSupClosed_countableSupClosure :
    CountableSupClosed (countableSupClosure s) := CountableSupClosed.sInter fun _ ht ↦ ht.2

@[to_dual (attr := simp)] lemma supClosed_countableSupClosure : SupClosed (countableSupClosure s) :=
  countableSupClosed_countableSupClosure.supClosed

@[to_dual]
lemma countableSupClosure_mono : Monotone (countableSupClosure : Set α → Set α) := by
  intro s t hst
  simp [countableSupClosure] at hst ⊢
  grind

@[to_dual countableInfClosure_min]
lemma countableSupClosure_min (hst : s ⊆ t) (ht : CountableSupClosed t) :
    countableSupClosure s ⊆ t := Set.sInter_subset_of_mem ⟨hst, ht⟩

@[to_dual (attr := simp)]
lemma countableSupClosure_eq_self :
    countableSupClosure s = s ↔ CountableSupClosed s := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    exact countableSupClosed_countableSupClosure
  · refine subset_antisymm ?_ subset_countableSupClosure
    exact countableSupClosure_min subset_rfl h

@[to_dual]
alias ⟨_, CountableSupClosed.countableSupClosure_eq⟩ := countableSupClosure_eq_self

@[to_dual]
lemma countableSupClosure_idem (s : Set α) : countableSupClosure (countableSupClosure s) =
    countableSupClosure s := by
  rw [countableSupClosure_eq_self]
  exact countableSupClosed_countableSupClosure

@[to_dual (attr := simp)] lemma countableSupClosure_singleton_bot :
    countableSupClosure {(⊥ : α)} = {⊥} := by simp

@[to_dual (attr := simp)] lemma countableSupClosure_univ :
    countableSupClosure (Set.univ : Set α) = Set.univ := by simp

@[to_dual (attr := simp)] lemma upperBounds_countableSupClosure (s : Set α) :
    upperBounds (countableSupClosure s) = upperBounds s :=
  (upperBounds_mono_set subset_countableSupClosure).antisymm <| by
    intro a ha b hb
    rw [mem_countableSupClosure_iff] at hb
    obtain ⟨t, ht, rfl⟩ := hb
    exact iSup_le fun n ↦ ha (ht n)

@[to_dual (attr := simp)] lemma isLUB_countableSupClosure :
    IsLUB (countableSupClosure s) a ↔ IsLUB s a := by simp [IsLUB]

@[to_dual]
lemma sup_mem_countableSupClosure (ha : a ∈ s) (hb : b ∈ s) : a ⊔ b ∈ countableSupClosure s :=
  supClosed_countableSupClosure (subset_countableSupClosure ha) (subset_countableSupClosure hb)

@[to_dual]
lemma iSup_mem_countableSupClosure [Countable ι] [Nonempty ι] {A : ι → α} (hA : ∀ n, A n ∈ s) :
    (⨆ n, A n) ∈ countableSupClosure s :=
  countableSupClosed_countableSupClosure.iSup_mem (fun n ↦ subset_countableSupClosure (hA n))

@[to_dual]
lemma finsetSup'_mem_countableSupClosure {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.sup' ht f ∈ countableSupClosure s :=
  supClosed_countableSupClosure.finsetSup'_mem _ fun _i hi ↦ subset_countableSupClosure <| hf _ hi

@[to_dual (attr := simp)] lemma countableSupClosure_prod (s : Set α) (t : Set β) :
    countableSupClosure (s ×ˢ t) = countableSupClosure s ×ˢ countableSupClosure t :=
  le_antisymm (countableSupClosure_min
    (Set.prod_mono subset_countableSupClosure subset_countableSupClosure) <|
    countableSupClosed_countableSupClosure.prod countableSupClosed_countableSupClosure) <| by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      simp only [mem_countableSupClosure_iff] at ha hb ⊢
      obtain ⟨u, hu, rfl⟩ := ha
      obtain ⟨v, hv, rfl⟩ := hb
      exact ⟨fun n ↦ (u n, v n), fun n ↦ ⟨hu n, hv n⟩, by rw [Prod.iSup_mk]⟩

end CompleteLattice

section Frame

/-- If a set is closed under binary suprema, then its countable infimum closure is also closed under
binary suprema. -/
protected lemma SupClosed.countableInfClosure [Order.Coframe α] (hs : SupClosed s) :
    SupClosed (countableInfClosure s) := by
  rintro a ha b hb
  rw [mem_countableInfClosure_iff] at ha hb ⊢
  obtain ⟨t, ht, hts, rfl⟩ := ha
  obtain ⟨u, hu, hus, rfl⟩ := hb
  rw [iInf_sup_iInf]
  refine ⟨fun n ↦ t (Nat.unpair n).1 ⊔ u (Nat.unpair n).2, fun n ↦ ?_, ?_⟩
  · simp only
    exact hs (ht (Nat.unpair n).1) (hu (Nat.unpair n).2)
  · rw [iInf_unpair (f := (fun n m ↦ t n ⊔ u m)), iInf_prod']

/-- If a set is closed under binary infima, then its countable supremum closure is also closed under
binary infima. -/
@[to_dual existing]
protected lemma InfClosed.countableSupClosure [Order.Frame α] (hs : InfClosed s) :
    InfClosed (countableSupClosure s) := by
  rintro a ha b hb
  rw [mem_countableSupClosure_iff] at ha hb ⊢
  obtain ⟨t, ht, hts, rfl⟩ := ha
  obtain ⟨u, hu, hus, rfl⟩ := hb
  rw [iSup_inf_iSup]
  refine ⟨fun n ↦ t (Nat.unpair n).1 ⊓ u (Nat.unpair n).2, fun n ↦ ?_, ?_⟩
  · simp only
    exact hs (ht (Nat.unpair n).1) (hu (Nat.unpair n).2)
  · rw [iSup_unpair (f := (fun n m ↦ t n ⊓ u m)), iSup_prod']

attribute [to_dual existing] SupClosed.countableInfClosure

end Frame
