/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.SupClosed

import Mathlib.Order.Bounds.Lattice

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

public section

variable {ι : Sort*} {α β : Type*} {S : Set (Set α)} {s t : Set α} {a b : α}

section Set
open Set

/-- A set `s` is closed under countable supremum if for every nonempty countable subset of `s`, any
least upper bound of that subset is in `s`. -/
structure CountableSupClosed [LE α] (s : Set α) : Prop where
  isLUB_mem : ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ x, IsLUB t x → x ∈ s

/-- A set `s` is closed under countable infimum if for every nonempty countable subset of `s`, any
greatest lower bound of that subset is in `s`. -/
@[to_dual existing]
structure CountableInfClosed [LE α] (s : Set α) : Prop where
  isGLB_mem : ∀ t ⊆ s, t.Nonempty → t.Countable → ∀ x, IsGLB t x → x ∈ s

@[to_dual]
lemma CountableSupClosed.iSup_mem [CompleteLattice α] [Countable ι] [Nonempty ι]
    (hs : CountableSupClosed s) {A : ι → α} (hA : ∀ n, A n ∈ s) :
    ⨆ n, A n ∈ s := by
  let i₀ := Nonempty.some (α := ι) inferInstance
  exact hs.isLUB_mem (range A) (by simp [range]; grind) ⟨A i₀, by simp⟩ (countable_range A) _
    isLUB_iSup

@[to_dual]
lemma CountableSupClosed.of_iSup_mem [CompleteLattice α]
    (hs : ∀ A : ℕ → α, (∀ n, A n ∈ s) → ⨆ n, A n ∈ s) :
    CountableSupClosed s where
  isLUB_mem A hAs hA_ne hAc x hx := by
    obtain ⟨f, rfl⟩ := hAc.exists_eq_range hA_ne
    rw [(IsLUB.unique hx isLUB_iSup : x = ⨆ n, f n)]
    exact hs f (by grind)

@[to_dual]
lemma CountableSupClosed.sSup_mem [CompleteLattice α] (hs : CountableSupClosed s)
    {A : Set α} (hA_c : A.Countable) (hA_ne : A.Nonempty) (hA : ∀ a ∈ A, a ∈ s) :
    sSup A ∈ s := by
  rw [sSup_eq_iSup']
  have : Countable A := hA_c
  have : Nonempty A := nonempty_coe_sort.mpr hA_ne
  exact hs.iSup_mem fun a ↦ hA a a.2

@[to_dual]
protected lemma CountableSupClosed.supClosed [SemilatticeSup α] (hs : CountableSupClosed s) :
    SupClosed s := fun a ha b hb ↦ hs.isLUB_mem {a, b} (by grind) (by simp) (by simp) _ isLUB_pair

@[to_dual (attr := simp)]
protected lemma CountableSupClosed.singleton [PartialOrder α] {x : α} :
    CountableSupClosed ({x} : Set α) where
  isLUB_mem s hs_subset hs_ne _ y hy := by
    have h_eq : s = {x} := by
      ext y
      simp_all only [subset_singleton_iff, mem_singleton_iff]
      refine ⟨hs_subset y, ?_⟩
      rintro rfl
      obtain ⟨z, hzs⟩ := hs_ne
      rwa [hs_subset z hzs] at hzs
    simp_all only [subset_refl, singleton_nonempty, countable_singleton, mem_singleton_iff]
    exact IsLUB.unique hy isLUB_singleton

@[to_dual (attr := simp)]
protected lemma CountableSupClosed.univ [LE α] :
    CountableSupClosed (univ : Set α) where
  isLUB_mem _ _ _ _ _ _ := by simp

@[to_dual (attr := simp)]
protected lemma CountableSupClosed.empty [LE α] :
    CountableSupClosed (∅ : Set α) where
  isLUB_mem _ _ _ _ _ _ := by simp_all

@[to_dual]
protected lemma CountableSupClosed.inter [LE α]
    (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s ∩ t) where
  isLUB_mem A hAst hA_ne hAc x hx :=
    ⟨hs.isLUB_mem A (hAst.trans Set.inter_subset_left) hA_ne hAc x hx,
      ht.isLUB_mem A (hAst.trans Set.inter_subset_right) hA_ne hAc x hx⟩

@[to_dual]
protected lemma CountableSupClosed.sInter [LE α] (hS : ∀ s ∈ S, CountableSupClosed s) :
    CountableSupClosed (⋂₀ S) where
  isLUB_mem A hAS hA_ne hAc x hx := by
    simp only [subset_sInter_iff, mem_sInter] at hAS ⊢
    exact fun s hs ↦ (hS s hs).isLUB_mem A (hAS s hs) hA_ne hAc x hx

@[to_dual]
protected lemma CountableSupClosed.iInter [LE α]
    {f : ι → Set α} (hf : ∀ i, CountableSupClosed (f i)) :
    CountableSupClosed (⋂ i, f i) :=
  .sInter <| forall_mem_range.2 hf

@[to_dual]
protected lemma CountableSupClosed.directedOn [SemilatticeSup α] (hs : CountableSupClosed s) :
    DirectedOn (· ≤ ·) s := hs.supClosed.directedOn

@[to_dual]
protected lemma CountableSupClosed.prod [Preorder α] [Preorder β]
    {t : Set β} (hs : CountableSupClosed s) (ht : CountableSupClosed t) :
    CountableSupClosed (s ×ˢ t) where
  isLUB_mem A hAst hA_ne hAc := by
    intro (x, y) hxy
    rw [isLUB_prod] at hxy
    exact ⟨hs.isLUB_mem (Prod.fst '' A) (by grind) (by simpa) (hAc.image Prod.fst) _ hxy.1,
      ht.isLUB_mem (Prod.snd '' A) (by grind) (by simpa) (hAc.image Prod.snd) _ hxy.2⟩

end Set

section Finset
variable {ι : Type*} {f : ι → α} {t : Finset ι}

@[to_dual]
lemma CountableSupClosed.finsetSup'_mem [SemilatticeSup α]
    (hs : CountableSupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup' ht f ∈ s :=
  hs.supClosed.finsetSup'_mem ht

@[to_dual]
lemma CountableSupClosed.finsetSup_mem [SemilatticeSup α] [OrderBot α]
    (hs : CountableSupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup f ∈ s :=
  Finset.sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

end Finset

open OrderDual

@[to_dual (attr := simp)] lemma countableSupClosed_preimage_toDual [LE α] {s : Set αᵒᵈ} :
    CountableSupClosed (toDual ⁻¹' s) ↔ CountableInfClosed s :=
  ⟨fun h ↦ ⟨h.isLUB_mem⟩, fun h ↦ ⟨h.isGLB_mem⟩⟩

@[to_dual (attr := simp)] lemma countableSupClosed_preimage_ofDual [LE α] {s : Set α} :
    CountableSupClosed (ofDual ⁻¹' s) ↔ CountableInfClosed s :=
  ⟨fun h ↦ ⟨h.isLUB_mem⟩, fun h ↦ ⟨h.isGLB_mem⟩⟩

@[to_dual] alias ⟨_, CountableSupClosed.dual⟩ := countableInfClosed_preimage_ofDual

/-! ### Closure -/

section Preorder

variable [Preorder α]

/-- Every set generates a set closed under countable supremum. -/
@[to_dual /-- Every set generates a set closed under countable infimum. -/]
def countableSupClosure : ClosureOperator (Set α) := .ofPred
  (fun s a ↦ ∃ (A : Set α) (_ : A ⊆ s) (_ : A.Nonempty) (_ : A.Countable), IsLUB A a)
  CountableSupClosed
  (fun s x hxs ↦ ⟨{x}, by simp; grind, by simp, by simp, by simp⟩)
  (fun s ↦ by
    constructor
    intro A hA hA_ne hAc x hx
    choose B hB hB_ne hBc hB_lub using hA
    refine ⟨⋃ a : A, B a.2, by simp; grind, ?_, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hA_ne
      simp
      grind
    · have : Countable A := Set.countable_coe_iff.mpr hAc
      exact Set.countable_iUnion fun a ↦ hBc a.2
    · have : Nonempty A := Set.nonempty_coe_sort.mpr hA_ne
      rw [← isLUB_iUnion_iff_of_isLUB (u := fun a : A ↦ a.1) (fun a ↦ hB_lub a.2)]
      simpa)
  (fun s t (hst : s ⊆ t) ht a ⟨A, hAs, hA_ne, hA_c, hA_lub⟩ ↦
    ht.isLUB_mem A (hAs.trans hst) hA_ne hA_c _ hA_lub)

@[to_dual (attr := simp)] lemma subset_countableSupClosure :
    s ⊆ countableSupClosure s := countableSupClosure.le_closure _

@[to_dual countableInfClosure_min]
lemma countableSupClosure_min (hst : s ⊆ t) (ht : CountableSupClosed t) :
    countableSupClosure s ⊆ t := countableSupClosure.closure_min hst ht

@[to_dual (attr := simp)] lemma countableSupClosed_countableSupClosure :
    CountableSupClosed (countableSupClosure s) := countableSupClosure.isClosed_closure _

@[to_dual (attr := gcongr)]
lemma countableSupClosure_mono : Monotone (countableSupClosure : Set α → Set α) :=
  countableSupClosure.mono

@[to_dual (attr := simp)] lemma countableSupClosure_eq_self :
    countableSupClosure s = s ↔ CountableSupClosed s := countableSupClosure.isClosed_iff.symm

@[to_dual]
alias ⟨_, CountableSupClosed.countableSupClosure_eq⟩ := countableSupClosure_eq_self

@[to_dual]
lemma countableSupClosure_idem (s : Set α) :
    countableSupClosure (countableSupClosure s) = countableSupClosure s :=
  countableSupClosure.idempotent _

@[to_dual]
lemma countableSupClosure_eq_sInter (s : Set α) :
    countableSupClosure s = ⋂₀ {t | s ⊆ t ∧ CountableSupClosed t} := by
  have : CountableSupClosed (⋂₀ {t | s ⊆ t ∧ CountableSupClosed t}) := by
    constructor
    simp only [Set.subset_sInter_iff, Set.mem_setOf_eq, and_imp, Set.mem_sInter]
    intro t ht ht_ne ht_c x hx t' hst' ht'
    exact ht'.isLUB_mem t (ht t' hst' ht') ht_ne ht_c x hx
  refine le_antisymm (countableSupClosure_min (by grind) (by grind)) (Set.sInter_subset_of_mem ?_)
  exact ⟨subset_countableSupClosure, countableSupClosed_countableSupClosure⟩

@[to_dual]
lemma mem_countableSupClosure_iff :
    a ∈ countableSupClosure s ↔
      ∃ (A : Set α) (_ : A ⊆ s) (_ : A.Nonempty) (_ : A.Countable), IsLUB A a := by rfl

@[to_dual (attr := simp)] lemma countableSupClosure_univ :
    countableSupClosure (Set.univ : Set α) = Set.univ := by simp

@[to_dual (attr := simp)] lemma countableSupClosure_empty :
    countableSupClosure (∅ : Set α) = ∅ := by simp

@[to_dual (attr := simp)] lemma upperBounds_countableSupClosure (s : Set α) :
    upperBounds (countableSupClosure s) = upperBounds s :=
  (upperBounds_mono_set subset_countableSupClosure).antisymm <| by
    intro a ha b hb
    rw [mem_countableSupClosure_iff] at hb
    obtain ⟨t, hts, ht_ne, ht_c, ht_lub⟩ := hb
    have hat : a ∈ upperBounds t := fun x hx ↦ ha (hts hx)
    exact (isLUB_le_iff ht_lub).mpr hat

@[to_dual (attr := simp)] lemma isLUB_countableSupClosure :
    IsLUB (countableSupClosure s) a ↔ IsLUB s a := by simp [IsLUB]

@[to_dual (attr := simp)] lemma countableSupClosure_prod [Preorder β]
    (s : Set α) (t : Set β) :
    countableSupClosure (s ×ˢ t) = countableSupClosure s ×ˢ countableSupClosure t :=
  le_antisymm (countableSupClosure_min
    (Set.prod_mono subset_countableSupClosure subset_countableSupClosure) <|
    countableSupClosed_countableSupClosure.prod countableSupClosed_countableSupClosure) <| by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      simp only [mem_countableSupClosure_iff] at ha hb ⊢
      obtain ⟨u, hu, hu_ne, hu_c, hu_lub⟩ := ha
      obtain ⟨v, hv, hv_ne, hv_c, hv_lub⟩ := hb
      refine ⟨u ×ˢ v, by grind, by simp [hu_ne, hv_ne], hu_c.prod hv_c, ?_⟩
      exact IsLUB.prod hu_ne hv_ne hu_lub hv_lub

end Preorder

@[to_dual]
lemma mem_countableSupClosure_iff_iSup [CompleteLattice α] :
    a ∈ countableSupClosure s ↔ ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a := by
  suffices countableSupClosure s = {a | ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a} by simp [this]
  have h_csc : CountableSupClosed {a | ∃ (t : ℕ → α), (∀ n, t n ∈ s) ∧ ⨆ n, t n = a} := by
    refine .of_iSup_mem fun A hA ↦ ?_
    choose B hB hB_eq using hA
    refine ⟨fun n ↦ B (Nat.unpair n).1 (Nat.unpair n).2, fun _ ↦ hB _ _, ?_⟩
    simp [iSup_unpair, ← hB_eq]
  refine le_antisymm (countableSupClosure_min ?_ h_csc) ?_
  · exact fun a ha ↦ ⟨fun _ ↦ a, by simp [ha]⟩
  · rintro _ ⟨u, hus, rfl⟩
    exact countableSupClosed_countableSupClosure.iSup_mem fun n ↦ subset_countableSupClosure (hus n)

@[to_dual (attr := simp)] lemma supClosed_countableSupClosure [SemilatticeSup α] :
    SupClosed (countableSupClosure s) :=
  countableSupClosed_countableSupClosure.supClosed

@[to_dual (attr := simp)] lemma countableSupClosure_singleton [PartialOrder α] {x : α} :
    countableSupClosure {x} = {x} := by simp

@[to_dual]
lemma sup_mem_countableSupClosure [SemilatticeSup α] (ha : a ∈ s) (hb : b ∈ s) :
    a ⊔ b ∈ countableSupClosure s :=
  supClosed_countableSupClosure (subset_countableSupClosure ha) (subset_countableSupClosure hb)

@[to_dual]
lemma iSup_mem_countableSupClosure [CompleteLattice α] [Countable ι] [Nonempty ι] {A : ι → α}
    (hA : ∀ n, A n ∈ s) :
    ⨆ n, A n ∈ countableSupClosure s :=
  countableSupClosed_countableSupClosure.iSup_mem (fun n ↦ subset_countableSupClosure (hA n))

@[to_dual]
lemma finsetSup'_mem_countableSupClosure {ι : Type*} [SemilatticeSup α]
    {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.sup' ht f ∈ countableSupClosure s :=
  supClosed_countableSupClosure.finsetSup'_mem _ fun _i hi ↦ subset_countableSupClosure <| hf _ hi

/-- If a set is closed under binary suprema, then its countable infimum closure is also closed under
binary suprema. -/
@[to_dual
/-- If a set is closed under binary infima, then its countable supremum closure is also closed under
binary infima. -/]
protected lemma SupClosed.countableInfClosure [Order.Coframe α] (hs : SupClosed s) :
    SupClosed (countableInfClosure s) := by
  rintro a ha b hb
  rw [mem_countableInfClosure_iff_iInf] at ha hb ⊢
  obtain ⟨t, ht, hts, rfl⟩ := ha
  obtain ⟨u, hu, hus, rfl⟩ := hb
  rw [iInf_sup_iInf]
  refine ⟨fun n ↦ t (Nat.unpair n).1 ⊔ u (Nat.unpair n).2, fun n ↦ ?_, ?_⟩
  · simp only
    exact hs (ht (Nat.unpair n).1) (hu (Nat.unpair n).2)
  · rw [iInf_unpair (f := (fun n m ↦ t n ⊔ u m)), iInf_prod']
