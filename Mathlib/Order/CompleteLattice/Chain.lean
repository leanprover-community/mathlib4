/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Lattice
import Mathlib.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!
# Hausdorff's maximality principle

This file proves Hausdorff's maximality principle.

## Main declarations

* `maxChain_spec`: Hausdorff's Maximality Principle.

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

@[expose] public section

open Set

variable {α : Type*} {r : α → α → Prop} {c c₁ c₂ s t : Set α} {a b x y : α}

/-- Predicate for whether a set is reachable from `∅` using `SuccChain` and `⋃₀`. -/
inductive ChainClosure (r : α → α → Prop) : Set α → Prop
  | succ : ∀ {s}, ChainClosure r s → ChainClosure r (SuccChain r s)
  | union : ∀ {s}, (∀ a ∈ s, ChainClosure r a) → ChainClosure r (⋃₀ s)

/-- An explicit maximal chain. `maxChain` is taken to be the union of all sets in `ChainClosure`. -/
def maxChain (r : α → α → Prop) : Set α := ⋃₀ setOf (ChainClosure r)

lemma chainClosure_empty : ChainClosure r ∅ := by
  have : ChainClosure r (⋃₀ ∅) := ChainClosure.union fun a h => (notMem_empty _ h).elim
  simpa using this

lemma chainClosure_maxChain : ChainClosure r (maxChain r) :=
  ChainClosure.union fun _ => id

private lemma chainClosure_succ_total_aux (hc₁ : ChainClosure r c₁)
    (h : ∀ ⦃c₃⦄, ChainClosure r c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ SuccChain r c₃ ⊆ c₂) :
    SuccChain r c₂ ⊆ c₁ ∨ c₁ ⊆ c₂ := by
  induction hc₁ with
  | @succ c₃ hc₃ ih =>
    obtain ih | ih := ih
    · exact Or.inl (ih.trans subset_succChain)
    · exact (h hc₃ ih).imp_left fun (h : c₂ = c₃) => h ▸ Subset.rfl
  | union _ ih =>
    refine or_iff_not_imp_left.2 fun hn => sUnion_subset fun a ha => ?_
    exact (ih a ha).resolve_left fun h => hn <| h.trans <| subset_sUnion_of_mem ha

private lemma chainClosure_succ_total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (h : c₁ ⊆ c₂) : c₂ = c₁ ∨ SuccChain r c₁ ⊆ c₂ := by
  induction hc₂ generalizing c₁ hc₁ with
  | succ _ ih =>
    refine ((chainClosure_succ_total_aux hc₁) fun c₁ => ih).imp h.antisymm' fun h₁ => ?_
    obtain rfl | h₂ := ih hc₁ h₁
    · exact Subset.rfl
    · exact h₂.trans subset_succChain
  | union _ ih =>
    apply Or.imp_left h.antisymm'
    apply by_contradiction
    simp only [sUnion_subset_iff, not_or, not_forall, exists_prop, and_imp, forall_exists_index]
    intro c₃ hc₃ h₁ h₂
    obtain h | h := chainClosure_succ_total_aux hc₁ fun c₄ => ih _ hc₃
    · exact h₁ (subset_succChain.trans h)
    obtain h' | h' := ih c₃ hc₃ hc₁ h
    · exact h₁ h'.subset
    · exact h₂ (h'.trans <| subset_sUnion_of_mem hc₃)

lemma ChainClosure.total (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂) :
    c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
  ((chainClosure_succ_total_aux hc₂) fun _ hc₃ => chainClosure_succ_total hc₃ hc₁).imp_left
    subset_succChain.trans

lemma ChainClosure.succ_fixpoint (hc₁ : ChainClosure r c₁) (hc₂ : ChainClosure r c₂)
    (hc : SuccChain r c₂ = c₂) : c₁ ⊆ c₂ := by
  induction hc₁ with
  | succ hc₁ h => exact (chainClosure_succ_total hc₁ hc₂ h).elim (fun h => h ▸ hc.subset) id
  | union _ ih => exact sUnion_subset ih

lemma ChainClosure.succ_fixpoint_iff (hc : ChainClosure r c) :
    SuccChain r c = c ↔ c = maxChain r :=
  ⟨fun h => (subset_sUnion_of_mem hc).antisymm <| chainClosure_maxChain.succ_fixpoint hc h,
    fun h => subset_succChain.antisymm' <| (subset_sUnion_of_mem hc.succ).trans h.symm.subset⟩

lemma ChainClosure.isChain (hc : ChainClosure r c) : IsChain r c := by
  induction hc with
  | succ _ h => exact h.succ
  | union hs h =>
    exact fun c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq =>
      ((hs _ ht₁).total <| hs _ ht₂).elim (fun ht => h t₂ ht₂ (ht hc₁) hc₂ hneq) fun ht =>
        h t₁ ht₁ hc₁ (ht hc₂) hneq

/-- **Hausdorff's maximality principle**

There exists a maximal totally ordered set of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
theorem maxChain_spec : IsMaxChain r (maxChain r) :=
  by_contradiction fun h =>
    let ⟨_, H⟩ := chainClosure_maxChain.isChain.superChain_succChain h
    H.ne (chainClosure_maxChain.succ_fixpoint_iff.mpr rfl).symm
