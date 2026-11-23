/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.DFinsupp.Order
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Order.Preorder.Finsupp

/-!
# Finitely supported functions into a conditionally complete lattice

This file shows that `ι →₀ M` is a conditionally complete lattice when `M` is. The supremum of a
nonempty set that is bounded above is computed pointwise, and has finite support because it is
sandwiched between an element of the set and an upper bound, both of finite support.
-/

@[expose] public section

namespace Finsupp
variable {ι M : Type*} [Zero M] [ConditionallyCompleteLattice M]

@[to_dual]
noncomputable instance : SupSet (ι →₀ M) where
  sSup S :=
    open scoped Classical in
    if h : BddAbove S ∧ S.Nonempty then
      onFinset (h.1.some.support ∪ h.2.some.support) (fun i ↦ sSup ((· i) '' S)) fun i hi ↦ by
        contrapose hi
        simp only [Finset.mem_union, mem_support_iff, not_or, not_not] at hi
        refine le_antisymm (csSup_le (h.2.image _) ?_) <|
          le_csSup_of_le (bddAbove_image_apply h.1) ⟨_, h.2.some_mem, rfl⟩ hi.2.ge
        rintro _ ⟨f, hf, rfl⟩
        exact (h.1.some_mem hf i).trans_eq hi.1
    else 0

@[to_dual]
lemma sSup_apply {S : Set (ι →₀ M)} (hS : BddAbove S) (hS₀ : S.Nonempty) (i : ι) :
    sSup S i = ⨆ f : S, f.val i := by simp [sSup, sSup_image', *]

@[to_dual]
lemma iSup_apply {κ : Type*} [Nonempty κ] {f : κ → ι →₀ M} (hf : BddAbove (.range f)) (i : ι) :
    (⨆ j, f j) i = ⨆ j, f j i := by
  rw [iSup, sSup_apply hf (Set.range_nonempty _), iSup_range' (· i) f]

@[to_dual]
private lemma isLUB_sSup {S : Set (ι →₀ M)} (hS₀ : S.Nonempty) (hS : BddAbove S) :
    IsLUB S (sSup S) := by
  refine ⟨fun f hf i ↦ ?_, fun g hg i ↦ ?_⟩
  · rw [sSup_apply hS hS₀]
    refine le_ciSup (f := fun f : S ↦ f.val i) ?_ ⟨f, hf⟩
    simpa [Set.range_comp' (· i) (Subtype.val : S → _)] using bddAbove_image_apply hS
  · rw [sSup_apply hS hS₀]
    have := hS₀.to_subtype
    exact ciSup_le (hg ·.property i)

noncomputable instance : ConditionallyCompleteLattice (ι →₀ M) where
  isLUB_csSup _ := private isLUB_sSup
  isGLB_csInf _ := private isGLB_sInf

end Finsupp

namespace DFinsupp
variable {ι : Type*} {M : ι → Type*} [∀ i, Zero (M i)] [∀ i, ConditionallyCompleteLattice (M i)]

@[to_dual]
noncomputable instance : SupSet (Π₀ i, M i) where
  sSup S :=
    open scoped Classical in
    if h : BddAbove S ∧ S.Nonempty then
      mk (h.1.some.support ∪ h.2.some.support) fun i ↦ sSup ((· i.val) '' S)
    else 0

@[to_dual]
lemma sSup_apply {S : Set (Π₀ i, M i)} (hS : BddAbove S) (hS₀ : S.Nonempty) (i : ι) :
    sSup S i = ⨆ f : S, f.val i := by
  classical
  simp only [sSup, hS, hS₀, and_self, ↓reduceDIte, mk_apply]
  split_ifs with hi
  · rw [sSup_image']
  · simp only [Finset.mem_union, mem_support_toFun, not_or, not_not] at hi
    have := hS₀.to_subtype
    refine le_antisymm (le_ciSup_of_le ?_ (⟨_, hS₀.some_mem⟩ : S) hi.2.ge) ?_
    · simpa [Set.range_comp' (· i) (Subtype.val : S → _)] using bddAbove_image_apply hS
    · exact ciSup_le fun f ↦ (hS.some_mem f.property i).trans_eq hi.1

@[to_dual]
lemma iSup_apply {κ : Type*} [Nonempty κ] {f : κ → Π₀ i, M i} (hf : BddAbove (.range f)) (i : ι) :
    (⨆ j, f j) i = ⨆ j, f j i := by
  rw [iSup, sSup_apply hf (Set.range_nonempty _), iSup_range' (· i) f]

@[to_dual]
private lemma isLUB_sSup {S : Set (Π₀ i, M i)} (hS₀ : S.Nonempty) (hS : BddAbove S) :
    IsLUB S (sSup S) := by
  refine ⟨fun f hf i ↦ ?_, fun g hg i ↦ ?_⟩
  · rw [sSup_apply hS hS₀]
    refine le_ciSup (f := fun f : S ↦ f.val i) ?_ ⟨f, hf⟩
    simpa [Set.range_comp' (· i) (Subtype.val : S → _)] using bddAbove_image_apply hS
  · rw [sSup_apply hS hS₀]
    have := hS₀.to_subtype
    exact ciSup_le fun f ↦ hg f.property i

noncomputable instance : ConditionallyCompleteLattice (Π₀ i, M i) where
  isLUB_csSup _ := private isLUB_sSup
  isGLB_csInf _ := private isGLB_sInf

end DFinsupp
