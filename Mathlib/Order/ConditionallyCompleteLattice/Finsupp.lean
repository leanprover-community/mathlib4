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

This file shows that `ι →₀ M` is a conditionally complete lattice when `M` is and `0` is the
bottom element of `M`. The supremum of a set that is bounded above is computed pointwise,
and has finite support because it is bounded above by an element of finite support.
-/

@[expose] public section

namespace Finsupp
variable {ι M : Type*} [Zero M] [ConditionallyCompleteLattice M] [IsBotZeroClass M]

open scoped Classical in
noncomputable instance : SupSet (ι →₀ M) where
  sSup S := if h : BddAbove S ∧ S.Nonempty then
      onFinset h.1.some.support (fun i ↦ sSup ((· i) '' S)) fun i hi ↦ by
        contrapose hi
        have : (· i) '' S = {0} := Set.eq_singleton_iff_nonempty_unique_mem.2 ⟨h.2.image _, by
          rintro _ ⟨f, hf, rfl⟩
          exact le_zero_iff.1 <| (h.1.some_mem hf i).trans_eq (by simpa using hi)⟩
        rw [this, csSup_singleton]
    else 0

lemma sSup_apply {S : Set (ι →₀ M)} (hS : BddAbove S) (hS₀ : S.Nonempty) (i : ι) :
    sSup S i = ⨆ f : S, f.1 i := by simp [sSup, sSup_image', *]

lemma iSup_apply {κ : Type*} [Nonempty κ] {f : κ → ι →₀ M} (hf : BddAbove (.range f)) (i : ι) :
    (⨆ j, f j) i = ⨆ j, f j i := by
  rw [iSup, sSup_apply hf (Set.range_nonempty _), ciSup_range f (· i)]

noncomputable instance : ConditionallyCompleteLattice (ι →₀ M) := by
  refine conditionallyCompleteLatticeOfLatticeOfsSup _ fun S hS hS₀ ↦
    ⟨fun f hf i ↦ ?_, fun g hg i ↦ ?_⟩
  · rw [sSup_apply hS hS₀]
    refine le_ciSup (f := fun f : S ↦ f.1 i) ?_ ⟨f, hf⟩
    simpa [Set.range_comp' (· i) (Subtype.val : S → _)] using bddAbove_image_apply hS
  · rw [sSup_apply hS hS₀]
    have := hS₀.to_subtype
    exact ciSup_le (hg ·.2 i)

end Finsupp

namespace DFinsupp
variable {ι : Type*} {M : ι → Type*} [∀ i, Zero (M i)] [∀ i, ConditionallyCompleteLattice (M i)]
  [∀ i, IsBotZeroClass (M i)]

open scoped Classical in
noncomputable instance : SupSet (Π₀ i, M i) where
  sSup S := if h : BddAbove S ∧ S.Nonempty then
      mk h.1.some.support fun i ↦ sSup ((· i.1) '' S)
    else 0

lemma sSup_apply {S : Set (Π₀ i, M i)} (hS : BddAbove S) (hS₀ : S.Nonempty) (i : ι) :
    sSup S i = ⨆ f : S, f.1 i := by
  classical
  simp only [sSup, hS, hS₀, and_self, ↓reduceDIte, mk_apply]
  split_ifs with hi
  · rw [sSup_image']
  · have hf (f : S) : f.1 i = 0 := le_zero_iff.1 <| (hS.some_mem f.2 i).trans_eq (by simpa using hi)
    simp [hf, hS₀.to_subtype]

lemma iSup_apply {κ : Type*} [Nonempty κ] {f : κ → Π₀ i, M i} (hf : BddAbove (.range f)) (i : ι) :
    (⨆ j, f j) i = ⨆ j, f j i := by
  rw [iSup, sSup_apply hf (Set.range_nonempty _), ciSup_range f (· i)]

noncomputable instance : ConditionallyCompleteLattice (Π₀ i, M i) := by
  refine conditionallyCompleteLatticeOfLatticeOfsSup _ fun S hS hS₀ ↦
    ⟨fun f hf i ↦ ?_, fun g hg i ↦ ?_⟩
  · rw [sSup_apply hS hS₀]
    refine le_ciSup (f := fun f : S ↦ f.1 i) ?_ ⟨f, hf⟩
    simpa [Set.range_comp' (· i) (Subtype.val : S → _)] using bddAbove_image_apply hS
  · rw [sSup_apply hS hS₀]
    have := hS₀.to_subtype
    exact ciSup_le fun f ↦ hg f.2 i

end DFinsupp
