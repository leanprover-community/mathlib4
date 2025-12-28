/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Vlad Tsyrklevich
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card

/-!

# Maximal length of chains

This file contains lemmas to work with the maximal lengths of chains of arbitrary relations. See
`Order.height` for a definition specialized to finding the height of an element in a preorder.

## Main definition

- `Set.chainHeight`: The maximal length of a chain in a set `s` with relation `r`.

## Main results

- `Set.exists_isChain_of_le_chainHeight`: For each `n : ℕ` such that `n ≤ s.chainHeight`, there
  exists a subset `t` of length `n` such that `IsChain r t`.
- `Set.chainHeight_mono`: If `s ⊆ t` then `s.chainHeight ≤ t.chainHeight`.
- `Set.chainHeight_eq_of_relEmbedding`: If `f` is an relation embedding, then
  `(f '' s).chainHeight = s.chainHeight`.

-/

@[expose] public section

assert_not_exists Field

namespace Set

open ENat

variable {α β : Type*} (s : Set α) (r : α → α → Prop)

/-- The maximal length of a chain in a set `s` with relation `r`. -/
noncomputable def chainHeight : ℕ∞ := ⨆ t : {t : Set α // t ⊆ s ∧ IsChain r t}, t.val.encard

theorem chainHeight_eq_iSup :
    s.chainHeight r = ⨆ t : {t : Set α // t ⊆ s ∧ IsChain r t}, t.val.encard := rfl

theorem chainHeight_le_encard : s.chainHeight r ≤ s.encard := by
  simp_all [chainHeight, encard_le_encard]

theorem chainHeight_ne_top_of_finite (h : s.Finite) : s.chainHeight r ≠ ⊤ :=
  LT.lt.ne_top <| lt_of_le_of_lt (chainHeight_le_encard s r) <| lt_top_iff_ne_top.mpr <|
    encard_ne_top_iff.mpr h

theorem exists_isChain_of_le_chainHeight {r} {s : Set α} (n : ℕ) (h : n ≤ s.chainHeight r) :
    ∃ t ⊆ s, t.encard = n ∧ IsChain r t := by
  by_cases h' : n = 0
  · exact ⟨∅, by simp [h']⟩
  · obtain ⟨t, ht₁, ht₂, ht₃⟩ : ∃ t ⊆ s, IsChain r t ∧ n ≤ t.encard := by
      contrapose! h
      refine iSup_lt_iff.mpr ⟨n - 1, ?_, fun m ↦ ENat.le_sub_one_of_lt <| h m.1 m.2.1 m.2.2⟩
      exact_mod_cast Nat.sub_one_lt h'
    obtain ⟨u, hu₁, hu₂⟩ := exists_subset_encard_eq ht₃
    exact ⟨u, hu₁.trans ht₁, hu₂, ht₂.mono hu₁⟩

theorem exists_eq_chainHeight_of_chainHeight_ne_top (h : s.chainHeight r ≠ ⊤) :
    ∃ t ⊆ s, t.encard = s.chainHeight r ∧ IsChain r t := by
  have : Nonempty { t // t ⊆ s ∧ IsChain r t } := ⟨∅, by simp⟩
  obtain ⟨t, ht⟩ := exists_eq_iSup_of_lt_top (by rwa [← chainHeight_eq_iSup, lt_top_iff_ne_top])
  exact ⟨t.1, t.2.1, ht, t.2.2⟩

theorem exists_eq_chainHeight_of_finite (h : s.Finite) :
     ∃ t ⊆ s, t.encard = s.chainHeight r ∧ IsChain r t :=
  exists_eq_chainHeight_of_chainHeight_ne_top s r (chainHeight_ne_top_of_finite s r h)

theorem encard_le_chainHeight_of_isChain {r} (s t : Set α) (hs : t ⊆ s) (hc : IsChain r t) :
    t.encard ≤ s.chainHeight r :=
  le_iSup_iff.mpr fun _ hb ↦ hb ⟨t, hs, hc⟩

theorem encard_eq_chainHeight_of_isChain {r} (s : Set α) (hc : IsChain r s) :
    s.encard = s.chainHeight r :=
  le_antisymm (encard_le_chainHeight_of_isChain _ _ Set.Subset.rfl hc) (chainHeight_le_encard _ _)

theorem finite_of_chainHeight_ne_top {r} {s : Set α} (hc : IsChain r s) (h : s.chainHeight r ≠ ⊤) :
    s.Finite :=
  Set.encard_ne_top_iff.mp <| ne_top_of_le_ne_top h <|
    encard_le_chainHeight_of_isChain _ _ (subset_refl _) hc

theorem not_isChain_of_chainHeight_lt_encard (s t : Set α) (ht : t ⊆ s)
    (he : s.chainHeight r < t.encard) : ¬ IsChain r t := by
  by_contra! hh
  grw [encard_le_chainHeight_of_isChain _ _ ht hh] at he
  exact (lt_self_iff_false _).mp he

theorem chainHeight_eq_top_iff :
    s.chainHeight r = ⊤ ↔ ∀ n : ℕ, ∃ t ⊆ s, t.encard = n ∧ IsChain r t := by
  refine ⟨fun h _ ↦ exists_isChain_of_le_chainHeight _ (le_top.trans_eq h.symm), fun h ↦ ?_⟩
  contrapose! h
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h
  refine ⟨n + 1, fun l hl he ↦ not_isChain_of_chainHeight_lt_encard r s l hl ?_⟩
  rw [← hn, some_eq_coe, he, Nat.cast_lt]
  exact lt_add_one _

@[simp]
theorem chainHeight_eq_zero_iff : s.chainHeight r = 0 ↔ s = ∅ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simp only [chainHeight, iSup_eq_zero, encard_eq_zero, Subtype.forall, and_imp] at h
    ext x
    simpa using h {x}
  · simp_all [chainHeight]

@[simp]
theorem chainHeight_empty : (∅ : Set α).chainHeight r = 0 :=
  chainHeight_eq_zero_iff _ _ |>.mpr rfl

@[simp]
theorem one_le_chainHeight_iff : 1 ≤ s.chainHeight r ↔ s.Nonempty := by
  constructor
  all_goals
  · intros
    by_contra! hh
    simp_all [lt_one_iff_eq_zero]

@[simp]
theorem chainHeight_of_isEmpty [IsEmpty α] : s.chainHeight r = 0 :=
  chainHeight_eq_zero_iff s r |>.mpr (Subsingleton.elim _ _)

@[mono]
theorem chainHeight_mono (s t : Set α) (h : s ⊆ t) : s.chainHeight r ≤ t.chainHeight r := by
  refine forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
  exact ha₂ ▸ encard_le_chainHeight_of_isChain _ _ (ha₁.trans h) ha₃

@[simp]
theorem chainHeight_flip : s.chainHeight (flip r) = s.chainHeight r := by
  refine eq_of_forall_natCast_le_iff fun n ↦ ⟨fun hn ↦ ?_, fun hn ↦ ?_⟩
  all_goals
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
    exact ha₂ ▸ encard_le_chainHeight_of_isChain _ _ ha₁ <|
      fun _ hx _ hy hne ↦ by simpa [flip, Or.comm] using ha₃ hx hy hne

section Rel

variable {r : α → α → Prop} {r' : β → β → Prop} (s : Set α)

theorem chainHeight_eq_of_relEmbedding (e : r ↪r r') :
    (e '' s).chainHeight r' = s.chainHeight r := by
  refine eq_of_forall_natCast_le_iff fun n ↦ ⟨fun hn ↦ ?_, fun hn ↦ ?_⟩
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
    rw [← ha₂, ← Set.encard_preimage_of_injective_subset_range e.injective (by grind)]
    exact encard_le_chainHeight_of_isChain _ _ (preimage_subset ha₁ e.injective.injOn) <|
      ha₃.preimage_relEmbedding e
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
    rw [← ha₂, ← e.injective.encard_image]
    exact encard_le_chainHeight_of_isChain _ _ (by grind) <| ha₃.image_relEmbedding e

theorem chainHeight_eq_of_relIso (e : r ≃r r') : (e '' s).chainHeight r' = s.chainHeight r :=
  chainHeight_eq_of_relEmbedding s e.toRelEmbedding

end Rel

@[simp]
theorem chainHeight_coe_univ : (@Set.univ ↑s).chainHeight (r ↑· ↑·) = s.chainHeight r := by
  have hc := Set.chainHeight_eq_of_relEmbedding univ <| Subtype.relEmbedding (r · ·) (· ∈ s)
  have hs : Subtype.val ⁻¹'o (r · ·) = (fun x y : s ↦ r x y) := by funext; simp
  simpa [hs] using hc.symm

@[simp]
theorem chainHeight_coe_univ_le [LE α] :
    (@Set.univ ↑s).chainHeight (· ≤ ·) = s.chainHeight (· ≤ ·) := by
  simpa using chainHeight_coe_univ s (· ≤ ·)

@[simp]
theorem chainHeight_coe_univ_lt [LT α] :
    (@Set.univ ↑s).chainHeight (· < ·) = s.chainHeight (· < ·) := by
  simpa using chainHeight_coe_univ s (· < ·)

end Set
