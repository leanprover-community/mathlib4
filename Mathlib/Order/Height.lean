/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Vlad Tsyrklevich
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Order.KrullDimension

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
- `Order.height_eq_chainHeight_Iio`: In a preorder, `height a = (Set.Iio a).chainHeight (· < ·)`.
- `Order.height_eq_encard_Iio`: In a linear order, `height a = (Set.Iio a).encard`.

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
  by_contra hh
  grw [encard_le_chainHeight_of_isChain _ _ ht hh] at he
  exact (lt_self_iff_false _).mp he

theorem chainHeight_eq_top_iff :
    s.chainHeight r = ⊤ ↔ ∀ n : ℕ, ∃ t ⊆ s, t.encard = n ∧ IsChain r t := by
  refine ⟨fun h _ ↦ exists_isChain_of_le_chainHeight _ (le_top.trans_eq h.symm), fun h ↦ ?_⟩
  contrapose! h
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
  refine ⟨n + 1, fun l hl he ↦ not_isChain_of_chainHeight_lt_encard r s l hl ?_⟩
  rw [← hn, he]
  exact_mod_cast lt_add_one _

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
    simp_all

@[simp]
theorem chainHeight_of_isEmpty [IsEmpty α] : s.chainHeight r = 0 :=
  chainHeight_eq_zero_iff s r |>.mpr (Subsingleton.elim _ _)

@[gcongr, mono]
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
    exact encard_le_chainHeight_of_isChain _ _ (by grind) <| ha₃.image e

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

namespace Order

variable {α : Type*}

/-- In a preorder, the height of an element `a` is the supremum of the cardinalities of the sets
of elements less than `a` that are chains for `<`. -/
theorem height_eq_chainHeight_Iio [Preorder α] (a : α) :
    height a = (Set.Iio a).chainHeight (· < ·) := by
  refine le_antisymm (height_le fun p hp ↦ ?_) (ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_)
  · have hf : StrictMono fun i ↦ p (Fin.castSucc i) := p.strictMono.comp Fin.strictMono_castSucc
    simpa [hf.injective.encard_range] using Set.encard_le_chainHeight_of_isChain (Set.Iio a) _
      (Set.range_subset_iff.mpr fun i ↦ (p.strictMono (Fin.castSucc_lt_last i)).trans_eq hp)
      (Set.image_univ ▸ (isChain_of_trichotomous _).image_of_map_rel _ _ _ fun _ _ ↦ (hf ·))
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    obtain ⟨t, hta, htn, htc⟩ := Set.exists_isChain_of_le_chainHeight _ hn
    obtain ⟨m, hm⟩ := (Set.finite_of_encard_eq_coe htn).exists_maximal
      (Set.nonempty_of_encard_ne_zero (by simp [htn]))
    grw [Nat.cast_add_one, ih m ?_, height_add_one_le (hta hm.1)]
    simpa [Set.encard_sdiff_singleton_of_mem hm.1, htn] using
      Set.encard_le_chainHeight_of_isChain (Set.Iio m) (t \ {m})
        (fun _ hx ↦ (htc hx.1 hm.1 hx.2).resolve_right (hm.not_gt hx.1)) htc.diff

/-- In a preorder, the coheight of an element `a` is the supremum of the cardinalities of the sets
of elements greater than `a` that are chains for `<`. -/
theorem coheight_eq_chainHeight_Ioi [Preorder α] (a : α) :
    coheight a = (Set.Ioi a).chainHeight (· < ·) :=
  (height_eq_chainHeight_Iio (α := αᵒᵈ) a).trans (Set.chainHeight_flip _ _)

theorem height_le_encard_Iio [Preorder α] (a : α) : height a ≤ (Set.Iio a).encard :=
  (height_eq_chainHeight_Iio a).trans_le (Set.chainHeight_le_encard _ _)

theorem coheight_le_encard_Ioi [Preorder α] (a : α) : coheight a ≤ (Set.Ioi a).encard :=
  height_le_encard_Iio (α := αᵒᵈ) a

/-- In a linear order, the height of an element `a` is the cardinality of the set of elements
less than `a`. -/
theorem height_eq_encard_Iio [LinearOrder α] (a : α) : height a = (Set.Iio a).encard :=
  (height_eq_chainHeight_Iio a).trans
    (Set.encard_eq_chainHeight_of_isChain _ (isChain_of_trichotomous _)).symm

/-- In a linear order, the coheight of an element `a` is the cardinality of the set of elements
greater than `a`. -/
theorem coheight_eq_encard_Ioi [LinearOrder α] (a : α) : coheight a = (Set.Ioi a).encard :=
  height_eq_encard_Iio (α := αᵒᵈ) a

end Order
