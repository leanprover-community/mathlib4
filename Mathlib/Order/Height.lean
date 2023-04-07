/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module order.height
! leanprover-community/mathlib commit bf27744463e9620ca4e4ebe951fe83530ae6949b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Enat.Lattice
import Mathbin.Order.OrderIsoNat
import Mathbin.Tactic.Tfae

/-!

# Maximal length of chains

This file contains lemmas to work with the maximal length of strictly descending finite
sequences (chains) in a partial order.

## Main definition

- `set.subchain`: The set of strictly ascending lists of `α` contained in a `set α`.
- `set.chain_height`: The maximal length of a strictly ascending sequence in a partial order.
This is defined as the maximum of the lengths of `set.subchain`s, valued in `ℕ∞`.

## Main results

- `set.exists_chain_of_le_chain_height`: For each `n : ℕ` such that `n ≤ s.chain_height`, there
  exists `s.subchain` of length `n`.
- `set.chain_height_mono`: If `s ⊆ t` then `s.chain_height ≤ t.chain_height`.
- `set.chain_height_image`: If `f` is an order embedding, then
  `(f '' s).chain_height = s.chain_height`.
- `set.chain_height_insert_of_forall_lt`: If `∀ y ∈ s, y < x`, then
  `(insert x s).chain_height = s.chain_height + 1`.
- `set.chain_height_insert_of_lt_forall`: If `∀ y ∈ s, x < y`, then
  `(insert x s).chain_height = s.chain_height + 1`.
- `set.chain_height_union_eq`: If `∀ x ∈ s, ∀ y ∈ t, s ≤ t`, then
  `(s ∪ t).chain_height = s.chain_height + t.chain_height`.
- `set.well_founded_gt_of_chain_height_ne_top`:
  If `s` has finite height, then `>` is well-founded on `s`.
- `set.well_founded_lt_of_chain_height_ne_top`:
  If `s` has finite height, then `<` is well-founded on `s`.

-/


open List OrderDual

universe u v

variable {α β : Type _}

namespace Set

section LT

variable [LT α] [LT β] (s t : Set α)

/-- The set of strictly ascending lists of `α` contained in a `set α`. -/
def subchain : Set (List α) :=
  { l | l.Chain' (· < ·) ∧ ∀ i ∈ l, i ∈ s }
#align set.subchain Set.subchain

theorem nil_mem_subchain : [] ∈ s.subchain :=
  ⟨trivial, fun x hx => hx.elim⟩
#align set.nil_mem_subchain Set.nil_mem_subchain

variable {s} {l : List α} {a : α}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cons_mem_subchain_iff :
    (a::l) ∈ s.subchain ↔ a ∈ s ∧ l ∈ s.subchain ∧ ∀ b ∈ l.head?, a < b :=
  by
  refine'
    ⟨fun h =>
      ⟨h.2 _ (Or.inl rfl), ⟨(chain'_cons'.mp h.1).2, fun i hi => h.2 _ (Or.inr hi)⟩,
        (chain'_cons'.mp h.1).1⟩,
      _⟩
  rintro ⟨h₁, h₂, h₃⟩
  constructor
  · rw [chain'_cons']
    exact ⟨h₃, h₂.1⟩
  · rintro i (rfl | hi)
    exacts[h₁, h₂.2 _ hi]
#align set.cons_mem_subchain_iff Set.cons_mem_subchain_iff

instance : Nonempty s.subchain :=
  ⟨⟨[], s.nil_mem_subchain⟩⟩

variable (s)

/-- The maximal length of a strictly ascending sequence in a partial order. -/
noncomputable def chainHeight : ℕ∞ :=
  ⨆ l ∈ s.subchain, length l
#align set.chain_height Set.chainHeight

theorem chainHeight_eq_supᵢ_subtype : s.chainHeight = ⨆ l : s.subchain, l.1.length :=
  supᵢ_subtype'
#align set.chain_height_eq_supr_subtype Set.chainHeight_eq_supᵢ_subtype

theorem exists_chain_of_le_chainHeight {n : ℕ} (hn : ↑n ≤ s.chainHeight) :
    ∃ l ∈ s.subchain, length l = n :=
  by
  cases' (le_top : s.chain_height ≤ ⊤).eq_or_lt with ha ha <;>
    rw [chain_height_eq_supr_subtype] at ha
  · obtain ⟨_, ⟨⟨l, h₁, h₂⟩, rfl⟩, h₃⟩ :=
      not_bdd_above_iff'.mp ((WithTop.supr_coe_eq_top _).mp ha) n
    exact
      ⟨l.take n, ⟨h₁.take _, fun x h => h₂ _ <| take_subset _ _ h⟩,
        (l.length_take n).trans <| min_eq_left <| le_of_not_ge h₃⟩
  · rw [WithTop.supr_coe_lt_top] at ha
    obtain ⟨⟨l, h₁, h₂⟩, e : l.length = _⟩ := Nat.supₛ_mem (Set.range_nonempty _) ha
    refine'
      ⟨l.take n, ⟨h₁.take _, fun x h => h₂ _ <| take_subset _ _ h⟩,
        (l.length_take n).trans <| min_eq_left <| _⟩
    rwa [e, ← WithTop.coe_le_coe, supₛ_range, WithTop.coe_supᵢ _ ha, ← chain_height_eq_supr_subtype]
#align set.exists_chain_of_le_chain_height Set.exists_chain_of_le_chainHeight

theorem le_chainHeight_tFAE (n : ℕ) :
    TFAE [↑n ≤ s.chainHeight, ∃ l ∈ s.subchain, length l = n, ∃ l ∈ s.subchain, n ≤ length l] :=
  by
  tfae_have 1 → 2; · exact s.exists_chain_of_le_chain_height
  tfae_have 2 → 3;
  · rintro ⟨l, hls, he⟩
    exact ⟨l, hls, he.ge⟩
  tfae_have 3 → 1;
  · rintro ⟨l, hs, hn⟩
    exact le_supᵢ₂_of_le l hs (WithTop.coe_le_coe.2 hn)
  tfae_finish
#align set.le_chain_height_tfae Set.le_chainHeight_tFAE

variable {s t}

theorem le_chainHeight_iff {n : ℕ} : ↑n ≤ s.chainHeight ↔ ∃ l ∈ s.subchain, length l = n :=
  (le_chainHeight_tFAE s n).out 0 1
#align set.le_chain_height_iff Set.le_chainHeight_iff

theorem length_le_chainHeight_of_mem_subchain (hl : l ∈ s.subchain) : ↑l.length ≤ s.chainHeight :=
  le_chainHeight_iff.mpr ⟨l, hl, rfl⟩
#align set.length_le_chain_height_of_mem_subchain Set.length_le_chainHeight_of_mem_subchain

theorem chainHeight_eq_top_iff : s.chainHeight = ⊤ ↔ ∀ n, ∃ l ∈ s.subchain, length l = n :=
  by
  refine' ⟨fun h n => le_chain_height_iff.1 (le_top.trans_eq h.symm), fun h => _⟩
  contrapose! h; obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h
  exact
    ⟨n + 1, fun l hs =>
      (Nat.lt_succ_iff.2 <|
          WithTop.coe_le_coe.1 <| (length_le_chain_height_of_mem_subchain hs).trans_eq hn.symm).Ne⟩
#align set.chain_height_eq_top_iff Set.chainHeight_eq_top_iff

@[simp]
theorem one_le_chainHeight_iff : 1 ≤ s.chainHeight ↔ s.Nonempty :=
  by
  change ((1 : ℕ) : ENat) ≤ _ ↔ _
  rw [Set.le_chainHeight_iff]
  constructor
  · rintro ⟨_ | ⟨x, xs⟩, ⟨h₁, h₂⟩, h₃⟩
    · cases h₃
    · exact ⟨x, h₂ _ (Or.inl rfl)⟩
  · rintro ⟨x, hx⟩
    exact ⟨[x], ⟨chain.nil, fun y h => (list.mem_singleton.mp h).symm ▸ hx⟩, rfl⟩
#align set.one_le_chain_height_iff Set.one_le_chainHeight_iff

@[simp]
theorem chainHeight_eq_zero_iff : s.chainHeight = 0 ↔ s = ∅ := by
  rw [← not_iff_not, ← Ne.def, ← bot_eq_zero, ← bot_lt_iff_ne_bot, bot_eq_zero, ←
    ENat.one_le_iff_pos, one_le_chain_height_iff, nonempty_iff_ne_empty]
#align set.chain_height_eq_zero_iff Set.chainHeight_eq_zero_iff

@[simp]
theorem chainHeight_empty : (∅ : Set α).chainHeight = 0 :=
  chainHeight_eq_zero_iff.2 rfl
#align set.chain_height_empty Set.chainHeight_empty

@[simp]
theorem chainHeight_of_isEmpty [IsEmpty α] : s.chainHeight = 0 :=
  chainHeight_eq_zero_iff.mpr (Subsingleton.elim _ _)
#align set.chain_height_of_is_empty Set.chainHeight_of_isEmpty

theorem le_chainHeight_add_nat_iff {n m : ℕ} :
    ↑n ≤ s.chainHeight + m ↔ ∃ l ∈ s.subchain, n ≤ length l + m := by
  simp_rw [← tsub_le_iff_right, ← WithTop.coe_sub, (le_chain_height_tfae s (n - m)).out 0 2]
#align set.le_chain_height_add_nat_iff Set.le_chainHeight_add_nat_iff

theorem chainHeight_add_le_chainHeight_add (s : Set α) (t : Set β) (n m : ℕ) :
    s.chainHeight + n ≤ t.chainHeight + m ↔
      ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l + n ≤ length l' + m :=
  by
  refine'
    ⟨fun e l h =>
      le_chain_height_add_nat_iff.1
        ((add_le_add_right (length_le_chain_height_of_mem_subchain h) _).trans e),
      fun H => _⟩
  by_cases s.chain_height = ⊤
  · suffices t.chain_height = ⊤ by
      rw [this, top_add]
      exact le_top
    rw [chain_height_eq_top_iff] at h⊢
    intro k
    rw [(le_chain_height_tfae t k).out 1 2]
    obtain ⟨l, hs, hl⟩ := h (k + m)
    obtain ⟨l', ht, hl'⟩ := H l hs
    exact ⟨l', ht, (add_le_add_iff_right m).1 <| trans (hl.symm.trans_le le_self_add) hl'⟩
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 h
    obtain ⟨l, hs, hl⟩ := le_chain_height_iff.1 hk.le
    rw [← hk, ← hl]
    exact le_chain_height_add_nat_iff.2 (H l hs)
#align set.chain_height_add_le_chain_height_add Set.chainHeight_add_le_chainHeight_add

theorem chainHeight_le_chainHeight_tFAE (s : Set α) (t : Set β) :
    TFAE
      [s.chainHeight ≤ t.chainHeight, ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l = length l',
        ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l ≤ length l'] :=
  by
  tfae_have 1 ↔ 3; · convert← chain_height_add_le_chain_height_add s t 0 0 <;> apply add_zero
  tfae_have 2 ↔ 3;
  · refine' forall₂_congr fun l hl => _
    simp_rw [← (le_chain_height_tfae t l.length).out 1 2, eq_comm]
  tfae_finish
#align set.chain_height_le_chain_height_tfae Set.chainHeight_le_chainHeight_tFAE

theorem chainHeight_le_chainHeight_iff {t : Set β} :
    s.chainHeight ≤ t.chainHeight ↔ ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l = length l' :=
  (chainHeight_le_chainHeight_tFAE s t).out 0 1
#align set.chain_height_le_chain_height_iff Set.chainHeight_le_chainHeight_iff

theorem chainHeight_le_chainHeight_iff_le {t : Set β} :
    s.chainHeight ≤ t.chainHeight ↔ ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l ≤ length l' :=
  (chainHeight_le_chainHeight_tFAE s t).out 0 2
#align set.chain_height_le_chain_height_iff_le Set.chainHeight_le_chainHeight_iff_le

theorem chainHeight_mono (h : s ⊆ t) : s.chainHeight ≤ t.chainHeight :=
  chainHeight_le_chainHeight_iff.2 fun l hl => ⟨l, ⟨hl.1, fun i hi => h <| hl.2 i hi⟩, rfl⟩
#align set.chain_height_mono Set.chainHeight_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem chainHeight_image (f : α → β) (hf : ∀ {x y}, x < y ↔ f x < f y) (s : Set α) :
    (f '' s).chainHeight = s.chainHeight :=
  by
  apply le_antisymm <;> rw [chain_height_le_chain_height_iff]
  · suffices ∀ l ∈ (f '' s).subchain, ∃ l' ∈ s.subchain, map f l' = l
      by
      intro l hl
      obtain ⟨l', h₁, rfl⟩ := this l hl
      exact ⟨l', h₁, length_map _ _⟩
    intro l
    induction' l with x xs hx
    · exact fun _ => ⟨nil, ⟨trivial, fun _ h => h.elim⟩, rfl⟩
    · intro h
      rw [cons_mem_subchain_iff] at h
      obtain ⟨⟨x, hx', rfl⟩, h₁, h₂⟩ := h
      obtain ⟨l', h₃, rfl⟩ := hx h₁
      refine' ⟨x::l', set.cons_mem_subchain_iff.mpr ⟨hx', h₃, _⟩, rfl⟩
      cases l'
      · simp
      · simpa [← hf] using h₂
  · intro l hl
    refine' ⟨l.map f, ⟨_, _⟩, _⟩
    · simp_rw [chain'_map, ← hf]
      exact hl.1
    · intro _ e
      obtain ⟨a, ha, rfl⟩ := mem_map.mp e
      exact Set.mem_image_of_mem _ (hl.2 _ ha)
    · rw [length_map]
#align set.chain_height_image Set.chainHeight_image

variable (s)

@[simp]
theorem chainHeight_dual : (ofDual ⁻¹' s).chainHeight = s.chainHeight := by
  apply le_antisymm <;>
    · rw [chain_height_le_chain_height_iff]
      rintro l ⟨h₁, h₂⟩
      exact
        ⟨l.reverse, ⟨chain'_reverse.mpr h₁, fun i h => h₂ i (mem_reverse.mp h)⟩,
          (length_reverse _).symm⟩
#align set.chain_height_dual Set.chainHeight_dual

end LT

section Preorder

variable (s t : Set α) [Preorder α]

theorem chainHeight_eq_supᵢ_Ici : s.chainHeight = ⨆ i ∈ s, (s ∩ Set.Ici i).chainHeight :=
  by
  apply le_antisymm
  · refine' supᵢ₂_le _
    rintro (_ | ⟨x, xs⟩) h
    · exact zero_le _
    · apply le_trans _ (le_supᵢ₂ x (cons_mem_subchain_iff.mp h).1)
      apply length_le_chain_height_of_mem_subchain
      refine' ⟨h.1, fun i hi => ⟨h.2 i hi, _⟩⟩
      cases hi
      · exact hi.symm.le
      cases' chain'_iff_pairwise.mp h.1 with _ _ h'
      exact (h' _ hi).le
  · exact supᵢ₂_le fun i hi => chain_height_mono <| Set.inter_subset_left _ _
#align set.chain_height_eq_supr_Ici Set.chainHeight_eq_supᵢ_Ici

theorem chainHeight_eq_supᵢ_Iic : s.chainHeight = ⨆ i ∈ s, (s ∩ Set.Iic i).chainHeight :=
  by
  simp_rw [← chain_height_dual (_ ∩ _)]
  rw [← chain_height_dual, chain_height_eq_supr_Ici]
  rfl
#align set.chain_height_eq_supr_Iic Set.chainHeight_eq_supᵢ_Iic

variable {s t}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem chainHeight_insert_of_forall_gt (a : α) (hx : ∀ b ∈ s, a < b) :
    (insert a s).chainHeight = s.chainHeight + 1 :=
  by
  rw [← add_zero (insert a s).chainHeight]
  change (insert a s).chainHeight + (0 : ℕ) = s.chain_height + (1 : ℕ)
  apply le_antisymm <;> rw [chain_height_add_le_chain_height_add]
  · rintro (_ | ⟨y, ys⟩) h
    · exact ⟨[], nil_mem_subchain _, zero_le _⟩
    · have h' := cons_mem_subchain_iff.mp h
      refine' ⟨ys, ⟨h'.2.1.1, fun i hi => _⟩, by simp⟩
      apply (h'.2.1.2 i hi).resolve_left
      rintro rfl
      cases' chain'_iff_pairwise.mp h.1 with _ _ hy
      cases' h'.1 with h' h'
      exacts[(hy _ hi).Ne h', not_le_of_gt (hy _ hi) (hx _ h').le]
  · intro l hl
    refine' ⟨a::l, ⟨_, _⟩, by simp⟩
    · rw [chain'_cons']
      exact ⟨fun y hy => hx _ (hl.2 _ (mem_of_mem_head' hy)), hl.1⟩
    · rintro x (rfl | hx)
      exacts[Or.inl (Set.mem_singleton x), Or.inr (hl.2 x hx)]
#align set.chain_height_insert_of_forall_gt Set.chainHeight_insert_of_forall_gt

theorem chainHeight_insert_of_forall_lt (a : α) (ha : ∀ b ∈ s, b < a) :
    (insert a s).chainHeight = s.chainHeight + 1 :=
  by
  rw [← chain_height_dual, ← chain_height_dual s]
  exact chain_height_insert_of_forall_gt _ ha
#align set.chain_height_insert_of_forall_lt Set.chainHeight_insert_of_forall_lt

theorem chainHeight_union_le : (s ∪ t).chainHeight ≤ s.chainHeight + t.chainHeight := by
  classical
    refine' supᵢ₂_le fun l hl => _
    let l₁ := l.filter (· ∈ s)
    let l₂ := l.filter (· ∈ t)
    have hl₁ : ↑l₁.length ≤ s.chain_height :=
      by
      apply Set.length_le_chainHeight_of_mem_subchain
      exact ⟨hl.1.Sublist (filter_sublist _), fun i h => (of_mem_filter h : _)⟩
    have hl₂ : ↑l₂.length ≤ t.chain_height :=
      by
      apply Set.length_le_chainHeight_of_mem_subchain
      exact ⟨hl.1.Sublist (filter_sublist _), fun i h => (of_mem_filter h : _)⟩
    refine' le_trans _ (add_le_add hl₁ hl₂)
    simp_rw [← WithTop.coe_add, WithTop.coe_le_coe, ← Multiset.coe_card, ← Multiset.card_add, ←
      Multiset.coe_filter]
    rw [Multiset.filter_add_filter, multiset.filter_eq_self.mpr, Multiset.card_add]
    exacts[le_add_right rfl.le, hl.2]
#align set.chain_height_union_le Set.chainHeight_union_le

theorem chainHeight_union_eq (s t : Set α) (H : ∀ a ∈ s, ∀ b ∈ t, a < b) :
    (s ∪ t).chainHeight = s.chainHeight + t.chainHeight :=
  by
  cases h : t.chain_height
  · rw [WithTop.none_eq_top, add_top, eq_top_iff, ← WithTop.none_eq_top, ← h]
    exact Set.chainHeight_mono (Set.subset_union_right _ _)
  apply le_antisymm
  · rw [← h]
    exact chain_height_union_le
  rw [WithTop.some_eq_coe, ← add_zero (s ∪ t).chainHeight, ← WithTop.coe_zero,
    chain_height_add_le_chain_height_add]
  intro l hl
  obtain ⟨l', hl', rfl⟩ := exists_chain_of_le_chain_height t h.symm.le
  refine' ⟨l ++ l', ⟨chain'.append hl.1 hl'.1 fun x hx y hy => _, fun i hi => _⟩, by simp⟩
  · exact H x (hl.2 _ <| mem_of_mem_last' hx) y (hl'.2 _ <| mem_of_mem_head' hy)
  · rw [mem_append] at hi
    cases hi
    exacts[Or.inl (hl.2 _ hi), Or.inr (hl'.2 _ hi)]
#align set.chain_height_union_eq Set.chainHeight_union_eq

theorem wellFoundedGT_of_chainHeight_ne_top (s : Set α) (hs : s.chainHeight ≠ ⊤) :
    WellFoundedGT s := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hs
  refine' ⟨RelEmbedding.wellFounded_iff_no_descending_seq.2 ⟨fun f => _⟩⟩
  refine' n.lt_succ_self.not_le (WithTop.coe_le_coe.1 <| hn.symm ▸ _)
  refine'
    le_supᵢ₂_of_le _
      ⟨chain'_map_of_chain' coe (fun _ _ => id)
          (chain'_iff_pairwise.2 <| pairwise_of_fn.2 fun i j => f.map_rel_iff.2),
        fun i h => _⟩
      _
  · exact n.succ
  · obtain ⟨a, ha, rfl⟩ := mem_map.1 h
    exact a.prop
  · rw [length_map, length_of_fn]
    exact le_rfl
#align set.well_founded_gt_of_chain_height_ne_top Set.wellFoundedGT_of_chainHeight_ne_top

theorem wellFoundedLT_of_chainHeight_ne_top (s : Set α) (hs : s.chainHeight ≠ ⊤) :
    WellFoundedLT s :=
  wellFoundedGT_of_chainHeight_ne_top (ofDual ⁻¹' s) <| by rwa [chain_height_dual]
#align set.well_founded_lt_of_chain_height_ne_top Set.wellFoundedLT_of_chainHeight_ne_top

end Preorder

end Set

