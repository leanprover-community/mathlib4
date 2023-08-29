/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.OrderIsoNat
import Mathlib.Tactic.TFAE

#align_import order.height from "leanprover-community/mathlib"@"bf27744463e9620ca4e4ebe951fe83530ae6949b"

/-!

# Maximal length of chains

This file contains lemmas to work with the maximal length of strictly descending finite
sequences (chains) in a partial order.

## Main definition

- `Set.subchain`: The set of strictly ascending lists of `α` contained in a `Set α`.
- `Set.chainHeight`: The maximal length of a strictly ascending sequence in a partial order.
This is defined as the maximum of the lengths of `Set.subchain`s, valued in `ℕ∞`.

## Main results

- `Set.exists_chain_of_le_chainHeight`: For each `n : ℕ` such that `n ≤ s.chainHeight`, there
  exists `s.subchain` of length `n`.
- `Set.chainHeight_mono`: If `s ⊆ t` then `s.chainHeight ≤ t.chainHeight`.
- `Set.chainHeight_image`: If `f` is an order embedding, then
  `(f '' s).chainHeight = s.chainHeight`.
- `Set.chainHeight_insert_of_forall_lt`: If `∀ y ∈ s, y < x`, then
  `(insert x s).chainHeight = s.chainHeight + 1`.
- `Set.chainHeight_insert_of_forall_gt`: If `∀ y ∈ s, x < y`, then
  `(insert x s).chainHeight = s.chainHeight + 1`.
- `Set.chainHeight_union_eq`: If `∀ x ∈ s, ∀ y ∈ t, s ≤ t`, then
  `(s ∪ t).chainHeight = s.chainHeight + t.chainHeight`.
- `Set.wellFoundedGT_of_chainHeight_ne_top`:
  If `s` has finite height, then `>` is well-founded on `s`.
- `Set.wellFoundedLT_of_chainHeight_ne_top`:
  If `s` has finite height, then `<` is well-founded on `s`.

-/


open List hiding le_antisymm
open OrderDual

universe u v

variable {α β : Type*}

namespace Set

section LT

variable [LT α] [LT β] (s t : Set α)

/-- The set of strictly ascending lists of `α` contained in a `Set α`. -/
def subchain : Set (List α) :=
  { l | l.Chain' (· < ·) ∧ ∀ i ∈ l, i ∈ s }
#align set.subchain Set.subchain

@[simp] -- porting note: new `simp`
theorem nil_mem_subchain : [] ∈ s.subchain := ⟨trivial, fun _ ↦ fun.⟩
#align set.nil_mem_subchain Set.nil_mem_subchain

variable {s} {l : List α} {a : α}

theorem cons_mem_subchain_iff :
    (a::l) ∈ s.subchain ↔ a ∈ s ∧ l ∈ s.subchain ∧ ∀ b ∈ l.head?, a < b := by
  simp only [subchain, mem_setOf_eq, forall_mem_cons, chain'_cons', and_left_comm, and_comm,
    and_assoc]
#align set.cons_mem_subchain_iff Set.cons_mem_subchain_iff

@[simp] -- porting note: new lemma + `simp`
theorem singleton_mem_subchain_iff : [a] ∈ s.subchain ↔ a ∈ s := by simp [cons_mem_subchain_iff]
                                                                    -- 🎉 no goals

instance : Nonempty s.subchain :=
  ⟨⟨[], s.nil_mem_subchain⟩⟩

variable (s)

/-- The maximal length of a strictly ascending sequence in a partial order. -/
noncomputable def chainHeight : ℕ∞ :=
  ⨆ l ∈ s.subchain, length l
#align set.chain_height Set.chainHeight

theorem chainHeight_eq_iSup_subtype : s.chainHeight = ⨆ l : s.subchain, ↑l.1.length :=
  iSup_subtype'
#align set.chain_height_eq_supr_subtype Set.chainHeight_eq_iSup_subtype

theorem exists_chain_of_le_chainHeight {n : ℕ} (hn : ↑n ≤ s.chainHeight) :
    ∃ l ∈ s.subchain, length l = n := by
  cases' (le_top : s.chainHeight ≤ ⊤).eq_or_lt with ha ha <;>
  -- ⊢ ∃ l, l ∈ subchain s ∧ length l = n
    rw [chainHeight_eq_iSup_subtype] at ha
    -- ⊢ ∃ l, l ∈ subchain s ∧ length l = n
    -- ⊢ ∃ l, l ∈ subchain s ∧ length l = n
  · obtain ⟨_, ⟨⟨l, h₁, h₂⟩, rfl⟩, h₃⟩ :=
      not_bddAbove_iff'.mp ((WithTop.iSup_coe_eq_top _).mp ha) n
    exact ⟨l.take n, ⟨h₁.take _, fun x h ↦ h₂ _ <| take_subset _ _ h⟩,
      (l.length_take n).trans <| min_eq_left <| le_of_not_ge h₃⟩
  · rw [ENat.iSup_coe_lt_top] at ha
    -- ⊢ ∃ l, l ∈ subchain s ∧ length l = n
    obtain ⟨⟨l, h₁, h₂⟩, e : l.length = _⟩ := Nat.sSup_mem (Set.range_nonempty _) ha
    -- ⊢ ∃ l, l ∈ subchain s ∧ length l = n
    refine'
      ⟨l.take n, ⟨h₁.take _, fun x h ↦ h₂ _ <| take_subset _ _ h⟩,
        (l.length_take n).trans <| min_eq_left <| _⟩
    rwa [e, ← Nat.cast_le (α := ℕ∞), sSup_range, ENat.coe_iSup ha, ← chainHeight_eq_iSup_subtype]
    -- 🎉 no goals
#align set.exists_chain_of_le_chain_height Set.exists_chain_of_le_chainHeight

theorem le_chainHeight_TFAE (n : ℕ) :
    TFAE [↑n ≤ s.chainHeight, ∃ l ∈ s.subchain, length l = n, ∃ l ∈ s.subchain, n ≤ length l] := by
  tfae_have 1 → 2; · exact s.exists_chain_of_le_chainHeight
  -- ⊢ ↑n ≤ chainHeight s → ∃ l, l ∈ subchain s ∧ length l = n
                     -- 🎉 no goals
  tfae_have 2 → 3; · rintro ⟨l, hls, he⟩; exact ⟨l, hls, he.ge⟩
  -- ⊢ (∃ l, l ∈ subchain s ∧ length l = n) → ∃ l, l ∈ subchain s ∧ n ≤ length l
                     -- ⊢ ∃ l, l ∈ subchain s ∧ n ≤ length l
                                          -- 🎉 no goals
  tfae_have 3 → 1; · rintro ⟨l, hs, hn⟩; exact le_iSup₂_of_le l hs (WithTop.coe_le_coe.2 hn)
  -- ⊢ (∃ l, l ∈ subchain s ∧ n ≤ length l) → ↑n ≤ chainHeight s
                     -- ⊢ ↑n ≤ chainHeight s
                                         -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align set.le_chain_height_tfae Set.le_chainHeight_TFAE

variable {s t}

theorem le_chainHeight_iff {n : ℕ} : ↑n ≤ s.chainHeight ↔ ∃ l ∈ s.subchain, length l = n :=
  (le_chainHeight_TFAE s n).out 0 1
#align set.le_chain_height_iff Set.le_chainHeight_iff

theorem length_le_chainHeight_of_mem_subchain (hl : l ∈ s.subchain) : ↑l.length ≤ s.chainHeight :=
  le_chainHeight_iff.mpr ⟨l, hl, rfl⟩
#align set.length_le_chain_height_of_mem_subchain Set.length_le_chainHeight_of_mem_subchain

theorem chainHeight_eq_top_iff : s.chainHeight = ⊤ ↔ ∀ n, ∃ l ∈ s.subchain, length l = n := by
  refine' ⟨fun h n ↦ le_chainHeight_iff.1 (le_top.trans_eq h.symm), fun h ↦ _⟩
  -- ⊢ chainHeight s = ⊤
  contrapose! h; obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h
  -- ⊢ ∃ n, ∀ (l : List α), l ∈ subchain s → length l ≠ n
                 -- ⊢ ∃ n, ∀ (l : List α), l ∈ subchain s → length l ≠ n
  exact ⟨n + 1, fun l hs ↦ (Nat.lt_succ_iff.2 <| Nat.cast_le.1 <|
    (length_le_chainHeight_of_mem_subchain hs).trans_eq hn.symm).ne⟩
#align set.chain_height_eq_top_iff Set.chainHeight_eq_top_iff

@[simp]
theorem one_le_chainHeight_iff : 1 ≤ s.chainHeight ↔ s.Nonempty := by
  rw [← Nat.cast_one, Set.le_chainHeight_iff]
  -- ⊢ (∃ l, l ∈ subchain s ∧ length l = 1) ↔ Set.Nonempty s
  simp only [length_eq_one, @and_comm (_ ∈ _), @eq_comm _ _ [_], exists_exists_eq_and,
    singleton_mem_subchain_iff, Set.Nonempty]
#align set.one_le_chain_height_iff Set.one_le_chainHeight_iff

@[simp]
theorem chainHeight_eq_zero_iff : s.chainHeight = 0 ↔ s = ∅ := by
  rw [← not_iff_not, ← Ne.def, ← ENat.one_le_iff_ne_zero, one_le_chainHeight_iff,
    nonempty_iff_ne_empty]
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
  simp_rw [← tsub_le_iff_right, ← ENat.coe_sub, (le_chainHeight_TFAE s (n - m)).out 0 2]
  -- 🎉 no goals
#align set.le_chain_height_add_nat_iff Set.le_chainHeight_add_nat_iff

theorem chainHeight_add_le_chainHeight_add (s : Set α) (t : Set β) (n m : ℕ) :
    s.chainHeight + n ≤ t.chainHeight + m ↔
      ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l + n ≤ length l' + m := by
  refine'
    ⟨fun e l h ↦
      le_chainHeight_add_nat_iff.1
        ((add_le_add_right (length_le_chainHeight_of_mem_subchain h) _).trans e),
      fun H ↦ _⟩
  by_cases s.chainHeight = ⊤
  -- ⊢ chainHeight s + ↑n ≤ chainHeight t + ↑m
  -- ⊢ chainHeight s + ↑n ≤ chainHeight t + ↑m
  · suffices t.chainHeight = ⊤ by
      rw [this, top_add]
      exact le_top
    rw [chainHeight_eq_top_iff] at h ⊢
    -- ⊢ ∀ (n : ℕ), ∃ l, l ∈ subchain t ∧ length l = n
    intro k
    -- ⊢ ∃ l, l ∈ subchain t ∧ length l = k
    have := (le_chainHeight_TFAE t k).out 1 2
    -- ⊢ ∃ l, l ∈ subchain t ∧ length l = k
    rw [this]
    -- ⊢ ∃ l, l ∈ subchain t ∧ k ≤ length l
    obtain ⟨l, hs, hl⟩ := h (k + m)
    -- ⊢ ∃ l, l ∈ subchain t ∧ k ≤ length l
    obtain ⟨l', ht, hl'⟩ := H l hs
    -- ⊢ ∃ l, l ∈ subchain t ∧ k ≤ length l
    exact ⟨l', ht, (add_le_add_iff_right m).1 <| _root_.trans (hl.symm.trans_le le_self_add) hl'⟩
    -- 🎉 no goals
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 h
    -- ⊢ chainHeight s + ↑n ≤ chainHeight t + ↑m
    obtain ⟨l, hs, hl⟩ := le_chainHeight_iff.1 hk.le
    -- ⊢ chainHeight s + ↑n ≤ chainHeight t + ↑m
    rw [← hk, ← hl]
    -- ⊢ ↑(length l) + ↑n ≤ chainHeight t + ↑m
    exact le_chainHeight_add_nat_iff.2 (H l hs)
    -- 🎉 no goals
#align set.chain_height_add_le_chain_height_add Set.chainHeight_add_le_chainHeight_add

theorem chainHeight_le_chainHeight_TFAE (s : Set α) (t : Set β) :
    TFAE [s.chainHeight ≤ t.chainHeight, ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l = length l',
      ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l ≤ length l'] := by
  tfae_have 1 ↔ 3
  -- ⊢ chainHeight s ≤ chainHeight t ↔ ∀ (l : List α), l ∈ subchain s → ∃ l', l' ∈  …
  · convert ← chainHeight_add_le_chainHeight_add s t 0 0 <;> apply add_zero
    -- ⊢ chainHeight s + ↑0 = chainHeight s
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
  tfae_have 2 ↔ 3
  -- ⊢ (∀ (l : List α), l ∈ subchain s → ∃ l', l' ∈ subchain t ∧ length l = length  …
  · refine' forall₂_congr fun l hl ↦ _
    -- ⊢ (∃ l', l' ∈ subchain t ∧ length l = length l') ↔ ∃ l', l' ∈ subchain t ∧ len …
    simp_rw [← (le_chainHeight_TFAE t l.length).out 1 2, eq_comm]
    -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align set.chain_height_le_chain_height_tfae Set.chainHeight_le_chainHeight_TFAE

theorem chainHeight_le_chainHeight_iff {t : Set β} :
    s.chainHeight ≤ t.chainHeight ↔ ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l = length l' :=
  (chainHeight_le_chainHeight_TFAE s t).out 0 1
#align set.chain_height_le_chain_height_iff Set.chainHeight_le_chainHeight_iff

theorem chainHeight_le_chainHeight_iff_le {t : Set β} :
    s.chainHeight ≤ t.chainHeight ↔ ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l ≤ length l' :=
  (chainHeight_le_chainHeight_TFAE s t).out 0 2
#align set.chain_height_le_chain_height_iff_le Set.chainHeight_le_chainHeight_iff_le

theorem chainHeight_mono (h : s ⊆ t) : s.chainHeight ≤ t.chainHeight :=
  chainHeight_le_chainHeight_iff.2 fun l hl ↦ ⟨l, ⟨hl.1, fun i hi ↦ h <| hl.2 i hi⟩, rfl⟩
#align set.chain_height_mono Set.chainHeight_mono

theorem chainHeight_image (f : α → β) (hf : ∀ {x y}, x < y ↔ f x < f y) (s : Set α) :
    (f '' s).chainHeight = s.chainHeight := by
  apply le_antisymm <;> rw [chainHeight_le_chainHeight_iff]
  -- ⊢ chainHeight (f '' s) ≤ chainHeight s
                        -- ⊢ ∀ (l : List β), l ∈ subchain (f '' s) → ∃ l', l' ∈ subchain s ∧ length l = l …
                        -- ⊢ ∀ (l : List α), l ∈ subchain s → ∃ l', l' ∈ subchain (f '' s) ∧ length l = l …
  · suffices ∀ l ∈ (f '' s).subchain, ∃ l' ∈ s.subchain, map f l' = l by
      intro l hl
      obtain ⟨l', h₁, rfl⟩ := this l hl
      exact ⟨l', h₁, length_map _ _⟩
    intro l
    -- ⊢ l ∈ subchain (f '' s) → ∃ l', l' ∈ subchain s ∧ map f l' = l
    induction' l with x xs hx
    -- ⊢ [] ∈ subchain (f '' s) → ∃ l', l' ∈ subchain s ∧ map f l' = []
    · exact fun _ ↦ ⟨nil, ⟨trivial, fun x h ↦ (not_mem_nil x h).elim⟩, rfl⟩
      -- 🎉 no goals
    · intro h
      -- ⊢ ∃ l', l' ∈ subchain s ∧ map f l' = x :: xs
      rw [cons_mem_subchain_iff] at h
      -- ⊢ ∃ l', l' ∈ subchain s ∧ map f l' = x :: xs
      obtain ⟨⟨x, hx', rfl⟩, h₁, h₂⟩ := h
      -- ⊢ ∃ l', l' ∈ subchain s ∧ map f l' = f x :: xs
      obtain ⟨l', h₃, rfl⟩ := hx h₁
      -- ⊢ ∃ l'_1, l'_1 ∈ subchain s ∧ map f l'_1 = f x :: map f l'
      refine' ⟨x::l', Set.cons_mem_subchain_iff.mpr ⟨hx', h₃, _⟩, rfl⟩
      -- ⊢ ∀ (b : α), b ∈ head? l' → x < b
      cases l'
      -- ⊢ ∀ (b : α), b ∈ head? [] → x < b
      · simp
        -- 🎉 no goals
      · simpa [← hf] using h₂
        -- 🎉 no goals
  · intro l hl
    -- ⊢ ∃ l', l' ∈ subchain (f '' s) ∧ length l = length l'
    refine' ⟨l.map f, ⟨_, _⟩, _⟩
    · simp_rw [chain'_map, ← hf]
      -- ⊢ Chain' (fun a b => a < b) l
      exact hl.1
      -- 🎉 no goals
    · intro _ e
      -- ⊢ i✝ ∈ f '' s
      obtain ⟨a, ha, rfl⟩ := mem_map.mp e
      -- ⊢ f a ∈ f '' s
      exact Set.mem_image_of_mem _ (hl.2 _ ha)
      -- 🎉 no goals
    · rw [length_map]
      -- 🎉 no goals
#align set.chain_height_image Set.chainHeight_image

variable (s)

@[simp]
theorem chainHeight_dual : (ofDual ⁻¹' s).chainHeight = s.chainHeight := by
  apply le_antisymm <;>
  -- ⊢ chainHeight (↑ofDual ⁻¹' s) ≤ chainHeight s
  · rw [chainHeight_le_chainHeight_iff]
    -- ⊢ ∀ (l : List αᵒᵈ), l ∈ subchain (↑ofDual ⁻¹' s) → ∃ l', l' ∈ subchain s ∧ len …
    -- ⊢ ∀ (l : List α), l ∈ subchain s → ∃ l', l' ∈ subchain (↑ofDual ⁻¹' s) ∧ lengt …
    -- ⊢ ∃ l', l' ∈ subchain s ∧ length l = length l'
    rintro l ⟨h₁, h₂⟩
    -- ⊢ ∃ l', l' ∈ subchain (↑ofDual ⁻¹' s) ∧ length l = length l'
    exact ⟨l.reverse, ⟨chain'_reverse.mpr h₁, fun i h ↦ h₂ i (mem_reverse.mp h)⟩,
      (length_reverse _).symm⟩
#align set.chain_height_dual Set.chainHeight_dual

end LT

section Preorder

variable (s t : Set α) [Preorder α]

theorem chainHeight_eq_iSup_Ici : s.chainHeight = ⨆ i ∈ s, (s ∩ Set.Ici i).chainHeight := by
  apply le_antisymm
  -- ⊢ chainHeight s ≤ ⨆ (i : α) (_ : i ∈ s), chainHeight (s ∩ Ici i)
  · refine' iSup₂_le _
    -- ⊢ ∀ (i : List α), i ∈ subchain s → ↑(length i) ≤ ⨆ (i : α) (_ : i ∈ s), chainH …
    rintro (_ | ⟨x, xs⟩) h
    -- ⊢ ↑(length []) ≤ ⨆ (i : α) (_ : i ∈ s), chainHeight (s ∩ Ici i)
    · exact zero_le _
      -- 🎉 no goals
    · apply le_trans _ (le_iSup₂ x (cons_mem_subchain_iff.mp h).1)
      -- ⊢ ↑(length (x :: xs)) ≤ chainHeight (s ∩ Ici x)
      apply length_le_chainHeight_of_mem_subchain
      -- ⊢ x :: xs ∈ subchain (s ∩ Ici x)
      refine' ⟨h.1, fun i hi ↦ ⟨h.2 i hi, _⟩⟩
      -- ⊢ i ∈ Ici x
      cases hi
      -- ⊢ x ∈ Ici x
      · exact left_mem_Ici
        -- 🎉 no goals
      rename_i hi
      -- ⊢ i ∈ Ici x
      cases' chain'_iff_pairwise.mp h.1 with _ _ h'
      -- ⊢ i ∈ Ici x
      exact (h' _ hi).le
      -- 🎉 no goals
  · exact iSup₂_le fun i _ ↦ chainHeight_mono <| Set.inter_subset_left _ _
    -- 🎉 no goals
#align set.chain_height_eq_supr_Ici Set.chainHeight_eq_iSup_Ici

theorem chainHeight_eq_iSup_Iic : s.chainHeight = ⨆ i ∈ s, (s ∩ Set.Iic i).chainHeight := by
  simp_rw [← chainHeight_dual (_ ∩ _)]
  -- ⊢ chainHeight s = ⨆ (i : α) (_ : i ∈ s), chainHeight (↑ofDual ⁻¹' (s ∩ Iic i))
  rw [← chainHeight_dual, chainHeight_eq_iSup_Ici]
  -- ⊢ ⨆ (i : αᵒᵈ) (_ : i ∈ ↑ofDual ⁻¹' s), chainHeight (↑ofDual ⁻¹' s ∩ Ici i) = ⨆ …
  rfl
  -- 🎉 no goals
#align set.chain_height_eq_supr_Iic Set.chainHeight_eq_iSup_Iic

variable {s t}

theorem chainHeight_insert_of_forall_gt (a : α) (hx : ∀ b ∈ s, a < b) :
    (insert a s).chainHeight = s.chainHeight + 1 := by
  rw [← add_zero (insert a s).chainHeight]
  -- ⊢ chainHeight (insert a s) + 0 = chainHeight s + 1
  change (insert a s).chainHeight + (0 : ℕ) = s.chainHeight + (1 : ℕ)
  -- ⊢ chainHeight (insert a s) + ↑0 = chainHeight s + ↑1
  apply le_antisymm <;> rw [chainHeight_add_le_chainHeight_add]
  -- ⊢ chainHeight (insert a s) + ↑0 ≤ chainHeight s + ↑1
                        -- ⊢ ∀ (l : List α), l ∈ subchain (insert a s) → ∃ l', l' ∈ subchain s ∧ length l …
                        -- ⊢ ∀ (l : List α), l ∈ subchain s → ∃ l', l' ∈ subchain (insert a s) ∧ length l …
  · rintro (_ | ⟨y, ys⟩) h
    -- ⊢ ∃ l', l' ∈ subchain s ∧ length [] + 0 ≤ length l' + 1
    · exact ⟨[], nil_mem_subchain _, zero_le _⟩
      -- 🎉 no goals
    · have h' := cons_mem_subchain_iff.mp h
      -- ⊢ ∃ l', l' ∈ subchain s ∧ length (y :: ys) + 0 ≤ length l' + 1
      refine' ⟨ys, ⟨h'.2.1.1, fun i hi ↦ _⟩, by simp⟩
      -- ⊢ i ∈ s
      apply (h'.2.1.2 i hi).resolve_left
      -- ⊢ ¬i = a
      rintro rfl
      -- ⊢ False
      cases' chain'_iff_pairwise.mp h.1 with _ _ hy
      -- ⊢ False
      cases' h'.1 with h' h'
      -- ⊢ False
      exacts [(hy _ hi).ne h', not_le_of_gt (hy _ hi) (hx _ h').le]
      -- 🎉 no goals
  · intro l hl
    -- ⊢ ∃ l', l' ∈ subchain (insert a s) ∧ length l + 1 ≤ length l' + 0
    refine' ⟨a::l, ⟨_, _⟩, by simp⟩
    -- ⊢ Chain' (fun x x_1 => x < x_1) (a :: l)
    · rw [chain'_cons']
      -- ⊢ (∀ (y : α), y ∈ head? l → a < y) ∧ Chain' (fun x x_1 => x < x_1) l
      exact ⟨fun y hy ↦ hx _ (hl.2 _ (mem_of_mem_head? hy)), hl.1⟩
      -- 🎉 no goals
    · -- Porting note: originally this was
        -- rintro x (rfl | hx)
        -- exacts [Or.inl (Set.mem_singleton x), Or.inr (hl.2 x hx)]
      -- but this fails because `List.Mem` is now an inductive prop.
      -- I couldn't work out how to drive `rcases` here but asked at
      -- https://leanprover.zulipchat.com/#narrow/stream/348111-std4/topic/rcases.3F/near/347976083
      rintro x (_ | _)
      -- ⊢ a ∈ insert a s
      exacts [Or.inl (Set.mem_singleton a), Or.inr (hl.2 x ‹_›)]
      -- 🎉 no goals
#align set.chain_height_insert_of_forall_gt Set.chainHeight_insert_of_forall_gt

theorem chainHeight_insert_of_forall_lt (a : α) (ha : ∀ b ∈ s, b < a) :
    (insert a s).chainHeight = s.chainHeight + 1 := by
  rw [← chainHeight_dual, ← chainHeight_dual s]
  -- ⊢ chainHeight (↑ofDual ⁻¹' insert a s) = chainHeight (↑ofDual ⁻¹' s) + 1
  exact chainHeight_insert_of_forall_gt _ ha
  -- 🎉 no goals
#align set.chain_height_insert_of_forall_lt Set.chainHeight_insert_of_forall_lt

theorem chainHeight_union_le : (s ∪ t).chainHeight ≤ s.chainHeight + t.chainHeight := by
  classical
    refine' iSup₂_le fun l hl ↦ _
    let l₁ := l.filter (· ∈ s)
    let l₂ := l.filter (· ∈ t)
    have hl₁ : ↑l₁.length ≤ s.chainHeight := by
      apply Set.length_le_chainHeight_of_mem_subchain
      exact ⟨hl.1.sublist (filter_sublist _), fun i h ↦ by simpa using (of_mem_filter h : _)⟩
    have hl₂ : ↑l₂.length ≤ t.chainHeight := by
      apply Set.length_le_chainHeight_of_mem_subchain
      exact ⟨hl.1.sublist (filter_sublist _), fun i h ↦ by simpa using (of_mem_filter h : _)⟩
    refine' le_trans _ (add_le_add hl₁ hl₂)
    simp_rw [← Nat.cast_add, ← Multiset.coe_card, ← Multiset.card_add, ← Multiset.coe_filter]
    rw [Multiset.filter_add_filter, Multiset.filter_eq_self.mpr, Multiset.card_add, Nat.cast_add]
    exacts [le_add_right rfl.le, hl.2]
#align set.chain_height_union_le Set.chainHeight_union_le

theorem chainHeight_union_eq (s t : Set α) (H : ∀ a ∈ s, ∀ b ∈ t, a < b) :
    (s ∪ t).chainHeight = s.chainHeight + t.chainHeight := by
  cases h : t.chainHeight
  -- ⊢ chainHeight (s ∪ t) = chainHeight s + none
  · rw [WithTop.none_eq_top, add_top, eq_top_iff, ← WithTop.none_eq_top, ← h]
    -- ⊢ chainHeight t ≤ chainHeight (s ∪ t)
    exact Set.chainHeight_mono (Set.subset_union_right _ _)
    -- 🎉 no goals
  apply le_antisymm
  -- ⊢ chainHeight (s ∪ t) ≤ chainHeight s + some val✝
  · rw [← h]
    -- ⊢ chainHeight (s ∪ t) ≤ chainHeight s + chainHeight t
    exact chainHeight_union_le
    -- 🎉 no goals
  rw [WithTop.some_eq_coe, ← add_zero (s ∪ t).chainHeight, ← WithTop.coe_zero,
    ENat.some_eq_coe, chainHeight_add_le_chainHeight_add]
  intro l hl
  -- ⊢ ∃ l', l' ∈ subchain (s ∪ t) ∧ length l + val✝ ≤ length l' + 0
  obtain ⟨l', hl', rfl⟩ := exists_chain_of_le_chainHeight t h.symm.le
  -- ⊢ ∃ l'_1, l'_1 ∈ subchain (s ∪ t) ∧ length l + length l' ≤ length l'_1 + 0
  refine' ⟨l ++ l', ⟨Chain'.append hl.1 hl'.1 fun x hx y hy ↦ _, fun i hi ↦ _⟩, by simp⟩
  -- ⊢ x < y
  · exact H x (hl.2 _ <| mem_of_mem_getLast? hx) y (hl'.2 _ <| mem_of_mem_head? hy)
    -- 🎉 no goals
  · rw [mem_append] at hi
    -- ⊢ i ∈ s ∪ t
    cases' hi with hi hi
    -- ⊢ i ∈ s ∪ t
    exacts [Or.inl (hl.2 _ hi), Or.inr (hl'.2 _ hi)]
    -- 🎉 no goals
#align set.chain_height_union_eq Set.chainHeight_union_eq

theorem wellFoundedGT_of_chainHeight_ne_top (s : Set α) (hs : s.chainHeight ≠ ⊤) :
    WellFoundedGT s := by
  -- Porting note: added
  haveI : IsTrans { x // x ∈ s } (↑· < ↑·) := inferInstance
  -- ⊢ WellFoundedGT ↑s

  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hs
  -- ⊢ WellFoundedGT ↑s
  refine' ⟨RelEmbedding.wellFounded_iff_no_descending_seq.2 ⟨fun f ↦ _⟩⟩
  -- ⊢ False
  refine' n.lt_succ_self.not_le (WithTop.coe_le_coe.1 <| hn.symm ▸ _)
  -- ⊢ ↑(Nat.succ n) ≤ chainHeight s
  refine'
    le_iSup₂_of_le _
      ⟨chain'_map_of_chain' ((↑) : {x // x ∈ s} → α) (fun _ _ ↦ id)
          (chain'_iff_pairwise.2 <| pairwise_ofFn.2 fun i j ↦ f.map_rel_iff.2),
        fun i h ↦ _⟩
      _
  · exact n.succ
    -- 🎉 no goals
  · obtain ⟨a, -, rfl⟩ := mem_map.1 h
    -- ⊢ ↑a ∈ s
    exact a.prop
    -- 🎉 no goals
  · rw [length_map, length_ofFn]
    -- ⊢ ↑(Nat.succ n) ≤ ↑(Nat.succ n)
    exact le_rfl
    -- 🎉 no goals
#align set.well_founded_gt_of_chain_height_ne_top Set.wellFoundedGT_of_chainHeight_ne_top

theorem wellFoundedLT_of_chainHeight_ne_top (s : Set α) (hs : s.chainHeight ≠ ⊤) :
    WellFoundedLT s :=
  wellFoundedGT_of_chainHeight_ne_top (ofDual ⁻¹' s) <| by rwa [chainHeight_dual]
                                                           -- 🎉 no goals
#align set.well_founded_lt_of_chain_height_ne_top Set.wellFoundedLT_of_chainHeight_ne_top

end Preorder

end Set
