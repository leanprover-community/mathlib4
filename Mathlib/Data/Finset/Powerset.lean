/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Multiset.Powerset

#align_import data.finset.powerset from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# The powerset of a finset
-/


namespace Finset

open Function Multiset

variable {α : Type*} {s t : Finset α}

/-! ### powerset -/


section Powerset

/-- When `s` is a finset, `s.powerset` is the finset of all subsets of `s` (seen as finsets). -/
def powerset (s : Finset α) : Finset (Finset α) :=
  ⟨(s.1.powerset.pmap Finset.mk) fun _t h => nodup_of_le (mem_powerset.1 h) s.nodup,
    s.nodup.powerset.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩
#align finset.powerset Finset.powerset

@[simp]
theorem mem_powerset {s t : Finset α} : s ∈ powerset t ↔ s ⊆ t := by
  cases s
  simp [powerset, mem_mk, mem_pmap, mk.injEq, mem_powerset, exists_prop, exists_eq_right,
    ← val_le_iff]
#align finset.mem_powerset Finset.mem_powerset

@[simp, norm_cast]
theorem coe_powerset (s : Finset α) :
    (s.powerset : Set (Finset α)) = ((↑) : Finset α → Set α) ⁻¹' (s : Set α).powerset := by
  ext
  simp
#align finset.coe_powerset Finset.coe_powerset

-- Porting note: remove @[simp], simp can prove it
theorem empty_mem_powerset (s : Finset α) : ∅ ∈ powerset s :=
  mem_powerset.2 (empty_subset _)
#align finset.empty_mem_powerset Finset.empty_mem_powerset

-- Porting note: remove @[simp], simp can prove it
theorem mem_powerset_self (s : Finset α) : s ∈ powerset s :=
  mem_powerset.2 Subset.rfl
#align finset.mem_powerset_self Finset.mem_powerset_self

@[aesop safe apply (rule_sets := [finsetNonempty])]
theorem powerset_nonempty (s : Finset α) : s.powerset.Nonempty :=
  ⟨∅, empty_mem_powerset _⟩
#align finset.powerset_nonempty Finset.powerset_nonempty

@[simp]
theorem powerset_mono {s t : Finset α} : powerset s ⊆ powerset t ↔ s ⊆ t :=
  ⟨fun h => mem_powerset.1 <| h <| mem_powerset_self _, fun st _u h =>
    mem_powerset.2 <| Subset.trans (mem_powerset.1 h) st⟩
#align finset.powerset_mono Finset.powerset_mono

theorem powerset_injective : Injective (powerset : Finset α → Finset (Finset α)) :=
  (injective_of_le_imp_le _) powerset_mono.1
#align finset.powerset_injective Finset.powerset_injective

@[simp]
theorem powerset_inj : powerset s = powerset t ↔ s = t :=
  powerset_injective.eq_iff
#align finset.powerset_inj Finset.powerset_inj

@[simp]
theorem powerset_empty : (∅ : Finset α).powerset = {∅} :=
  rfl
#align finset.powerset_empty Finset.powerset_empty

@[simp]
theorem powerset_eq_singleton_empty : s.powerset = {∅} ↔ s = ∅ := by
  rw [← powerset_empty, powerset_inj]
#align finset.powerset_eq_singleton_empty Finset.powerset_eq_singleton_empty

/-- **Number of Subsets of a Set** -/
@[simp]
theorem card_powerset (s : Finset α) : card (powerset s) = 2 ^ card s :=
  (card_pmap _ _ _).trans (Multiset.card_powerset s.1)
#align finset.card_powerset Finset.card_powerset

theorem not_mem_of_mem_powerset_of_not_mem {s t : Finset α} {a : α} (ht : t ∈ s.powerset)
    (h : a ∉ s) : a ∉ t := by
  apply mt _ h
  apply mem_powerset.1 ht
#align finset.not_mem_of_mem_powerset_of_not_mem Finset.not_mem_of_mem_powerset_of_not_mem

theorem powerset_insert [DecidableEq α] (s : Finset α) (a : α) :
    powerset (insert a s) = s.powerset ∪ s.powerset.image (insert a) := by
  ext t
  simp only [exists_prop, mem_powerset, mem_image, mem_union, subset_insert_iff]
  by_cases h : a ∈ t
  · constructor
    · exact fun H => Or.inr ⟨_, H, insert_erase h⟩
    · intro H
      cases' H with H H
      · exact Subset.trans (erase_subset a t) H
      · rcases H with ⟨u, hu⟩
        rw [← hu.2]
        exact Subset.trans (erase_insert_subset a u) hu.1
  · have : ¬∃ u : Finset α, u ⊆ s ∧ insert a u = t := by simp [Ne.symm (ne_insert_of_not_mem _ _ h)]
    simp [Finset.erase_eq_of_not_mem h, this]
#align finset.powerset_insert Finset.powerset_insert

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for any subset. -/
instance decidableExistsOfDecidableSubsets {s : Finset α} {p : ∀ t ⊆ s, Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∃ (t : _) (h : t ⊆ s), p t h) :=
  decidable_of_iff (∃ (t : _) (hs : t ∈ s.powerset), p t (mem_powerset.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_powerset.2 hs, hp⟩⟩
#align finset.decidable_exists_of_decidable_subsets Finset.decidableExistsOfDecidableSubsets

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for every subset. -/
instance decidableForallOfDecidableSubsets {s : Finset α} {p : ∀ t ⊆ s, Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∀ (t) (h : t ⊆ s), p t h) :=
  decidable_of_iff (∀ (t) (h : t ∈ s.powerset), p t (mem_powerset.1 h))
    ⟨fun h t hs => h t (mem_powerset.2 hs), fun h _ _ => h _ _⟩
#align finset.decidable_forall_of_decidable_subsets Finset.decidableForallOfDecidableSubsets

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for any subset. -/
instance decidableExistsOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop}
    [∀ t, Decidable (p t)] : Decidable (∃ t ⊆ s, p t) :=
  decidable_of_iff (∃ (t : _) (_h : t ⊆ s), p t) $ by simp
#align finset.decidable_exists_of_decidable_subsets' Finset.decidableExistsOfDecidableSubsets'

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for every subset. -/
instance decidableForallOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop}
    [∀ t, Decidable (p t)] : Decidable (∀ t ⊆ s, p t) :=
  decidable_of_iff (∀ (t : _) (_h : t ⊆ s), p t) $ by simp
#align finset.decidable_forall_of_decidable_subsets' Finset.decidableForallOfDecidableSubsets'

end Powerset

section SSubsets

variable [DecidableEq α]

/-- For `s` a finset, `s.ssubsets` is the finset comprising strict subsets of `s`. -/
def ssubsets (s : Finset α) : Finset (Finset α) :=
  erase (powerset s) s
#align finset.ssubsets Finset.ssubsets

@[simp]
theorem mem_ssubsets {s t : Finset α} : t ∈ s.ssubsets ↔ t ⊂ s := by
  rw [ssubsets, mem_erase, mem_powerset, ssubset_iff_subset_ne, and_comm]
#align finset.mem_ssubsets Finset.mem_ssubsets

theorem empty_mem_ssubsets {s : Finset α} (h : s.Nonempty) : ∅ ∈ s.ssubsets := by
  rw [mem_ssubsets, ssubset_iff_subset_ne]
  exact ⟨empty_subset s, h.ne_empty.symm⟩
#align finset.empty_mem_ssubsets Finset.empty_mem_ssubsets

/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for any ssubset. -/
def decidableExistsOfDecidableSSubsets {s : Finset α} {p : ∀ t ⊂ s, Prop}
    [∀ t h, Decidable (p t h)] : Decidable (∃ t h, p t h) :=
  decidable_of_iff (∃ (t : _) (hs : t ∈ s.ssubsets), p t (mem_ssubsets.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_ssubsets.2 hs, hp⟩⟩
#align finset.decidable_exists_of_decidable_ssubsets Finset.decidableExistsOfDecidableSSubsets

/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for every ssubset. -/
def decidableForallOfDecidableSSubsets {s : Finset α} {p : ∀ t ⊂ s, Prop}
    [∀ t h, Decidable (p t h)] : Decidable (∀ t h, p t h) :=
  decidable_of_iff (∀ (t) (h : t ∈ s.ssubsets), p t (mem_ssubsets.1 h))
    ⟨fun h t hs => h t (mem_ssubsets.2 hs), fun h _ _ => h _ _⟩
#align finset.decidable_forall_of_decidable_ssubsets Finset.decidableForallOfDecidableSSubsets

/-- A version of `Finset.decidableExistsOfDecidableSSubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableExistsOfDecidableSSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ t ⊂ s, Decidable (p t)) : Decidable (∃ (t : _) (_h : t ⊂ s), p t) :=
  @Finset.decidableExistsOfDecidableSSubsets _ _ _ _ hu
#align finset.decidable_exists_of_decidable_ssubsets' Finset.decidableExistsOfDecidableSSubsets'

/-- A version of `Finset.decidableForallOfDecidableSSubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableForallOfDecidableSSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ t ⊂ s, Decidable (p t)) : Decidable (∀ t ⊂ s, p t) :=
  @Finset.decidableForallOfDecidableSSubsets _ _ _ _ hu
#align finset.decidable_forall_of_decidable_ssubsets' Finset.decidableForallOfDecidableSSubsets'

end SSubsets

section powersetCard
variable {n} {s t : Finset α}

/-- Given an integer `n` and a finset `s`, then `powersetCard n s` is the finset of subsets of `s`
of cardinality `n`. -/
def powersetCard (n : ℕ) (s : Finset α) : Finset (Finset α) :=
  ⟨((s.1.powersetCard n).pmap Finset.mk) fun _t h => nodup_of_le (mem_powersetCard.1 h).1 s.2,
    s.2.powersetCard.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩
#align finset.powerset_len Finset.powersetCard

@[simp] lemma mem_powersetCard : s ∈ powersetCard n t ↔ s ⊆ t ∧ card s = n := by
  cases s; simp [powersetCard, val_le_iff.symm]
#align finset.mem_powerset_len Finset.mem_powersetCard

@[simp]
theorem powersetCard_mono {n} {s t : Finset α} (h : s ⊆ t) : powersetCard n s ⊆ powersetCard n t :=
  fun _u h' => mem_powersetCard.2 <|
    And.imp (fun h₂ => Subset.trans h₂ h) id (mem_powersetCard.1 h')
#align finset.powerset_len_mono Finset.powersetCard_mono

/-- **Formula for the Number of Combinations** -/
@[simp]
theorem card_powersetCard (n : ℕ) (s : Finset α) :
    card (powersetCard n s) = Nat.choose (card s) n :=
  (card_pmap _ _ _).trans (Multiset.card_powersetCard n s.1)
#align finset.card_powerset_len Finset.card_powersetCard

@[simp]
theorem powersetCard_zero (s : Finset α) : s.powersetCard 0 = {∅} := by
  ext; rw [mem_powersetCard, mem_singleton, card_eq_zero]
  refine
    ⟨fun h => h.2, fun h => by
      rw [h]
      exact ⟨empty_subset s, rfl⟩⟩
#align finset.powerset_len_zero Finset.powersetCard_zero

lemma powersetCard_empty_subsingleton (n : ℕ) :
    (powersetCard n (∅ : Finset α) : Set $ Finset α).Subsingleton := by
  simp [Set.Subsingleton, subset_empty]

@[simp]
theorem map_val_val_powersetCard (s : Finset α) (i : ℕ) :
    (s.powersetCard i).val.map Finset.val = s.1.powersetCard i := by
  simp [Finset.powersetCard, map_pmap, pmap_eq_map, map_id']
#align finset.map_val_val_powerset_len Finset.map_val_val_powersetCard

theorem powersetCard_one (s : Finset α) :
    s.powersetCard 1 = s.map ⟨_, Finset.singleton_injective⟩ :=
  eq_of_veq <| Multiset.map_injective val_injective <| by simp [Multiset.powersetCard_one]

@[simp]
lemma powersetCard_eq_empty : powersetCard n s = ∅ ↔ s.card < n := by
  refine ⟨?_, fun h ↦ card_eq_zero.1 $ by rw [card_powersetCard, Nat.choose_eq_zero_of_lt h]⟩
  contrapose!
  exact fun h ↦ nonempty_iff_ne_empty.1 $ (exists_subset_card_eq h).imp $ by simp
#align finset.powerset_len_empty Finset.powersetCard_eq_empty

@[simp] lemma powersetCard_card_add (s : Finset α) (hn : 0 < n) :
    s.powersetCard (s.card + n) = ∅ := by simpa
#align finset.powerset_len_card_add Finset.powersetCard_card_add

theorem powersetCard_eq_filter {n} {s : Finset α} :
    powersetCard n s = (powerset s).filter fun x => x.card = n := by
  ext
  simp [mem_powersetCard]
#align finset.powerset_len_eq_filter Finset.powersetCard_eq_filter

theorem powersetCard_succ_insert [DecidableEq α] {x : α} {s : Finset α} (h : x ∉ s) (n : ℕ) :
    powersetCard n.succ (insert x s) =
    powersetCard n.succ s ∪ (powersetCard n s).image (insert x) := by
  rw [powersetCard_eq_filter, powerset_insert, filter_union, ← powersetCard_eq_filter]
  congr
  rw [powersetCard_eq_filter, filter_image]
  congr 1
  ext t
  simp only [mem_powerset, mem_filter, Function.comp_apply, and_congr_right_iff]
  intro ht
  have : x ∉ t := fun H => h (ht H)
  simp [card_insert_of_not_mem this, Nat.succ_inj']
#align finset.powerset_len_succ_insert Finset.powersetCard_succ_insert

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
lemma powersetCard_nonempty : (powersetCard n s).Nonempty ↔ n ≤ s.card := by
  aesop (add simp [Finset.Nonempty, exists_subset_card_eq, card_le_card])
#align finset.powerset_len_nonempty Finset.powersetCard_nonempty

@[simp]
theorem powersetCard_self (s : Finset α) : powersetCard s.card s = {s} := by
  ext
  rw [mem_powersetCard, mem_singleton]
  constructor
  · exact fun ⟨hs, hc⟩ => eq_of_subset_of_card_le hs hc.ge
  · rintro rfl
    simp
#align finset.powerset_len_self Finset.powersetCard_self

theorem pairwise_disjoint_powersetCard (s : Finset α) :
    Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j) := fun _i _j hij =>
  Finset.disjoint_left.mpr fun _x hi hj =>
    hij <| (mem_powersetCard.mp hi).2.symm.trans (mem_powersetCard.mp hj).2
#align finset.pairwise_disjoint_powerset_len Finset.pairwise_disjoint_powersetCard

theorem powerset_card_disjiUnion (s : Finset α) :
    Finset.powerset s =
      (range (s.card + 1)).disjiUnion (fun i => powersetCard i s)
        (s.pairwise_disjoint_powersetCard.set_pairwise _) := by
  refine ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [mem_disjiUnion]
    exact
      ⟨a.card, mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp ha))),
        mem_powersetCard.mpr ⟨mem_powerset.mp ha, rfl⟩⟩
  · rcases mem_disjiUnion.mp ha with ⟨i, _hi, ha⟩
    exact mem_powerset.mpr (mem_powersetCard.mp ha).1
#align finset.powerset_card_disj_Union Finset.powerset_card_disjiUnion

theorem powerset_card_biUnion [DecidableEq (Finset α)] (s : Finset α) :
    Finset.powerset s = (range (s.card + 1)).biUnion fun i => powersetCard i s := by
  simpa only [disjiUnion_eq_biUnion] using powerset_card_disjiUnion s
#align finset.powerset_card_bUnion Finset.powerset_card_biUnion

theorem powersetCard_sup [DecidableEq α] (u : Finset α) (n : ℕ) (hn : n < u.card) :
    (powersetCard n.succ u).sup id = u := by
  apply le_antisymm
  · simp_rw [Finset.sup_le_iff, mem_powersetCard]
    rintro x ⟨h, -⟩
    exact h
  · rw [sup_eq_biUnion, le_iff_subset, subset_iff]
    intro x hx
    simp only [mem_biUnion, exists_prop, id]
    obtain ⟨t, ht⟩ : ∃ t, t ∈ powersetCard n (u.erase x) := powersetCard_nonempty.2
      (le_trans (Nat.le_sub_one_of_lt hn) pred_card_le_card_erase)
    refine ⟨insert x t, ?_, mem_insert_self _ _⟩
    rw [← insert_erase hx, powersetCard_succ_insert (not_mem_erase _ _)]
    exact mem_union_right _ (mem_image_of_mem _ ht)
#align finset.powerset_len_sup Finset.powersetCard_sup

theorem powersetCard_map {β : Type*} (f : α ↪ β) (n : ℕ) (s : Finset α) :
    powersetCard n (s.map f) = (powersetCard n s).map (mapEmbedding f).toEmbedding :=
  ext fun t => by
    simp only [card_map, mem_powersetCard, le_eq_subset, gt_iff_lt, mem_map, mapEmbedding_apply]
    constructor
    · classical
      intro h
      have : map f (filter (fun x => (f x ∈ t)) s) = t := by
        ext x
        simp only [mem_map, mem_filter, decide_eq_true_eq]
        exact ⟨fun ⟨_y, ⟨_hy₁, hy₂⟩, hy₃⟩ => hy₃ ▸ hy₂,
          fun hx => let ⟨y, hy⟩ := mem_map.1 (h.1 hx); ⟨y, ⟨hy.1, hy.2 ▸ hx⟩, hy.2⟩⟩
      refine ⟨_, ?_, this⟩
      rw [← card_map f, this, h.2]; simp
    · rintro ⟨a, ⟨has, rfl⟩, rfl⟩
      dsimp [RelEmbedding.coe_toEmbedding]
      -- Porting note: Why is `rw` required here and not `simp`?
      rw [mapEmbedding_apply]
      simp [has]
#align finset.powerset_len_map Finset.powersetCard_map

end powersetCard

end Finset
