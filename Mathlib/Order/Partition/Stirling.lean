/-
Copyright (c) 2023 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

-/
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Fintype.BigOperators

/-!
# Cardinality of finite partitions

In this file, we calculate the cardinality of finite partitions, also known as
Stirling's number of the second kind.
-/

set_option autoImplicit false

open BigOperators Finset Function

variable {α β : Type _} [DecidableEq α] (s : Finset α)

-- mathlib3/#11932
lemma Finset.supIndep.image {α ι ι' : Type _} [Lattice α] [OrderBot α] [DecidableEq ι]
    {s : Finset ι'} {f : ι → α} {g : ι' ↪ ι} (hs : s.SupIndep (f ∘ g)) :
    (s.image g).SupIndep f := by
  intros t ht i hi hit
  rw [mem_image] at hi
  obtain ⟨i, hi, rfl⟩ := hi
  classical
  suffices hts : t ⊆ (s.erase i).image g
  · refine' (supIndep_iff_disjoint_erase.1 hs i hi).mono_right ((sup_mono hts).trans _)
    rw [sup_image]
  rintro j hjt
  obtain ⟨j, hj, rfl⟩ := mem_image.1 (ht hjt)
  exact mem_image_of_mem _ (mem_erase.2 ⟨ne_of_apply_ne g (ne_of_mem_of_not_mem hjt hit), hj⟩)

-- mathlib3/#11932
lemma Finset.supIndep_map {α ι ι' : Type _} [Lattice α] [OrderBot α] {s : Finset ι'} {f : ι → α}
    {g : ι' ↪ ι} : (s.map g).SupIndep f ↔ s.SupIndep (f ∘ g) := by
  refine' ⟨λ hs t ht i hi hit => _, λ hs => _⟩
  · rw [←sup_map]
    exact hs (map_subset_map.2 ht) ((mem_map' _).2 hi) (by rwa [mem_map'])
  · classical
    rw [map_eq_image]
    exact Finset.supIndep.image hs

@[simp] lemma Finset.subtype_map_subtype {α : Type _} {p : α → Prop} [DecidablePred p]
    (s : Finset (Subtype p)) : Finset.subtype p (s.map (Embedding.subtype p)) = s := by
  ext x
  simp [x.prop]

lemma Finset.isAtom_singleton {α : Type _} (a : α) : IsAtom ({a} : Finset α) :=
⟨by simp, by simp⟩

@[to_additive]
lemma Finset.prod_eq_one_iff {α β : Type _} [CanonicallyOrderedMonoid β] (s : Finset α)
    (f : α → β) : s.prod f = 1 ↔ ∀ x ∈ s, f x = 1 := by
  cases s
  simp [Multiset.prod_eq_one_iff]

lemma Finset.card_le_sum_card_of_ne_empty {α : Type _} (s : Finset (Finset α))
    (hs : ∀ t ∈ s, t ≠ ∅) : card s ≤ s.sum card := by
  induction' s using Finset.cons_induction_on with a s ha IH
  · simp
  · simp only [card_cons, sum_cons]
    simp only [mem_cons, ne_eq, forall_eq_or_imp] at hs
    rw [add_comm]
    refine' add_le_add (card_pos.mpr _) (IH hs.right)
    rw [nonempty_iff_ne_empty]
    exact hs.left

lemma Finset.cons_inj {α : Type _} {x : α} {a b : Finset α} (ha : x ∉ a) (hb : x ∉ b) :
    cons x a ha = cons x b hb ↔ a = b := by
  simp [ext_iff, mem_cons]
  constructor
  · intro h y
    rcases eq_or_ne y x with rfl|hx
    · simp [ha, hb]
    · simpa [hx] using h y
  · intro h y
    simp [h y]

lemma Finset.insert_left_inj {α : Type _} [DecidableEq α] {x : α} {a b : Finset α}
    (ha : x ∉ a) (hb : x ∉ b) : insert x a = insert x b ↔ a = b := by
  rw [←cons_eq_insert _ _ ha, ←cons_eq_insert _ _ hb, cons_inj]

lemma Finset.erase_union_eq_of_mem {α : Type _} [DecidableEq α] {s : Finset α} {x : α} (h : x ∈ s) :
    erase s x ∪ {x} = s := by
  ext y
  rcases eq_or_ne y x with rfl|hy
  · simp [h]
  · simp [hy]

namespace Finpartition

lemma subset_of_mem_parts {s : Finset α} {t : Finpartition s} {x : Finset α}
    (hx : x ∈ t.parts) : x ⊆ s := by
  intro b hb
  rw [←t.supParts, mem_sup]
  exact ⟨x, hx, hb⟩

lemma eq_of_mem_of_mem {s : Finset α} {P : Finpartition s} {x y : Finset α} (hx : x ∈ P.parts)
    (hy : y ∈ P.parts) {a : α} (hxa : a ∈ x) (hya : a ∈ y) : x = y := by
  have := P.supIndep (singleton_subset_iff.mpr hx) hy
  by_contra H
  simp only [mem_singleton, id_eq, sup_singleton] at this
  simpa using this (Ne.symm H) (singleton_subset_iff.mpr hya) (singleton_subset_iff.mpr hxa)

def Equiv_Subtype : Finpartition s ≃
    {parts : Finset (Finset s) // parts.SupIndep id ∧ parts.sup id = univ ∧ ⊥ ∉ parts} where
  toFun := λ ⟨parts, supIndep, supParts, not_bot_mem⟩ => ⟨parts.image (Finset.subtype (· ∈ s)),
    by
      intro t ht i hi hit j hj hj' x hx
      simp only [mem_attach, forall_true_left, Subtype.forall, mem_image] at hi
      obtain ⟨t', ht', rfl⟩ := hi
      have hxt : (x : α) ∈ t'
      · simpa using hj hx
      have hts : (t.map (mapEmbedding <| Embedding.subtype (· ∈ s)).toEmbedding) ⊆ parts
      · refine' (map_subset_map.mpr ht).trans _
        intro x hx
        simp only [le_eq_subset, mem_map, mem_image, mapEmbedding_apply, exists_exists_and_eq_and,
                   subtype_map] at hx
        obtain ⟨x, hx, rfl⟩ := hx
        rwa [(Finset.filter_eq_self x).mpr]
        intros el hel
        rw [←supParts, mem_sup]
        exact ⟨_, hx, hel⟩
      have hji : (j.map (Embedding.subtype (· ∈ s))) ≤ id t'
      · refine' (map_subset_map.mpr hj).trans _
        simp
      have hxj : (x : α) ∈ j.map (Embedding.subtype (· ∈ s))
      · simp [hx]
      specialize supIndep hts ht' _ hji _ hxj
      · contrapose! hit
        simp only [le_eq_subset, mem_map, mapEmbedding_apply] at hit
        obtain ⟨u, hu, rfl⟩ := hit
        simp [hu]
      · rw [sup_map]
        refine' (map_subset_map.mpr hj').trans _
        intro y
        simp only [mem_map, mem_sup, id_eq, Embedding.coe_subtype, Subtype.exists, exists_and_right,
                   exists_eq_right, le_eq_subset, comp.left_id, mapEmbedding_apply,
                   forall_exists_index, and_imp]
        intro hy u hu hy'
        refine' ⟨_, hu, _, hy'⟩
        exact hy
      simp at supIndep,
    by
      rw [←(mapEmbedding (Embedding.subtype (· ∈ s))).apply_eq_iff_eq]
      simp only [le_eq_subset, mapEmbedding_apply, univ_eq_attach, attach_map_val]
      rw [←supParts]
      ext
      simp [mem_sup],
    by
      simp only [bot_eq_empty, mem_image, subtype_eq_empty, ← supParts, mem_sup, id_eq,
                 forall_exists_index, and_imp, not_exists, not_and, not_forall, not_not,
                 exists_prop, exists_and_left]
      intro t ht
      rcases t.eq_empty_or_nonempty with rfl|⟨x, hx⟩
      · exact absurd ht not_bot_mem
      exact ⟨x, t, ht, hx, hx⟩⟩
  invFun := λ ⟨parts, supIndep, supParts, not_bot_mem⟩ =>
    ⟨parts.map (mapEmbedding (Embedding.subtype (· ∈ s))).toEmbedding,
      by
        rw [Finset.supIndep_map]
        simp only [le_eq_subset, comp.left_id]
        intro t ht i hi hit j hj hj' x hx
        specialize hj hx
        simp only [mapEmbedding_apply, mem_map, Embedding.coe_subtype, Subtype.exists,
                   exists_and_right, exists_eq_right] at hj
        obtain ⟨hx', hxi⟩ := hj
        specialize hj' hx
        suffices : {⟨x, hx'⟩} ≤ sup t id
        · simpa using supIndep ht hi hit (singleton_subset_iff.mpr hxi : {⟨x, hx'⟩} ⊆ i) this
        intro z hz
        simp only [mem_singleton] at hz
        subst hz
        simp only [mem_sup, mapEmbedding_apply, mem_map, Embedding.coe_subtype, Subtype.exists,
                    exists_and_right, exists_eq_right] at hj' ⊢
        refine' hj'.imp _
        simp (config := { contextual := true }),
      by
        have : mapEmbedding (Embedding.subtype (· ∈ s)) (univ : Finset s) = s
        · ext
          simp
        simp_rw [←this, ←supParts, sup_map]
        ext
        simp [mem_sup, exists_comm],
      by simpa using not_bot_mem⟩
  left_inv := λ ⟨parts, supIndep, supParts, not_bot_mem⟩ => by
    ext
    simp only [le_eq_subset, mem_map, mem_image, mapEmbedding_apply, exists_exists_and_eq_and,
                subtype_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rwa [(filter_eq_self t).mpr]
      rw [←supParts]
      simp only [mem_sup, id_eq]
      exact λ x hx => ⟨t, ht, hx⟩
    · intro ht
      refine' ⟨_, ht, _⟩
      rw [(filter_eq_self _).mpr]
      rw [←supParts]
      simp only [mem_sup, id_eq]
      exact λ x hx => ⟨_, ht, hx⟩
  right_inv := λ ⟨_, _, _, _⟩ => by ext; simp

-- inefficient construction
-- instance : Fintype (Finpartition s) :=
-- Fintype.ofEquiv _ (Equiv_Subtype s).symm

instance {α : Type _} [DecidableEq α] (a : Finset α) : Fintype (Finpartition a) where
  elems := a.powerset.powerset.image
    (λ p => if h : p.SupIndep id ∧ p.sup id = a ∧ ⊥ ∉ p then ⟨p, h.1, h.2.1, h.2.2⟩ else ⊥)
  complete := by
    rintro p
    rw [Finset.mem_image]
    refine' ⟨p.parts, _, _⟩
    · simp only [Finset.mem_powerset]
      intros i hi
      rw [Finset.mem_powerset]
      exact p.le hi
    · rw [dif_pos]
      simp only [p.supIndep, p.supParts, p.not_bot_mem, eq_self_iff_true, not_false_iff, and_self]

lemma top_eq_indiscrete {α : Type _} [Lattice α] [OrderBot α] {a : α} [Decidable (a = ⊥)]
    (ha : a ≠ ⊥) : (⊤ : Finpartition a) = indiscrete ha := dif_neg ha

@[simp] lemma top_eq_empty (α : Type _) [DecidableEq α] :
    (⊤ : Finpartition (∅ : Finset α)) = Finpartition.empty _ := dif_pos rfl

lemma card_Finpartition_singleton (a : α) : Fintype.card (Finpartition ({a} : Finset α)) = 1 := by
  rw [Fintype.card_eq_one_iff_nonempty_unique]
  refine' ⟨IsAtom.uniqueFinpartition (isAtom_singleton a)⟩
  exact ⊤

theorem exists_lt_of_lt {s : Finset α} {P Q : Finpartition s} (h : P < Q) :
    ∃ b ∈ P.parts, ∃ c ∈ Q.parts, b < c := by
  contrapose! h
  intro H
  rw [lt_iff_le_and_ne] at H
  cases' H with Hle Hne
  rw [Ne.def, Finpartition.ext_iff, Finset.ext_iff] at Hne
  push_neg at Hne
  obtain ⟨b, H⟩ := Hne
  rw [not_iff] at H
  by_cases hb : b ∈ P.parts
  · obtain ⟨c, hc, hbc⟩ := Hle hb
    have := eq_of_le_of_not_lt hbc (h _ hb _ hc)
    subst this
    exact H.mpr hc hb
  · rw [H] at hb
    obtain ⟨c, hc, hbc⟩ := exists_le_of_le Hle hb
    have := eq_of_le_of_not_lt hbc (h _ hc _ hb)
    subst this
    exact H.mpr hb hc

-- theorem card_strict_mono {s : Finset α} {P Q : Finpartition s} (h : P < Q) :
--     Q.parts.card < P.parts.card := by
--   refine' (card_mono h.le).eq_or_lt.resolve_left λ H => _
--   obtain ⟨b, hb, c, hc, hbc⟩ := exists_lt_of_lt h
--   obtain ⟨x, hx, hx'⟩ : ∃ x ∈ c, x ∉ b
--   · simp only [lt_eq_subset, ssubset_iff] at hbc
--     obtain ⟨x, hx, hx'⟩ := hbc
--     exact ⟨x, hx' (mem_insert_self _ _), hx⟩
--   obtain ⟨d, hd, hd'⟩ := P.exists_mem (subset_of_mem_parts hc hx)
--   have hPQ : card (P.parts.erase b) < card Q.parts.attach
--   · rw [card_attach, H]
--     exact card_erase_lt_of_mem hb
--   have : ∀ c ∈ Q.parts, ∃ b ∈ P.parts, b ≤ c := fun c ↦ exists_le_of_le h.le
--   choose f hP hf using this
--   have := exists_ne_map_eq_of_card_lt_of_maps_to hPQ (f := λ p => if x ∈ (p : Finset α) then f c hc else f p p.2)
--   specialize this _
--   · rintro ⟨p, hp⟩
--     simp only [mem_attach, mem_erase, ne_eq, forall_true_left]
--     split_ifs with H
--     · refine' ⟨_, hP _ hc⟩
--       rintro rfl
--     · _

lemma card_parts_eq_card_iff_eq_bot (t : Finpartition s) :
    t.parts.card = s.card ↔ t = ⊥ := by
  constructor
  · intro h
    ext x
    simp only [parts_bot, mem_map, Embedding.coeFn_mk]
    have : ∀ x ∈ t.parts, x.card = 1
    · intro x hx
      refine' le_antisymm _ _
      · rw [←t.sum_card_parts, ←add_sum_erase t.parts _ hx, ←card_erase_add_one hx] at h
        simp only [mem_erase, ne_eq, card_eq_zero, and_imp, self_eq_add_right,
                   sum_eq_zero_iff, mem_erase, ne_eq, card_eq_zero, and_imp] at h
        have : card (erase t.parts x) ≤ (erase t.parts x).sum card
        · refine' card_le_sum_card_of_ne_empty _ _
          simp only [mem_erase, ne_eq, and_imp]
          exact λ x _ hx => t.ne_bot hx
        rw [add_comm, ←eq_tsub_iff_add_eq_of_le (this.trans le_add_self),
            add_tsub_assoc_of_le this] at h
        rw [h]
        exact le_self_add
      · refine' card_pos.mpr _
        rw [nonempty_iff_ne_empty]
        rintro rfl
        exact t.not_bot_mem hx
    constructor
    · intro hx
      specialize this x hx
      rw [card_eq_one] at this
      obtain ⟨x, rfl⟩ := this
      refine' ⟨x, _, rfl⟩
      simpa using subset_of_mem_parts hx (mem_singleton_self x)
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hy'⟩ := t.exists_mem hx
      specialize this y hy
      rw [card_eq_one] at this
      obtain ⟨z, rfl⟩ := this
      simp only [mem_singleton] at hy'
      rwa [hy']
  · rintro rfl
    exact card_bot _

lemma card_parts_eq_one_iff_eq_top (t : Finpartition s) (hs : s ≠ ∅) :
    t.parts.card = 1 ↔ t = ⊤ := by
  rw [card_eq_one, top_eq_indiscrete hs]
  constructor
  · rintro ⟨p, hp⟩
    ext x
    simp [ hp, ←t.supParts]
  · rintro rfl
    simp

lemma card_filter_card_parts_eq_one (hs : s ≠ ∅) :
    Finset.card ((univ : Finset (Finpartition s)).filter (λ p => p.parts.card = 1)) = 1 := by
  rw [card_eq_one]
  refine' ⟨⊤, _⟩
  ext
  simp [card_parts_eq_one_iff_eq_top _ _ hs]

lemma card_filter_card_parts_eq_card :
    Finset.card ((univ : Finset (Finpartition s)).filter (λ p => p.parts.card = s.card)) = 1 := by
  rw [card_eq_one]
  refine' ⟨⊥, _⟩
  ext
  simp [card_parts_eq_card_iff_eq_bot]

lemma univ_eq_singleton_bot :
    (univ : Finset (Finpartition (∅ : Finset α))) = {⊥} := by
  ext t
  have : Unique (Finpartition (∅ : Finset α)) :=
    instUniqueFinpartitionBotToBotToLEToPreorderToPartialOrderToSemilatticeInf
  simp only [Subsingleton.elim t ⊥, mem_univ, true_iff, mem_singleton]

lemma card_range_zero :
    Finset.card (univ : Finset (Finpartition (range 0))) = 1 := by
  have : range 0 = ∅ := rfl
  rw [this, univ_eq_singleton_bot, card_singleton]

lemma card_filter_card_eq_zero_iff :
    Finset.card ((univ : Finset (Finpartition s)).filter
      (λ p => p.parts.card = 0)) = 0 ↔ s ≠ ∅ := by
  simp [filter_eq_empty_iff, parts_eq_empty_iff]

lemma card_range_succ_filter_card_zero (k : ℕ) :
    Finset.card ((univ : Finset (Finpartition (range (k + 1)))).filter
      (λ p => p.parts.card = 0)) = 0 := by
  rw [card_filter_card_eq_zero_iff]
  simp

lemma card_range_succ_filter_card_eq_one (k : ℕ) :
    Finset.card ((univ : Finset (Finpartition (range (k + 1)))).filter
      (λ p => p.parts.card = 1)) = 1 := by
  rw [card_filter_card_parts_eq_one]
  simp

lemma card_range_filter_card_eq_self (k : ℕ) :
    Finset.card ((univ : Finset (Finpartition (range k))).filter
      (λ p => p.parts.card = k)) = 1 := by
  have : range (card (range k)) = range k
  · simp
  rw [←card_range k, ←card_filter_card_parts_eq_card (range k), this]

lemma card_filter_card_lt_eq_zero (n : ℕ) (h : s.card < n) :
    Finset.card ((univ : Finset (Finpartition s)).filter
      (λ p => p.parts.card = n)) = 0 := by
  simp only [card_eq_zero, filter_eq_empty_iff, mem_univ, forall_true_left]
  rintro p rfl
  exact h.not_le (card_parts_le_card _)

lemma card_range_filter_card_lt_eq_zero (k n : ℕ) (h : k < n) :
    Finset.card ((univ : Finset (Finpartition (range k))).filter
      (λ p => p.parts.card = n)) = 0 := by
  refine' card_filter_card_lt_eq_zero (range k) _ _
  simp [h]

def extend_injective {α : Type _} [DistribLattice α] [OrderBot α] [DecidableEq α] {a b c : α}
    (hb : b ≠ ⊥) (hab : Disjoint a b) (hc : a ⊔ b = c) {P Q : Finpartition a}
    (h : P.extend hb hab hc = Q.extend hb hab hc) : P = Q := by
  ext p
  rw [Finpartition.ext_iff, Finset.ext_iff] at h
  specialize h p
  simp only [extend_parts, mem_insert] at h
  rcases eq_or_ne p b with rfl|hp
  · constructor <;> intro H <;>
    · refine' absurd (le_bot_iff.mp (hab _ le_rfl)) (Finpartition.ne_bot _ H)
      refine' (le_sup (f := id) H).trans (le_of_eq _)
      exact Finpartition.supParts _
  · simpa [hp] using h

lemma univ_map_extend_eq_univ_filter {x : α} (hx : x ∉ s) :
    (univ : Finset (Finpartition s)).map
    ⟨λ (p : Finpartition s) => p.extend (singleton_ne_empty x) (by simp [hx]) rfl,
     λ P Q => extend_injective _ _ _⟩ = univ.filter (λ p => {x} ∈ p.parts) := by
  ext P
  simp only [sup_eq_union, mem_map, mem_univ, Embedding.coeFn_mk, Finpartition.ext_iff,
             extend_parts, true_and]
  rw [mem_filter (a := P)]
  simp only [sup_eq_union, mem_univ, true_and]
  constructor
  · rintro ⟨Q, hQ⟩
    simp [←hQ]
  · intro hP
    refine' ⟨(P.avoid {x}).copy _, _⟩
    · ext y
      contrapose! hx
      suffices : y ∈ s ∧ y = x
      · simpa [this.right] using this.left
      simpa [or_and_right] using hx
    · ext y
      rcases eq_or_ne y {x} with rfl|hy
      · simp [hP]
      · simp only [sup_eq_union, copy_parts, mem_avoid, le_eq_subset, subset_singleton_iff, not_or,
                   mem_insert, hy, false_or]
        constructor
        · rintro ⟨d, hd, hd', rfl⟩
          convert hd
          simp only [sdiff_eq_left, disjoint_singleton_right]
          intro H
          simpa using P.disjoint hP hd (Ne.symm hd'.right) le_rfl (singleton_subset_iff.mpr H)
        · intro hy'
          refine' ⟨y, hy', ⟨P.ne_bot hy', hy⟩, _⟩
          simp only [sdiff_eq_left, disjoint_singleton_right]
          intro H
          simpa using P.disjoint hP hy' (Ne.symm hy) le_rfl (singleton_subset_iff.mpr H)

lemma card_filter_singleton_mem_parts_eq_card_erase {x : α} (hx : x ∈ s) :
    card ((univ : Finset (Finpartition s)).filter (λ p => {x} ∈ p.parts)) =
    card (univ : Finset (Finpartition (s.erase x))) := by
  classical
  have hs : erase s x ⊔ {x} = s := erase_union_eq_of_mem hx
  rw [eq_comm, ←card_map, univ_map_extend_eq_univ_filter _ (not_mem_erase x s)]
  refine' card_congr (λ p _ => p.copy hs) _ _ _
  · intro p hp
    rw [mem_filter] at hp ⊢
    simpa using hp
  · intros p q _ _
    simp [Finpartition.ext_iff]
  · intros p hp
    refine' ⟨p.copy hs.symm, _, _⟩
    · rw [mem_filter] at hp ⊢
      simpa using hp
    · simp [Finpartition.ext_iff]

lemma parts_avoid_of_mem {P : Finpartition s} {t : Finset α} (ht : t ∈ P.parts) :
    (P.avoid t).parts = P.parts.erase t := by
  ext x
  simp only [mem_avoid, le_eq_subset, mem_erase, ne_eq]
  constructor
  · rintro ⟨d, hd, hd', rfl⟩
    have : t ≠ d
    · rintro rfl
      simp at hd'
    refine' ⟨_, _⟩
    · intro h
      have : Disjoint (d \ t) t := disjoint_sdiff.symm
      simp only [h, disjoint_self, bot_eq_empty] at this
      subst this
      exact P.not_bot_mem ht
    · convert hd
      rw [sdiff_eq_left]
      exact P.disjoint hd ht this.symm
  · rintro ⟨hne, hx⟩
    have := P.disjoint hx ht hne
    refine' ⟨x, hx, _, _⟩
    · intro H
      obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.mpr (P.ne_bot hx)
      simpa using this (singleton_subset_iff.mpr ha) (singleton_subset_iff.mpr (H ha))
    · rw [sdiff_eq_left]
      exact this

def singleton_equiv (k n : ℕ) :
    {P : Finpartition (range (k + 1)) // {k} ∈ P.parts ∧ P.parts.card = n + 1} ≃
    {Q : Finpartition (range k) // Q.parts.card = n} where
  toFun := λ ⟨P, hP, hP'⟩ => by
    refine' ⟨(P.avoid {k}).copy _, _⟩
    · ext
      simp (config := {contextual := true }) [Nat.lt_succ, le_iff_lt_or_eq, or_and_right, ne_of_lt]
    · simp [copy_parts, parts_avoid_of_mem _ hP, card_erase_of_mem hP, hP']
  invFun := λ ⟨Q, hQ⟩ => by
    refine' ⟨(Q.extend (b := {k}) _ _ _), _⟩
    · simp
    · simp
    · ext
      simp [Nat.lt_succ, le_iff_lt_or_eq]
    · constructor
      · simp
      suffices : card (insert {k} Q.parts) = n + 1
      · simpa
      rw [card_insert_of_not_mem, hQ]
      intro H
      suffices : k ∈ range k
      · simp at this
      exact subset_of_mem_parts H (mem_singleton_self _)
  left_inv := λ ⟨P, hP, hP'⟩ => by
    ext x
    simp only [extend_parts, copy_parts, mem_avoid, le_eq_subset, subset_singleton_iff, mem_insert,
               not_or]
    constructor
    · rintro (rfl|⟨d, hd, ⟨-, hne⟩, rfl⟩)
      · exact hP
      · convert hd
        rw [sdiff_eq_left]
        exact P.disjoint hd hP hne
    · intro hx
      rcases eq_or_ne x {k} with rfl|hne
      · simp
      · refine' Or.inr ⟨x, hx, ⟨P.ne_bot hx, hne⟩, _⟩
        rw [sdiff_eq_left]
        exact P.disjoint hx hP hne
  right_inv := λ ⟨Q, hQ⟩ => by
    ext x
    simp only [copy_parts, mem_avoid, extend_parts, mem_insert, le_eq_subset, subset_singleton_iff,
               exists_eq_or_imp, singleton_ne_empty, or_true, not_true, _root_.sdiff_self,
               bot_eq_empty, false_and, false_or, not_or]
    constructor
    · rintro ⟨y, hy, -, rfl⟩
      convert hy
      rw [sdiff_eq_left]
      suffices : Disjoint (range k) {k}
      · exact this.mono_left (subset_of_mem_parts hy)
      simp
    · intro hx
      refine' ⟨x, hx, ⟨Q.ne_bot hx, _⟩, _⟩
      · rintro rfl
        simpa using subset_of_mem_parts hx
      · rw [sdiff_eq_left]
        suffices : Disjoint (range k) {k}
        · exact this.mono_left (subset_of_mem_parts hx)
        simp

lemma findIdx_go_eq_findIdx {α : Type _} (l : List α) (f : α → Bool) (n : ℕ) :
    List.findIdx.go f l n = List.findIdx f l + n := by
  rw [List.findIdx]
  induction' l with hd tl IH generalizing n
  · simp [List.findIdx.go]
  by_cases h : f hd = true
  · simp [List.findIdx.go, h]
  · simp [List.findIdx.go, h, cond_false, zero_add, IH 1, IH (n + 1), add_assoc, add_comm]


lemma length_le_findIdx_iff {α : Type _} {l : List α} {f : α → Bool} :
    l.length ≤ l.findIdx f ↔ ∀ x ∈ l, ¬ f x := by
  rw [List.findIdx]
  induction' l with hd tl IH
  · simp
  by_cases h : f hd = true
  · simp [List.findIdx.go, h]
  · simp [List.findIdx, List.findIdx.go, h, findIdx_go_eq_findIdx _ _ 1, Nat.succ_le_succ_iff, IH]

lemma findIdx_lt_length_of_exists {α : Type _} {l : List α} {f : α → Bool} :
    l.findIdx f < l.length ↔ ∃ x ∈ l, f x := by
  refine' not_iff_not.mp _
  push_neg
  exact length_le_findIdx_iff

lemma card_avoid_of_mem {s : Finset α} (P : Finpartition s) (t : Finset α) (ht : t ∈ P.parts) :
    card (P.avoid t).parts = card P.parts - 1 := by
  simp only [avoid, ofErase_parts, bot_eq_empty, mem_image, sdiff_eq_empty_iff_subset, not_exists,
             not_and, ge_iff_le]
  rw [card_erase_of_mem, tsub_left_inj, card_image_iff]
  · intros a ha b hb
    rcases eq_or_ne a t with rfl|ht'
    · simp only [_root_.sdiff_self, bot_eq_empty, eq_comm (b := b \ a), sdiff_eq_empty_iff_subset]
      intro H
      cases' eq_or_ne a b with h hne
      · exact h
      · refine' absurd _ (P.ne_bot hb)
        simpa using (P.disjoint ht hb hne).mono_left H
    rcases eq_or_ne b t with rfl|ht''
    · simp only [_root_.sdiff_self, bot_eq_empty, eq_comm (b := b \ a), sdiff_eq_empty_iff_subset]
      intro H
      cases' eq_or_ne a b with h hne
      · exact h
      · refine' absurd _ (P.ne_bot ha)
        simpa using (P.disjoint ht ha hne.symm).mono_left H
    · simp only [ext_iff, mem_sdiff, and_congr_left_iff]
      intro H x
      by_cases hx : x ∈ t
      · constructor <;> intro hx'
        · simpa using P.disjoint ha ht ht' (singleton_subset_iff.mpr hx')
            (singleton_subset_iff.mpr hx)
        · simpa using P.disjoint hb ht ht'' (singleton_subset_iff.mpr hx')
            (singleton_subset_iff.mpr hx)
      · exact H _ hx
  · refine' card_pos.mpr ⟨∅, _⟩
    simp only [mem_image, sdiff_eq_empty_iff_subset]
    exact ⟨t, ht, subset_refl _⟩
  · exact card_pos.mpr ⟨t, ht⟩
  · simp only [mem_image, sdiff_eq_empty_iff_subset]
    exact ⟨t, ht, subset_refl _⟩

lemma card_avoid_of_forall_disjoint {s : Finset α} (P : Finpartition s) (t : Finset α)
    (ht : ∀ x ∈ P.parts, Disjoint x t) : card (P.avoid t).parts = card P.parts := by
  simp only [avoid, ofErase_parts, bot_eq_empty, mem_image, sdiff_eq_empty_iff_subset, not_exists,
             not_and, ge_iff_le]
  rw [card_erase_eq_ite, if_neg, card_image_iff]
  · intros a ha b hb
    simp [sdiff_eq_left.mpr (ht _ ha), sdiff_eq_left.mpr (ht _ hb)]
  · simp only [mem_image, sdiff_eq_empty_iff_subset, not_exists, not_and]
    intros x hx hx'
    refine' P.ne_bot hx _
    simpa using (ht x hx).mono_right hx'

lemma card_avoid_singleton_of_forall_disjoint {s : Finset α} (P : Finpartition s) (x : α)
    (hx' : {x} ∉ P.parts) : card (P.avoid {x}).parts = card P.parts := by
  simp only [avoid, ofErase_parts, bot_eq_empty, mem_image, sdiff_eq_empty_iff_subset, not_exists,
             not_and, ge_iff_le]
  rw [card_erase_eq_ite, if_neg, card_image_iff]
  · intros a ha b hb
    simp only [ext_iff, mem_sdiff, mem_singleton, and_congr_left_iff]
    intros H y
    obtain ⟨z, hz, hne⟩ : ∃ z ∈ a, x ≠ z
    · contrapose! hx'
      have ha' : ∀ y ∈ a, y = x
      · intros y hy
        exact (hx' y hy).symm
      obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.mpr (P.ne_bot ha)
      rw [ha' _ hz] at hz
      replace ha' : a = {x}
      · ext
        constructor
        · simpa using ha' _
        · simp (config := {contextual := true}) [hz]
      rwa [←ha']
    have hz' : z ∈ b := (H _ hne.symm).mp hz
    suffices : a = b
    · simp [this]
    rcases eq_or_ne a b with rfl|hne
    · rfl
    simpa using P.disjoint ha hb hne (singleton_subset_iff.mpr hz) (singleton_subset_iff.mpr hz')
  · simp only [mem_image, sdiff_eq_empty_iff_subset, not_exists, not_and, subset_singleton_iff,
               not_or]
    intro a ha
    refine' ⟨P.ne_bot ha, _⟩
    rintro rfl
    exact hx' ha

def insert_at {α : Type _} [DecidableEq α] {a b : Finset α} (P : Finpartition a)
    (x : Finset α) (hx : x ∈ P.parts) (hb : Disjoint a b) : Finpartition (a ⊔ b) where
  parts := P.parts.image λ y => if y = x then y ⊔ b else y
  supIndep := by
    intro u hu
    simp only [ge_iff_le, mem_image, id_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intros v hv hv' _ hw hw' k hk
    specialize hw' hk
    simp only [mem_sup, id_eq] at hw'
    obtain ⟨y, hy, hy'⟩ := hw'
    specialize hu hy
    simp only [ge_iff_le, le_eq_subset, singleton_subset_iff, subset_singleton_iff, sup_eq_union,
               mem_image] at hu
    obtain ⟨c, hc, rfl⟩ := hu
    specialize hw hk
    split_ifs at hw hv' with hvx <;> split_ifs at hy hy' with hcx
    · subst hvx hcx
      exact absurd hy hv'
    · subst hvx
      simp only [ge_iff_le, le_eq_subset, singleton_subset_iff, subset_singleton_iff, sup_eq_union,
                 mem_union, mem_singleton] at hw
      rcases hw with hw|hw
      · exact absurd (eq_of_mem_of_mem hc hv hy' hw) hcx
      · exact hb (singleton_subset_iff.mpr (subset_of_mem_parts hc hy'))
          (singleton_subset_iff.mpr hw) (mem_singleton_self _)
    · subst hcx
      simp only [ge_iff_le, le_eq_subset, singleton_subset_iff, subset_singleton_iff, sup_eq_union,
                 mem_union, mem_singleton] at hy'
      rcases hy' with hy'|hy'
      · exact absurd (eq_of_mem_of_mem hc hv hy' hw) (Ne.symm hvx)
      · exact hb (singleton_subset_iff.mpr (subset_of_mem_parts hv hw))
          (singleton_subset_iff.mpr hy') (mem_singleton_self _)
    · rw [eq_of_mem_of_mem hc hv hy' hw] at hy
      exact absurd hy hv'
  supParts := by
    ext k
    simp only [ge_iff_le, le_eq_subset, singleton_subset_iff, subset_singleton_iff, sup_eq_union,
               mem_sup, mem_image, id_eq, exists_exists_and_eq_and, mem_range]
    constructor
    · rintro ⟨y, hy, hy'⟩
      split_ifs at hy' with hxy
      · simp only [mem_union, mem_singleton] at hy'
        rcases hy' with hy'|hy'
        · simp [subset_of_mem_parts hy hy']
        · simp [hy']
      · simp [subset_of_mem_parts hy hy']
    · rw [mem_union]
      rintro (hk|hk)
      · obtain ⟨y, hy, hy'⟩ := P.exists_mem hk
        refine' ⟨y, hy, _⟩
        split_ifs <;> simp [hy']
      · refine' ⟨x, hx, _⟩
        simp [hk]
  not_bot_mem := by
    simp only [bot_eq_empty, ge_iff_le, le_eq_subset, singleton_subset_iff, subset_singleton_iff,
               sup_eq_union, mem_image, not_exists, not_and]
    intro y hy
    split_ifs
    · rw [union_comm, union_eq_empty_iff, not_and]
      intro
      exact P.ne_bot hy
    · exact P.ne_bot hy

def insert_at_range (n : ℕ) (P : Finpartition (range n))
    (x : Finset ℕ) (hx : x ∈ P.parts) : Finpartition (range (n + 1)) :=
  (P.insert_at (b := {n}) x hx (by simp)).copy (by ext; simp [Nat.lt_succ_iff_lt_or_eq])

theorem exists_unique_mem {a : α} {s : Finset α} (P : Finpartition s) (ha : a ∈ s) :
    ∃! t, t ∈ P.parts ∧ a ∈ t := by
  obtain ⟨t, ht, ht'⟩ := P.exists_mem ha
  refine' ⟨t, ⟨ht, ht'⟩, _⟩
  rintro u ⟨hu, hu'⟩
  exact eq_of_mem_of_mem hu ht hu' ht'

def nonsingleton_equiv (k n : ℕ) :
    {P : Finpartition (range (k + 1)) // {k} ∉ P.parts ∧ P.parts.card = n + 1} ≃
    Σ (q : {Q : Finpartition (range k) // Q.parts.card = n + 1}), q.1.parts where
  toFun := λ ⟨P, hP, hP'⟩ => by
    have H := (P.exists_unique_mem (self_mem_range_succ k))
    set t := P.parts.choose (k ∈ ·) H with ht
    refine' ⟨⟨(P.avoid {k}).copy _, _⟩, ⟨t \ {k}, _⟩⟩
    · ext
      simp [Nat.lt_succ, Nat.lt_iff_le_and_ne]
    · rw [←hP', copy_parts, card_avoid_singleton_of_forall_disjoint _ _ hP]
    · simp only [copy_parts, mem_avoid, le_eq_subset, subset_singleton_iff, ←ht, not_or]
      have hPt := P.parts.choose_mem _ H
      refine' ⟨t, P.parts.choose_mem _ H, ⟨P.ne_bot hPt, _⟩, rfl⟩
      intro H
      rw [←ht, H] at hPt
      exact hP hPt
  invFun := λ ⟨⟨Q, hQ⟩, t, hQt⟩ => by
    refine' ⟨((Q.avoid t).extend (b := t ∪ {k})) _ _ _, _, _⟩
    · simp [union_eq_empty_iff]
    · simp [disjoint_sdiff.symm]
    · rw [sup_eq_union, ←union_assoc, sdiff_union_self_eq_union,
          union_eq_left_iff_subset.mpr (subset_of_mem_parts hQt)]
      ext
      simp [Nat.lt_succ_iff_lt_or_eq]
    · simp only [extend_parts, mem_avoid, le_eq_subset, mem_insert, right_eq_union_iff_subset,
                 subset_singleton_iff, not_or, not_exists, not_and]
      refine' ⟨⟨Q.ne_bot hQt, _⟩, _⟩
      · rintro rfl
        simpa using subset_of_mem_parts hQt
      · rintro u hu _ huk
        suffices : {k} ⊆ range k
        · simp at this
        exact huk.ge.trans ((sdiff_subset _ _).trans (subset_of_mem_parts hu))
    · simp only [extend_parts, mem_avoid, le_eq_subset, not_exists, not_and]
      rw [card_insert_of_not_mem]
      · simp [card_avoid_of_mem Q t hQt, hQ]
      · intro H
        have : t ⊆ range k \ t := subset_trans (subset_union_left _ _) (subset_of_mem_parts H)
        simp only [subset_sdiff, disjoint_self, bot_eq_empty] at this
        exact (Q.ne_bot hQt) this.right
  left_inv := λ ⟨P, hP, hP'⟩ => by
    ext t
    simp only [sdiff_union_self_eq_union, extend_parts, mem_avoid, copy_parts, le_eq_subset,
               subset_singleton_iff, mem_insert, not_or]
    have H := (P.exists_unique_mem (self_mem_range_succ k))
    constructor
    · rintro (rfl|⟨_, ⟨u, hPu, ⟨hubot, huk⟩, rfl⟩, hu', rfl⟩)
      · convert (P.parts.choose_mem _ H)
        rw [union_eq_left_iff_subset]
        simpa using P.parts.choose_property _ H
      · convert hPu
        rw [sdiff_sdiff]
        have hPt := P.parts.choose_mem _ H
        set t := P.parts.choose (k ∈ ·) H
        rcases eq_or_ne t u with rfl|hne
        · simp at hu'
        suffices : ¬k ∈ u ∧ Disjoint u (choose (fun x => k ∈ x) P.parts H)
        · simpa using this
        refine' ⟨_, P.disjoint hPu hPt hne.symm⟩
        intro hk
        exact hne (eq_of_mem_of_mem hPt hPu (P.parts.choose_property _ H) hk)
    · intro h
      by_cases htk : k ∈ t
      · refine' Or.inl _
        rw [eq_of_mem_of_mem h (P.parts.choose_mem _ H) htk (P.parts.choose_property _ H), eq_comm,
            union_eq_left_iff_subset]
        simpa using P.parts.choose_property _ H
      · refine' Or.inr ⟨t, ⟨t, h, ⟨P.ne_bot h, _⟩, _⟩, _, _⟩
        · rintro rfl
          simp at htk
        · simp [htk]
        · contrapose! htk
          obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr (P.ne_bot h)
          rw [eq_of_mem_of_mem h (P.parts.choose_mem _ H) hx _]
          · exact P.parts.choose_property _ H
          · exact (htk.trans (sdiff_subset _ _)) hx
        · rw [_root_.sdiff_eq_self_iff_disjoint]
          refine' (P.disjoint (P.parts.choose_mem _ H) h _).mono_left (sdiff_subset _ _)
          rintro rfl
          exact htk (P.parts.choose_property _ H)
  right_inv := λ ⟨⟨Q, hQ⟩, t, ht⟩ => by
    simp only [sup_eq_union, Eq.ndrec, id_eq, eq_mpr_eq_cast, cast_eq, ne_eq, copy_parts,
               extend_parts, bot_eq_empty, eq_mp_eq_cast, le_eq_subset, mem_avoid, Sigma.mk.inj_iff,
               Subtype.mk.injEq]
    have : ∀ h₁ h₂ h₃ x, x ∈ (avoid
        (extend (avoid Q t) (h₁ : ¬t ∪ {k} = ∅) (h₂ : Disjoint (range k \ t) (t ∪ {k}))
          (h₃ : range k \ t ∪ (t ∪ {k}) = range (k + 1)))
        {k}).parts ↔ x ∈ Q.parts
    · intro h₁ h₂ h₃ u
      simp only [copy_parts, mem_avoid, extend_parts, le_eq_subset, mem_insert,
                subset_singleton_iff, not_or, exists_eq_or_imp, union_eq_right_iff_subset,
                mem_union, mem_singleton, or_true, not_true, union_sdiff_right]
      constructor
      · rintro (⟨_, rfl⟩|⟨_, ⟨v, hv, hv', rfl⟩, _, rfl⟩)
        · convert ht
          simp only [sdiff_eq_left, disjoint_singleton_right]
          intro H
          simpa using subset_of_mem_parts ht H
        · rw [sdiff_sdiff]
          rcases eq_or_ne v t with rfl|htv
          · simp at hv'
          rwa [sdiff_eq_left.mpr]
          simp only [ge_iff_le, le_eq_subset, singleton_subset_iff, subset_singleton_iff,
                    sup_eq_union, disjoint_union_right, disjoint_singleton_right]
          refine' ⟨Q.disjoint hv ht htv, _⟩
          intro H
          simpa using subset_of_mem_parts hv H
      · intro hu
        have huk : k ∉ u
        · intro H
          simpa using subset_of_mem_parts hu H
        rcases eq_or_ne t u with rfl|hne
        · refine' Or.inl _
          simp only [union_eq_empty_iff, singleton_ne_empty, and_false, not_false_iff, true_and,
                    sdiff_eq_left, disjoint_singleton_right, huk, and_true]
          refine' ⟨Q.ne_bot hu, _⟩
          rintro rfl
          simp at huk
        · refine' Or.inr ⟨u, ⟨u, hu, _, _⟩, ⟨Q.ne_bot hu, _⟩, _⟩
          · intro H
            obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr (Q.ne_bot hu)
            exact hne (eq_of_mem_of_mem ht hu (H hx) hx)
          · simpa using Q.disjoint hu ht hne.symm
          · rintro rfl
            simp at huk
          · simp [huk]
    constructor
    · ext u
      simp only [copy_parts, this]
    · have he : { x // x ∈ (avoid
          (extend (avoid Q t) (_ : ¬t ∪ {k} = ∅) (_ : Disjoint (range k \ t) (t ∪ {k}))
            (_ : range k \ t ∪ (t ∪ {k}) = range (k + 1)))
          {k}).parts } = { x // x ∈ Q.parts }
      · simp only [this]
      refine' heq_of_cast_eq he _
      ext u
      have mem_coe_cast : ∀ {α : Type _} {p q : Finset α → Prop} {h : {x // p x} = {x // q x}}
        {x : α} {s : {x // p x}} (_ : ∀ x, p x ↔ q x),
          x ∈ ((cast h s : {x // q x}) : Finset α) ↔ x ∈ (s : Finset α)
      · intros α p q h x s h'
        have : p = q
        · funext
          rw [h']
        subst this
        simp
      rw [mem_coe_cast]; swap
      · exact this _ _ _
      simp only
      convert Iff.rfl
      have htk : (t ∪ {k}) \ {k} = t
      · have : k ∉ t
        · intro H
          simpa using subset_of_mem_parts ht H
        simp [union_sdiff_right, this]
      refine' htk.symm.trans _
      congr
      generalize_proofs H
      refine' H.unique _ ⟨Finset.choose_mem _ _ H, Finset.choose_property _ _ H⟩
      simp

lemma stirling (k n : ℕ) :
    card ((univ : Finset (Finpartition (range (k + 1)))).filter
      (λ P => P.parts.card = n + 1)) = card
        ((univ : Finset (Finpartition (range k))).filter (λ P => P.parts.card = n)) +
      (n + 1) * card
        ((univ : Finset (Finpartition (range k))).filter (λ P => P.parts.card = n + 1)) := by
  rw [←filter_union_filter_neg_eq (λ P : Finpartition (range (k + 1)) => {k} ∈ P.parts) univ,
      filter_union, filter_filter, filter_filter, card_union_eq]
  · refine' congr_arg₂ _ _ _
    · rw [←card_attach, ←card_attach (α := Finpartition (range k)),
          ←univ_eq_attach, ←univ_eq_attach,
          ←Fintype.card, ←Fintype.card, Fintype.card_eq]
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨(singleton_equiv k n)⟩
    · rw [←card_attach, ←card_attach (α := Finpartition (range k)),
          ←univ_eq_attach, ←univ_eq_attach,
          ←Fintype.card, ←Fintype.card]
      simp only [mem_filter, mem_univ, true_and]
      rw [Fintype.card_congr (nonsingleton_equiv k n), Fintype.card_sigma,
          sum_eq_card_nsmul (b := n + 1), nsmul_eq_mul, mul_comm]
      · congr
      · rintro ⟨P, hP⟩ _
        simp [hP]
  · rw [disjoint_filter]
    simp only [mem_univ]
    simp (config := { contextual := true})

lemma card_range_succ_filter_card_eq (k : ℕ) :
    Finset.card ((univ : Finset (Finpartition (range (k + 1)))).filter
      (λ p => p.parts.card = 2)) = 2 ^ k - 1 := by
  induction' k with k IH
  · rw [card_range_filter_card_lt_eq_zero] <;>
    simp
  rw [stirling, IH, card_filter_card_parts_eq_one]
  · rw [show 1 + 1 = 2 from rfl]
    simp only [Nat.succ_eq_add_one, pow_add, Nat.mul_sub_left_distrib, add_comm 1, mul_one, pow_one]
    rw [←tsub_tsub_assoc]
    · simp [mul_comm]
    · simpa using Nat.one_le_pow _ _ zero_lt_two
    · exact one_le_two
  · simp

lemma card_Finpartition_univ_singleton :
    Finset.card ((univ : Finset (Finpartition s)).filter
      (λ t => ∀ p ∈ t.parts, p.card = 1)) = 1 := by
  rw [card_eq_one]
  refine' ⟨⊥, _⟩
  ext t
  simp only [mem_singleton, mem_filter, mem_univ, true_and]
  constructor
  · intro ht
    ext x
    simp only [parts_bot, mem_map, Embedding.coeFn_mk]
    constructor
    · intro hx
      specialize ht x hx
      rw [card_eq_one] at ht
      obtain ⟨x, rfl⟩ := ht
      suffices : x ∈ s
      · simp [this]
      simp only [← t.supParts, mem_sup, id_eq]
      exact ⟨_, hx, mem_singleton_self _⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hy'⟩ := t.exists_mem hx
      convert hy
      specialize ht y hy
      rw [card_eq_one] at ht
      obtain ⟨y, rfl⟩ := ht
      simpa using hy'
  · rintro rfl
    simp

lemma card_Finpartition_univ_univ :
    Finset.card ((univ : Finset (Finpartition s)).filter
      (λ t => ∀ p ∈ t.parts, p.card = s.card)) = 1 := by
  rw [card_eq_one]
  refine' ⟨⊤, _⟩
  ext t
  simp only [mem_singleton, mem_filter, mem_univ, true_and]
  rcases eq_or_ne s ∅ with rfl|hs
  · simp only [card_empty, card_eq_zero, bot_eq_empty, top_eq_empty]
    constructor
    · intro ht
      ext x
      simp only [empty_parts, not_mem_empty, iff_false]
      intro hx
      refine' t.not_bot_mem _
      simp_rw [bot_eq_empty, ←ht x hx, hx]
    · rintro rfl
      simp
  constructor
  · intro ht
    ext x
    simp only [top_eq_indiscrete hs, mem_map, Embedding.coeFn_mk, indiscrete_parts, mem_singleton]
    constructor
    · intro hx
      specialize ht x hx
      ext y
      simp only [←t.supParts, mem_sup, id_eq]
      constructor
      · intro hy
        exact ⟨x, hx, hy⟩
      · rintro ⟨z, hz, hy⟩
        convert hy
        contrapose! hy
        rw [←t.sum_card_parts, ←add_sum_erase t.parts _ hx] at ht
        simp only [mem_erase, ne_eq, card_eq_zero, and_imp, self_eq_add_right,
                   sum_eq_zero_iff, mem_erase, ne_eq, card_eq_zero, and_imp] at ht
        refine' absurd _ t.not_bot_mem
        convert hz
        simp [ht z hy.symm hz]
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, ha⟩ := nonempty_of_ne_empty hs
      obtain ⟨y, hy, _⟩ := t.exists_mem ha
      convert hy
      specialize ht y hy
      rw [←t.sum_card_parts, ←add_sum_erase t.parts _ hy] at ht
      simp only [mem_erase, ne_eq, card_eq_zero, and_imp, self_eq_add_right,
                  sum_eq_zero_iff, mem_erase, ne_eq, card_eq_zero, and_imp] at ht
      rw [←t.supParts]
      refine' le_antisymm _ (le_sup (f := id) hy)
      intro z
      simp only [mem_sup, id_eq, forall_exists_index, and_imp]
      intros y' hy' hz
      convert hz
      refine' (eq_or_ne y y').resolve_right (λ H => t.not_bot_mem _)
      rwa [bot_eq_empty, ←ht y' H.symm hy']
  · rintro rfl
    simp [top_eq_indiscrete hs]

end Finpartition
