/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.LocallyFinite.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Cast.Order

#align_import data.nat.interval from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Finite intervals of naturals

This file proves that `ℕ` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.

## TODO

Some lemmas can be generalized using `OrderedGroup`, `CanonicallyOrderedCommMonoid` or `SuccOrder`
and subsequently be moved upstream to `Data.Finset.LocallyFinite`.

Remove `Finset.range` in favour of `Finset.Iio`
-/

open Nat

namespace Finset
variable {α : Type*} {s : Finset α} {n m l : ℕ}

/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : Finset ℕ := ⟨_, Multiset.nodup_range n⟩
#align finset.range Finset.range

@[simp]
theorem range_val (n : ℕ) : (range n).1 = Multiset.range n :=
  rfl
#align finset.range_val Finset.range_val

@[simp]
theorem mem_range : m ∈ range n ↔ m < n :=
  Multiset.mem_range
#align finset.mem_range Finset.mem_range

@[simp, norm_cast]
theorem coe_range (n : ℕ) : (range n : Set ℕ) = Set.Iio n :=
  Set.ext fun _ => mem_range
#align finset.coe_range Finset.coe_range

@[simp]
theorem range_zero : range 0 = ∅ :=
  rfl
#align finset.range_zero Finset.range_zero

@[simp]
theorem range_one : range 1 = {0} :=
  rfl
#align finset.range_one Finset.range_one

theorem range_succ : range (succ n) = insert n (range n) :=
  eq_of_veq <| (Multiset.range_succ n).trans <|
    (Multiset.ndinsert_of_not_mem Multiset.not_mem_range_self).symm
#align finset.range_succ Finset.range_succ

theorem range_add_one : range (n + 1) = insert n (range n) :=
  range_succ
#align finset.range_add_one Finset.range_add_one

-- Porting note (#10618): @[simp] can prove this
theorem not_mem_range_self : n ∉ range n :=
  Multiset.not_mem_range_self
#align finset.not_mem_range_self Finset.not_mem_range_self

-- Porting note (#10618): @[simp] can prove this
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) :=
  Multiset.self_mem_range_succ n
#align finset.self_mem_range_succ Finset.self_mem_range_succ

@[simp]
theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m :=
  Multiset.range_subset
#align finset.range_subset Finset.range_subset

theorem range_mono : Monotone range := fun _ _ => range_subset.2
#align finset.range_mono Finset.range_mono

@[gcongr] alias ⟨_, _root_.GCongr.finset_range_subset_of_le⟩ := range_subset

theorem mem_range_succ_iff {a b : ℕ} : a ∈ Finset.range b.succ ↔ a ≤ b :=
  Finset.mem_range.trans Nat.lt_succ_iff
#align finset.mem_range_succ_iff Finset.mem_range_succ_iff

theorem mem_range_le {n x : ℕ} (hx : x ∈ range n) : x ≤ n :=
  (mem_range.1 hx).le
#align finset.mem_range_le Finset.mem_range_le

theorem mem_range_sub_ne_zero {n x : ℕ} (hx : x ∈ range n) : n - x ≠ 0 :=
  _root_.ne_of_gt <| tsub_pos_of_lt <| mem_range.1 hx
#align finset.mem_range_sub_ne_zero Finset.mem_range_sub_ne_zero

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem nonempty_range_iff : (range n).Nonempty ↔ n ≠ 0 :=
  ⟨fun ⟨k, hk⟩ => ((_root_.zero_le k).trans_lt <| mem_range.1 hk).ne',
   fun h => ⟨0, mem_range.2 <| pos_iff_ne_zero.2 h⟩⟩
#align finset.nonempty_range_iff Finset.nonempty_range_iff

@[simp]
theorem range_eq_empty_iff : range n = ∅ ↔ n = 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_range_iff, not_not]
#align finset.range_eq_empty_iff Finset.range_eq_empty_iff

theorem nonempty_range_succ : (range <| n + 1).Nonempty :=
  nonempty_range_iff.2 n.succ_ne_zero
#align finset.nonempty_range_succ Finset.nonempty_range_succ

@[simp]
theorem range_filter_eq {n m : ℕ} : (range n).filter (· = m) = if m < n then {m} else ∅ := by
  convert filter_eq (range n) m using 2
  · ext
    rw [eq_comm]
  · simp
#align finset.range_filter_eq Finset.range_filter_eq

lemma range_nontrivial {n : ℕ} (hn : 1 < n) : (Finset.range n).Nontrivial := by
  rw [Finset.Nontrivial, Finset.coe_range]
  exact ⟨0, zero_lt_one.trans hn, 1, hn, zero_ne_one⟩

theorem disjoint_range_addLeftEmbedding (a b : ℕ) :
    Disjoint (range a) (map (addLeftEmbedding a) (range b)) := by
  refine' disjoint_iff_inf_le.mpr _
  intro k hk
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, addLeftEmbedding, mem_inter]
    at hk
  obtain ⟨a, _, ha⟩ := hk.2
  simpa [← ha] using hk.1
#align finset.disjoint_range_add_left_embedding Finset.disjoint_range_addLeftEmbedding

theorem disjoint_range_addRightEmbedding (a b : ℕ) :
    Disjoint (range a) (map (addRightEmbedding a) (range b)) := by
  refine' disjoint_iff_inf_le.mpr _
  intro k hk
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, addRightEmbedding, mem_inter]
    at hk
  obtain ⟨a, _, ha⟩ := hk.2
  simpa [← ha] using hk.1
#align finset.disjoint_range_add_right_embedding Finset.disjoint_range_addRightEmbedding

theorem range_add_one' (n : ℕ) :
    range (n + 1) = insert 0 ((range n).map ⟨fun i => i + 1, fun i j => by simp⟩) := by
  ext (⟨⟩ | ⟨n⟩) <;> simp [Nat.succ_eq_add_one, Nat.zero_lt_succ n]
#align finset.range_add_one' Finset.range_add_one'

lemma mem_range_iff_mem_finset_range_of_mod_eq' [DecidableEq α] {f : ℕ → α} {a : α} {n : ℕ}
    (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
    a ∈ Set.range f ↔ a ∈ (Finset.range n).image fun i => f i := by
  constructor
  · rintro ⟨i, hi⟩
    simp only [mem_image, exists_prop, mem_range]
    exact ⟨i % n, Nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩
  · rintro h
    simp only [mem_image, exists_prop, Set.mem_range, mem_range] at *
    rcases h with ⟨i, _, ha⟩
    exact ⟨i, ha⟩
#align finset.mem_range_iff_mem_finset_range_of_mod_eq' Finset.mem_range_iff_mem_finset_range_of_mod_eq'

lemma mem_range_iff_mem_finset_range_of_mod_eq [DecidableEq α] {f : ℤ → α} {a : α} {n : ℕ}
    (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
    a ∈ Set.range f ↔ a ∈ (Finset.range n).image (fun (i : ℕ) => f i) :=
  suffices (∃ i, f (i % n) = a) ↔ ∃ i, i < n ∧ f ↑i = a by simpa [h]
  have hn' : 0 < (n : ℤ) := Int.ofNat_lt.mpr hn
  Iff.intro
    (fun ⟨i, hi⟩ =>
      have : 0 ≤ i % ↑n := Int.emod_nonneg _ (ne_of_gt hn')
      ⟨Int.toNat (i % n), by
        rw [← Int.ofNat_lt, Int.toNat_of_nonneg this]; exact ⟨Int.emod_lt_of_pos i hn', hi⟩⟩)
    fun ⟨i, hi, ha⟩ =>
    ⟨i, by rw [Int.emod_eq_of_lt (Int.ofNat_zero_le _) (Int.ofNat_lt_ofNat_of_lt hi), ha]⟩
#align finset.mem_range_iff_mem_finset_range_of_mod_eq Finset.mem_range_iff_mem_finset_range_of_mod_eq

lemma range_add (a b : ℕ) : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) := by
  rw [← val_inj, union_val]
  exact Multiset.range_add_eq_union a b
#align finset.range_add Finset.range_add

theorem range_sdiff_zero {n : ℕ} : range (n + 1) \ {0} = (range n).image Nat.succ := by
  induction' n with k hk
  · simp
  conv_rhs => rw [range_succ]
  rw [range_succ, image_insert, ← hk, insert_sdiff_of_not_mem]
  simp
#align finset.range_sdiff_zero Finset.range_sdiff_zero

@[simp]
theorem card_range (n : ℕ) : (range n).card = n :=
  Multiset.card_range n
  #align finset.card_range Finset.card_range

theorem card_eq_of_bijective (f : ∀ i, i < n → α) (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a)
    (hf' : ∀ i (h : i < n), f i h ∈ s)
    (f_inj : ∀ i j (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) : s.card = n := by
  classical
  have : s = (range n).attach.image fun i => f i.1 (mem_range.1 i.2) := by
    ext a
    suffices _ : a ∈ s ↔ ∃ (i : _) (hi : i ∈ range n), f i (mem_range.1 hi) = a by
      simpa only [mem_image, mem_attach, true_and_iff, Subtype.exists]
    constructor
    · intro ha; obtain ⟨i, hi, rfl⟩ := hf a ha; use i, mem_range.2 hi
    · rintro ⟨i, hi, rfl⟩; apply hf'
  calc
    s.card = ((range n).attach.image fun i => f i.1 (mem_range.1 i.2)).card := by rw [this]
    _      = (range n).attach.card := ?_
    _      = (range n).card := card_attach
    _      = n := card_range n
  apply card_image_of_injective
  intro ⟨i, hi⟩ ⟨j, hj⟩ eq
  exact Subtype.eq <| f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq
#align finset.card_eq_of_bijective Finset.card_eq_of_bijective

theorem le_card_of_inj_on_range (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ s.card :=
  calc
    n = card (range n) := (card_range n).symm
    _ ≤ s.card := card_le_card_of_inj_on f (by simpa only [mem_range]) (by simpa only [mem_range])
#align finset.le_card_of_inj_on_range Finset.le_card_of_inj_on_range

theorem subset_range_sup_succ (s : Finset ℕ) : s ⊆ range (s.sup id).succ := fun _ hn =>
  mem_range.2 <| Nat.lt_succ_of_le <| @le_sup _ _ _ _ _ id _ hn
#align finset.subset_range_sup_succ Finset.subset_range_sup_succ

theorem exists_nat_subset_range (s : Finset ℕ) : ∃ n : ℕ, s ⊆ range n :=
  ⟨_, s.subset_range_sup_succ⟩
#align finset.exists_nat_subset_range Finset.exists_nat_subset_range

theorem powerset_card_disjiUnion (s : Finset α) :
    Finset.powerset s = (range (s.card + 1)).disjiUnion (powersetCard · s)
      (s.pairwise_disjoint_powersetCard.set_pairwise _) := by
  refine' ext fun a => ⟨fun ha => _, fun ha => _⟩
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

end Finset

@[simp] lemma Multiset.toFinset_range (n : ℕ) : toFinset (range n) = Finset.range n := by ext; simp

@[simp] lemma List.toFinset_range (n : ℕ) : (range n).toFinset = Finset.range n := by ext; simp

open Finset Nat

variable (a b c : ℕ)

namespace Nat

instance instLocallyFiniteOrder : LocallyFiniteOrder ℕ where
  finsetIcc a b := ⟨List.range' a (b + 1 - a), List.nodup_range' _ _⟩
  finsetIco a b := ⟨List.range' a (b - a), List.nodup_range' _ _⟩
  finsetIoc a b := ⟨List.range' (a + 1) (b - a), List.nodup_range' _ _⟩
  finsetIoo a b := ⟨List.range' (a + 1) (b - a - 1), List.nodup_range' _ _⟩
  finset_mem_Icc a b x := by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]
    cases le_or_lt a b with
    | inl h => rw [add_tsub_cancel_of_le (Nat.lt_succ_of_le h).le, Nat.lt_succ_iff]
    | inr h =>
      rw [tsub_eq_zero_iff_le.2 (succ_le_of_lt h), add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2)
  finset_mem_Ico a b x := by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]
    cases le_or_lt a b with
    | inl h => rw [add_tsub_cancel_of_le h]
    | inr h =>
      rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2.le)
  finset_mem_Ioc a b x := by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]
    cases le_or_lt a b with
    | inl h =>
      rw [← succ_sub_succ, add_tsub_cancel_of_le (succ_le_succ h), Nat.lt_succ_iff, Nat.succ_le_iff]
    | inr h =>
      rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.le.trans hx.2)
  finset_mem_Ioo a b x := by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1, ← tsub_add_eq_tsub_tsub]
    cases le_or_lt (a + 1) b with
    | inl h => rw [add_tsub_cancel_of_le h, Nat.succ_le_iff]
    | inr h =>
      rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2)

theorem Icc_eq_range' : Icc a b = ⟨List.range' a (b + 1 - a), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Icc_eq_range' Nat.Icc_eq_range'

theorem Ico_eq_range' : Ico a b = ⟨List.range' a (b - a), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Ico_eq_range' Nat.Ico_eq_range'

theorem Ioc_eq_range' : Ioc a b = ⟨List.range' (a + 1) (b - a), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Ioc_eq_range' Nat.Ioc_eq_range'

theorem Ioo_eq_range' : Ioo a b = ⟨List.range' (a + 1) (b - a - 1), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Ioo_eq_range' Nat.Ioo_eq_range'

theorem uIcc_eq_range' :
    uIcc a b = ⟨List.range' (min a b) (max a b + 1 - min a b), List.nodup_range' _ _⟩ := rfl
#align nat.uIcc_eq_range' Nat.uIcc_eq_range'

theorem Iio_eq_range : Iio = range := by
  ext b x
  rw [mem_Iio, mem_range]
#align nat.Iio_eq_range Nat.Iio_eq_range

@[simp]
theorem Ico_zero_eq_range : Ico 0 = range := by rw [← bot_eq_zero, ← Iio_eq_Ico, Iio_eq_range]
#align nat.Ico_zero_eq_range Nat.Ico_zero_eq_range

theorem _root_.Finset.range_eq_Ico : range = Ico 0 :=
  Ico_zero_eq_range.symm
#align finset.range_eq_Ico Finset.range_eq_Ico

@[simp]
theorem card_Icc : (Icc a b).card = b + 1 - a :=
  List.length_range' _ _ _
#align nat.card_Icc Nat.card_Icc

@[simp]
theorem card_Ico : (Ico a b).card = b - a :=
  List.length_range' _ _ _
#align nat.card_Ico Nat.card_Ico

@[simp]
theorem card_Ioc : (Ioc a b).card = b - a :=
  List.length_range' _ _ _
#align nat.card_Ioc Nat.card_Ioc

@[simp]
theorem card_Ioo : (Ioo a b).card = b - a - 1 :=
  List.length_range' _ _ _
#align nat.card_Ioo Nat.card_Ioo

@[simp]
theorem card_uIcc : (uIcc a b).card = (b - a : ℤ).natAbs + 1 := by
  refine' (card_Icc _ _).trans (Int.ofNat.inj _)
  change ((↑) : ℕ → ℤ) _ = _
  rw [sup_eq_max, inf_eq_min, Int.ofNat_sub]
  · rw [add_comm, Int.ofNat_add, add_sub_assoc]
    -- Porting note: `norm_cast` puts a `Int.subSubNat` in the goal
    -- norm_cast
    change _ = ↑(Int.natAbs (b - a) + 1)
    push_cast
    rw [max_sub_min_eq_abs, add_comm]
  · exact min_le_max.trans le_self_add
#align nat.card_uIcc Nat.card_uIcc

@[simp]
theorem card_Iic : (Iic b).card = b + 1 := by rw [Iic_eq_Icc, card_Icc, bot_eq_zero, tsub_zero]
#align nat.card_Iic Nat.card_Iic

@[simp]
theorem card_Iio : (Iio b).card = b := by rw [Iio_eq_Ico, card_Ico, bot_eq_zero, tsub_zero]
#align nat.card_Iio Nat.card_Iio

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem card_fintypeIcc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [Fintype.card_ofFinset, card_Icc]
#align nat.card_fintype_Icc Nat.card_fintypeIcc

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem card_fintypeIco : Fintype.card (Set.Ico a b) = b - a := by
  rw [Fintype.card_ofFinset, card_Ico]
#align nat.card_fintype_Ico Nat.card_fintypeIco

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem card_fintypeIoc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [Fintype.card_ofFinset, card_Ioc]
#align nat.card_fintype_Ioc Nat.card_fintypeIoc

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem card_fintypeIoo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [Fintype.card_ofFinset, card_Ioo]
#align nat.card_fintype_Ioo Nat.card_fintypeIoo

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem card_fintypeIic : Fintype.card (Set.Iic b) = b + 1 := by
  rw [Fintype.card_ofFinset, card_Iic]
#align nat.card_fintype_Iic Nat.card_fintypeIic

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem card_fintypeIio : Fintype.card (Set.Iio b) = b := by rw [Fintype.card_ofFinset, card_Iio]
#align nat.card_fintype_Iio Nat.card_fintypeIio

-- TODO@Yaël: Generalize all the following lemmas to `SuccOrder`
theorem Icc_succ_left : Icc a.succ b = Ioc a b := by
  ext x
  rw [mem_Icc, mem_Ioc, succ_le_iff]
#align nat.Icc_succ_left Nat.Icc_succ_left

theorem Ico_succ_right : Ico a b.succ = Icc a b := by
  ext x
  rw [mem_Ico, mem_Icc, Nat.lt_succ_iff]
#align nat.Ico_succ_right Nat.Ico_succ_right

theorem Ico_succ_left : Ico a.succ b = Ioo a b := by
  ext x
  rw [mem_Ico, mem_Ioo, succ_le_iff]
#align nat.Ico_succ_left Nat.Ico_succ_left

theorem Icc_pred_right {b : ℕ} (h : 0 < b) : Icc a (b - 1) = Ico a b := by
  ext x
  rw [mem_Icc, mem_Ico, lt_iff_le_pred h]
#align nat.Icc_pred_right Nat.Icc_pred_right

theorem Ico_succ_succ : Ico a.succ b.succ = Ioc a b := by
  ext x
  rw [mem_Ico, mem_Ioc, succ_le_iff, Nat.lt_succ_iff]
#align nat.Ico_succ_succ Nat.Ico_succ_succ

@[simp]
theorem Ico_succ_singleton : Ico a (a + 1) = {a} := by rw [Ico_succ_right, Icc_self]
#align nat.Ico_succ_singleton Nat.Ico_succ_singleton

@[simp]
theorem Ico_pred_singleton {a : ℕ} (h : 0 < a) : Ico (a - 1) a = {a - 1} := by
  rw [← Icc_pred_right _ h, Icc_self]
#align nat.Ico_pred_singleton Nat.Ico_pred_singleton

@[simp]
theorem Ioc_succ_singleton : Ioc b (b + 1) = {b + 1} := by rw [← Nat.Icc_succ_left, Icc_self]
#align nat.Ioc_succ_singleton Nat.Ioc_succ_singleton

variable {a b c}

theorem Ico_succ_right_eq_insert_Ico (h : a ≤ b) : Ico a (b + 1) = insert b (Ico a b) := by
  rw [Ico_succ_right, ← Ico_insert_right h]
#align nat.Ico_succ_right_eq_insert_Ico Nat.Ico_succ_right_eq_insert_Ico

theorem Ico_insert_succ_left (h : a < b) : insert a (Ico a.succ b) = Ico a b := by
  rw [Ico_succ_left, ← Ioo_insert_left h]
#align nat.Ico_insert_succ_left Nat.Ico_insert_succ_left

theorem image_sub_const_Ico (h : c ≤ a) :
    ((Ico a b).image fun x => x - c) = Ico (a - c) (b - c) := by
  ext x
  rw [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Ico] at hx ⊢
    exact ⟨tsub_le_tsub_right hx.1 _, tsub_lt_tsub_right_of_le (h.trans hx.1) hx.2⟩
  · rintro h
    refine' ⟨x + c, _, add_tsub_cancel_right _ _⟩
    rw [mem_Ico] at h ⊢
    exact ⟨tsub_le_iff_right.1 h.1, lt_tsub_iff_right.1 h.2⟩
#align nat.image_sub_const_Ico Nat.image_sub_const_Ico

theorem Ico_image_const_sub_eq_Ico (hac : a ≤ c) :
    ((Ico a b).image fun x => c - x) = Ico (c + 1 - b) (c + 1 - a) := by
  ext x
  rw [mem_image, mem_Ico]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Ico] at hx
    refine'
      ⟨_,
        ((tsub_le_tsub_iff_left hac).2 hx.1).trans_lt
          ((tsub_lt_tsub_iff_right hac).2 (Nat.lt_succ_self _))⟩
    cases lt_or_le c b with
    | inl h =>
      rw [tsub_eq_zero_iff_le.mpr (succ_le_of_lt h)]
      exact zero_le _
    | inr h =>
      rw [← succ_sub_succ c]
      exact (tsub_le_tsub_iff_left (succ_le_succ <| hx.2.le.trans h)).2 hx.2
  · rintro ⟨hb, ha⟩
    rw [lt_tsub_iff_left, Nat.lt_succ_iff] at ha
    have hx : x ≤ c := (Nat.le_add_left _ _).trans ha
    refine' ⟨c - x, _, tsub_tsub_cancel_of_le hx⟩
    · rw [mem_Ico]
      exact
        ⟨le_tsub_of_add_le_right ha,
          (tsub_lt_iff_left hx).2 <| succ_le_iff.1 <| tsub_le_iff_right.1 hb⟩
#align nat.Ico_image_const_sub_eq_Ico Nat.Ico_image_const_sub_eq_Ico

theorem Ico_succ_left_eq_erase_Ico : Ico a.succ b = erase (Ico a b) a := by
  ext x
  rw [Ico_succ_left, mem_erase, mem_Ico, mem_Ioo, ← and_assoc, ne_comm, @and_comm (a ≠ x),
    lt_iff_le_and_ne]
#align nat.Ico_succ_left_eq_erase_Ico Nat.Ico_succ_left_eq_erase_Ico

theorem mod_injOn_Ico (n a : ℕ) : Set.InjOn (· % a) (Finset.Ico n (n + a)) := by
  induction' n with n ih
  · simp only [zero_add, Nat.zero_eq, Ico_zero_eq_range]
    rintro k hk l hl (hkl : k % a = l % a)
    simp only [Finset.mem_range, Finset.mem_coe] at hk hl
    rwa [mod_eq_of_lt hk, mod_eq_of_lt hl] at hkl
  rw [Ico_succ_left_eq_erase_Ico, succ_add, succ_eq_add_one,
    Ico_succ_right_eq_insert_Ico le_self_add]
  rintro k hk l hl (hkl : k % a = l % a)
  have ha : 0 < a := by
    by_contra ha
    simp only [not_lt, nonpos_iff_eq_zero] at ha
    simp [ha] at hk
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hk hl
  rcases hk with ⟨hkn, rfl | hk⟩ <;> rcases hl with ⟨hln, rfl | hl⟩
  · rfl
  · rw [add_mod_right] at hkl
    refine' (hln <| ih hl _ hkl.symm).elim
    simp only [lt_add_iff_pos_right, Set.left_mem_Ico, Finset.coe_Ico, ha]
  · rw [add_mod_right] at hkl
    suffices k = n by contradiction
    refine' ih hk _ hkl
    simp only [lt_add_iff_pos_right, Set.left_mem_Ico, Finset.coe_Ico, ha]
  · refine' ih _ _ hkl <;> simp only [Finset.mem_coe, hk, hl]
#align nat.mod_inj_on_Ico Nat.mod_injOn_Ico

/-- Note that while this lemma cannot be easily generalized to a type class, it holds for ℤ as
well. See `Int.image_Ico_emod` for the ℤ version. -/
theorem image_Ico_mod (n a : ℕ) : (Ico n (n + a)).image (· % a) = range a := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [range_zero, add_zero, Ico_self, image_empty]
  ext i
  simp only [mem_image, exists_prop, mem_range, mem_Ico]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact mod_lt i ha.bot_lt
  intro hia
  have hn := Nat.mod_add_div n a
  obtain hi | hi := lt_or_le i (n % a)
  · refine' ⟨i + a * (n / a + 1), ⟨_, _⟩, _⟩
    · rw [add_comm (n / a), mul_add, mul_one, ← add_assoc]
      refine' hn.symm.le.trans (add_le_add_right _ _)
      simpa only [zero_add] using add_le_add (zero_le i) (Nat.mod_lt n ha.bot_lt).le
    · refine' lt_of_lt_of_le (add_lt_add_right hi (a * (n / a + 1))) _
      rw [mul_add, mul_one, ← add_assoc, hn]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]
  · refine' ⟨i + a * (n / a), ⟨_, _⟩, _⟩
    · exact hn.symm.le.trans (add_le_add_right hi _)
    · rw [add_comm n a]
      refine' add_lt_add_of_lt_of_le hia (le_trans _ hn.le)
      simp only [zero_le, le_add_iff_nonneg_left]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]
#align nat.image_Ico_mod Nat.image_Ico_mod

section Multiset

open Multiset

theorem multiset_Ico_map_mod (n a : ℕ) :
    (Multiset.Ico n (n + a)).map (· % a) = Multiset.range a := by
  convert congr_arg Finset.val (image_Ico_mod n a)
  refine' ((nodup_map_iff_inj_on (Finset.Ico _ _).nodup).2 <| _).dedup.symm
  exact mod_injOn_Ico _ _
#align nat.multiset_Ico_map_mod Nat.multiset_Ico_map_mod

end Multiset

end Nat

namespace Finset

theorem range_image_pred_top_sub (n : ℕ) :
    ((Finset.range n).image fun j => n - 1 - j) = Finset.range n := by
  cases n
  · rw [range_zero, image_empty]
  · rw [Finset.range_eq_Ico, Nat.Ico_image_const_sub_eq_Ico (Nat.zero_le _)]
    simp_rw [succ_sub_succ, tsub_zero, tsub_self]
#align finset.range_image_pred_top_sub Finset.range_image_pred_top_sub

-- Porting note: had to use `@` and specify `(a + b)` explicitly. mathlib3 managed without.
theorem range_add_eq_union : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) := by
  rw [Finset.range_eq_Ico, map_eq_image]
  convert (@Ico_union_Ico_eq_Ico _ _ _ _ _ (a + b) a.zero_le le_self_add).symm
  exact image_add_left_Ico _ _ _
#align finset.range_add_eq_union Finset.range_add_eq_union

end Finset

section Induction

variable {P : ℕ → Prop} (h : ∀ n, P (n + 1) → P n)

theorem Nat.decreasing_induction_of_not_bddAbove (hP : ¬BddAbove { x | P x }) (n : ℕ) : P n :=
  let ⟨_, hm, hl⟩ := not_bddAbove_iff.1 hP n
  decreasingInduction h hl.le hm
#align nat.decreasing_induction_of_not_bdd_above Nat.decreasing_induction_of_not_bddAbove

theorem Nat.decreasing_induction_of_infinite (hP : { x | P x }.Infinite) (n : ℕ) : P n :=
  Nat.decreasing_induction_of_not_bddAbove h (mt BddAbove.finite hP) n
#align nat.decreasing_induction_of_infinite Nat.decreasing_induction_of_infinite

theorem Nat.cauchy_induction' (seed : ℕ) (hs : P seed) (hi : ∀ x, seed ≤ x → P x → ∃ y, x < y ∧ P y)
    (n : ℕ) : P n := by
  apply Nat.decreasing_induction_of_infinite h fun hf => _
  intro hf
  obtain ⟨m, hP, hm⟩ := hf.exists_maximal_wrt id _ ⟨seed, hs⟩
  obtain ⟨y, hl, hy⟩ := hi m (le_of_not_lt fun hl => hl.ne <| hm seed hs hl.le) hP
  exact hl.ne (hm y hy hl.le)
#align nat.cauchy_induction' Nat.cauchy_induction'

theorem Nat.cauchy_induction (seed : ℕ) (hs : P seed) (f : ℕ → ℕ)
    (hf : ∀ x, seed ≤ x → P x → x < f x ∧ P (f x)) (n : ℕ) : P n :=
  seed.cauchy_induction' h hs (fun x hl hx => ⟨f x, hf x hl hx⟩) n
#align nat.cauchy_induction Nat.cauchy_induction

theorem Nat.cauchy_induction_mul (k seed : ℕ) (hk : 1 < k) (hs : P seed.succ)
    (hm : ∀ x, seed < x → P x → P (k * x)) (n : ℕ) : P n := by
  apply Nat.cauchy_induction h _ hs (k * ·) fun x hl hP => ⟨_, hm x hl hP⟩
  intro _ hl _
  convert (mul_lt_mul_right <| seed.succ_pos.trans_le hl).2 hk
  rw [one_mul]
#align nat.cauchy_induction_mul Nat.cauchy_induction_mul

theorem Nat.cauchy_induction_two_mul (seed : ℕ) (hs : P seed.succ)
    (hm : ∀ x, seed < x → P x → P (2 * x)) (n : ℕ) : P n :=
  Nat.cauchy_induction_mul h 2 seed one_lt_two hs hm n
#align nat.cauchy_induction_two_mul Nat.cauchy_induction_two_mul

theorem Nat.pow_imp_self_of_one_lt {M} [Monoid M] (k : ℕ) (hk : 1 < k)
    (P : M → Prop) (hmul : ∀ x y, P x → P (x * y) ∨ P (y * x))
    (hpow : ∀ x, P (x ^ k) → P x) : ∀ n x, P (x ^ n) → P x :=
  k.cauchy_induction_mul (fun n ih x hx ↦ ih x <| (hmul _ x hx).elim
    (fun h ↦ by rwa [_root_.pow_succ]) fun h ↦ by rwa [_root_.pow_succ']) 0 hk
    (fun x hx ↦ pow_one x ▸ hx) fun n _ hn x hx ↦ hpow x <| hn _ <| (pow_mul x k n).subst hx

end Induction
