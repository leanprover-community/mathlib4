/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Finite.Card
import Mathlib.Algebra.BigOperators.Finprod

#align_import data.set.ncard from "leanprover-community/mathlib"@"74c2af38a828107941029b03839882c5c6f87a04"

/-!
# Noncomputable Set Cardinality

We define the cardinality `Set.ncard s` of a set `s` as a natural number. This function is
noncomputable (being defined in terms of `Nat.card`) and takes the value `0` if `s` is Infinite.

This can be seen as an API for `Nat.card α` in the special case where `α` is a subtype arising from
a set. It is intended as an alternative to `Finset.card` and `Fintype.card`,  both of which contain
data in their definition that can cause awkwardness when using `Set.toFinset`.  Using `Set.ncard`
allows cardinality computations to avoid `Finset`/`Fintype` completely, staying in `Set` and letting
Finiteness be handled explicitly, or (where a `Finite α` instance is present and the sets are
in `Set α`) via default arguments.

## Main Definitions

* `Set.ncard s` is the cardinality of the set `s` as a natural number, provided `s` is Finite.
  If `s` is Infinite, then `Set.ncard s = 0`.
* `toFinite_tac` is a tactic that tries to synthesize a `Set.Finite s` argument with
  `Set.toFinite`. This will work for `s : Set α` where there is a `Finite α` instance.

## Implementation Notes

The theorems in this file are very similar to those in `Data.Finset.Card`, but with `Set` operations
instead of `Finset`; most of the proofs invoke their `Finset` analogues. Nearly all the theorems
require finiteness of one or more of their arguments. We provide this assumption with a
default argument of the form `(hs : s.Finite := by toFinite_tac)`, where `toFinite_tac` will find
a `Finite s` term in the cases where `s` is a set in a `Finite` type.

Often, where there are two set arguments `s` and `t`, the Finiteness of one follows from the other
in the context of the theorem, in which case we only include the ones that are needed, and derive
the other inside the proof. A few of the theorems, such as `ncard_union_le` do not require
finiteness arguments; they are true by coincidence due to junk values.
-/

open BigOperators

variable {α β : Type _} {s t : Set α} {a b x y : α} {f : α → β}

/-- A tactic (for use in default params) that applies `Set.toFinite` to synthesize a
  `Set.Finite` term. -/
syntax "toFinite_tac" : tactic

macro_rules
  | `(tactic| toFinite_tac) => `(tactic| apply Set.toFinite)

namespace Set

/-- The cardinality of `s : Set α` . Has the junk value `0` if `s` is infinite -/
noncomputable def ncard (s : Set α) :=
  Nat.card s
#align set.ncard Set.ncard

theorem ncard_def (s : Set α) : s.ncard = Nat.card s := rfl
#align set.ncard_def Set.ncard_def

theorem ncard_eq_toFinset_card (s : Set α) (hs : s.Finite := by toFinite_tac) :
    s.ncard = hs.toFinset.card := by
  rw [ncard_def, @Nat.card_eq_fintype_card _ hs.fintype, @Finite.card_toFinset _ _ hs.fintype hs]
#align set.ncard_eq_to_finset_card Set.ncard_eq_toFinset_card

theorem ncard_eq_toFinset_card' (s : Set α) [Fintype s] :
    s.ncard = s.toFinset.card := by
  simp [ncard_def, Nat.card_eq_fintype_card]

theorem ncard_le_of_subset (hst : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ t.ncard :=
  @Finite.card_le_of_embedding _ _ (finite_coe_iff.mpr ht) (Set.embeddingOfSubset _ _ hst)
#align set.ncard_le_of_subset Set.ncard_le_of_subset

theorem ncard_mono [Finite α] : @Monotone (Set α) _ _ _ ncard := fun _ _ ↦ ncard_le_of_subset
#align set.ncard_mono Set.ncard_mono

@[simp] theorem ncard_eq_zero (hs : s.Finite := by toFinite_tac) :
    s.ncard = 0 ↔ s = ∅ := by
  rw [ncard_def, @Finite.card_eq_zero_iff _ hs.to_subtype, isEmpty_subtype,
    eq_empty_iff_forall_not_mem]
#align set.ncard_eq_zero Set.ncard_eq_zero

@[simp] theorem ncard_coe_Finset (s : Finset α) : (s : Set α).ncard = s.card := by
  rw [ncard_eq_toFinset_card _, Finset.finite_toSet_toFinset]
#align set.ncard_coe_finset Set.ncard_coe_Finset

theorem Infinite.ncard (hs : s.Infinite) : s.ncard = 0 :=
  @Nat.card_eq_zero_of_infinite _ hs.to_subtype
#align set.infinite.ncard Set.Infinite.ncard

theorem ncard_univ (α : Type _) : (univ : Set α).ncard = Nat.card α := by
  cases' finite_or_infinite α with h h
  · have hft := Fintype.ofFinite α
    rw [ncard_eq_toFinset_card, Finite.toFinset_univ, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [Nat.card_eq_zero_of_infinite, Infinite.ncard]
  exact infinite_univ
#align set.ncard_univ Set.ncard_univ

@[simp] theorem ncard_empty (α : Type _) : (∅ : Set α).ncard = 0 := by
  rw [ncard_eq_zero]
#align set.ncard_empty Set.ncard_empty

theorem ncard_pos (hs : s.Finite := by toFinite_tac) : 0 < s.ncard ↔ s.Nonempty := by
  rw [pos_iff_ne_zero, Ne.def, ncard_eq_zero hs, nonempty_iff_ne_empty]
#align set.ncard_pos Set.ncard_pos

theorem ncard_ne_zero_of_mem (h : a ∈ s) (hs : s.Finite := by toFinite_tac) : s.ncard ≠ 0 :=
  ((ncard_pos hs).mpr ⟨a, h⟩).ne.symm
#align set.ncard_ne_zero_of_mem Set.ncard_ne_zero_of_mem

theorem finite_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.Finite :=
  s.finite_or_infinite.elim id fun h ↦ (hs h.ncard).elim
#align set.finite_of_ncard_ne_zero Set.finite_of_ncard_ne_zero

theorem finite_of_ncard_pos (hs : 0 < s.ncard) : s.Finite :=
  finite_of_ncard_ne_zero hs.ne.symm
#align set.finite_of_ncard_pos Set.finite_of_ncard_pos

theorem nonempty_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; simp at hs
#align set.nonempty_of_ncard_ne_zero Set.nonempty_of_ncard_ne_zero

@[simp] theorem ncard_singleton (a : α) : ({a} : Set α).ncard = 1 := by
  simp [ncard_eq_toFinset_card]
#align set.ncard_singleton Set.ncard_singleton

theorem ncard_singleton_inter : ({a} ∩ s).ncard ≤ 1 := by
  classical
  rw [← inter_self {a}, inter_assoc, ncard_eq_toFinset_card _, Finite.toFinset_inter,
    Finite.toFinset_singleton]
  · apply Finset.card_singleton_inter
  all_goals toFinite_tac
#align set.ncard_singleton_inter Set.ncard_singleton_inter

section InsertErase

@[simp] theorem ncard_insert_of_not_mem (h : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    (insert a s).ncard = s.ncard + 1 := by
  classical
  have hft := hs.fintype
  rw [ncard_eq_toFinset_card _, ncard_eq_toFinset_card _, Finite.toFinset_insert,
    Finset.card_insert_of_not_mem]
  rwa [Finite.mem_toFinset]
#align set.ncard_insert_of_not_mem Set.ncard_insert_of_not_mem

theorem ncard_insert_of_mem (h : a ∈ s) : ncard (insert a s) = s.ncard := by rw [insert_eq_of_mem h]
#align set.ncard_insert_of_mem Set.ncard_insert_of_mem

theorem ncard_insert_le (a : α) (s : Set α) : (insert a s).ncard ≤ s.ncard + 1 := by
  obtain hs | hs := s.finite_or_infinite
  · exact (em (a ∈ s)).elim (fun h ↦ (ncard_insert_of_mem h).trans_le (Nat.le_succ _))
      (fun h ↦ by rw [ncard_insert_of_not_mem h hs])
  rw [(hs.mono (subset_insert a s)).ncard]
  exact Nat.zero_le _
#align set.ncard_insert_le Set.ncard_insert_le

theorem ncard_insert_eq_ite [Decidable (a ∈ s)] (hs : s.Finite := by toFinite_tac) :
    ncard (insert a s) = if a ∈ s then s.ncard else s.ncard + 1 := by
  by_cases h : a ∈ s
  · rw [ncard_insert_of_mem h, if_pos h]
  · rw [ncard_insert_of_not_mem h hs, if_neg h]
#align set.ncard_insert_eq_ite Set.ncard_insert_eq_ite

theorem ncard_le_ncard_insert (a : α) (s : Set α) : s.ncard ≤ (insert a s).ncard := by
  classical
  refine'
    s.finite_or_infinite.elim (fun h ↦ _) (fun h ↦ by (rw [h.ncard]; exact Nat.zero_le _))
  rw [ncard_insert_eq_ite h]; split_ifs <;> simp
#align set.ncard_le_ncard_insert Set.ncard_le_ncard_insert

@[simp] theorem ncard_pair (h : a ≠ b) : ({a, b} : Set α).ncard = 2 := by
  rw [ncard_insert_of_not_mem, ncard_singleton]; simpa
#align set.card_doubleton Set.ncard_pair

@[simp] theorem ncard_diff_singleton_add_one (h : a ∈ s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard + 1 = s.ncard := by
  have h' : a ∉ s \ {a} := by rw [mem_diff_singleton]; tauto
  rw [← ncard_insert_of_not_mem h' (hs.diff {a})]
  congr
  simpa
#align set.ncard_diff_singleton_add_one Set.ncard_diff_singleton_add_one

@[simp] theorem ncard_diff_singleton_of_mem (h : a ∈ s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard = s.ncard - 1 :=
  eq_tsub_of_add_eq (ncard_diff_singleton_add_one h hs)
#align set.ncard_diff_singleton_of_mem Set.ncard_diff_singleton_of_mem

theorem ncard_diff_singleton_lt_of_mem (h : a ∈ s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard < s.ncard := by
  rw [← ncard_diff_singleton_add_one h hs]
  apply lt_add_one
#align set.ncard_diff_singleton_lt_of_mem Set.ncard_diff_singleton_lt_of_mem

theorem ncard_diff_singleton_le (s : Set α) (a : α) : (s \ {a}).ncard ≤ s.ncard := by
  obtain hs | hs := s.finite_or_infinite
  · apply ncard_le_of_subset (diff_subset _ _) hs
  convert @zero_le ℕ _ _
  exact (hs.diff (by simp : Set.Finite {a})).ncard
#align set.ncard_diff_singleton_le Set.ncard_diff_singleton_le

theorem pred_ncard_le_ncard_diff_singleton (s : Set α) (a : α) : s.ncard - 1 ≤ (s \ {a}).ncard := by
  cases' s.finite_or_infinite with hs hs
  · by_cases h : a ∈ s
    · rw [ncard_diff_singleton_of_mem h hs]
    rw [diff_singleton_eq_self h]
    apply Nat.pred_le
  convert Nat.zero_le _
  rw [hs.ncard]
#align set.pred_ncard_le_ncard_diff_singleton Set.pred_ncard_le_ncard_diff_singleton

theorem ncard_exchange (ha : a ∉ s) (hb : b ∈ s) : (insert a (s \ {b})).ncard = s.ncard := by
  cases' s.finite_or_infinite with h h
  · haveI := h.to_subtype
    rw [ncard_insert_of_not_mem, ncard_diff_singleton_add_one hb]
    simp [mem_diff, not_and, not_not, ha];
  rw [((h.diff (Set.toFinite {b})).mono (subset_insert _ _)).ncard, h.ncard]
#align set.ncard_exchange Set.ncard_exchange

theorem ncard_exchange' (ha : a ∉ s) (hb : b ∈ s) : (insert a s \ {b}).ncard = s.ncard := by
  rw [← ncard_exchange ha hb, ← singleton_union, ← singleton_union, union_diff_distrib,
    @diff_singleton_eq_self _ b {a} fun h ↦ ha (by rwa [← mem_singleton_iff.mp h])]
#align set.ncard_exchange' Set.ncard_exchange'

end InsertErase

theorem ncard_image_le (hs : s.Finite := by toFinite_tac) : (f '' s).ncard ≤ s.ncard := by
  classical
  rw [ncard_eq_toFinset_card s hs]
  convert @Finset.card_image_le _ _ hs.toFinset f _
  simp only
  rw [@ncard_eq_toFinset_card _ _ (hs.image f), Finite.toFinset_image]
#align set.ncard_image_le Set.ncard_image_le

theorem ncard_image_of_injOn (H : Set.InjOn f s) : (f '' s).ncard = s.ncard := by
  classical
  cases' s.finite_or_infinite with h h
  · haveI := @Fintype.ofFinite s h.to_subtype
    haveI := @Fintype.ofFinite _ (h.image f).to_subtype
    convert card_image_of_inj_on H <;> simp [ncard_def]
  rw [h.ncard, ((infinite_image_iff H).mpr h).ncard]
#align set.ncard_image_of_inj_on Set.ncard_image_of_injOn

theorem injOn_of_ncard_image_eq (h : (f '' s).ncard = s.ncard) (hs : s.Finite := by toFinite_tac) :
    Set.InjOn f s := by
  classical
  have hft := hs.fintype
  rw [@ncard_eq_toFinset_card _ _ (hs.image f), @ncard_eq_toFinset_card _ _ hs] at h
  rw [←coe_toFinset s]
  apply Finset.injOn_of_card_image_eq
  convert h
  · ext; simp
  ext; simp
#align set.inj_on_of_ncard_image_eq Set.injOn_of_ncard_image_eq

theorem ncard_image_iff (hs : s.Finite := by toFinite_tac) :
    (f '' s).ncard = s.ncard ↔ Set.InjOn f s :=
  ⟨fun h ↦ injOn_of_ncard_image_eq h hs, ncard_image_of_injOn⟩
#align set.ncard_image_iff Set.ncard_image_iff

theorem ncard_image_of_injective (s : Set α) (H : f.Injective) : (f '' s).ncard = s.ncard :=
  ncard_image_of_injOn fun _ _ _ _ h ↦ H h
#align set.ncard_image_of_injective Set.ncard_image_of_injective

theorem ncard_preimage_of_injective_subset_range {s : Set β} (H : f.Injective)
  (hs : s ⊆ Set.range f) :
    (f ⁻¹' s).ncard = s.ncard := by
  rw [← ncard_image_of_injective _ H, image_preimage_eq_iff.mpr hs]
#align set.ncard_preimage_of_injective_subset_range Set.ncard_preimage_of_injective_subset_range

theorem fiber_ncard_ne_zero_iff_mem_image {y : β} (hs : s.Finite := by toFinite_tac) :
    { x ∈ s | f x = y }.ncard ≠ 0 ↔ y ∈ f '' s := by
  refine' ⟨nonempty_of_ncard_ne_zero, _⟩
  rintro ⟨z, hz, rfl⟩
  exact @ncard_ne_zero_of_mem _ ({ x ∈ s | f x = f z }) z (mem_sep hz rfl)
    (hs.subset (sep_subset _ _))
#align set.fiber_ncard_ne_zero_iff_mem_image Set.fiber_ncard_ne_zero_iff_mem_image

@[simp] theorem ncard_map (f : α ↪ β) : (f '' s).ncard = s.ncard :=
  ncard_image_of_injective _ f.inj'
#align set.ncard_map Set.ncard_map

@[simp] theorem ncard_subtype (P : α → Prop) (s : Set α) :
    { x : Subtype P | (x : α) ∈ s }.ncard = (s ∩ setOf P).ncard := by
  convert (ncard_image_of_injective _ (@Subtype.coe_injective _ P)).symm
  ext x
  simp [←and_assoc, exists_eq_right]
#align set.ncard_subtype Set.ncard_subtype

@[simp] theorem Nat.card_coe_set_eq (s : Set α) : Nat.card s = s.ncard := by
  convert (ncard_image_of_injective univ Subtype.coe_injective).symm using 1
  · rw [ncard_univ]
  simp
#align set.nat.card_coe_set_eq Set.Nat.card_coe_set_eq

theorem ncard_inter_le_ncard_left (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    (s ∩ t).ncard ≤ s.ncard :=
  ncard_le_of_subset (inter_subset_left _ _) hs
#align set.ncard_inter_le_ncard_left Set.ncard_inter_le_ncard_left

theorem ncard_inter_le_ncard_right (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    (s ∩ t).ncard ≤ t.ncard :=
  ncard_le_of_subset (inter_subset_right _ _) ht
#align set.ncard_inter_le_ncard_right Set.ncard_inter_le_ncard_right

theorem eq_of_subset_of_ncard_le (h : s ⊆ t) (h' : t.ncard ≤ s.ncard)
    (ht : t.Finite := by toFinite_tac) : s = t := by
  have htfin := ht.fintype
  have hft := (ht.subset h).fintype
  rw [← @toFinset_inj]
  apply Finset.eq_of_subset_of_card_le
  · simpa
  rw [ncard_eq_toFinset_card _ ht, ncard_eq_toFinset_card _ (ht.subset h)] at h'
  convert h'
  · ext; simp
  ext; simp
#align set.eq_of_subset_of_ncard_le Set.eq_of_subset_of_ncard_le

theorem subset_iff_eq_of_ncard_le (h : t.ncard ≤ s.ncard) (ht : t.Finite := by toFinite_tac) :
    s ⊆ t ↔ s = t :=
  ⟨fun hst ↦ eq_of_subset_of_ncard_le hst h ht, Eq.subset'⟩
#align set.subset_iff_eq_of_ncard_le Set.subset_iff_eq_of_ncard_le

theorem map_eq_of_subset {f : α ↪ α} (h : f '' s ⊆ s) (hs : s.Finite := by toFinite_tac) :
    f '' s = s :=
  eq_of_subset_of_ncard_le h (ncard_map _).ge hs
#align set.map_eq_of_subset Set.map_eq_of_subset

theorem sep_of_ncard_eq {P : α → Prop} (h : { x ∈ s | P x }.ncard = s.ncard) (ha : a ∈ s)
    (hs : s.Finite := by toFinite_tac) : P a :=
  sep_eq_self_iff_mem_true.mp (eq_of_subset_of_ncard_le (by simp) h.symm.le hs) _ ha
#align set.sep_of_ncard_eq Set.sep_of_ncard_eq

theorem ncard_lt_ncard (h : s ⊂ t) (ht : t.Finite := by toFinite_tac) :
    s.ncard < t.ncard := by
  rw [ncard_eq_toFinset_card _ (ht.subset h.subset), ncard_eq_toFinset_card t ht]
  refine' Finset.card_lt_card _
  rwa [Finite.toFinset_ssubset_toFinset]
#align set.ncard_lt_ncard Set.ncard_lt_ncard

theorem ncard_strictMono [Finite α] : @StrictMono (Set α) _ _ _ ncard :=
  fun _ _ h ↦ ncard_lt_ncard h
#align set.ncard_strict_mono Set.ncard_strictMono

theorem ncard_eq_of_bijective {n : ℕ} (f : ∀ i, i < n → α)
    (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a) (hf' : ∀ (i) (h : i < n), f i h ∈ s)
    (f_inj : ∀ (i j) (hi : i < n) (hj : j < n), f i hi = f j hj → i = j)
    (hs : s.Finite := by toFinite_tac) :
    s.ncard = n := by
  rw [ncard_eq_toFinset_card _ hs]
  apply Finset.card_eq_of_bijective
  all_goals simpa
#align set.ncard_eq_of_bijective Set.ncard_eq_of_bijective

theorem ncard_congr {t : Set β} (f : ∀ a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
    (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) :
    s.ncard = t.ncard := by
  set f' : s → t := fun x ↦ ⟨f x.1 x.2, h₁ _ _⟩
  have hbij : f'.Bijective := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [Subtype.mk.injEq] at hxy ⊢
      exact h₂ _ _ hx hy hxy
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := h₃ y hy
    simp only [Subtype.mk.injEq, Subtype.exists]
    exact ⟨_, ha, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective f' hbij)
#align set.ncard_congr Set.ncard_congr

theorem ncard_le_ncard_of_injOn {t : Set β} (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (f_inj : InjOn f s)
    (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ t.ncard := by
  cases' s.finite_or_infinite with h h
  · haveI := h.to_subtype
    rw [ncard_eq_toFinset_card _ ht, ncard_eq_toFinset_card _ (toFinite s)]
    exact Finset.card_le_card_of_inj_on f (by simpa) (by simpa)
  convert Nat.zero_le _
  rw [h.ncard]
#align set.ncard_le_ncard_of_inj_on Set.ncard_le_ncard_of_injOn

theorem exists_ne_map_eq_of_ncard_lt_of_maps_to {t : Set β} (hc : t.ncard < s.ncard) {f : α → β}
  (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Finite := by toFinite_tac) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  by_contra h'
  simp only [Ne.def, exists_prop, not_exists, not_and, not_imp_not] at h'
  exact (ncard_le_ncard_of_injOn f hf h' ht).not_lt hc
#align set.exists_ne_map_eq_of_ncard_lt_of_maps_to Set.exists_ne_map_eq_of_ncard_lt_of_maps_to

theorem le_ncard_of_inj_on_range {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
  (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) (hs : s.Finite := by toFinite_tac) :
    n ≤ s.ncard := by
  rw [ncard_eq_toFinset_card _ hs]
  apply Finset.le_card_of_inj_on_range <;> simpa
#align set.le_ncard_of_inj_on_range Set.le_ncard_of_inj_on_range

theorem surj_on_of_inj_on_of_ncard_le {t : Set β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
  (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : t.ncard ≤ s.ncard)
  (ht : t.Finite := by toFinite_tac) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  intro b hb
  set f' : s → t := fun x ↦ ⟨f x.1 x.2, hf _ _⟩
  have finj : f'.Injective := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk.injEq] at hxy ⊢
    apply hinj _ _ hx hy hxy
  have hft := ht.fintype
  have hft' := Fintype.ofInjective f' finj
  simp_rw [ncard_eq_toFinset_card] at hst
  set f'' : ∀ a, a ∈ s.toFinset → β := fun a h ↦ f a (by simpa using h)
  convert @Finset.surj_on_of_inj_on_of_card_le _ _ _ t.toFinset f'' _ _ _ _ (by simpa)
  · simp
  · simp [hf]
  · intros a₁ a₂ ha₁ ha₂ h
    rw [mem_toFinset] at ha₁ ha₂
    exact hinj _ _ ha₁ ha₂ h
  rwa [←ncard_eq_toFinset_card', ←ncard_eq_toFinset_card']
#align set.surj_on_of_inj_on_of_ncard_le Set.surj_on_of_inj_on_of_ncard_le

theorem inj_on_of_surj_on_of_ncard_le {t : Set β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀ b ∈ t, ∃ a ha, b = f a ha) (hst : s.ncard ≤ t.ncard) ⦃a₁ a₂⦄ (ha₁ : a₁ ∈ s)
    (ha₂ : a₂ ∈ s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) (hs : s.Finite := by toFinite_tac) :
    a₁ = a₂ := by
  classical
  set f' : s → t := fun x ↦ ⟨f x.1 x.2, hf _ _⟩
  have hsurj : f'.Surjective := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := hsurj y hy
    simp only [Subtype.mk.injEq, Subtype.exists]
    exact ⟨_, ha, rfl⟩
  haveI := hs.fintype
  haveI := Fintype.ofSurjective _ hsurj
  simp_rw [ncard_eq_toFinset_card] at hst
  set f'' : ∀ a, a ∈ s.toFinset → β := fun a h ↦ f a (by simpa using h)
  exact
    @Finset.inj_on_of_surj_on_of_card_le _ _ _ t.toFinset f''
      (fun a ha ↦ by { rw [mem_toFinset] at ha ⊢; exact hf a ha }) (by simpa)
      (by { rwa [←ncard_eq_toFinset_card', ←ncard_eq_toFinset_card'] }) a₁ a₂
      (by simpa) (by simpa) (by simpa)
#align set.inj_on_of_surj_on_of_ncard_le Set.inj_on_of_surj_on_of_ncard_le

section Lattice

theorem ncard_union_add_ncard_inter (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∪ t).ncard + (s ∩ t).ncard = s.ncard + t.ncard := by
  have hu := hs.union ht
  have hi := hs.subset (inter_subset_left s t)
  classical
  rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht, ncard_eq_toFinset_card _ hu,
    ncard_eq_toFinset_card _ hi, Finite.toFinset_union, Finite.toFinset_inter]
  · exact Finset.card_union_add_card_inter _ _
#align set.ncard_union_add_ncard_inter Set.ncard_union_add_ncard_inter

theorem ncard_inter_add_ncard_union (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∩ t).ncard + (s ∪ t).ncard = s.ncard + t.ncard := by
  rw [add_comm, ncard_union_add_ncard_inter _ _ hs ht]
#align set.ncard_inter_add_ncard_union Set.ncard_inter_add_ncard_union

theorem ncard_union_le (s t : Set α) : (s ∪ t).ncard ≤ s.ncard + t.ncard := by
  classical
  cases' (s ∪ t).finite_or_infinite with h h
  · have hs := h.subset (subset_union_left s t)
    have ht := h.subset (subset_union_right s t)
    rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht, ncard_eq_toFinset_card _ h,
      Finite.toFinset_union]
    exact Finset.card_union_le _ _
  convert Nat.zero_le _
  rw [h.ncard]
#align set.ncard_union_le Set.ncard_union_le

theorem ncard_union_eq (h : Disjoint s t) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∪ t).ncard = s.ncard + t.ncard := by
  classical
  rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht,
    ncard_eq_toFinset_card _ (hs.union ht), Finite.toFinset_union]
  refine' Finset.card_union_eq _
  rwa [Finite.disjoint_toFinset]
#align set.ncard_union_eq Set.ncard_union_eq

theorem ncard_diff_add_ncard_eq_ncard (h : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    (t \ s).ncard + s.ncard = t.ncard := by
  classical
  rw [ncard_eq_toFinset_card _ ht, ncard_eq_toFinset_card _ (ht.subset h),
    ncard_eq_toFinset_card _ (ht.diff s), Finite.toFinset_diff]
  refine' Finset.card_sdiff_add_card_eq_card _
  rwa [Finite.toFinset_subset_toFinset]
#align set.ncard_diff_add_ncard_eq_ncard Set.ncard_diff_add_ncard_eq_ncard

theorem ncard_diff (h : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    (t \ s).ncard = t.ncard - s.ncard := by
  rw [← ncard_diff_add_ncard_eq_ncard h ht, add_tsub_cancel_right]
#align set.ncard_diff Set.ncard_diff

theorem ncard_le_ncard_diff_add_ncard (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ (s \ t).ncard + t.ncard := by
  cases' s.finite_or_infinite with h h
  · rw [← diff_inter_self_eq_diff, ← ncard_diff_add_ncard_eq_ncard (inter_subset_right t s) h,
      add_le_add_iff_left]
    apply ncard_inter_le_ncard_left _ _ ht
  convert Nat.zero_le _
  rw [h.ncard]
#align set.ncard_le_ncard_diff_add_ncard Set.ncard_le_ncard_diff_add_ncard

theorem le_ncard_diff (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    t.ncard - s.ncard ≤ (t \ s).ncard :=
  tsub_le_iff_left.mpr (by rw [add_comm]; apply ncard_le_ncard_diff_add_ncard _ _ hs)
#align set.le_ncard_diff Set.le_ncard_diff

theorem ncard_diff_add_ncard (s t : Set α) (hs : s.Finite := by toFinite_tac)
  (ht : t.Finite := by toFinite_tac) :
    (s \ t).ncard + t.ncard = (s ∪ t).ncard := by
  rw [← union_diff_right, ncard_diff_add_ncard_eq_ncard (subset_union_right s t) (hs.union ht)]
#align set.ncard_diff_add_ncard Set.ncard_diff_add_ncard

theorem diff_nonempty_of_ncard_lt_ncard (h : s.ncard < t.ncard) (hs : s.Finite := by toFinite_tac) :
    (t \ s).Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Ne.def, diff_eq_empty]
  exact fun h' ↦ h.not_le (ncard_le_of_subset h' hs)
#align set.diff_nonempty_of_ncard_lt_ncard Set.diff_nonempty_of_ncard_lt_ncard

theorem exists_mem_not_mem_of_ncard_lt_ncard (h : s.ncard < t.ncard)
  (hs : s.Finite := by toFinite_tac) : ∃ e, e ∈ t ∧ e ∉ s :=
  diff_nonempty_of_ncard_lt_ncard h hs
#align set.exists_mem_not_mem_of_ncard_lt_ncard Set.exists_mem_not_mem_of_ncard_lt_ncard

@[simp] theorem ncard_inter_add_ncard_diff_eq_ncard (s t : Set α)
    (hs : s.Finite := by toFinite_tac) :
    (s ∩ t).ncard + (s \ t).ncard = s.ncard := by
  simp_rw [← ncard_diff_add_ncard_eq_ncard (diff_subset s t) hs, sdiff_sdiff_right_self,
    inf_eq_inter]
#align set.ncard_inter_add_ncard_diff_eq_ncard Set.ncard_inter_add_ncard_diff_eq_ncard

theorem ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard = t.ncard ↔ (s \ t).ncard = (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_right_inj]
#align set.ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff Set.ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff

theorem ncard_le_ncard_iff_ncard_diff_le_ncard_diff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard ≤ t.ncard ↔ (s \ t).ncard ≤ (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_le_add_iff_left]
#align set.ncard_le_ncard_iff_ncard_diff_le_ncard_diff
  Set.ncard_le_ncard_iff_ncard_diff_le_ncard_diff

theorem ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard < t.ncard ↔ (s \ t).ncard < (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_lt_add_iff_left]
#align set.ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff Set.ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff

theorem ncard_add_ncard_compl (s : Set α) (hs : s.Finite := by toFinite_tac)
    (hsc : sᶜ.Finite := by toFinite_tac) : s.ncard + sᶜ.ncard = Nat.card α := by
  rw [← ncard_univ, ← ncard_union_eq (@disjoint_compl_right _ _ s) hs hsc, union_compl_self]
#align set.ncard_add_ncard_compl Set.ncard_add_ncard_compl

end Lattice

/-- Given a set `t` and a set `s` inside it, we can shrink `t` to any appropriate size, and keep `s`
    inside it. -/
theorem exists_intermediate_Set (i : ℕ) (h₁ : i + s.ncard ≤ t.ncard) (h₂ : s ⊆ t) :
    ∃ r : Set α, s ⊆ r ∧ r ⊆ t ∧ r.ncard = i + s.ncard := by
  cases' t.finite_or_infinite with ht ht
  · rw [ncard_eq_toFinset_card _ (ht.subset h₂)] at h₁ ⊢
    rw [ncard_eq_toFinset_card t ht] at h₁
    obtain ⟨r', hsr', hr't, hr'⟩ := Finset.exists_intermediate_set _ h₁ (by simpa)
    exact ⟨r', by simpa using hsr', by simpa using hr't, by rw [← hr', ncard_coe_Finset]⟩
  rw [ht.ncard] at h₁
  have h₁' := Nat.eq_zero_of_le_zero h₁
  rw [add_eq_zero_iff] at h₁'
  refine' ⟨t, h₂, rfl.subset, _⟩
  rw [h₁'.2, h₁'.1, ht.ncard, add_zero]
#align set.exists_intermediate_set Set.exists_intermediate_Set

theorem exists_intermediate_set' {m : ℕ} (hs : s.ncard ≤ m) (ht : m ≤ t.ncard) (h : s ⊆ t) :
    ∃ r : Set α, s ⊆ r ∧ r ⊆ t ∧ r.ncard = m := by
  obtain ⟨r, hsr, hrt, hc⟩ :=
    exists_intermediate_Set (m - s.ncard) (by rwa [tsub_add_cancel_of_le hs]) h
  rw [tsub_add_cancel_of_le hs] at hc
  exact ⟨r, hsr, hrt, hc⟩
#align set.exists_intermediate_set' Set.exists_intermediate_set'

/-- We can shrink `s` to any smaller size. -/
theorem exists_smaller_set (s : Set α) (i : ℕ) (h₁ : i ≤ s.ncard) :
    ∃ t : Set α, t ⊆ s ∧ t.ncard = i :=
  (exists_intermediate_Set i (by simpa) (empty_subset s)).imp fun t ht ↦
    ⟨ht.2.1, by simpa using ht.2.2⟩
#align set.exists_smaller_set Set.exists_smaller_set

theorem Infinite.exists_subset_ncard_eq {s : Set α} (hs : s.Infinite) (k : ℕ) :
    ∃ t, t ⊆ s ∧ t.Finite ∧ t.ncard = k := by
  have := hs.to_subtype
  obtain ⟨t', -, rfl⟩ := @Infinite.exists_subset_card_eq s univ infinite_univ k
  refine' ⟨Subtype.val '' (t' : Set s), by simp, Finite.image _ (by simp), _⟩
  rw [ncard_image_of_injective _ Subtype.coe_injective]
  simp
#align set.Infinite.exists_subset_ncard_eq Set.Infinite.exists_subset_ncard_eq

theorem Infinite.exists_supset_ncard_eq {s t : Set α} (ht : t.Infinite) (hst : s ⊆ t)
    (hs : s.Finite) {k : ℕ} (hsk : s.ncard ≤ k) : ∃ s', s ⊆ s' ∧ s' ⊆ t ∧ s'.ncard = k := by
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.diff hs).exists_subset_ncard_eq (k - s.ncard)
  refine' ⟨s ∪ s₁, subset_union_left _ _, union_subset hst (hs₁.trans (diff_subset _ _)), _⟩
  rwa [ncard_union_eq (disjoint_of_subset_right hs₁ disjoint_sdiff_right) hs hs₁fin, hs₁card,
    add_tsub_cancel_of_le]
#align set.infinite.exists_supset_ncard_eq Set.Infinite.exists_supset_ncard_eq

theorem exists_subset_or_subset_of_two_mul_lt_ncard {n : ℕ} (hst : 2 * n < (s ∪ t).ncard) :
    ∃ r : Set α, n < r.ncard ∧ (r ⊆ s ∨ r ⊆ t) := by
  classical
  have hu := finite_of_ncard_ne_zero ((Nat.zero_le _).trans_lt hst).ne.symm
  rw [ncard_eq_toFinset_card _ hu,
    Finite.toFinset_union (hu.subset (subset_union_left _ _))
      (hu.subset (subset_union_right _ _))] at hst
  obtain ⟨r', hnr', hr'⟩ := Finset.exists_subset_or_subset_of_two_mul_lt_card hst
  exact ⟨r', by simpa, by simpa using hr'⟩
#align set.exists_subset_or_subset_of_two_mul_lt_ncard
  Set.exists_subset_or_subset_of_two_mul_lt_ncard

/-! ### Explicit description of a set from its cardinality -/

@[simp] theorem ncard_eq_one : s.ncard = 1 ↔ ∃ a, s = {a} := by
  refine' ⟨fun h ↦ _, by rintro ⟨a, rfl⟩; rw [ncard_singleton]⟩
  have hft := (finite_of_ncard_ne_zero (ne_zero_of_eq_one h)).fintype
  simp_rw [ncard_eq_toFinset_card', @Finset.card_eq_one _ (toFinset s)] at h
  refine' h.imp fun a ha ↦ _
  simp_rw [Set.ext_iff, mem_singleton_iff]
  simp only [Finset.ext_iff, mem_toFinset, Finset.mem_singleton] at ha
  exact ha
#align set.ncard_eq_one Set.ncard_eq_one

theorem exists_eq_insert_iff_ncard (hs : s.Finite := by toFinite_tac) :
    (∃ (a : α) (_ : a ∉ s), insert a s = t) ↔ s ⊆ t ∧ s.ncard + 1 = t.ncard := by
  classical
  cases' t.finite_or_infinite with ht ht
  · rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht,
      ←@Finite.toFinset_subset_toFinset _ _ _ hs ht, ←Finset.exists_eq_insert_iff]
    convert Iff.rfl using 2; simp
    ext x
    simp [Finset.ext_iff, Set.ext_iff]
  simp only [ht.ncard, exists_prop, add_eq_zero, and_false, iff_false, not_exists, not_and]
  rintro x - rfl
  exact ht (hs.insert x)
#align set.exists_eq_insert_iff_ncard Set.exists_eq_insert_iff_ncard

theorem ncard_le_one (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one, Finite.mem_toFinset]
#align set.ncard_le_one Set.ncard_le_one

theorem ncard_le_one_iff (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by
  rw [ncard_le_one hs]
  tauto
#align set.ncard_le_one_iff Set.ncard_le_one_iff

theorem ncard_le_one_iff_eq (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ s = ∅ ∨ ∃ a, s = {a} := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact iff_of_true (by simp) (Or.inl rfl)
  rw [ncard_le_one_iff hs]
  refine' ⟨fun h ↦ Or.inr ⟨x, (singleton_subset_iff.mpr hx).antisymm' fun y hy ↦ h hy hx⟩, _⟩
  rintro (rfl | ⟨a, rfl⟩)
  · exact (not_mem_empty _ hx).elim
  simp_rw [mem_singleton_iff] at hx ⊢; subst hx
  simp only [forall_eq_apply_imp_iff', imp_self, implies_true]
#align set.ncard_le_one_iff_eq Set.ncard_le_one_iff_eq

theorem ncard_le_one_iff_subset_singleton [Nonempty α]
  (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∃ x : α, s ⊆ {x} := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one_iff_subset_singleton,
    Finite.toFinset_subset, Finset.coe_singleton]
#align set.ncard_le_one_iff_subset_singleton Set.ncard_le_one_iff_subset_singleton

/-- A `Set` of a subsingleton type has cardinality at most one. -/
theorem ncard_le_one_of_subsingleton [Subsingleton α] (s : Set α) : s.ncard ≤ 1 := by
  rw [ncard_eq_toFinset_card]
  exact Finset.card_le_one_of_subsingleton _
#align ncard_le_one_of_subsingleton Set.ncard_le_one_of_subsingleton

theorem one_lt_ncard (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.one_lt_card, Finite.mem_toFinset]
#align set.one_lt_ncard Set.one_lt_ncard

theorem one_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b :=   by
  rw [one_lt_ncard hs]
  simp only [exists_prop, exists_and_left]
#align set.one_lt_ncard_iff Set.one_lt_ncard_iff

theorem two_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.two_lt_card_iff, Finite.mem_toFinset]
#align set.two_lt_ncard_iff Set.two_lt_ncard_iff

theorem two_lt_ncard (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp only [two_lt_ncard_iff hs, exists_and_left, exists_prop]
#align set.two_lt_card Set.two_lt_ncard

theorem exists_ne_of_one_lt_ncard (hs : 1 < s.ncard) (a : α) : ∃ b, b ∈ s ∧ b ≠ a := by
  have hsf := (finite_of_ncard_ne_zero (zero_lt_one.trans hs).ne.symm)
  rw [ncard_eq_toFinset_card _ hsf] at hs
  simpa only [Finite.mem_toFinset] using Finset.exists_ne_of_one_lt_card hs a
#align set.exists_ne_of_one_lt_ncard Set.exists_ne_of_one_lt_ncard

theorem eq_insert_of_ncard_eq_succ {n : ℕ} (h : s.ncard = n + 1) :
    ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  classical
  have hsf := finite_of_ncard_pos (n.zero_lt_succ.trans_eq h.symm)
  rw [ncard_eq_toFinset_card _ hsf, Finset.card_eq_succ] at h
  obtain ⟨a, t, hat, hts, rfl⟩ := h
  simp only [Finset.ext_iff, Finset.mem_insert, Finite.mem_toFinset] at hts
  refine' ⟨a, t, hat, _, _⟩
  · simp only [Finset.mem_coe, ext_iff, mem_insert_iff]
    tauto
  simp
#align set.eq_insert_of_ncard_eq_succ Set.eq_insert_of_ncard_eq_succ

theorem ncard_eq_succ {n : ℕ} (hs : s.Finite := by toFinite_tac) :
    s.ncard = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  refine' ⟨eq_insert_of_ncard_eq_succ, _⟩
  rintro ⟨a, t, hat, h, rfl⟩
  rw [← h, ncard_insert_of_not_mem hat (hs.subset ((subset_insert a t).trans_eq h))]
#align set.ncard_eq_succ Set.ncard_eq_succ

theorem ncard_eq_two : s.ncard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  classical
  refine' ⟨fun h ↦ _, _⟩
  · obtain ⟨x, t, hxt, rfl, ht⟩ := eq_insert_of_ncard_eq_succ h
    obtain ⟨y, rfl⟩ := ncard_eq_one.mp ht
    rw [mem_singleton_iff] at hxt
    exact ⟨_, _, hxt, rfl⟩
  rintro ⟨x, y, hxy, rfl⟩
  rw [ncard_eq_toFinset_card _, Finset.card_eq_two]
  exact ⟨x, y, hxy, by ext; simp⟩
#align set.ncard_eq_two Set.ncard_eq_two

theorem ncard_eq_three : s.ncard = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  refine' ⟨fun h ↦ _, _⟩
  · obtain ⟨x, t, hxt, rfl, ht⟩ := eq_insert_of_ncard_eq_succ h
    obtain ⟨y, z, hyz, rfl⟩ := ncard_eq_two.mp ht
    rw [mem_insert_iff, mem_singleton_iff, not_or] at hxt
    exact ⟨x, y, z, hxt.1, hxt.2, hyz, rfl⟩
  rintro ⟨x, y, z, xy, xz, yz, rfl⟩
  rw [ncard_insert_of_not_mem, ncard_insert_of_not_mem, ncard_singleton]
  · rwa [mem_singleton_iff]
  rw [mem_insert_iff, mem_singleton_iff]
  tauto
#align set.ncard_eq_three Set.ncard_eq_three

end Set
