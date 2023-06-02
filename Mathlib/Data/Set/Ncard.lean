/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson

! This file was ported from Lean 3 source module data.set.ncard
! leanprover-community/mathlib commit 74c2af38a828107941029b03839882c5c6f87a04
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Finite.Card
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Noncomputable Set Cardinality

We define the cardinality `Set.ncard s` of a set `s` as a natural number. This λction is
noncomputable (being defined in terms of `Nat.card`) and takes the value `0` if `s` is Infinite.

This can be seen as an API for `Nat.card α` in the special case where `α` is a subtype arising from
a set. It is intended as an alternative to `Finset.card` and `Fintype.card`,  both of which contain
data in their definition that can cause awkwardness when using `Set.toFinset`.  Using `Set.ncard`
allows cardinality computations to avoid `Finset`/`Fintype` completely, staying in `Set` and letting
Finiteness be handled explicitly, or (where a `Finite α` instance is present and the sets are
in `set α`) via default arguments.

## Main Definitions

* `Set.ncard s` is the cardinality of the set `s` as a natural number, provided `s` is Finite.
  If `s` is Infinite, then `set.ncard s = 0`.
* `toFinite_tac` is a tactic that tries to synthesize an `set.Finite s` argument with
  `set.toFinite`. This will work for `s : set α` where there is a `Finite α` instance.

## Implementation Notes

The lemmas in this file are very similar to those in `Data.Finset.Card`, but with `Set` operations
instead of `Finset`; most of the proofs invoke their `Finset` analogues. Nearly all the lemmas
require finiteness of one or more of their arguments. We provide this assumption with a
default argument of the form `(hs : s.Finite := by toFinite_tac)`, where `toFinite_tac` will find
a `Finite s` term in the cases where `s` is a set in a `Finite` type.

Often, where there are two set arguments `s` and `t`, the Finiteness of one follows from the other
in the context of the lemma, in which case we only include the ones that are needed, and derive the
other inside the proof. A few of the lemmas, such as `ncard_union_le` do not require finiteness
arguments; they are are true by coincidence due to junk values.
-/

open BigOperators

variable {α β : Type _} {s t : Set α} {a b x y : α} {f : α → β}

/-- A tactic (for use in default params) that applies `Set.toFinite` to synthesize a
  `Set.finite` term. -/
syntax "toFinite_tac" : tactic

macro_rules
  | `(tactic| toFinite_tac) => `(tactic| apply Set.toFinite)

namespace Set

/-- The cardinality of `s : set α` . Has the junk value `0` if `s` is Infinite -/
noncomputable def ncard (s : Set α) :=
  Nat.card s

lemma ncard_def (s : Set α) : s.ncard = Nat.card s := rfl

lemma ncard_eq_toFinset_card (s : Set α) (hs : s.Finite := by toFinite_tac) :
    s.ncard = hs.toFinset.card := by
  rw [ncard_def, @Nat.card_eq_fintype_card _ hs.fintype, @Finite.card_toFinset _ _ hs.fintype hs]

lemma ncard_eq_toFinset_card' (s : Set α) [Fintype s] :
    s.ncard = s.toFinset.card := by
  simp [ncard_def, Nat.card_eq_fintype_card]

lemma ncard_le_of_subset (hst : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ t.ncard :=
  @Finite.card_le_of_embedding _ _ (finite_coe_iff.mpr ht) (Set.embeddingOfSubset _ _ hst)

lemma ncard_mono [Finite α] : @Monotone (Set α) _ _ _ ncard := λ _ _ ↦ ncard_le_of_subset

@[simp] lemma ncard_eq_zero (hs : s.Finite := by toFinite_tac) :
    s.ncard = 0 ↔ s = ∅ := by
  rw [ncard_def, @Finite.card_eq_zero_iff _ hs.to_subtype, isEmpty_subtype,
    eq_empty_iff_forall_not_mem]

@[simp] lemma ncard_coe_Finset (s : Finset α) : (s : Set α).ncard = s.card := by
  rw [ncard_eq_toFinset_card _, Finset.finite_toSet_toFinset]

lemma Infinite.ncard (hs : s.Infinite) : s.ncard = 0 :=
  @Nat.card_eq_zero_of_infinite _ hs.to_subtype

lemma ncard_univ (α : Type _) : (univ : Set α).ncard = Nat.card α := by
  cases' finite_or_infinite α with h h
  · have hft := Fintype.ofFinite α
    rw [ncard_eq_toFinset_card, Finite.toFinset_univ, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [Nat.card_eq_zero_of_infinite, Infinite.ncard]
  exact infinite_univ

@[simp] lemma ncard_empty (α : Type _) : (∅ : Set α).ncard = 0 := by
  rw [ncard_eq_zero]

lemma ncard_pos (hs : s.Finite := by toFinite_tac) : 0 < s.ncard ↔ s.Nonempty := by
  rw [pos_iff_ne_zero, Ne.def, ncard_eq_zero hs, nonempty_iff_ne_empty]

lemma ncard_ne_zero_of_mem (h : a ∈ s) (hs : s.Finite := by toFinite_tac) : s.ncard ≠ 0 :=
  ((ncard_pos hs).mpr ⟨a, h⟩).ne.symm

lemma Finite_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.Finite :=
  s.finite_or_infinite.elim id λ h ↦ (hs h.ncard).elim

lemma Finite_of_ncard_pos (hs : 0 < s.ncard) : s.Finite :=
  Finite_of_ncard_ne_zero hs.ne.symm

lemma nonempty_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; simp at hs

@[simp] lemma ncard_singleton (a : α) : ({a} : Set α).ncard = 1 := by
  simp [ncard_eq_toFinset_card]

lemma ncard_singleton_inter : ({a} ∩ s).ncard ≤ 1 := by
  classical
  rw [← inter_self {a}, inter_assoc, ncard_eq_toFinset_card _, Finite.toFinset_inter,
    Finite.toFinset_singleton]
  · apply Finset.card_singleton_inter
  all_goals toFinite_tac
section InsertErase

@[simp] lemma ncard_insert_of_not_mem (h : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    (insert a s).ncard = s.ncard + 1 := by
  classical
  have hft := hs.fintype
  rw [ncard_eq_toFinset_card _, ncard_eq_toFinset_card _, Finite.toFinset_insert,
    Finset.card_insert_of_not_mem]
  rwa [Finite.mem_toFinset]

lemma ncard_insert_of_mem (h : a ∈ s) : ncard (insert a s) = s.ncard := by rw [insert_eq_of_mem h]

lemma ncard_insert_le (a : α) (s : Set α) : (insert a s).ncard ≤ s.ncard + 1 :=
  by
  obtain hs | hs := s.finite_or_infinite
  · exact (em (a ∈ s)).elim (λ h ↦ (ncard_insert_of_mem h).trans_le (Nat.le_succ _))
      (λ h ↦ by rw [ncard_insert_of_not_mem h hs])
  rw [(hs.mono (subset_insert a s)).ncard]
  exact Nat.zero_le _

lemma ncard_insert_eq_ite [Decidable (a ∈ s)] (hs : s.Finite := by toFinite_tac) :
    ncard (insert a s) = if a ∈ s then s.ncard else s.ncard + 1 := by
  by_cases h : a ∈ s
  · rw [ncard_insert_of_mem h, if_pos h]
  · rw [ncard_insert_of_not_mem h hs, if_neg h]

lemma ncard_le_ncard_insert (a : α) (s : Set α) : s.ncard ≤ (insert a s).ncard := by
  classical
  refine'
    s.finite_or_infinite.elim (λ h ↦ _) (λ h ↦ by (rw [h.ncard]; exact Nat.zero_le _))
  rw [ncard_insert_eq_ite h]; split_ifs <;> simp

@[simp] lemma card_doubleton (h : a ≠ b) : ({a, b} : Set α).ncard = 2 := by
  rw [ncard_insert_of_not_mem, ncard_singleton]; simpa

@[simp] lemma ncard_diff_singleton_add_one (h : a ∈ s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard + 1 = s.ncard := by
  have h' : a ∉ s \ {a} := by rw [mem_diff_singleton]; tauto
  rw [← ncard_insert_of_not_mem h' (hs.diff {a})]
  congr
  simpa

@[simp] lemma ncard_diff_singleton_of_mem (h : a ∈ s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard = s.ncard - 1 :=
  eq_tsub_of_add_eq (ncard_diff_singleton_add_one h hs)

lemma ncard_diff_singleton_lt_of_mem (h : a ∈ s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard < s.ncard := by
  rw [← ncard_diff_singleton_add_one h hs]
  apply lt_add_one

lemma ncard_diff_singleton_le (s : Set α) (a : α) : (s \ {a}).ncard ≤ s.ncard := by
  obtain hs | hs := s.finite_or_infinite
  · apply ncard_le_of_subset (diff_subset _ _) hs
  convert @zero_le ℕ _ _
  exact (hs.diff (by simp : Set.Finite {a})).ncard

lemma pred_ncard_le_ncard_diff_singleton (s : Set α) (a : α) : s.ncard - 1 ≤ (s \ {a}).ncard := by
  cases' s.finite_or_infinite with hs hs
  · by_cases h : a ∈ s
    · rw [ncard_diff_singleton_of_mem h hs]
    rw [diff_singleton_eq_self h]
    apply Nat.pred_le
  convert Nat.zero_le _
  rw [hs.ncard]

lemma ncard_exchange (ha : a ∉ s) (hb : b ∈ s) : (insert a (s \ {b})).ncard = s.ncard := by
  cases' s.finite_or_infinite with h h
  · haveI := h.to_subtype
    rw [ncard_insert_of_not_mem, ncard_diff_singleton_add_one hb]
    simp [mem_diff, not_and, not_not, ha];
  rw [((h.diff (Set.toFinite {b})).mono (subset_insert _ _)).ncard, h.ncard]

lemma ncard_exchange' (ha : a ∉ s) (hb : b ∈ s) : (insert a s \ {b}).ncard = s.ncard := by
  rw [← ncard_exchange ha hb, ← singleton_union, ← singleton_union, union_diff_distrib,
    @diff_singleton_eq_self _ b {a} λ h ↦ ha (by rwa [← mem_singleton_iff.mp h])]

end InsertErase

lemma ncard_image_le (hs : s.Finite := by toFinite_tac) : (f '' s).ncard ≤ s.ncard := by
  classical
  rw [ncard_eq_toFinset_card s hs]
  convert @Finset.card_image_le _ _ hs.toFinset f _
  simp only
  rw [@ncard_eq_toFinset_card _ _ (hs.image f), Finite.toFinset_image]

lemma ncard_image_of_injOn (H : Set.InjOn f s) : (f '' s).ncard = s.ncard := by
  classical
  cases' s.finite_or_infinite with h h
  · haveI := @Fintype.ofFinite s h.to_subtype
    haveI := @Fintype.ofFinite _ (h.image f).to_subtype
    convert card_image_of_inj_on H <;> simp [ncard_def]
  rw [h.ncard, ((infinite_image_iff H).mpr h).ncard]

lemma injOn_of_ncard_image_eq (h : (f '' s).ncard = s.ncard) (hs : s.Finite := by toFinite_tac) :
    Set.InjOn f s := by
  classical
  have hft := hs.fintype
  rw [@ncard_eq_toFinset_card _ _ (hs.image f), @ncard_eq_toFinset_card _ _ hs] at h
  rw [←coe_toFinset s]
  apply Finset.injOn_of_card_image_eq
  convert h
  · ext; simp
  ext; simp

lemma ncard_image_iff (hs : s.Finite := by toFinite_tac) :
    (f '' s).ncard = s.ncard ↔ Set.InjOn f s :=
  ⟨λ h ↦ injOn_of_ncard_image_eq h hs, ncard_image_of_injOn⟩

lemma ncard_image_of_injective (s : Set α) (H : f.Injective) : (f '' s).ncard = s.ncard :=
  ncard_image_of_injOn λ _ _ _ _ h ↦ H h

lemma ncard_preimage_of_injective_subset_range {s : Set β} (H : f.Injective)
  (hs : s ⊆ Set.range f) :
    (f ⁻¹' s).ncard = s.ncard := by
  rw [← ncard_image_of_injective _ H, image_preimage_eq_iff.mpr hs]

lemma fiber_ncard_ne_zero_iff_mem_image {y : β} (hs : s.Finite := by toFinite_tac) :
    { x ∈ s | f x = y }.ncard ≠ 0 ↔ y ∈ f '' s := by
  refine' ⟨nonempty_of_ncard_ne_zero, _⟩
  rintro ⟨z, hz, rfl⟩
  exact @ncard_ne_zero_of_mem _ ({ x ∈ s | f x = f z }) z (mem_sep hz rfl)
    (hs.subset (sep_subset _ _))

@[simp] lemma ncard_map (f : α ↪ β) : (f '' s).ncard = s.ncard :=
  ncard_image_of_injective _ f.inj'

@[simp] lemma ncard_subtype (P : α → Prop) (s : Set α) :
    { x : Subtype P | (x : α) ∈ s }.ncard = (s ∩ setOf P).ncard := by
  convert (ncard_image_of_injective _ (@Subtype.coe_injective _ P)).symm
  ext x
  simp [←and_assoc, exists_eq_right]

@[simp] lemma Nat.card_coe_set_eq (s : Set α) : Nat.card s = s.ncard := by
  convert (ncard_image_of_injective univ Subtype.coe_injective).symm using 1
  · rw [ncard_univ]
  simp

lemma ncard_inter_le_ncard_left (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    (s ∩ t).ncard ≤ s.ncard :=
  ncard_le_of_subset (inter_subset_left _ _) hs

lemma ncard_inter_le_ncard_right (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    (s ∩ t).ncard ≤ t.ncard :=
  ncard_le_of_subset (inter_subset_right _ _) ht

lemma eq_of_subset_of_ncard_le (h : s ⊆ t) (h' : t.ncard ≤ s.ncard)
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

lemma subset_iff_eq_of_ncard_le (h : t.ncard ≤ s.ncard) (ht : t.Finite := by toFinite_tac) :
    s ⊆ t ↔ s = t :=
  ⟨λ hst ↦ eq_of_subset_of_ncard_le hst h ht, Eq.subset'⟩

lemma map_eq_of_subset {f : α ↪ α} (h : f '' s ⊆ s) (hs : s.Finite := by toFinite_tac) :
    f '' s = s :=
  eq_of_subset_of_ncard_le h (ncard_map _).ge hs

lemma sep_of_ncard_eq {P : α → Prop} (h : { x ∈ s | P x }.ncard = s.ncard) (ha : a ∈ s)
    (hs : s.Finite := by toFinite_tac) : P a :=
  sep_eq_self_iff_mem_true.mp (eq_of_subset_of_ncard_le (by simp) h.symm.le hs) _ ha

lemma ncard_lt_ncard (h : s ⊂ t) (ht : t.Finite := by toFinite_tac) :
    s.ncard < t.ncard := by
  rw [ncard_eq_toFinset_card _ (ht.subset h.subset), ncard_eq_toFinset_card t ht]
  refine' Finset.card_lt_card _
  rwa [Finite.toFinset_ssubset_toFinset]

lemma ncard_strictMono [Finite α] : @StrictMono (Set α) _ _ _ ncard :=
  λ _ _ h ↦ ncard_lt_ncard h

lemma ncard_eq_of_bijective {n : ℕ} (f : ∀ i, i < n → α) (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a)
    (hf' : ∀ (i) (h : i < n), f i h ∈ s)
    (f_inj : ∀ (i j) (hi : i < n) (hj : j < n), f i hi = f j hj → i = j)
    (hs : s.Finite := by toFinite_tac) :
    s.ncard = n := by
  rw [ncard_eq_toFinset_card _ hs]
  apply Finset.card_eq_of_bijective
  all_goals simpa

lemma ncard_congr {t : Set β} (f : ∀ a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
    (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b)
    (hs : s.Finite := by toFinite_tac) :
    s.ncard = t.ncard := by
  classical
  set f' : s → t := λ x ↦ ⟨f x.1 x.2, h₁ _ _⟩
  have hbij : f'.Bijective := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [Subtype.mk.injEq] at hxy ⊢
      exact h₂ _ _ hx hy hxy
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := h₃ y hy
    simp only [Subtype.mk.injEq, Subtype.exists]
    exact ⟨_, ha, rfl⟩
  haveI := hs.to_subtype
  haveI := @Fintype.ofFinite _ (Finite.ofBijective hbij)
  haveI := Fintype.ofFinite s
  convert Fintype.card_of_bijective hbij
  <;> rw [ncard_def, Nat.card_eq_fintype_card]

lemma ncard_le_ncard_of_injOn {t : Set β} (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (f_inj : InjOn f s)
    (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ t.ncard := by
  cases' s.finite_or_infinite with h h
  · haveI := h.to_subtype
    rw [ncard_eq_toFinset_card _ ht, ncard_eq_toFinset_card _ (toFinite s)]
    exact Finset.card_le_card_of_inj_on f (by simpa) (by simpa)
  convert Nat.zero_le _
  rw [h.ncard]

lemma exists_ne_map_eq_of_ncard_lt_of_maps_to {t : Set β} (hc : t.ncard < s.ncard) {f : α → β}
  (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Finite := by toFinite_tac) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  by_contra h'
  simp only [Ne.def, exists_prop, not_exists, not_and, not_imp_not] at h'
  exact (ncard_le_ncard_of_injOn f hf h' ht).not_lt hc

lemma le_ncard_of_inj_on_range {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
  (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) (hs : s.Finite := by toFinite_tac) :
    n ≤ s.ncard := by
  rw [ncard_eq_toFinset_card _ hs]
  apply Finset.le_card_of_inj_on_range <;> simpa

lemma surj_on_of_inj_on_of_ncard_le {t : Set β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
  (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : t.ncard ≤ s.ncard)
  (ht : t.Finite := by toFinite_tac) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  intro b hb
  set f' : s → t := λ x ↦ ⟨f x.1 x.2, hf _ _⟩ with hf'
  have finj : f'.Injective := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [hf', Subtype.mk.injEq] at hxy ⊢
    apply hinj _ _ hx hy hxy
  have hft := ht.fintype
  have hft' := Fintype.ofInjective f' finj
  simp_rw [ncard_eq_toFinset_card] at hst
  set f'' : ∀ a, a ∈ s.toFinset → β := λ a h ↦ f a (by simpa using h)
  convert @Finset.surj_on_of_inj_on_of_card_le _ _ _ t.toFinset f'' _ _ _ (by simpa) (by simpa)
  · simp
  · simp [hf]
  · intros a₁ a₂ ha₁ ha₂ h
    rw [mem_toFinset] at ha₁ ha₂
    exact hinj _ _ ha₁ ha₂ h
  rwa [←ncard_eq_toFinset_card', ←ncard_eq_toFinset_card']

lemma inj_on_of_surj_on_of_ncard_le {t : Set β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀ b ∈ t, ∃ a ha, b = f a ha) (hst : s.ncard ≤ t.ncard) ⦃a₁ a₂⦄ (ha₁ : a₁ ∈ s)
    (ha₂ : a₂ ∈ s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) (hs : s.Finite := by toFinite_tac) :
    a₁ = a₂ := by
  classical
  set f' : s → t := λ x ↦ ⟨f x.1 x.2, hf _ _⟩
  have hsurj : f'.Surjective := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := hsurj y hy
    simp only [Subtype.mk.injEq, Subtype.exists]
    exact ⟨_, ha, rfl⟩
  haveI := hs.fintype
  haveI := Fintype.ofSurjective _ hsurj
  simp_rw [ncard_eq_toFinset_card] at hst
  set f'' : ∀ a, a ∈ s.toFinset → β := λ a h ↦ f a (by simpa using h)
  exact
    @Finset.inj_on_of_surj_on_of_card_le _ _ _ t.toFinset f''
      (λ a ha ↦ by { rw [mem_toFinset] at ha ⊢; exact hf a ha }) (by simpa)
      (by { rwa [←ncard_eq_toFinset_card', ←ncard_eq_toFinset_card'] }) a₁ a₂
      (by simpa) (by simpa) (by simpa)

section Lattice

lemma ncard_union_add_ncard_inter (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∪ t).ncard + (s ∩ t).ncard = s.ncard + t.ncard := by
  have hu := hs.union ht
  have hi := hs.subset (inter_subset_left s t)
  classical
  rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht, ncard_eq_toFinset_card _ hu,
    ncard_eq_toFinset_card _ hi, Finite.toFinset_union, Finite.toFinset_inter]
  · exact Finset.card_union_add_card_inter _ _

lemma ncard_inter_add_ncard_union (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∩ t).ncard + (s ∪ t).ncard = s.ncard + t.ncard := by
  rw [add_comm, ncard_union_add_ncard_inter _ _ hs ht]

lemma ncard_union_le (s t : Set α) : (s ∪ t).ncard ≤ s.ncard + t.ncard := by
  classical
  cases' (s ∪ t).finite_or_infinite with h h
  · have hs := h.subset (subset_union_left s t)
    have ht := h.subset (subset_union_right s t)
    rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht, ncard_eq_toFinset_card _ h,
      Finite.toFinset_union]
    exact Finset.card_union_le _ _
  convert Nat.zero_le _
  rw [h.ncard]

lemma ncard_union_eq (h : Disjoint s t) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∪ t).ncard = s.ncard + t.ncard := by
  classical
  rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht,
    ncard_eq_toFinset_card _ (hs.union ht), Finite.toFinset_union]
  refine' Finset.card_union_eq _
  rwa [Finite.disjoint_toFinset]

lemma ncard_diff_add_ncard_eq_ncard (h : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    (t \ s).ncard + s.ncard = t.ncard := by
  classical
  rw [ncard_eq_toFinset_card _ ht, ncard_eq_toFinset_card _ (ht.subset h),
    ncard_eq_toFinset_card _ (ht.diff s), Finite.toFinset_diff]
  refine' Finset.card_sdiff_add_card_eq_card _
  rwa [Finite.toFinset_subset_toFinset]

lemma ncard_diff (h : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    (t \ s).ncard = t.ncard - s.ncard := by
  rw [← ncard_diff_add_ncard_eq_ncard h ht, add_tsub_cancel_right]

lemma ncard_le_ncard_diff_add_ncard (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ (s \ t).ncard + t.ncard := by
  cases' s.finite_or_infinite with h h
  · rw [← diff_inter_self_eq_diff, ← ncard_diff_add_ncard_eq_ncard (inter_subset_right t s) h,
      add_le_add_iff_left]
    apply ncard_inter_le_ncard_left _ _ ht
  convert Nat.zero_le _
  rw [h.ncard]

lemma le_ncard_diff (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    t.ncard - s.ncard ≤ (t \ s).ncard :=
  tsub_le_iff_left.mpr (by rw [add_comm]; apply ncard_le_ncard_diff_add_ncard _ _ hs)

lemma ncard_diff_add_ncard (s t : Set α) (hs : s.Finite := by toFinite_tac)
  (ht : t.Finite := by toFinite_tac) :
    (s \ t).ncard + t.ncard = (s ∪ t).ncard := by
  rw [← union_diff_right, ncard_diff_add_ncard_eq_ncard (subset_union_right s t) (hs.union ht)]

lemma diff_nonempty_of_ncard_lt_ncard (h : s.ncard < t.ncard) (hs : s.Finite := by toFinite_tac) :
    (t \ s).Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Ne.def, diff_eq_empty]
  exact λ h' ↦ h.not_le (ncard_le_of_subset h' hs)

lemma exists_mem_not_mem_of_ncard_lt_ncard (h : s.ncard < t.ncard)
  (hs : s.Finite := by toFinite_tac) : ∃ e, e ∈ t ∧ e ∉ s :=
  diff_nonempty_of_ncard_lt_ncard h hs

@[simp] lemma ncard_inter_add_ncard_diff_eq_ncard (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    (s ∩ t).ncard + (s \ t).ncard = s.ncard := by
  simp_rw [← ncard_diff_add_ncard_eq_ncard (diff_subset s t) hs, sdiff_sdiff_right_self,
    inf_eq_inter]

lemma ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard = t.ncard ↔ (s \ t).ncard = (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_right_inj]

lemma ncard_le_ncard_iff_ncard_diff_le_ncard_diff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard ≤ t.ncard ↔ (s \ t).ncard ≤ (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_le_add_iff_left]

lemma ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard < t.ncard ↔ (s \ t).ncard < (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_lt_add_iff_left]

lemma ncard_add_ncard_compl (s : Set α) (hs : s.Finite := by toFinite_tac)
    (hsc : sᶜ.Finite := by toFinite_tac) : s.ncard + sᶜ.ncard = Nat.card α := by
  rw [← ncard_univ, ← ncard_union_eq (@disjoint_compl_right _ _ s) hs hsc, union_compl_self]

end Lattice

/-- Given a set `t` and a set `s` inside it, we can shrink `t` to any appropriate size, and keep `s`
    inside it. -/
lemma exists_intermediate_set (i : ℕ) (h₁ : i + s.ncard ≤ t.ncard) (h₂ : s ⊆ t) :
    ∃ r : Set α, s ⊆ r ∧ r ⊆ t ∧ r.ncard = i + s.ncard := by
  cases' t.finite_or_infinite with ht ht
  · have hft := ht.to_subtype
    have hfs := (ht.subset h₂).to_subtype
    rw [ncard_eq_toFinset_card _ (ht.subset h₂)] at h₁ ⊢
    rw [ncard_eq_toFinset_card t ht] at h₁
    obtain ⟨r', hsr', hr't, hr'⟩ := Finset.exists_intermediate_set _ h₁ (by simpa)
    exact ⟨r', by simpa using hsr', by simpa using hr't, by rw [← hr', ncard_coe_Finset]⟩
  rw [ht.ncard] at h₁
  have h₁' := Nat.eq_zero_of_le_zero h₁
  rw [add_eq_zero_iff] at h₁'
  refine' ⟨t, h₂, rfl.subset, _⟩
  rw [h₁'.2, h₁'.1, ht.ncard, add_zero]

lemma exists_intermediate_set' {m : ℕ} (hs : s.ncard ≤ m) (ht : m ≤ t.ncard) (h : s ⊆ t) :
    ∃ r : Set α, s ⊆ r ∧ r ⊆ t ∧ r.ncard = m := by
  obtain ⟨r, hsr, hrt, hc⟩ :=
    exists_intermediate_set (m - s.ncard) (by rwa [tsub_add_cancel_of_le hs]) h
  rw [tsub_add_cancel_of_le hs] at hc
  exact ⟨r, hsr, hrt, hc⟩

/-- We can shrink `s` to any smaller size. -/
lemma exists_smaller_set (s : Set α) (i : ℕ) (h₁ : i ≤ s.ncard) :
    ∃ t : Set α, t ⊆ s ∧ t.ncard = i :=
  (exists_intermediate_set i (by simpa) (empty_subset s)).imp λ t ht ↦
    ⟨ht.2.1, by simpa using ht.2.2⟩

lemma Infinite.exists_subset_ncard_eq {s : Set α} (hs : s.Infinite) (k : ℕ) :
    ∃ t, t ⊆ s ∧ t.Finite ∧ t.ncard = k := by
  have := hs.to_subtype
  obtain ⟨t', -, rfl⟩ := @Infinite.exists_subset_card_eq s univ infinite_univ k
  refine' ⟨Subtype.val '' (t' : Set s), by simp, Finite.image _ (by simp), _⟩
  rw [ncard_image_of_injective _ Subtype.coe_injective]
  simp

lemma Infinite.exists_supset_ncard_eq {s t : Set α} (ht : t.Infinite) (hst : s ⊆ t)
    (hs : s.Finite) {k : ℕ} (hsk : s.ncard ≤ k) : ∃ s', s ⊆ s' ∧ s' ⊆ t ∧ s'.ncard = k := by
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.diff hs).exists_subset_ncard_eq (k - s.ncard)
  refine' ⟨s ∪ s₁, subset_union_left _ _, union_subset hst (hs₁.trans (diff_subset _ _)), _⟩
  rwa [ncard_union_eq (disjoint_of_subset_right hs₁ disjoint_sdiff_right) hs hs₁fin, hs₁card,
    add_tsub_cancel_of_le]

lemma exists_subset_or_subset_of_two_mul_lt_ncard {n : ℕ} (hst : 2 * n < (s ∪ t).ncard) :
    ∃ r : Set α, n < r.ncard ∧ (r ⊆ s ∨ r ⊆ t) := by
  classical
  have hu := Finite_of_ncard_ne_zero ((Nat.zero_le _).trans_lt hst).ne.symm
  rw [ncard_eq_toFinset_card _ hu,
    Finite.toFinset_union (hu.subset (subset_union_left _ _))
      (hu.subset (subset_union_right _ _))] at hst
  obtain ⟨r', hnr', hr'⟩ := Finset.exists_subset_or_subset_of_two_mul_lt_card hst
  exact ⟨r', by simpa, by simpa using hr'⟩

/-! ### Explicit description of a set from its cardinality -/

@[simp] lemma ncard_eq_one : s.ncard = 1 ↔ ∃ a, s = {a} := by
  refine' ⟨λ h ↦ _, by rintro ⟨a, rfl⟩; rw [ncard_singleton]⟩
  have hft := (Finite_of_ncard_ne_zero (ne_zero_of_eq_one h)).fintype
  simp_rw [ncard_eq_toFinset_card', @Finset.card_eq_one _ (toFinset s)] at h
  refine' h.imp λ a ha ↦ _
  simp_rw [Set.ext_iff, mem_singleton_iff]
  simp only [Finset.ext_iff, mem_toFinset, Finset.mem_singleton] at ha
  exact ha

lemma exists_eq_insert_iff_ncard (hs : s.Finite := by toFinite_tac) :
    (∃ (a : α) (_ : a ∉ s), insert a s = t) ↔ s ⊆ t ∧ s.ncard + 1 = t.ncard := by
  classical
  cases' t.finite_or_infinite with ht ht
  · rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht,
      ←@Finite.toFinset_subset_toFinset _ _ _ hs ht, ←Finset.exists_eq_insert_iff]
    convert Iff.rfl using 2 ; simp
    ext x
    simp [Finset.ext_iff, Set.ext_iff]
  simp only [ht.ncard, exists_prop, add_eq_zero, and_false, iff_false, not_exists, not_and]
  rintro x - rfl
  exact ht (hs.insert x)

lemma ncard_le_one (hs : s.Finite := by toFinite_tac) : s.ncard ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one, Finite.mem_toFinset]

lemma ncard_le_one_iff (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by
  rw [ncard_le_one hs]
  tauto

lemma ncard_le_one_iff_eq (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ s = ∅ ∨ ∃ a, s = {a} := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact iff_of_true (by simp) (Or.inl rfl)
  rw [ncard_le_one_iff hs]
  refine' ⟨λ h ↦ Or.inr ⟨x, (singleton_subset_iff.mpr hx).antisymm' λ y hy ↦ h hy hx⟩, _⟩
  rintro (rfl | ⟨a, rfl⟩)
  · exact (not_mem_empty _ hx).elim
  simp_rw [mem_singleton_iff] at hx⊢; subst hx
  simp only [forall_eq_apply_imp_iff', imp_self, implies_true]

lemma ncard_le_one_iff_subset_singleton [Nonempty α]
  (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∃ x : α, s ⊆ {x} := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one_iff_subset_singleton,
    Finite.toFinset_subset, Finset.coe_singleton]

/-- A `set` of a subsingleton type has cardinality at most one. -/
lemma ncard_le_one_of_subsingleton [Subsingleton α] (s : Set α) : s.ncard ≤ 1 := by
  rw [ncard_eq_toFinset_card]
  exact Finset.card_le_one_of_subsingleton _

lemma one_lt_ncard
    (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.one_lt_card, Finite.mem_toFinset]

lemma one_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b :=   by
  rw [one_lt_ncard hs]
  simp only [exists_prop, exists_and_left]

lemma two_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.two_lt_card_iff, Finite.mem_toFinset]

lemma two_lt_card (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp only [two_lt_ncard_iff hs, exists_and_left, exists_prop]

lemma exists_ne_of_one_lt_ncard (hs : 1 < s.ncard) (a : α) : ∃ b, b ∈ s ∧ b ≠ a := by
  have hsf := (Finite_of_ncard_ne_zero (zero_lt_one.trans hs).ne.symm)
  rw [ncard_eq_toFinset_card _ hsf] at hs
  simpa only [Finite.mem_toFinset] using Finset.exists_ne_of_one_lt_card hs a

lemma eq_insert_of_ncard_eq_succ {n : ℕ} (h : s.ncard = n + 1) :
    ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  classical
  have hsf := Finite_of_ncard_pos (n.zero_lt_succ.trans_eq h.symm)
  rw [ncard_eq_toFinset_card _ hsf, Finset.card_eq_succ] at h
  obtain ⟨a, t, hat, hts, rfl⟩ := h

  simp only [Finset.ext_iff, Finset.mem_insert, Finite.mem_toFinset] at hts
  refine' ⟨a, t, hat, _, _⟩
  · simp only [Finset.mem_coe, ext_iff, mem_insert_iff]
    tauto
  simp

lemma ncard_eq_succ {n : ℕ} (hs : s.Finite := by toFinite_tac) :
    s.ncard = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  refine' ⟨eq_insert_of_ncard_eq_succ, _⟩
  rintro ⟨a, t, hat, h, rfl⟩
  rw [← h, ncard_insert_of_not_mem hat (hs.subset ((subset_insert a t).trans_eq h))]

lemma ncard_eq_two : s.ncard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  classical
  refine' ⟨λ h ↦ _, _⟩
  · obtain ⟨x, t, hxt, rfl, ht⟩ := eq_insert_of_ncard_eq_succ h
    obtain ⟨y, rfl⟩ := ncard_eq_one.mp ht
    rw [mem_singleton_iff] at hxt
    exact ⟨_, _, hxt, rfl⟩
  rintro ⟨x, y, hxy, rfl⟩
  rw [ncard_eq_toFinset_card _, Finset.card_eq_two]
  exact ⟨x, y, hxy, by ext; simp⟩

lemma ncard_eq_three : s.ncard = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  refine' ⟨λ h ↦ _, _⟩
  · obtain ⟨x, t, hxt, rfl, ht⟩ := eq_insert_of_ncard_eq_succ h
    obtain ⟨y, z, hyz, rfl⟩ := ncard_eq_two.mp ht
    rw [mem_insert_iff, mem_singleton_iff, not_or] at hxt
    exact ⟨x, y, z, hxt.1, hxt.2, hyz, rfl⟩
  rintro ⟨x, y, z, xy, xz, yz, rfl⟩
  rw [ncard_insert_of_not_mem, ncard_insert_of_not_mem, ncard_singleton]
  · rwa [mem_singleton_iff]
  rw [mem_insert_iff, mem_singleton_iff]
  tauto

end Set
