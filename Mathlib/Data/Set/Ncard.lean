/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson

! This file was ported from Lean 3 source module data.set.ncard
! leanprover-community/mathlib commit 74c2af38a828107941029b03839882c5c6f87a04
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finite.Card
import Mathbin.Algebra.BigOperators.Finprod

/-!
# Noncomputable Set Cardinality

We define the cardinality `set.ncard s` of a set `s` as a natural number. This function is
noncomputable (being defined in terms of `nat.card`) and takes the value `0` if `s` is infinite.

This can be seen as an API for `nat.card α` in the special case where `α` is a subtype arising from
a set. It is intended as an alternative to `finset.card` and `fintype.card`,  both of which contain
data in their definition that can cause awkwardness when using `set.to_finset`.  Using `set.ncard`
allows cardinality computations to avoid `finset`/`fintype` completely, staying in `set` and letting
finiteness be handled explicitly, or (where a `finite α` instance is present and the sets are
in `set α`) via `auto_param`s.

## Main Definitions

* `set.ncard s` is the cardinality of the set `s` as a natural number, provided `s` is finite.
  If `s` is infinite, then `set.ncard s = 0`.
* `to_finite_tac` is a tactic that tries to synthesize an `set.finite s` argument with
  `set.to_finite`. This will work for `s : set α` where there is a `finite α` instance.

## Implementation Notes

The lemmas in this file are very similar to those in `data.finset.card`, but with `set` operations
instead of `finset`; most of the proofs invoke their `finset` analogues. Nearly all the lemmas
require finiteness of one or more of their arguments. We provide this assumption with an
`auto_param` argument of the form `(hs : s.finite . to_finite_tac)`, where `to_finite_tac` will find
a `finite s` term in the cases where `s` is a set in a `finite` type.

Often, where there are two set arguments `s` and `t`, the finiteness of one follows from the other
in the context of the lemma, in which case we only include the ones that are needed, and derive the
other inside the proof. A few of the lemmas, such as `ncard_union_le` do not require finiteness
arguments; they are are true by coincidence due to junk values.
-/


open scoped BigOperators

variable {α β : Type _} {s t : Set α} {a b x y : α} {f : α → β}

namespace Set

/-- The cardinality of `s : set α`. Has the junk value `0` if `s` is infinite -/
noncomputable def ncard (s : Set α) :=
  Nat.card s
#align set.ncard Set.ncard

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/-- A tactic, for use in `auto_param`s, that finds a `t.finite` term for a set `t`
  whose finiteness can be deduced from typeclasses (eg. in a `finite` type). -/
unsafe def to_finite_tac : tactic Unit :=
  sorry
#align set.to_finite_tac set.to_finite_tac

theorem ncard_def (s : Set α) : s.ncard = Nat.card s :=
  rfl
#align set.ncard_def Set.ncard_def

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_eq_toFinset_card (s : Set α)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard = hs.toFinset.card := by
  rw [ncard_def, @Nat.card_eq_fintype_card _ hs.fintype, @finite.card_to_finset _ _ hs.fintype hs]
#align set.ncard_eq_to_finset_card Set.ncard_eq_toFinset_card

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_le_of_subset (hst : s ⊆ t)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard ≤ t.ncard :=
  @Finite.card_le_of_embedding _ _ (finite_coe_iff.mpr ht) (Set.embeddingOfSubset _ _ hst)
#align set.ncard_le_of_subset Set.ncard_le_of_subset

theorem ncard_mono [Finite α] : @Monotone (Set α) _ _ _ ncard := fun _ _ => ncard_le_of_subset
#align set.ncard_mono Set.ncard_mono

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
@[simp]
theorem ncard_eq_zero
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard = 0 ↔ s = ∅ := by simp [ncard_def, @Finite.card_eq_zero_iff _ hs.to_subtype]
#align set.ncard_eq_zero Set.ncard_eq_zero

@[simp]
theorem ncard_coe_finset (s : Finset α) : (s : Set α).ncard = s.card := by
  rw [ncard_eq_to_finset_card, Finset.finite_toSet_toFinset]
#align set.ncard_coe_finset Set.ncard_coe_finset

theorem Infinite.ncard (hs : s.Infinite) : s.ncard = 0 :=
  @Nat.card_eq_zero_of_infinite _ hs.to_subtype
#align set.infinite.ncard Set.Infinite.ncard

theorem ncard_univ (α : Type _) : (univ : Set α).ncard = Nat.card α :=
  by
  cases' finite_or_infinite α with h h
  · haveI := @Fintype.ofFinite α h
    rw [ncard_eq_to_finset_card, finite.to_finset_univ, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [(@infinite_univ _ h).ncard, @Nat.card_eq_zero_of_infinite _ h]
#align set.ncard_univ Set.ncard_univ

@[simp]
theorem ncard_empty (α : Type _) : (∅ : Set α).ncard = 0 := by simp only [ncard_eq_zero]
#align set.ncard_empty Set.ncard_empty

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_pos
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    0 < s.ncard ↔ s.Nonempty := by
  rw [pos_iff_ne_zero, Ne.def, ncard_eq_zero hs, nonempty_iff_ne_empty]
#align set.ncard_pos Set.ncard_pos

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_ne_zero_of_mem (h : a ∈ s)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard ≠ 0 :=
  ((ncard_pos hs).mpr ⟨a, h⟩).Ne.symm
#align set.ncard_ne_zero_of_mem Set.ncard_ne_zero_of_mem

theorem finite_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.Finite :=
  s.finite_or_infinite.elim id fun h => (hs h.ncard).elim
#align set.finite_of_ncard_ne_zero Set.finite_of_ncard_ne_zero

theorem finite_of_ncard_pos (hs : 0 < s.ncard) : s.Finite :=
  finite_of_ncard_ne_zero hs.Ne.symm
#align set.finite_of_ncard_pos Set.finite_of_ncard_pos

theorem nonempty_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.Nonempty := by rw [nonempty_iff_ne_empty];
  rintro rfl; simpa using hs
#align set.nonempty_of_ncard_ne_zero Set.nonempty_of_ncard_ne_zero

@[simp]
theorem ncard_singleton (a : α) : ({a} : Set α).ncard = 1 := by simp [ncard_eq_to_finset_card]
#align set.ncard_singleton Set.ncard_singleton

theorem ncard_singleton_inter : ({a} ∩ s).ncard ≤ 1 := by
  classical
    rw [← inter_self {a}, inter_assoc, ncard_eq_to_finset_card, finite.to_finset_inter,
      finite.to_finset_singleton]
    · apply Finset.card_singleton_inter
    all_goals apply to_finite
#align set.ncard_singleton_inter Set.ncard_singleton_inter

section InsertErase

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
@[simp]
theorem ncard_insert_of_not_mem (h : a ∉ s)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    (insert a s).ncard = s.ncard + 1 := by
  classical
    haveI := hs.fintype
    rw [ncard_eq_to_finset_card, ncard_eq_to_finset_card, finite.to_finset_insert,
      Finset.card_insert_of_not_mem]
    rwa [finite.mem_to_finset]
#align set.ncard_insert_of_not_mem Set.ncard_insert_of_not_mem

theorem ncard_insert_of_mem (h : a ∈ s) : ncard (insert a s) = s.ncard := by rw [insert_eq_of_mem h]
#align set.ncard_insert_of_mem Set.ncard_insert_of_mem

theorem ncard_insert_le (a : α) (s : Set α) : (insert a s).ncard ≤ s.ncard + 1 := by
  classical
    obtain hs | hs := s.finite_or_infinite
    ·
      exact
        (em (a ∈ s)).elim (fun h => (ncard_insert_of_mem h).trans_le (Nat.le_succ _)) fun h => by
          rw [ncard_insert_of_not_mem h hs]
    rw [(hs.mono (subset_insert a s)).ncard]
    exact Nat.zero_le _
#align set.ncard_insert_le Set.ncard_insert_le

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_insert_eq_ite [Decidable (a ∈ s)]
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    ncard (insert a s) = if a ∈ s then s.ncard else s.ncard + 1 :=
  by
  by_cases h : a ∈ s
  · rw [ncard_insert_of_mem h, if_pos h]
  · rw [ncard_insert_of_not_mem h hs, if_neg h]
#align set.ncard_insert_eq_ite Set.ncard_insert_eq_ite

theorem ncard_le_ncard_insert (a : α) (s : Set α) : s.ncard ≤ (insert a s).ncard := by
  classical
    refine' s.finite_or_infinite.elim (fun h => _) fun h => by rw [h.ncard]; exact Nat.zero_le _
    rw [ncard_insert_eq_ite h]
    split_ifs
    · rfl
    · simp only [le_add_iff_nonneg_right, zero_le']
    exact Classical.dec (a ∈ s)
#align set.ncard_le_ncard_insert Set.ncard_le_ncard_insert

theorem ncard_pair (h : a ≠ b) : ({a, b} : Set α).ncard = 2 := by
  rw [ncard_insert_of_not_mem, ncard_singleton]; simpa
#align set.ncard_pair Set.ncard_pair

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_diff_singleton_add_one (h : a ∈ s)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    (s \ {a}).ncard + 1 = s.ncard :=
  by
  have h' : a ∉ s \ {a} := by rw [mem_diff_singleton]; tauto
  rw [← ncard_insert_of_not_mem h' (hs.diff {a})]
  congr
  simpa
#align set.ncard_diff_singleton_add_one Set.ncard_diff_singleton_add_one

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_diff_singleton_of_mem (h : a ∈ s)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    (s \ {a}).ncard = s.ncard - 1 :=
  eq_tsub_of_add_eq (ncard_diff_singleton_add_one h hs)
#align set.ncard_diff_singleton_of_mem Set.ncard_diff_singleton_of_mem

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_diff_singleton_lt_of_mem (h : a ∈ s)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    (s \ {a}).ncard < s.ncard := by rw [← ncard_diff_singleton_add_one h hs]; apply lt_add_one
#align set.ncard_diff_singleton_lt_of_mem Set.ncard_diff_singleton_lt_of_mem

theorem ncard_diff_singleton_le (s : Set α) (a : α) : (s \ {a}).ncard ≤ s.ncard :=
  by
  obtain hs | hs := s.finite_or_infinite
  · apply ncard_le_of_subset (diff_subset _ _) hs
  convert zero_le _
  exact (hs.diff (by simp : Set.Finite {a})).ncard
#align set.ncard_diff_singleton_le Set.ncard_diff_singleton_le

theorem pred_ncard_le_ncard_diff_singleton (s : Set α) (a : α) : s.ncard - 1 ≤ (s \ {a}).ncard :=
  by
  cases' s.finite_or_infinite with hs hs
  · by_cases h : a ∈ s
    · rw [ncard_diff_singleton_of_mem h hs]
    rw [diff_singleton_eq_self h]
    apply Nat.pred_le
  convert Nat.zero_le _
  rw [hs.ncard]
#align set.pred_ncard_le_ncard_diff_singleton Set.pred_ncard_le_ncard_diff_singleton

theorem ncard_exchange (ha : a ∉ s) (hb : b ∈ s) : (insert a (s \ {b})).ncard = s.ncard :=
  by
  cases' s.finite_or_infinite with h h
  · haveI := h.to_subtype
    rw [ncard_insert_of_not_mem, ncard_diff_singleton_add_one hb]
    simpa only [mem_diff, not_and] using ha
  rw [((h.diff (Set.toFinite {b})).mono (subset_insert _ _)).ncard, h.ncard]
#align set.ncard_exchange Set.ncard_exchange

theorem ncard_exchange' (ha : a ∉ s) (hb : b ∈ s) : (insert a s \ {b}).ncard = s.ncard := by
  rw [← ncard_exchange ha hb, ← singleton_union, ← singleton_union, union_diff_distrib,
    @diff_singleton_eq_self _ b {a} fun h => ha (by rwa [← mem_singleton_iff.mp h])]
#align set.ncard_exchange' Set.ncard_exchange'

end InsertErase

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_image_le
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    (f '' s).ncard ≤ s.ncard := by
  classical
    rw [ncard_eq_to_finset_card s hs]
    haveI := hs.fintype
    convert@Finset.card_image_le _ _ s.to_finset f _
    rw [ncard_eq_to_finset_card, finite.to_finset_image _ hs]
    · congr; rw [← Finset.coe_inj, finite.coe_to_finset, coe_to_finset]
    · infer_instance
    rw [← Finset.coe_inj, finite.coe_to_finset, coe_to_finset]
#align set.ncard_image_le Set.ncard_image_le

theorem ncard_image_of_injOn (H : Set.InjOn f s) : (f '' s).ncard = s.ncard :=
  by
  cases s.finite_or_infinite
  · haveI := @Fintype.ofFinite s h.to_subtype
    haveI := @Fintype.ofFinite _ (h.image f).to_subtype
    convert card_image_of_inj_on H <;> simp [ncard_def]
  rw [h.ncard, ((infinite_image_iff H).mpr h).ncard]
#align set.ncard_image_of_inj_on Set.ncard_image_of_injOn

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem injOn_of_ncard_image_eq (h : (f '' s).ncard = s.ncard)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    Set.InjOn f s := by
  classical
    haveI := hs.fintype
    haveI := ((to_finite s).image f).Fintype
    simp_rw [ncard_eq_to_finset_card] at h 
    rw [← coe_to_finset s]
    apply Finset.injOn_of_card_image_eq
    convert h
    ext
    simp
#align set.inj_on_of_ncard_image_eq Set.injOn_of_ncard_image_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_image_iff
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    (f '' s).ncard = s.ncard ↔ Set.InjOn f s :=
  ⟨fun h => injOn_of_ncard_image_eq h hs, ncard_image_of_injOn⟩
#align set.ncard_image_iff Set.ncard_image_iff

theorem ncard_image_of_injective (s : Set α) (H : f.Injective) : (f '' s).ncard = s.ncard :=
  ncard_image_of_injOn fun x _ y _ h => H h
#align set.ncard_image_of_injective Set.ncard_image_of_injective

theorem ncard_preimage_of_injective_subset_range {s : Set β} (H : f.Injective)
    (hs : s ⊆ Set.range f) : (f ⁻¹' s).ncard = s.ncard := by
  rw [← ncard_image_of_injective _ H, image_preimage_eq_iff.mpr hs]
#align set.ncard_preimage_of_injective_subset_range Set.ncard_preimage_of_injective_subset_range

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem fiber_ncard_ne_zero_iff_mem_image {y : β}
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    { x ∈ s | f x = y }.ncard ≠ 0 ↔ y ∈ f '' s :=
  by
  refine' ⟨nonempty_of_ncard_ne_zero, _⟩
  rintro ⟨z, hz, rfl⟩
  exact
    @ncard_ne_zero_of_mem _ ({ x ∈ s | f x = f z }) z (mem_sep hz rfl) (hs.subset (sep_subset _ _))
#align set.fiber_ncard_ne_zero_iff_mem_image Set.fiber_ncard_ne_zero_iff_mem_image

@[simp]
theorem ncard_map (f : α ↪ β) : (f '' s).ncard = s.ncard :=
  ncard_image_of_injective _ f.Injective
#align set.ncard_map Set.ncard_map

@[simp]
theorem ncard_subtype (P : α → Prop) (s : Set α) :
    { x : Subtype P | (x : α) ∈ s }.ncard = (s ∩ setOf P).ncard :=
  by
  convert(ncard_image_of_injective _ (@Subtype.coe_injective _ P)).symm
  ext; rw [inter_comm]; simp
#align set.ncard_subtype Set.ncard_subtype

@[simp]
theorem Nat.card_coe_set_eq (s : Set α) : Nat.card s = s.ncard :=
  by
  convert(ncard_image_of_injective univ Subtype.coe_injective).symm using 1
  · rw [ncard_univ]; rfl
  simp
#align set.nat.card_coe_set_eq Set.Nat.card_coe_set_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_inter_le_ncard_left (s t : Set α)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    (s ∩ t).ncard ≤ s.ncard :=
  ncard_le_of_subset (inter_subset_left _ _) hs
#align set.ncard_inter_le_ncard_left Set.ncard_inter_le_ncard_left

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_inter_le_ncard_right (s t : Set α)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    (s ∩ t).ncard ≤ t.ncard :=
  ncard_le_of_subset (inter_subset_right _ _) ht
#align set.ncard_inter_le_ncard_right Set.ncard_inter_le_ncard_right

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem eq_of_subset_of_ncard_le (h : s ⊆ t) (h' : t.ncard ≤ s.ncard)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    s = t := by
  haveI := ht.fintype
  haveI := (ht.subset h).Fintype
  rw [← @to_finset_inj]
  apply Finset.eq_of_subset_of_card_le
  · simpa
  rw [ncard_eq_to_finset_card _ ht, ncard_eq_to_finset_card _ (ht.subset h)] at h' 
  convert h'
#align set.eq_of_subset_of_ncard_le Set.eq_of_subset_of_ncard_le

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem subset_iff_eq_of_ncard_le (h : t.ncard ≤ s.ncard)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    s ⊆ t ↔ s = t :=
  ⟨fun hst => eq_of_subset_of_ncard_le hst h ht, Eq.subset'⟩
#align set.subset_iff_eq_of_ncard_le Set.subset_iff_eq_of_ncard_le

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem map_eq_of_subset {f : α ↪ α} (h : f '' s ⊆ s)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    f '' s = s :=
  eq_of_subset_of_ncard_le h (ncard_map _).ge hs
#align set.map_eq_of_subset Set.map_eq_of_subset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem sep_of_ncard_eq {P : α → Prop} (h : { x ∈ s | P x }.ncard = s.ncard) (ha : a ∈ s)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    P a :=
  sep_eq_self_iff_mem_true.mp (eq_of_subset_of_ncard_le (by simp) h.symm.le hs) _ ha
#align set.sep_of_ncard_eq Set.sep_of_ncard_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_lt_ncard (h : s ⊂ t)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard < t.ncard :=
  by
  rw [ncard_eq_to_finset_card _ (ht.subset h.subset), ncard_eq_to_finset_card t ht]
  refine' Finset.card_lt_card _
  rwa [finite.to_finset_ssubset_to_finset]
#align set.ncard_lt_ncard Set.ncard_lt_ncard

theorem ncard_strictMono [Finite α] : @StrictMono (Set α) _ _ _ ncard := fun _ _ h =>
  ncard_lt_ncard h
#align set.ncard_strict_mono Set.ncard_strictMono

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_eq_of_bijective {n : ℕ} (f : ∀ i, i < n → α)
    (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a) (hf' : ∀ (i) (h : i < n), f i h ∈ s)
    (f_inj : ∀ (i j) (hi : i < n) (hj : j < n), f i hi = f j hj → i = j)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard = n := by
  rw [ncard_eq_to_finset_card _ hs]
  apply Finset.card_eq_of_bijective
  all_goals simpa
#align set.ncard_eq_of_bijective Set.ncard_eq_of_bijective

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_congr {t : Set β} (f : ∀ a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
    (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard = t.ncard :=
  by
  set f' : s → t := fun x => ⟨f x.1 x.2, h₁ _ _⟩ with hf'
  have hbij : f'.bijective := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [hf', Subtype.val_eq_coe, Subtype.coe_mk, Subtype.mk_eq_mk] at hxy ⊢
      apply h₂ _ _ hx hy hxy
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := h₃ y hy
    simp only [Subtype.val_eq_coe, Subtype.coe_mk, Subtype.mk_eq_mk, SetCoe.exists]
    exact ⟨_, ha, rfl⟩
  haveI := hs.to_subtype
  haveI := @Fintype.ofFinite _ (Finite.ofBijective hbij)
  haveI := Fintype.ofFinite s
  convert Fintype.card_of_bijective hbij
  rw [ncard_def, Nat.card_eq_fintype_card]
  rw [ncard_def, Nat.card_eq_fintype_card]
#align set.ncard_congr Set.ncard_congr

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_le_ncard_of_injOn {t : Set β} (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (f_inj : InjOn f s)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard ≤ t.ncard := by
  cases s.finite_or_infinite
  · haveI := h.to_subtype
    rw [ncard_eq_to_finset_card _ ht, ncard_eq_to_finset_card _ (to_finite s)]
    exact Finset.card_le_card_of_inj_on f (by simpa) (by simpa)
  convert Nat.zero_le _
  rw [h.ncard]
#align set.ncard_le_ncard_of_inj_on Set.ncard_le_ncard_of_injOn

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem exists_ne_map_eq_of_ncard_lt_of_maps_to {t : Set β} (hc : t.ncard < s.ncard) {f : α → β}
    (hf : ∀ a ∈ s, f a ∈ t)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  by_contra h'
  simp only [Ne.def, exists_prop, not_exists, not_and, not_imp_not] at h' 
  exact (ncard_le_ncard_of_inj_on f hf h' ht).not_lt hc
#align set.exists_ne_map_eq_of_ncard_lt_of_maps_to Set.exists_ne_map_eq_of_ncard_lt_of_maps_to

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem le_ncard_of_inj_on_range {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    n ≤ s.ncard := by rw [ncard_eq_to_finset_card _ hs];
  apply Finset.le_card_of_inj_on_range <;> simpa
#align set.le_ncard_of_inj_on_range Set.le_ncard_of_inj_on_range

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem surj_on_of_inj_on_of_ncard_le {t : Set β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : t.ncard ≤ s.ncard)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  intro b hb
  set f' : s → t := fun x => ⟨f x.1 x.2, hf _ _⟩ with hf'
  have finj : f'.injective := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [hf', Subtype.val_eq_coe, Subtype.coe_mk, Subtype.mk_eq_mk] at hxy ⊢
    apply hinj _ _ hx hy hxy
  haveI := ht.fintype
  haveI := Fintype.ofInjective f' finj
  simp_rw [ncard_eq_to_finset_card] at hst 
  set f'' : ∀ a, a ∈ s.to_finset → β := fun a h => f a (by simpa using h) with hf''
  convert@Finset.surj_on_of_inj_on_of_card_le _ _ _ t.to_finset f'' (by simpa) (by simpa)
      (by convert hst) b (by simpa)
  simp
#align set.surj_on_of_inj_on_of_ncard_le Set.surj_on_of_inj_on_of_ncard_le

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem inj_on_of_surj_on_of_ncard_le {t : Set β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀ b ∈ t, ∃ a ha, b = f a ha) (hst : s.ncard ≤ t.ncard) ⦃a₁ a₂⦄ (ha₁ : a₁ ∈ s)
    (ha₂ : a₂ ∈ s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    a₁ = a₂ := by
  classical
    set f' : s → t := fun x => ⟨f x.1 x.2, hf _ _⟩ with hf'
    have hsurj : f'.surjective := by
      rintro ⟨y, hy⟩
      obtain ⟨a, ha, rfl⟩ := hsurj y hy
      simp only [Subtype.val_eq_coe, Subtype.coe_mk, Subtype.mk_eq_mk, SetCoe.exists]
      exact ⟨_, ha, rfl⟩
    haveI := hs.fintype
    haveI := Fintype.ofSurjective _ hsurj
    simp_rw [ncard_eq_to_finset_card] at hst 
    set f'' : ∀ a, a ∈ s.to_finset → β := fun a h => f a (by simpa using h) with hf''
    exact
      @Finset.inj_on_of_surj_on_of_card_le _ _ _ t.to_finset f'' (by simpa) (by simpa)
        (by convert hst) a₁ a₂ (by simpa) (by simpa) (by simpa)
#align set.inj_on_of_surj_on_of_ncard_le Set.inj_on_of_surj_on_of_ncard_le

section Lattice

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_union_add_ncard_inter (s t : Set α)
    (hs : s.Finite := by
      run_tac
        to_finite_tac)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    (s ∪ t).ncard + (s ∩ t).ncard = s.ncard + t.ncard := by
  classical
    have hu := hs.union ht
    have hi := hs.subset (inter_subset_left s t)
    rw [ncard_eq_to_finset_card _ hs, ncard_eq_to_finset_card _ ht, ncard_eq_to_finset_card _ hu,
      ncard_eq_to_finset_card _ hi, finite.to_finset_union, finite.to_finset_inter]
    · exact Finset.card_union_add_card_inter _ _
#align set.ncard_union_add_ncard_inter Set.ncard_union_add_ncard_inter

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_inter_add_ncard_union (s t : Set α)
    (hs : s.Finite := by
      run_tac
        to_finite_tac)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    (s ∩ t).ncard + (s ∪ t).ncard = s.ncard + t.ncard := by
  rw [add_comm, ncard_union_add_ncard_inter _ _ hs ht]
#align set.ncard_inter_add_ncard_union Set.ncard_inter_add_ncard_union

theorem ncard_union_le (s t : Set α) : (s ∪ t).ncard ≤ s.ncard + t.ncard := by
  classical
    cases (s ∪ t).finite_or_infinite
    · have hs := h.subset (subset_union_left s t)
      have ht := h.subset (subset_union_right s t)
      rw [ncard_eq_to_finset_card _ hs, ncard_eq_to_finset_card _ ht, ncard_eq_to_finset_card _ h,
        finite.to_finset_union]
      exact Finset.card_union_le _ _
    convert Nat.zero_le _
    rw [h.ncard]
#align set.ncard_union_le Set.ncard_union_le

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_union_eq (h : Disjoint s t)
    (hs : s.Finite := by
      run_tac
        to_finite_tac)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    (s ∪ t).ncard = s.ncard + t.ncard := by
  classical
    rw [ncard_eq_to_finset_card _ hs, ncard_eq_to_finset_card _ ht,
      ncard_eq_to_finset_card _ (hs.union ht), finite.to_finset_union]
    refine' Finset.card_union_eq _
    rwa [finite.disjoint_to_finset]
#align set.ncard_union_eq Set.ncard_union_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_diff_add_ncard_eq_ncard (h : s ⊆ t)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    (t \ s).ncard + s.ncard = t.ncard := by
  classical
    rw [ncard_eq_to_finset_card _ ht, ncard_eq_to_finset_card _ (ht.subset h),
      ncard_eq_to_finset_card _ (ht.diff s), finite.to_finset_diff]
    refine' Finset.card_sdiff_add_card_eq_card _
    rwa [finite.to_finset_subset_to_finset]
#align set.ncard_diff_add_ncard_eq_ncard Set.ncard_diff_add_ncard_eq_ncard

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_diff (h : s ⊆ t)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    (t \ s).ncard = t.ncard - s.ncard := by
  rw [← ncard_diff_add_ncard_eq_ncard h ht, add_tsub_cancel_right]
#align set.ncard_diff Set.ncard_diff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_le_ncard_diff_add_ncard (s t : Set α)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard ≤ (s \ t).ncard + t.ncard :=
  by
  cases s.finite_or_infinite
  · rw [← diff_inter_self_eq_diff, ← ncard_diff_add_ncard_eq_ncard (inter_subset_right t s) h,
      add_le_add_iff_left]
    apply ncard_inter_le_ncard_left _ _ ht
  convert Nat.zero_le _
  rw [h.ncard]
#align set.ncard_le_ncard_diff_add_ncard Set.ncard_le_ncard_diff_add_ncard

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem le_ncard_diff (s t : Set α)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    t.ncard - s.ncard ≤ (t \ s).ncard :=
  by
  refine' tsub_le_iff_left.mpr _
  rw [add_comm]
  apply ncard_le_ncard_diff_add_ncard _ _ hs
#align set.le_ncard_diff Set.le_ncard_diff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_diff_add_ncard (s t : Set α)
    (hs : s.Finite := by
      run_tac
        to_finite_tac)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    (s \ t).ncard + t.ncard = (s ∪ t).ncard := by
  rw [← union_diff_right, ncard_diff_add_ncard_eq_ncard (subset_union_right s t) (hs.union ht)]
#align set.ncard_diff_add_ncard Set.ncard_diff_add_ncard

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem diff_nonempty_of_ncard_lt_ncard (h : s.ncard < t.ncard)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    (t \ s).Nonempty :=
  by
  rw [Set.nonempty_iff_ne_empty, Ne.def, diff_eq_empty]
  exact fun h' => h.not_le (ncard_le_of_subset h' hs)
#align set.diff_nonempty_of_ncard_lt_ncard Set.diff_nonempty_of_ncard_lt_ncard

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem exists_mem_not_mem_of_ncard_lt_ncard (h : s.ncard < t.ncard)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    ∃ e, e ∈ t ∧ e ∉ s :=
  diff_nonempty_of_ncard_lt_ncard h hs
#align set.exists_mem_not_mem_of_ncard_lt_ncard Set.exists_mem_not_mem_of_ncard_lt_ncard

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
@[simp]
theorem ncard_inter_add_ncard_diff_eq_ncard (s t : Set α)
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    (s ∩ t).ncard + (s \ t).ncard = s.ncard := by
  rw [← ncard_diff_add_ncard_eq_ncard (diff_subset s t) hs, sdiff_sdiff_right_self, inf_eq_inter]
#align set.ncard_inter_add_ncard_diff_eq_ncard Set.ncard_inter_add_ncard_diff_eq_ncard

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff
    (hs : s.Finite := by
      run_tac
        to_finite_tac)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard = t.ncard ↔ (s \ t).ncard = (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_right_inj]
#align set.ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff Set.ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_le_ncard_iff_ncard_diff_le_ncard_diff
    (hs : s.Finite := by
      run_tac
        to_finite_tac)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard ≤ t.ncard ↔ (s \ t).ncard ≤ (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_le_add_iff_left]
#align set.ncard_le_ncard_iff_ncard_diff_le_ncard_diff Set.ncard_le_ncard_iff_ncard_diff_le_ncard_diff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff
    (hs : s.Finite := by
      run_tac
        to_finite_tac)
    (ht : t.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard < t.ncard ↔ (s \ t).ncard < (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_lt_add_iff_left]
#align set.ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff Set.ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_add_ncard_compl (s : Set α)
    (hs : s.Finite := by
      run_tac
        to_finite_tac)
    (hsc : sᶜ.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard + sᶜ.ncard = Nat.card α := by
  rw [← ncard_univ, ← ncard_union_eq (@disjoint_compl_right _ _ s) hs hsc, union_compl_self]
#align set.ncard_add_ncard_compl Set.ncard_add_ncard_compl

end Lattice

/-- Given a set `t` and a set `s` inside it, we can shrink `t` to any appropriate size, and keep `s`
    inside it. -/
theorem exists_intermediate_set (i : ℕ) (h₁ : i + s.ncard ≤ t.ncard) (h₂ : s ⊆ t) :
    ∃ r : Set α, s ⊆ r ∧ r ⊆ t ∧ r.ncard = i + s.ncard :=
  by
  cases' t.finite_or_infinite with ht ht
  · haveI := ht.to_subtype
    haveI := (ht.subset h₂).to_subtype
    simp_rw [ncard_eq_to_finset_card] at h₁ ⊢
    obtain ⟨r', hsr', hr't, hr'⟩ := Finset.exists_intermediate_set _ h₁ (by simpa)
    exact ⟨r', by simpa using hsr', by simpa using hr't, by rw [← hr', ncard_coe_finset]⟩
  rw [ht.ncard] at h₁ 
  have h₁' := Nat.eq_zero_of_le_zero h₁
  rw [add_eq_zero_iff] at h₁' 
  exact ⟨t, h₂, rfl.subset, by rw [ht.ncard, h₁'.1, h₁'.2]⟩
#align set.exists_intermediate_set Set.exists_intermediate_set

theorem exists_intermediate_set' {m : ℕ} (hs : s.ncard ≤ m) (ht : m ≤ t.ncard) (h : s ⊆ t) :
    ∃ r : Set α, s ⊆ r ∧ r ⊆ t ∧ r.ncard = m :=
  by
  obtain ⟨r, hsr, hrt, hc⟩ :=
    exists_intermediate_set (m - s.ncard) (by rwa [tsub_add_cancel_of_le hs]) h
  rw [tsub_add_cancel_of_le hs] at hc 
  exact ⟨r, hsr, hrt, hc⟩
#align set.exists_intermediate_set' Set.exists_intermediate_set'

/-- We can shrink `s` to any smaller size. -/
theorem exists_smaller_set (s : Set α) (i : ℕ) (h₁ : i ≤ s.ncard) :
    ∃ t : Set α, t ⊆ s ∧ t.ncard = i :=
  (exists_intermediate_set i (by simpa) (empty_subset s)).imp fun t ht =>
    ⟨ht.2.1, by simpa using ht.2.2⟩
#align set.exists_smaller_set Set.exists_smaller_set

theorem Infinite.exists_subset_ncard_eq {s : Set α} (hs : s.Infinite) (k : ℕ) :
    ∃ t, t ⊆ s ∧ t.Finite ∧ t.ncard = k :=
  by
  haveI := hs.to_subtype
  obtain ⟨t', -, rfl⟩ := @Infinite.exists_subset_card_eq s univ infinite_univ k
  refine' ⟨coe '' (t' : Set s), by simp, finite.image _ (by simp), _⟩
  rw [ncard_image_of_injective _ Subtype.coe_injective]
  simp
#align set.infinite.exists_subset_ncard_eq Set.Infinite.exists_subset_ncard_eq

theorem Infinite.exists_supset_ncard_eq {s t : Set α} (ht : t.Infinite) (hst : s ⊆ t)
    (hs : s.Finite) {k : ℕ} (hsk : s.ncard ≤ k) : ∃ s', s ⊆ s' ∧ s' ⊆ t ∧ s'.ncard = k :=
  by
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.diff hs).exists_subset_ncard_eq (k - s.ncard)
  refine' ⟨s ∪ s₁, subset_union_left _ _, union_subset hst (hs₁.trans (diff_subset _ _)), _⟩
  rwa [ncard_union_eq (disjoint_of_subset_right hs₁ disjoint_sdiff_right) hs hs₁fin, hs₁card,
    add_tsub_cancel_of_le]
#align set.infinite.exists_supset_ncard_eq Set.Infinite.exists_supset_ncard_eq

theorem exists_subset_or_subset_of_two_mul_lt_ncard {n : ℕ} (hst : 2 * n < (s ∪ t).ncard) :
    ∃ r : Set α, n < r.ncard ∧ (r ⊆ s ∨ r ⊆ t) := by
  classical
    have hu := finite_of_ncard_ne_zero ((Nat.zero_le _).trans_lt hst).Ne.symm
    rw [ncard_eq_to_finset_card _ hu,
      finite.to_finset_union (hu.subset (subset_union_left _ _))
        (hu.subset (subset_union_right _ _))] at
      hst 
    obtain ⟨r', hnr', hr'⟩ := Finset.exists_subset_or_subset_of_two_mul_lt_card hst
    exact ⟨r', by simpa, by simpa using hr'⟩
#align set.exists_subset_or_subset_of_two_mul_lt_ncard Set.exists_subset_or_subset_of_two_mul_lt_ncard

/-! ### Explicit description of a set from its cardinality -/


@[simp]
theorem ncard_eq_one : s.ncard = 1 ↔ ∃ a, s = {a} :=
  by
  refine' ⟨fun h => _, by rintro ⟨a, rfl⟩; rw [ncard_singleton]⟩
  haveI := (finite_of_ncard_ne_zero (ne_zero_of_eq_one h)).to_subtype
  rw [ncard_eq_to_finset_card, Finset.card_eq_one] at h 
  exact h.imp fun a ha => by rwa [← finite.to_finset_singleton, finite.to_finset_inj] at ha 
#align set.ncard_eq_one Set.ncard_eq_one

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ∉ » s) -/
theorem exists_eq_insert_iff_ncard
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    (∃ (a : _) (_ : a ∉ s), insert a s = t) ↔ s ⊆ t ∧ s.ncard + 1 = t.ncard := by
  classical
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [ncard_eq_to_finset_card _ hs, ncard_eq_to_finset_card _ (hs.insert a),
        finite.to_finset_insert, ← @finite.to_finset_subset_to_finset _ _ _ hs (hs.insert a),
        finite.to_finset_insert]
      refine' (@Finset.exists_eq_insert_iff _ _ hs.to_finset (insert a hs.to_finset)).mp _
      exact ⟨a, by rwa [finite.mem_to_finset], rfl⟩
    rintro ⟨hst, h⟩
    have ht := @finite_of_ncard_pos _ t (by rw [← h]; apply Nat.zero_lt_succ)
    rw [ncard_eq_to_finset_card _ hs, ncard_eq_to_finset_card _ ht] at h 
    obtain ⟨a, has, ha⟩ := finset.exists_eq_insert_iff.mpr ⟨by simpa, h⟩
    have hsa := hs.insert a
    rw [← finite.to_finset_insert] at ha 
    exact ⟨a, by rwa [finite.mem_to_finset] at has , by rwa [← @finite.to_finset_inj _ _ _ hsa ht]⟩
#align set.exists_eq_insert_iff_ncard Set.exists_eq_insert_iff_ncard

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_le_one
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b := by
  simp_rw [ncard_eq_to_finset_card _ hs, Finset.card_le_one, finite.mem_to_finset]
#align set.ncard_le_one Set.ncard_le_one

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_le_one_iff
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by rw [ncard_le_one hs]; tauto
#align set.ncard_le_one_iff Set.ncard_le_one_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_le_one_iff_eq
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard ≤ 1 ↔ s = ∅ ∨ ∃ a, s = {a} :=
  by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact iff_of_true (by simp) (Or.inl rfl)
  rw [ncard_le_one_iff hs]
  refine' ⟨fun h => Or.inr ⟨x, (singleton_subset_iff.mpr hx).antisymm' fun y hy => h hy hx⟩, _⟩
  rintro (rfl | ⟨a, rfl⟩)
  · exact (not_mem_empty _ hx).elim
  simp_rw [mem_singleton_iff] at hx ⊢; subst hx
  exact fun a b h h' => h.trans h'.symm
#align set.ncard_le_one_iff_eq Set.ncard_le_one_iff_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_le_one_iff_subset_singleton [Nonempty α]
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard ≤ 1 ↔ ∃ x : α, s ⊆ {x} := by
  simp_rw [ncard_eq_to_finset_card _ hs, Finset.card_le_one_iff_subset_singleton,
    finite.to_finset_subset, Finset.coe_singleton]
#align set.ncard_le_one_iff_subset_singleton Set.ncard_le_one_iff_subset_singleton

/-- A `set` of a subsingleton type has cardinality at most one. -/
theorem ncard_le_one_of_subsingleton [Subsingleton α] (s : Set α) : s.ncard ≤ 1 := by
  rw [ncard_eq_to_finset_card]; exact Finset.card_le_one_of_subsingleton _
#align set.ncard_le_one_of_subsingleton Set.ncard_le_one_of_subsingleton

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem one_lt_ncard
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    1 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  simp_rw [ncard_eq_to_finset_card _ hs, Finset.one_lt_card, finite.mem_to_finset]
#align set.one_lt_ncard Set.one_lt_ncard

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem one_lt_ncard_iff
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    1 < s.ncard ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by rw [one_lt_ncard hs];
  simp only [exists_prop, exists_and_left]
#align set.one_lt_ncard_iff Set.one_lt_ncard_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem two_lt_ncard_iff
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    2 < s.ncard ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [ncard_eq_to_finset_card _ hs, Finset.two_lt_card_iff, finite.mem_to_finset]
#align set.two_lt_ncard_iff Set.two_lt_ncard_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem two_lt_card
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    2 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp only [two_lt_ncard_iff hs, exists_and_left, exists_prop]
#align set.two_lt_card Set.two_lt_card

theorem exists_ne_of_one_lt_ncard (hs : 1 < s.ncard) (a : α) : ∃ b, b ∈ s ∧ b ≠ a :=
  by
  haveI := (finite_of_ncard_ne_zero (zero_lt_one.trans hs).Ne.symm).to_subtype
  rw [ncard_eq_to_finset_card] at hs 
  simpa only [finite.mem_to_finset] using Finset.exists_ne_of_one_lt_card hs a
#align set.exists_ne_of_one_lt_ncard Set.exists_ne_of_one_lt_ncard

theorem eq_insert_of_ncard_eq_succ {n : ℕ} (h : s.ncard = n + 1) :
    ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  classical
    haveI := @Fintype.ofFinite _ (finite_of_ncard_pos (n.zero_lt_succ.trans_eq h.symm)).to_subtype
    rw [ncard_eq_to_finset_card, Finset.card_eq_succ] at h 
    obtain ⟨a, t, hat, hts, rfl⟩ := h
    refine' ⟨a, t, hat, _, by rw [ncard_coe_finset]⟩
    rw [← to_finset_inj]
    convert hts
    simp only [to_finset_insert, Finset.toFinset_coe]
#align set.eq_insert_of_ncard_eq_succ Set.eq_insert_of_ncard_eq_succ

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic to_finite_tac -/
theorem ncard_eq_succ {n : ℕ}
    (hs : s.Finite := by
      run_tac
        to_finite_tac) :
    s.ncard = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  classical
    refine' ⟨eq_insert_of_ncard_eq_succ, _⟩
    rintro ⟨a, t, hat, h, rfl⟩
    rw [← h, ncard_insert_of_not_mem hat (hs.subset ((subset_insert a t).trans_eq h))]
#align set.ncard_eq_succ Set.ncard_eq_succ

theorem ncard_eq_two : s.ncard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  classical
    refine' ⟨fun h => _, _⟩
    · obtain ⟨x, t, hxt, rfl, ht⟩ := eq_insert_of_ncard_eq_succ h
      obtain ⟨y, rfl⟩ := ncard_eq_one.mp ht
      rw [mem_singleton_iff] at hxt 
      exact ⟨_, _, hxt, rfl⟩
    rintro ⟨x, y, hxy, rfl⟩
    rw [ncard_eq_to_finset_card, Finset.card_eq_two]
    exact ⟨x, y, hxy, by ext; simp⟩
#align set.ncard_eq_two Set.ncard_eq_two

theorem ncard_eq_three : s.ncard = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  classical
    refine' ⟨fun h => _, _⟩
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

