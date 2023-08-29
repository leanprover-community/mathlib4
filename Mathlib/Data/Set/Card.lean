/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Finite.Card

#align_import data.set.ncard from "leanprover-community/mathlib"@"74c2af38a828107941029b03839882c5c6f87a04"

/-!
# Noncomputable Set Cardinality

We define the cardinality of set `s` as a term `Set.encard s : ℕ∞` and a term `Set.ncard s : ℕ`.
The latter takes the junk value of zero if `s` is infinite. Both functions are noncomputable, and
are defined in terms of `PartENat.card` (which takes a type as its argument); this file can be seen
as an API for the same function in the special case where the type is a coercion of a `Set`,
allowing for smoother interactions with the `Set` API.

`Set.encard` never takes junk values, so is more mathematically natural than `Set.ncard`, even
though it takes values in a less convenient type. It is probably the right choice in settings where
one is concerned with the cardinalities of sets that may or may not be infinite.

`Set.ncard` has a nicer codomain, but when using it, `Set.Finite` hypotheses are normally needed to
make sure its values are meaningful.  More generally, `Set.ncard` is intended to be used over the
obvious alternative `Finset.card` when finiteness is 'propositional' rather than  'structural'.
When working with sets that are finite by virtue of their definition, then `Finset.card` probably
makes more sense. One setting where `Set.ncard` works nicely is in a type `α` with `[Finite α]`,
where every set is automatically finite. In this setting, we use default arguments and a simple
tactic so that finiteness goals are discharged automatically in `Set.ncard` theorems.

## Main Definitions

* `Set.encard s` is the cardinality of the set `s` as an extended natural number, with value `⊤` if
    `s` is infinite.
* `Set.ncard s` is the cardinality of the set `s` as a natural number, provided `s` is Finite.
  If `s` is Infinite, then `Set.ncard s = 0`.
* `toFinite_tac` is a tactic that tries to synthesize a `Set.Finite s` argument with
  `Set.toFinite`. This will work for `s : Set α` where there is a `Finite α` instance.

## Implementation Notes

The theorems in this file are very similar to those in `Data.Finset.Card`, but with `Set` operations
instead of `Finset`. We first prove all the theorems for `Set.encard`, and then derive most of the
`Set.ncard` results as a consequence. Things are done this way to avoid reliance on the `Finset` API
for theorems about infinite sets, and to allow for a refactor that removes or modifies `Set.ncard`
in the future.

Nearly all the theorems for `Set.ncard` require finiteness of one or more of their arguments. We
provide this assumption with a default argument of the form `(hs : s.Finite := by toFinite_tac)`,
where `toFinite_tac` will find an `s.Finite` term in the cases where `s` is a set in a `Finite`
type.

Often, where there are two set arguments `s` and `t`, the finiteness of one follows from the other
in the context of the theorem, in which case we only include the ones that are needed, and derive
the other inside the proof. A few of the theorems, such as `ncard_union_le` do not require
finiteness arguments; they are true by coincidence due to junk values.
-/

set_option autoImplicit true

namespace Set

variable {s t : Set α}

/-- The cardinality of a set as a term in `ℕ∞` -/
noncomputable def encard (s : Set α) := PartENat.withTopEquiv (PartENat.card s)

@[simp] theorem encard_univ_coe (s : Set α) : encard (univ : Set s) = encard s := by
  rw [encard, encard, PartENat.card_congr (Equiv.Set.univ ↑s)]
  -- 🎉 no goals

theorem encard_univ (α : Type*) :
    encard (univ : Set α) = PartENat.withTopEquiv (PartENat.card α) := by
  rw [encard, PartENat.card_congr (Equiv.Set.univ α)]
  -- 🎉 no goals

theorem Finite.encard_eq_coe_toFinset_card (h : s.Finite) : s.encard = h.toFinset.card := by
  have := h.fintype
  -- ⊢ encard s = ↑(Finset.card (Finite.toFinset h))
  rw [encard, PartENat.card_eq_coe_fintype_card,
    PartENat.withTopEquiv_natCast, toFinite_toFinset, toFinset_card]

theorem encard_eq_coe_toFinset_card (s : Set α) [Fintype s] : encard s = s.toFinset.card := by
  have h := toFinite s
  -- ⊢ encard s = ↑(Finset.card (toFinset s))
  rw [h.encard_eq_coe_toFinset_card, toFinite_toFinset, toFinset_card]
  -- 🎉 no goals

theorem encard_coe_eq_coe_finsetCard (s : Finset α) : encard (s : Set α) = s.card := by
  rw [Finite.encard_eq_coe_toFinset_card (Finset.finite_toSet s)]; simp
  -- ⊢ ↑(Finset.card (Finite.toFinset (_ : Set.Finite ↑s))) = ↑(Finset.card s)
                                                                   -- 🎉 no goals

theorem Infinite.encard_eq {s : Set α} (h : s.Infinite) : s.encard = ⊤ := by
  have := h.to_subtype
  -- ⊢ encard s = ⊤
  rw [encard, ←PartENat.withTopEquiv.symm.injective.eq_iff, Equiv.symm_apply_apply,
    PartENat.withTopEquiv_symm_top, PartENat.card_eq_top_of_infinite]

@[simp] theorem encard_eq_zero : s.encard = 0 ↔ s = ∅ := by
  rw [encard, ←PartENat.withTopEquiv.symm.injective.eq_iff, Equiv.symm_apply_apply,
    PartENat.withTopEquiv_symm_zero, PartENat.card_eq_zero_iff_empty, isEmpty_subtype,
    eq_empty_iff_forall_not_mem]

@[simp] theorem encard_empty : (∅ : Set α).encard = 0 := by
  rw [encard_eq_zero]
  -- 🎉 no goals

theorem nonempty_of_encard_ne_zero (h : s.encard ≠ 0) : s.Nonempty := by
  rwa [nonempty_iff_ne_empty, Ne.def, ←encard_eq_zero]
  -- 🎉 no goals

theorem encard_ne_zero : s.encard ≠ 0 ↔ s.Nonempty := by
  rw [ne_eq, encard_eq_zero, nonempty_iff_ne_empty]
  -- 🎉 no goals

@[simp] theorem encard_pos : 0 < s.encard ↔ s.Nonempty := by
  rw [pos_iff_ne_zero, encard_ne_zero]
  -- 🎉 no goals

@[simp] theorem encard_singleton (e : α) : ({e} : Set α).encard = 1 := by
  rw [encard, ←PartENat.withTopEquiv.symm.injective.eq_iff, Equiv.symm_apply_apply,
    PartENat.card_eq_coe_fintype_card, Fintype.card_ofSubsingleton, Nat.cast_one]; rfl
                                                                                   -- 🎉 no goals

theorem encard_union_eq (h : Disjoint s t) : (s ∪ t).encard = s.encard + t.encard := by
  classical
  have e := (Equiv.Set.union (by rwa [subset_empty_iff, ←disjoint_iff_inter_eq_empty])).symm
  simp [encard, ←PartENat.card_congr e, PartENat.card_sum, PartENat.withTopEquiv]

theorem encard_insert_of_not_mem (has : a ∉ s) : (insert a s).encard = s.encard + 1 := by
  rw [←union_singleton, encard_union_eq (by simpa), encard_singleton]
  -- 🎉 no goals

theorem Finite.encard_lt_top (h : s.Finite) : s.encard < ⊤ := by
  refine' h.induction_on (by simpa using WithTop.zero_lt_top) _
  -- ⊢ ∀ {a : α} {s : Set α}, ¬a ∈ s → Set.Finite s → encard s < ⊤ → encard (insert …
  rintro a t hat _ ht'
  -- ⊢ encard (insert a t) < ⊤
  rw [encard_insert_of_not_mem hat]
  -- ⊢ encard t + 1 < ⊤
  exact lt_tsub_iff_right.1 ht'
  -- 🎉 no goals

theorem Finite.encard_eq_coe (h : s.Finite) : s.encard = ENat.toNat s.encard :=
  (ENat.coe_toNat h.encard_lt_top.ne).symm

theorem Finite.exists_encard_eq_coe (h : s.Finite) : ∃ (n : ℕ), s.encard = n :=
  ⟨_, h.encard_eq_coe⟩

@[simp] theorem encard_lt_top_iff : s.encard < ⊤ ↔ s.Finite :=
  ⟨fun h ↦ by_contra fun h' ↦ h.ne (Infinite.encard_eq h'), Finite.encard_lt_top⟩

@[simp] theorem encard_eq_top_iff : s.encard = ⊤ ↔ s.Infinite := by
  rw [←not_iff_not, ←Ne.def, ←lt_top_iff_ne_top, encard_lt_top_iff, not_infinite]
  -- 🎉 no goals

theorem encard_ne_top_iff : s.encard ≠ ⊤ ↔ s.Finite := by
  simp
  -- 🎉 no goals

theorem finite_of_encard_le_coe {k : ℕ} (h : s.encard ≤ k) : s.Finite := by
  rw [←encard_lt_top_iff]; exact h.trans_lt (WithTop.coe_lt_top _)
  -- ⊢ encard s < ⊤
                           -- 🎉 no goals

theorem finite_of_encard_eq_coe {k : ℕ} (h : s.encard = k) : s.Finite :=
  finite_of_encard_le_coe h.le

theorem encard_le_coe_iff {k : ℕ} : s.encard ≤ k ↔ s.Finite ∧ ∃ (n₀ : ℕ), s.encard = n₀ ∧ n₀ ≤ k :=
  ⟨fun h ↦ ⟨finite_of_encard_le_coe h, by rwa [ENat.le_coe_iff] at h⟩,
                                          -- 🎉 no goals
    fun ⟨_,⟨n₀,hs, hle⟩⟩ ↦ by rwa [hs, Nat.cast_le]⟩
                              -- 🎉 no goals

section Lattice

theorem encard_le_of_subset (h : s ⊆ t) : s.encard ≤ t.encard := by
  rw [←union_diff_cancel h, encard_union_eq disjoint_sdiff_right]; exact le_self_add
  -- ⊢ encard s ≤ encard s + encard (t \ s)
                                                                   -- 🎉 no goals

theorem encard_mono {α : Type*} : Monotone (encard : Set α → ℕ∞) :=
  fun _ _ ↦ encard_le_of_subset

theorem encard_diff_add_encard_of_subset (h : s ⊆ t) : (t \ s).encard + s.encard = t.encard := by
  rw [←encard_union_eq disjoint_sdiff_left, diff_union_self, union_eq_self_of_subset_right h]
  -- 🎉 no goals

@[simp] theorem one_le_encard_iff_nonempty : 1 ≤ s.encard ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, Ne.def, ←encard_eq_zero, ENat.one_le_iff_ne_zero]
  -- 🎉 no goals

theorem encard_diff_add_encard_inter (s t : Set α) :
    (s \ t).encard + (s ∩ t).encard = s.encard := by
  rw [←encard_union_eq (disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left),
    diff_union_inter]

theorem encard_union_add_encard_inter (s t : Set α) :
    (s ∪ t).encard + (s ∩ t).encard = s.encard + t.encard :=
by rw [←diff_union_self, encard_union_eq disjoint_sdiff_left, add_right_comm,
  encard_diff_add_encard_inter]

theorem encard_eq_encard_iff_encard_diff_eq_encard_diff (h : (s ∩ t).Finite) :
    s.encard = t.encard ↔ (s \ t).encard = (t \ s).encard := by
  rw [← encard_diff_add_encard_inter s t, ← encard_diff_add_encard_inter t s, inter_comm t s,
    WithTop.add_right_cancel_iff h.encard_lt_top.ne]

theorem encard_le_encard_iff_encard_diff_le_encard_diff (h : (s ∩ t).Finite) :
    s.encard ≤ t.encard ↔ (s \ t).encard ≤ (t \ s).encard := by
  rw [← encard_diff_add_encard_inter s t, ← encard_diff_add_encard_inter t s, inter_comm t s,
    WithTop.add_le_add_iff_right h.encard_lt_top.ne]

theorem encard_lt_encard_iff_encard_diff_lt_encard_diff (h : (s ∩ t).Finite) :
    s.encard < t.encard ↔ (s \ t).encard < (t \ s).encard := by
  rw [← encard_diff_add_encard_inter s t, ← encard_diff_add_encard_inter t s, inter_comm t s,
    WithTop.add_lt_add_iff_right h.encard_lt_top.ne]

theorem encard_union_le (s t : Set α) : (s ∪ t).encard ≤ s.encard + t.encard := by
  rw [←encard_union_add_encard_inter]; exact le_self_add
  -- ⊢ encard (s ∪ t) ≤ encard (s ∪ t) + encard (s ∩ t)
                                       -- 🎉 no goals

theorem finite_iff_finite_of_encard_eq_encard (h : s.encard = t.encard) : s.Finite ↔ t.Finite := by
  rw [←encard_lt_top_iff, ←encard_lt_top_iff, h]
  -- 🎉 no goals

theorem infinite_iff_infinite_of_encard_eq_encard (h : s.encard = t.encard) :
    s.Infinite ↔ t.Infinite := by rw [←encard_eq_top_iff, h, encard_eq_top_iff]
                                  -- 🎉 no goals

theorem Finite.finite_of_encard_le {s : Set α} {t : Set β} (hs : s.Finite)
    (h : t.encard ≤ s.encard) : t.Finite :=
  encard_lt_top_iff.1 (h.trans_lt hs.encard_lt_top)

theorem Finite.eq_of_subset_of_encard_le (ht : t.Finite) (hst : s ⊆ t) (hts : t.encard ≤ s.encard) :
    s = t := by
  rw [←zero_add (a := encard s), ←encard_diff_add_encard_of_subset hst] at hts
  -- ⊢ s = t
  have hdiff := WithTop.le_of_add_le_add_right (ht.subset hst).encard_lt_top.ne hts
  -- ⊢ s = t
  rw [nonpos_iff_eq_zero, encard_eq_zero, diff_eq_empty] at hdiff
  -- ⊢ s = t
  exact hst.antisymm hdiff
  -- 🎉 no goals

theorem Finite.eq_of_subset_of_encard_le' (hs : s.Finite) (hst : s ⊆ t)
    (hts : t.encard ≤ s.encard) : s = t :=
  (hs.finite_of_encard_le hts).eq_of_subset_of_encard_le hst hts

theorem Finite.encard_lt_encard (ht : t.Finite) (h : s ⊂ t) : s.encard < t.encard :=
  (encard_mono h.subset).lt_of_ne (fun he ↦ h.ne (ht.eq_of_subset_of_encard_le h.subset he.symm.le))

theorem encard_strictMono [Finite α] : StrictMono (encard : Set α → ℕ∞) :=
  fun _ _ h ↦ (toFinite _).encard_lt_encard h

theorem encard_diff_add_encard (s t : Set α) : (s \ t).encard + t.encard = (s ∪ t).encard := by
  rw [←encard_union_eq disjoint_sdiff_left, diff_union_self]
  -- 🎉 no goals

theorem encard_le_encard_diff_add_encard (s t : Set α) : s.encard ≤ (s \ t).encard + t.encard :=
  (encard_mono (subset_union_left s t)).trans_eq (encard_diff_add_encard _ _).symm

theorem tsub_encard_le_encard_diff (s t : Set α) : s.encard - t.encard ≤ (s \ t).encard := by
  rw [tsub_le_iff_left, add_comm]; apply encard_le_encard_diff_add_encard
  -- ⊢ encard s ≤ encard (s \ t) + encard t
                                   -- 🎉 no goals

theorem encard_add_encard_compl (s : Set α) : s.encard + sᶜ.encard = (univ : Set α).encard := by
  rw [←encard_union_eq disjoint_compl_right, union_compl_self]
  -- 🎉 no goals

end Lattice

section InsertErase

theorem encard_insert_le (s : Set α) (x : α) : (insert x s).encard ≤ s.encard + 1 := by
  rw [←union_singleton, ←encard_singleton x]; apply encard_union_le
  -- ⊢ encard (s ∪ {x}) ≤ encard s + encard {x}
                                              -- 🎉 no goals

theorem encard_singleton_inter (s : Set α) (x : α) : ({x} ∩ s).encard ≤ 1 := by
  rw [←encard_singleton x]; exact encard_le_of_subset (inter_subset_left _ _)
  -- ⊢ encard ({x} ∩ s) ≤ encard {x}
                            -- 🎉 no goals

theorem encard_diff_singleton_add_one (h : a ∈ s) :
    (s \ {a}).encard + 1 = s.encard := by
  rw [←encard_insert_of_not_mem (fun h ↦ h.2 rfl), insert_diff_singleton, insert_eq_of_mem h]
  -- 🎉 no goals

theorem encard_diff_singleton_of_mem (h : a ∈ s) :
    (s \ {a}).encard = s.encard - 1 := by
  rw [←encard_diff_singleton_add_one h, ←WithTop.add_right_cancel_iff WithTop.one_ne_top,
    tsub_add_cancel_of_le (self_le_add_left _ _)]

theorem encard_tsub_one_le_encard_diff_singleton (s : Set α) (x : α) :
    s.encard - 1 ≤ (s \ {x}).encard := by
  rw [←encard_singleton x]; apply tsub_encard_le_encard_diff
  -- ⊢ encard s - encard {x} ≤ encard (s \ {x})
                            -- 🎉 no goals

theorem encard_exchange (ha : a ∉ s) (hb : b ∈ s) : (insert a (s \ {b})).encard = s.encard := by
  rw [encard_insert_of_not_mem, encard_diff_singleton_add_one hb]
  -- ⊢ ¬a ∈ s \ {b}
  simp_all only [not_true, mem_diff, mem_singleton_iff, false_and, not_false_eq_true]
  -- 🎉 no goals

theorem encard_exchange' (ha : a ∉ s) (hb : b ∈ s) : (insert a s \ {b}).encard = s.encard := by
  rw [←insert_diff_singleton_comm (by rintro rfl; exact ha hb), encard_exchange ha hb]
  -- 🎉 no goals

theorem encard_eq_add_one_iff {k : ℕ∞} :
    s.encard = k + 1 ↔ (∃ a t, ¬a ∈ t ∧ insert a t = s ∧ t.encard = k) := by
  refine' ⟨fun h ↦ _, _⟩
  -- ⊢ ∃ a t, ¬a ∈ t ∧ insert a t = s ∧ encard t = k
  · obtain ⟨a, ha⟩ := nonempty_of_encard_ne_zero (s := s) (by simp [h])
    -- ⊢ ∃ a t, ¬a ∈ t ∧ insert a t = s ∧ encard t = k
    refine' ⟨a, s \ {a}, fun h ↦ h.2 rfl, by rwa [insert_diff_singleton, insert_eq_of_mem], _⟩
    -- ⊢ encard (s \ {a}) = k
    rw [←WithTop.add_right_cancel_iff WithTop.one_ne_top, ←h,
      encard_diff_singleton_add_one ha]
  rintro ⟨a, t, h, rfl, rfl⟩
  -- ⊢ encard (insert a t) = encard t + 1
  rw [encard_insert_of_not_mem h]
  -- 🎉 no goals

/-- Every set is either empty, infinite, or can have its `encard` reduced by a removal. Intended
  for well-founded induction on the value of `encard`. -/
theorem eq_empty_or_encard_eq_top_or_encard_diff_singleton_lt (s : Set α) :
    s = ∅ ∨ s.encard = ⊤ ∨ ∃ a ∈ s, (s \ {a}).encard < s.encard := by
  refine' s.eq_empty_or_nonempty.elim Or.inl (Or.inr ∘ fun ⟨a,ha⟩ ↦
    (s.finite_or_infinite.elim (fun hfin ↦ Or.inr ⟨a, ha, _⟩) (Or.inl ∘ Infinite.encard_eq)))
  rw [←encard_diff_singleton_add_one ha]; nth_rw 1 [←add_zero (encard _)]
  -- ⊢ encard (s \ {a}) < encard (s \ {a}) + 1
                                          -- ⊢ encard (s \ {a}) + 0 < encard (s \ {a}) + 1
  exact WithTop.add_lt_add_left (hfin.diff _).encard_lt_top.ne zero_lt_one
  -- 🎉 no goals

end InsertErase

section SmallSets

theorem encard_pair (hne : x ≠ y) : ({x,y} : Set α).encard = 2 := by
  rw [encard_insert_of_not_mem (by simpa), ←one_add_one_eq_two,
    WithTop.add_right_cancel_iff WithTop.one_ne_top, encard_singleton]

theorem encard_eq_one : s.encard = 1 ↔ ∃ x, s = {x} := by
  refine' ⟨fun h ↦ _, fun ⟨x, hx⟩ ↦ by rw [hx, encard_singleton]⟩
  -- ⊢ ∃ x, s = {x}
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  -- ⊢ ∃ x, s = {x}
  exact ⟨x, ((finite_singleton x).eq_of_subset_of_encard_le' (by simpa) (by simp [h])).symm⟩
  -- 🎉 no goals

theorem encard_le_one_iff_eq : s.encard ≤ 1 ↔ s = ∅ ∨ ∃ x, s = {x} := by
  rw [le_iff_lt_or_eq, lt_iff_not_le, ENat.one_le_iff_ne_zero, not_not, encard_eq_zero,
    encard_eq_one]

theorem encard_le_one_iff : s.encard ≤ 1 ↔ ∀ a b, a ∈ s → b ∈ s → a = b := by
  rw [encard_le_one_iff_eq, or_iff_not_imp_left, ←Ne.def, ←nonempty_iff_ne_empty]
  -- ⊢ (Set.Nonempty s → ∃ x, s = {x}) ↔ ∀ (a b : α), a ∈ s → b ∈ s → a = b
  refine' ⟨fun h a b has hbs ↦ _,
    fun h ⟨x, hx⟩ ↦ ⟨x, ((singleton_subset_iff.2 hx).antisymm' (fun y hy ↦ h _ _ hy hx))⟩⟩
  obtain ⟨x, rfl⟩ := h ⟨_, has⟩
  -- ⊢ a = b
  rw [(has : a = x), (hbs : b = x)]
  -- 🎉 no goals

theorem one_lt_encard_iff : 1 < s.encard ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  rw [←not_iff_not, not_exists, not_lt, encard_le_one_iff]; aesop
  -- ⊢ (∀ (a b : α), a ∈ s → b ∈ s → a = b) ↔ ∀ (x : α), ¬∃ b, x ∈ s ∧ b ∈ s ∧ x ≠ b
                                                            -- 🎉 no goals

theorem exists_ne_of_one_lt_encard (h : 1 < s.encard) (a : α) : ∃ b ∈ s, b ≠ a := by
  by_contra' h'
  -- ⊢ False
  obtain ⟨b,b',hb,hb',hne⟩ := one_lt_encard_iff.1 h
  -- ⊢ False
  apply hne
  -- ⊢ b = b'
  rw [h' b hb, h' b' hb']
  -- 🎉 no goals

theorem encard_eq_two : s.encard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x,y} := by
  refine' ⟨fun h ↦ _, fun ⟨x, y, hne, hs⟩ ↦ by rw [hs, encard_pair hne]⟩
  -- ⊢ ∃ x y, x ≠ y ∧ s = {x, y}
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  -- ⊢ ∃ x y, x ≠ y ∧ s = {x, y}
  rw [←insert_eq_of_mem hx, ←insert_diff_singleton, encard_insert_of_not_mem (fun h ↦ h.2 rfl),
    ←one_add_one_eq_two, WithTop.add_right_cancel_iff (WithTop.one_ne_top), encard_eq_one] at h
  obtain ⟨y, h⟩ := h
  -- ⊢ ∃ x y, x ≠ y ∧ s = {x, y}
  refine' ⟨x, y, by rintro rfl; exact (h.symm.subset rfl).2 rfl, _⟩
  -- ⊢ s = {x, y}
  rw [←h, insert_diff_singleton, insert_eq_of_mem hx]
  -- 🎉 no goals

theorem encard_eq_three {α : Type u_1} {s : Set α} :
    encard s = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  refine' ⟨fun h ↦ _, fun ⟨x, y, z, hxy, hyz, hxz, hs⟩ ↦ _⟩
  -- ⊢ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z}
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
    -- ⊢ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z}
    rw [←insert_eq_of_mem hx, ←insert_diff_singleton,
      encard_insert_of_not_mem (fun h ↦ h.2 rfl), (by exact rfl : (3 : ℕ∞) = 2 + 1),
      WithTop.add_right_cancel_iff WithTop.one_ne_top, encard_eq_two] at h
    obtain ⟨y,z,hne, hs⟩ := h
    -- ⊢ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z}
    refine' ⟨x,y,z, _, _, hne, _⟩
    · rintro rfl; exact (hs.symm.subset (Or.inl rfl)).2 rfl
      -- ⊢ False
                  -- 🎉 no goals
    · rintro rfl; exact (hs.symm.subset (Or.inr rfl)).2 rfl
      -- ⊢ False
                  -- 🎉 no goals
    rw [←hs, insert_diff_singleton, insert_eq_of_mem hx]
    -- 🎉 no goals
  rw [hs, encard_insert_of_not_mem, encard_insert_of_not_mem, encard_singleton] <;> aesop
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals
                                                                                    -- 🎉 no goals

theorem Nat.encard_range (k : ℕ) : {i | i < k}.encard = k := by
  convert encard_coe_eq_coe_finsetCard (Finset.range k) using 1
  -- ⊢ encard {i | i < k} = encard ↑(Finset.range k)
  · rw [Finset.coe_range, Iio_def]
    -- 🎉 no goals
  rw [Finset.card_range]
  -- 🎉 no goals

end SmallSets

theorem Finite.eq_insert_of_subset_of_encard_eq_succ (hs : s.Finite) (h : s ⊆ t)
    (hst : t.encard = s.encard + 1) : ∃ a, t = insert a s := by
  rw [←encard_diff_add_encard_of_subset h, add_comm,
    WithTop.add_left_cancel_iff hs.encard_lt_top.ne, encard_eq_one] at hst
  obtain ⟨x, hx⟩ := hst; use x; rw [←diff_union_of_subset h, hx, singleton_union]
  -- ⊢ ∃ a, t = insert a s
                         -- ⊢ t = insert x s
                                -- 🎉 no goals

theorem exists_subset_encard_eq (hk : k ≤ s.encard) : ∃ t, t ⊆ s ∧ t.encard = k := by
  revert hk
  -- ⊢ k ≤ encard s → ∃ t, t ⊆ s ∧ encard t = k
  refine' ENat.nat_induction k (fun _ ↦ ⟨∅, empty_subset _, by simp⟩) (fun n IH hle ↦ _) _
  -- ⊢ ∃ t, t ⊆ s ∧ encard t = ↑(Nat.succ n)
  · obtain ⟨t₀, ht₀s, ht₀⟩ := IH (le_trans (by simp) hle)
    -- ⊢ ∃ t, t ⊆ s ∧ encard t = ↑(Nat.succ n)
    simp only [Nat.cast_succ] at *
    -- ⊢ ∃ t, t ⊆ s ∧ encard t = ↑n + 1
    have hne : t₀ ≠ s
    -- ⊢ t₀ ≠ s
    · rintro rfl; rw [ht₀, ←Nat.cast_one, ←Nat.cast_add, Nat.cast_le] at hle; simp at hle
      -- ⊢ False
                  -- ⊢ False
                                                                              -- 🎉 no goals
    obtain ⟨x, hx⟩ := exists_of_ssubset (ht₀s.ssubset_of_ne hne)
    -- ⊢ ∃ t, t ⊆ s ∧ encard t = ↑n + 1
    exact ⟨insert x t₀, insert_subset hx.1 ht₀s, by rw [encard_insert_of_not_mem hx.2, ht₀]⟩
    -- 🎉 no goals
  simp only [top_le_iff, encard_eq_top_iff]
  -- ⊢ (∀ (n : ℕ), ↑n ≤ encard s → ∃ t, t ⊆ s ∧ encard t = ↑n) → Set.Infinite s → ∃ …
  exact fun _ hi ↦ ⟨s, Subset.rfl, hi⟩
  -- 🎉 no goals

theorem exists_supset_subset_encard_eq (hst : s ⊆ t) (hsk : s.encard ≤ k) (hkt : k ≤ t.encard) :
    ∃ r, s ⊆ r ∧ r ⊆ t ∧ r.encard = k := by
  obtain (hs | hs) := eq_or_ne s.encard ⊤
  -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ encard r = k
  · rw [hs, top_le_iff] at hsk; subst hsk; exact ⟨s, Subset.rfl, hst, hs⟩
    -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ encard r = k
                                -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ encard r = ⊤
                                           -- 🎉 no goals
  obtain ⟨k, rfl⟩ := exists_add_of_le hsk
  -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ encard r = encard s + k
  obtain ⟨k', hk'⟩ := exists_add_of_le hkt
  -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ encard r = encard s + k
  have hk : k ≤ encard (t \ s)
  -- ⊢ k ≤ encard (t \ s)
  · rw [←encard_diff_add_encard_of_subset hst, add_comm] at hkt
    -- ⊢ k ≤ encard (t \ s)
    exact WithTop.le_of_add_le_add_right hs hkt
    -- 🎉 no goals
  obtain ⟨r', hr', rfl⟩ := exists_subset_encard_eq hk
  -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ encard r = encard s + encard r'
  refine' ⟨s ∪ r', subset_union_left _ _, union_subset hst (hr'.trans (diff_subset _ _)), _⟩
  -- ⊢ encard (s ∪ r') = encard s + encard r'
  rw [encard_union_eq (disjoint_of_subset_right hr' disjoint_sdiff_right)]
  -- 🎉 no goals

section Function

variable {s : Set α} {t : Set β} {f : α → β}

theorem InjOn.encard_image (h : InjOn f s) : (f '' s).encard = s.encard := by
  rw [encard, PartENat.card_image_of_injOn h, encard]
  -- 🎉 no goals

theorem encard_congr (e : s ≃ t) : s.encard = t.encard := by
  rw [←encard_univ_coe, ←encard_univ_coe t, encard_univ, encard_univ, PartENat.card_congr e]
  -- 🎉 no goals

theorem _root_.Function.Injective.encard_image (hf : f.Injective) (s : Set α) :
    (f '' s).encard = s.encard :=
  (hf.injOn s).encard_image

theorem _root_.Function.Embedding.enccard_le (e : s ↪ t) : s.encard ≤ t.encard := by
  rw [←encard_univ_coe, ←e.injective.encard_image, ←Subtype.coe_injective.encard_image]
  -- ⊢ encard ((fun a => ↑a) '' (↑e '' univ)) ≤ encard t
  exact encard_mono (by simp)
  -- 🎉 no goals

theorem encard_image_le (f : α → β) (s : Set α) : (f '' s).encard ≤ s.encard := by
  obtain (h | h) := isEmpty_or_nonempty α
  -- ⊢ encard (f '' s) ≤ encard s
  · rw [s.eq_empty_of_isEmpty]; simp
    -- ⊢ encard (f '' ∅) ≤ encard ∅
                                -- 🎉 no goals
  rw [←(f.invFunOn_injOn_image s).encard_image]
  -- ⊢ encard (Function.invFunOn f s '' (f '' s)) ≤ encard s
  apply encard_le_of_subset
  -- ⊢ Function.invFunOn f s '' (f '' s) ⊆ s
  exact f.invFunOn_image_image_subset s
  -- 🎉 no goals

theorem Finite.injOn_of_encard_image_eq (hs : s.Finite) (h : (f '' s).encard = s.encard) :
    InjOn f s := by
  obtain (h' | hne) := isEmpty_or_nonempty α
  -- ⊢ InjOn f s
  · rw [s.eq_empty_of_isEmpty]; simp
    -- ⊢ InjOn f ∅
                                -- 🎉 no goals
  rw [←(f.invFunOn_injOn_image s).encard_image] at h
  -- ⊢ InjOn f s
  rw [injOn_iff_invFunOn_image_image_eq_self]
  -- ⊢ Function.invFunOn f s '' (f '' s) = s
  exact hs.eq_of_subset_of_encard_le (f.invFunOn_image_image_subset s) h.symm.le
  -- 🎉 no goals

theorem encard_preimage_of_injective_subset_range (hf : f.Injective) (ht : t ⊆ range f) :
    (f ⁻¹' t).encard = t.encard := by
  rw [←hf.encard_image, image_preimage_eq_inter_range, inter_eq_self_of_subset_left ht]
  -- 🎉 no goals

theorem encard_le_encard_of_injOn (hf : MapsTo f s t) (f_inj : InjOn f s) :
    s.encard ≤ t.encard := by
  rw [←f_inj.encard_image]; apply encard_le_of_subset; rintro _ ⟨x, hx, rfl⟩; exact hf hx
  -- ⊢ encard (f '' s) ≤ encard t
                            -- ⊢ f '' s ⊆ t
                                                       -- ⊢ f x ∈ t
                                                                              -- 🎉 no goals

theorem Finite.exists_injOn_of_encard_le [Nonempty β] {s : Set α} {t : Set β} (hs : s.Finite)
    (hle : s.encard ≤ t.encard) : ∃ (f : α → β), s ⊆ f ⁻¹' t ∧ InjOn f s := by
  classical
  obtain (rfl | h | ⟨a, has, -⟩) := s.eq_empty_or_encard_eq_top_or_encard_diff_singleton_lt
  · simp
  · exact (encard_ne_top_iff.mpr hs h).elim
  obtain ⟨b, hbt⟩ := encard_pos.1 ((encard_pos.2 ⟨_, has⟩).trans_le hle)
  have hle' : (s \ {a}).encard ≤ (t \ {b}).encard
  · rwa [←WithTop.add_le_add_iff_right WithTop.one_ne_top,
    encard_diff_singleton_add_one has, encard_diff_singleton_add_one hbt]

  obtain ⟨f₀, hf₀s, hinj⟩ := exists_injOn_of_encard_le (hs.diff {a}) hle'
  simp only [preimage_diff, subset_def, mem_diff, mem_singleton_iff, mem_preimage, and_imp] at hf₀s

  use Function.update f₀ a b
  rw [←insert_eq_of_mem has, ←insert_diff_singleton, injOn_insert (fun h ↦ h.2 rfl)]
  simp only [mem_diff, mem_singleton_iff, not_true, and_false, insert_diff_singleton, subset_def,
    mem_insert_iff, mem_preimage, ne_eq, Function.update_apply, forall_eq_or_imp, ite_true, and_imp,
    mem_image, ite_eq_left_iff, not_exists, not_and, not_forall, exists_prop, and_iff_right hbt]

  refine ⟨?_,?_,fun x hxs hxa ↦ ⟨hxa, (hf₀s x hxs hxa).2⟩⟩
  · rintro x hx; split_ifs with h; assumption; exact (hf₀s x hx h).1
  exact InjOn.congr hinj (fun x ⟨_, hxa⟩ ↦ by rwa [Function.update_noteq])
termination_by _ => encard s

theorem Finite.exists_bijOn_of_encard_eq [Nonempty β] (hs : s.Finite) (h : s.encard = t.encard) :
    ∃ (f : α → β), BijOn f s t := by
  obtain ⟨f, hf, hinj⟩ := hs.exists_injOn_of_encard_le h.le; use f
  -- ⊢ ∃ f, BijOn f s t
                                                             -- ⊢ BijOn f s t
  convert hinj.bijOn_image
  -- ⊢ t = f '' s
  rw [(hs.image f).eq_of_subset_of_encard_le' (image_subset_iff.mpr hf)
    (h.symm.trans hinj.encard_image.symm).le]

end Function

section ncard

open Nat

/-- A tactic (for use in default params) that applies `Set.toFinite` to synthesize a `Set.Finite`
  term. -/
syntax "toFinite_tac" : tactic

macro_rules
  | `(tactic| toFinite_tac) => `(tactic| apply Set.toFinite)

/-- A tactic useful for transferring proofs for `encard` to their corresponding `card` statements -/
syntax "to_encard_tac" : tactic

macro_rules
  | `(tactic| to_encard_tac) => `(tactic|
      simp only [←Nat.cast_le (α := ℕ∞), ←Nat.cast_inj (R := ℕ∞), Nat.cast_add, Nat.cast_one])


/-- The cardinality of `s : Set α` . Has the junk value `0` if `s` is infinite -/
noncomputable def ncard (s : Set α) :=
  ENat.toNat s.encard
#align set.ncard Set.ncard

theorem ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard := rfl

theorem Finite.cast_ncard_eq (hs : s.Finite) : s.ncard = s.encard := by
  rwa [ncard, ENat.coe_toNat_eq_self, ne_eq, encard_eq_top_iff, Set.Infinite, not_not]
  -- 🎉 no goals

@[simp] theorem Nat.card_coe_set_eq (s : Set α) : Nat.card s = s.ncard := by
  obtain (h | h) := s.finite_or_infinite
  -- ⊢ Nat.card ↑s = ncard s
  · have := h.fintype
    -- ⊢ Nat.card ↑s = ncard s
    rw [ncard, h.encard_eq_coe_toFinset_card, Nat.card_eq_fintype_card,
      toFinite_toFinset, toFinset_card, ENat.toNat_coe]
  have := infinite_coe_iff.2 h
  -- ⊢ Nat.card ↑s = ncard s
  rw [ncard, h.encard_eq, Nat.card_eq_zero_of_infinite, ENat.toNat_top]
  -- 🎉 no goals
#align set.nat.card_coe_set_eq Set.Nat.card_coe_set_eq

theorem ncard_eq_toFinset_card (s : Set α) (hs : s.Finite := by toFinite_tac) :
    s.ncard = hs.toFinset.card := by
  rw [←Nat.card_coe_set_eq, @Nat.card_eq_fintype_card _ hs.fintype,
    @Finite.card_toFinset _ _ hs.fintype hs]
#align set.ncard_eq_to_finset_card Set.ncard_eq_toFinset_card

theorem ncard_eq_toFinset_card' (s : Set α) [Fintype s] :
    s.ncard = s.toFinset.card := by
  simp [←Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  -- 🎉 no goals

theorem encard_le_coe_iff_finite_ncard_le {k : ℕ} : s.encard ≤ k ↔ s.Finite ∧ s.ncard ≤ k := by
  rw [encard_le_coe_iff, and_congr_right_iff]
  -- ⊢ Set.Finite s → ((∃ n₀, encard s = ↑n₀ ∧ n₀ ≤ k) ↔ ncard s ≤ k)
  exact fun hfin ↦ ⟨fun ⟨n₀, hn₀, hle⟩ ↦ by rwa [ncard_def, hn₀, ENat.toNat_coe],
    fun h ↦ ⟨s.ncard, by rw [hfin.cast_ncard_eq], h⟩⟩

theorem Infinite.ncard (hs : s.Infinite) : s.ncard = 0 := by
  rw [←Nat.card_coe_set_eq, @Nat.card_eq_zero_of_infinite _ hs.to_subtype]
  -- 🎉 no goals
#align set.infinite.ncard Set.Infinite.ncard

theorem ncard_le_of_subset (hst : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ t.ncard := by
  rw [←Nat.cast_le (α := ℕ∞), ht.cast_ncard_eq, (ht.subset hst).cast_ncard_eq]
  -- ⊢ encard s ≤ encard t
  exact encard_mono hst
  -- 🎉 no goals
#align set.ncard_le_of_subset Set.ncard_le_of_subset

theorem ncard_mono [Finite α] : @Monotone (Set α) _ _ _ ncard := fun _ _ ↦ ncard_le_of_subset
#align set.ncard_mono Set.ncard_mono

@[simp] theorem ncard_eq_zero (hs : s.Finite := by toFinite_tac) :
    s.ncard = 0 ↔ s = ∅ := by
  rw [←Nat.cast_inj (R := ℕ∞), hs.cast_ncard_eq, Nat.cast_zero, encard_eq_zero]
  -- 🎉 no goals
#align set.ncard_eq_zero Set.ncard_eq_zero

@[simp] theorem ncard_coe_Finset (s : Finset α) : (s : Set α).ncard = s.card := by
  rw [ncard_eq_toFinset_card _, Finset.finite_toSet_toFinset]
  -- 🎉 no goals
#align set.ncard_coe_finset Set.ncard_coe_Finset

theorem ncard_univ (α : Type*) : (univ : Set α).ncard = Nat.card α := by
  cases' finite_or_infinite α with h h
  -- ⊢ ncard univ = Nat.card α
  · have hft := Fintype.ofFinite α
    -- ⊢ ncard univ = Nat.card α
    rw [ncard_eq_toFinset_card, Finite.toFinset_univ, Finset.card_univ, Nat.card_eq_fintype_card]
    -- 🎉 no goals
  rw [Nat.card_eq_zero_of_infinite, Infinite.ncard]
  -- ⊢ Set.Infinite univ
  exact infinite_univ
  -- 🎉 no goals
#align set.ncard_univ Set.ncard_univ

@[simp] theorem ncard_empty (α : Type*) : (∅ : Set α).ncard = 0 := by
  rw [ncard_eq_zero]
  -- 🎉 no goals
#align set.ncard_empty Set.ncard_empty

theorem ncard_pos (hs : s.Finite := by toFinite_tac) : 0 < s.ncard ↔ s.Nonempty := by
  rw [pos_iff_ne_zero, Ne.def, ncard_eq_zero hs, nonempty_iff_ne_empty]
  -- 🎉 no goals
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
  -- ⊢ s ≠ ∅
                              -- ⊢ False
                                          -- 🎉 no goals
#align set.nonempty_of_ncard_ne_zero Set.nonempty_of_ncard_ne_zero

@[simp] theorem ncard_singleton (a : α) : ({a} : Set α).ncard = 1 := by
  simp [ncard_eq_toFinset_card]
  -- 🎉 no goals
#align set.ncard_singleton Set.ncard_singleton

theorem ncard_singleton_inter (a : α) (s : Set α) : ({a} ∩ s).ncard ≤ 1 := by
  rw [←Nat.cast_le (α := ℕ∞), (toFinite _).cast_ncard_eq, Nat.cast_one]
  -- ⊢ encard ({a} ∩ s) ≤ 1
  apply encard_singleton_inter
  -- 🎉 no goals
#align set.ncard_singleton_inter Set.ncard_singleton_inter
section InsertErase

@[simp] theorem ncard_insert_of_not_mem (h : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    (insert a s).ncard = s.ncard + 1 := by
  rw [←Nat.cast_inj (R := ℕ∞), (hs.insert a).cast_ncard_eq, Nat.cast_add, Nat.cast_one,
    hs.cast_ncard_eq, encard_insert_of_not_mem h]
#align set.ncard_insert_of_not_mem Set.ncard_insert_of_not_mem

theorem ncard_insert_of_mem (h : a ∈ s) : ncard (insert a s) = s.ncard := by
    rw [insert_eq_of_mem h]
    -- 🎉 no goals
#align set.ncard_insert_of_mem Set.ncard_insert_of_mem

theorem ncard_insert_le (a : α) (s : Set α) : (insert a s).ncard ≤ s.ncard + 1 := by
  obtain hs | hs := s.finite_or_infinite
  -- ⊢ ncard (insert a s) ≤ ncard s + 1
  · to_encard_tac; rw [hs.cast_ncard_eq, (hs.insert _).cast_ncard_eq]; apply encard_insert_le
    -- ⊢ ↑(ncard (insert a s)) ≤ ↑(ncard s) + 1
                   -- ⊢ encard (insert a s) ≤ encard s + 1
                                                                       -- 🎉 no goals
  rw [(hs.mono (subset_insert a s)).ncard]
  -- ⊢ 0 ≤ ncard s + 1
  exact Nat.zero_le _
  -- 🎉 no goals
#align set.ncard_insert_le Set.ncard_insert_le

theorem ncard_insert_eq_ite [Decidable (a ∈ s)] (hs : s.Finite := by toFinite_tac) :
    ncard (insert a s) = if a ∈ s then s.ncard else s.ncard + 1 := by
  by_cases h : a ∈ s
  -- ⊢ ncard (insert a s) = if a ∈ s then ncard s else ncard s + 1
  · rw [ncard_insert_of_mem h, if_pos h]
    -- 🎉 no goals
  · rw [ncard_insert_of_not_mem h hs, if_neg h]
    -- 🎉 no goals
#align set.ncard_insert_eq_ite Set.ncard_insert_eq_ite

theorem ncard_le_ncard_insert (a : α) (s : Set α) : s.ncard ≤ (insert a s).ncard := by
  classical
  refine'
    s.finite_or_infinite.elim (fun h ↦ _) (fun h ↦ by (rw [h.ncard]; exact Nat.zero_le _))
  rw [ncard_insert_eq_ite h]; split_ifs <;> simp
#align set.ncard_le_ncard_insert Set.ncard_le_ncard_insert

@[simp] theorem ncard_pair (h : a ≠ b) : ({a, b} : Set α).ncard = 2 := by
  rw [ncard_insert_of_not_mem, ncard_singleton]; simpa
  -- ⊢ ¬a ∈ {b}
                                                 -- 🎉 no goals
#align set.card_doubleton Set.ncard_pair

@[simp] theorem ncard_diff_singleton_add_one (h : a ∈ s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard + 1 = s.ncard := by
  to_encard_tac; rw [hs.cast_ncard_eq, (hs.diff _).cast_ncard_eq,
  -- ⊢ ↑(ncard (s \ {a})) + 1 = ↑(ncard s)
    encard_diff_singleton_add_one h]
#align set.ncard_diff_singleton_add_one Set.ncard_diff_singleton_add_one

@[simp] theorem ncard_diff_singleton_of_mem (h : a ∈ s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard = s.ncard - 1 :=
  eq_tsub_of_add_eq (ncard_diff_singleton_add_one h hs)
#align set.ncard_diff_singleton_of_mem Set.ncard_diff_singleton_of_mem

theorem ncard_diff_singleton_lt_of_mem (h : a ∈ s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard < s.ncard := by
  rw [← ncard_diff_singleton_add_one h hs]; apply lt_add_one
  -- ⊢ ncard (s \ {a}) < ncard (s \ {a}) + 1
                                            -- 🎉 no goals
#align set.ncard_diff_singleton_lt_of_mem Set.ncard_diff_singleton_lt_of_mem

theorem ncard_diff_singleton_le (s : Set α) (a : α) : (s \ {a}).ncard ≤ s.ncard := by
  obtain hs | hs := s.finite_or_infinite
  -- ⊢ ncard (s \ {a}) ≤ ncard s
  · apply ncard_le_of_subset (diff_subset _ _) hs
    -- 🎉 no goals
  convert @zero_le ℕ _ _
  -- ⊢ ncard (s \ {a}) = 0
  exact (hs.diff (by simp : Set.Finite {a})).ncard
  -- 🎉 no goals
#align set.ncard_diff_singleton_le Set.ncard_diff_singleton_le

theorem pred_ncard_le_ncard_diff_singleton (s : Set α) (a : α) : s.ncard - 1 ≤ (s \ {a}).ncard := by
  cases' s.finite_or_infinite with hs hs
  -- ⊢ ncard s - 1 ≤ ncard (s \ {a})
  · by_cases h : a ∈ s
    -- ⊢ ncard s - 1 ≤ ncard (s \ {a})
    · rw [ncard_diff_singleton_of_mem h hs]
      -- 🎉 no goals
    rw [diff_singleton_eq_self h]
    -- ⊢ ncard s - 1 ≤ ncard s
    apply Nat.pred_le
    -- 🎉 no goals
  convert Nat.zero_le _
  -- ⊢ ncard s - 1 = 0
  rw [hs.ncard]
  -- 🎉 no goals
#align set.pred_ncard_le_ncard_diff_singleton Set.pred_ncard_le_ncard_diff_singleton

theorem ncard_exchange (ha : a ∉ s) (hb : b ∈ s) : (insert a (s \ {b})).ncard = s.ncard :=
  congr_arg ENat.toNat <| encard_exchange ha hb
#align set.ncard_exchange Set.ncard_exchange

theorem ncard_exchange' (ha : a ∉ s) (hb : b ∈ s) : (insert a s \ {b}).ncard = s.ncard := by
  rw [← ncard_exchange ha hb, ← singleton_union, ← singleton_union, union_diff_distrib,
    @diff_singleton_eq_self _ b {a} fun h ↦ ha (by rwa [← mem_singleton_iff.mp h])]
#align set.ncard_exchange' Set.ncard_exchange'

end InsertErase

theorem ncard_image_le (hs : s.Finite := by toFinite_tac) : (f '' s).ncard ≤ s.ncard := by
  to_encard_tac; rw [hs.cast_ncard_eq, (hs.image _).cast_ncard_eq]; apply encard_image_le
  -- ⊢ ↑(ncard (f '' s)) ≤ ↑(ncard s)
                 -- ⊢ encard (f '' s) ≤ encard s
                                                                    -- 🎉 no goals
#align set.ncard_image_le Set.ncard_image_le

theorem ncard_image_of_injOn (H : Set.InjOn f s) : (f '' s).ncard = s.ncard :=
  congr_arg ENat.toNat <| H.encard_image
#align set.ncard_image_of_inj_on Set.ncard_image_of_injOn

theorem injOn_of_ncard_image_eq (h : (f '' s).ncard = s.ncard) (hs : s.Finite := by toFinite_tac) :
    Set.InjOn f s := by
  rw [←Nat.cast_inj (R := ℕ∞), hs.cast_ncard_eq, (hs.image _).cast_ncard_eq] at h
  -- ⊢ InjOn f s
  exact hs.injOn_of_encard_image_eq h
  -- 🎉 no goals
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
  -- 🎉 no goals
#align set.ncard_preimage_of_injective_subset_range Set.ncard_preimage_of_injective_subset_range

theorem fiber_ncard_ne_zero_iff_mem_image {y : β} (hs : s.Finite := by toFinite_tac) :
    { x ∈ s | f x = y }.ncard ≠ 0 ↔ y ∈ f '' s := by
  refine' ⟨nonempty_of_ncard_ne_zero, _⟩
  -- ⊢ y ∈ f '' s → ncard {x | x ∈ s ∧ f x = y} ≠ 0
  rintro ⟨z, hz, rfl⟩
  -- ⊢ ncard {x | x ∈ s ∧ f x = f z} ≠ 0
  exact @ncard_ne_zero_of_mem _ ({ x ∈ s | f x = f z }) z (mem_sep hz rfl)
    (hs.subset (sep_subset _ _))
#align set.fiber_ncard_ne_zero_iff_mem_image Set.fiber_ncard_ne_zero_iff_mem_image

@[simp] theorem ncard_map (f : α ↪ β) : (f '' s).ncard = s.ncard :=
  ncard_image_of_injective _ f.inj'
#align set.ncard_map Set.ncard_map

@[simp] theorem ncard_subtype (P : α → Prop) (s : Set α) :
    { x : Subtype P | (x : α) ∈ s }.ncard = (s ∩ setOf P).ncard := by
  convert (ncard_image_of_injective _ (@Subtype.coe_injective _ P)).symm
  -- ⊢ s ∩ setOf P = (fun a => ↑a) '' {x | ↑x ∈ s}
  ext x
  -- ⊢ x ∈ s ∩ setOf P ↔ x ∈ (fun a => ↑a) '' {x | ↑x ∈ s}
  simp [←and_assoc, exists_eq_right]
  -- 🎉 no goals
#align set.ncard_subtype Set.ncard_subtype

theorem ncard_inter_le_ncard_left (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    (s ∩ t).ncard ≤ s.ncard :=
  ncard_le_of_subset (inter_subset_left _ _) hs
#align set.ncard_inter_le_ncard_left Set.ncard_inter_le_ncard_left

theorem ncard_inter_le_ncard_right (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    (s ∩ t).ncard ≤ t.ncard :=
  ncard_le_of_subset (inter_subset_right _ _) ht
#align set.ncard_inter_le_ncard_right Set.ncard_inter_le_ncard_right

theorem eq_of_subset_of_ncard_le (h : s ⊆ t) (h' : t.ncard ≤ s.ncard)
    (ht : t.Finite := by toFinite_tac) : s = t :=
  ht.eq_of_subset_of_encard_le h
    (by rwa [←Nat.cast_le (α := ℕ∞), ht.cast_ncard_eq, (ht.subset h).cast_ncard_eq] at h')
        -- 🎉 no goals
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
                                                            -- 🎉 no goals
#align set.sep_of_ncard_eq Set.sep_of_ncard_eq

theorem ncard_lt_ncard (h : s ⊂ t) (ht : t.Finite := by toFinite_tac) :
    s.ncard < t.ncard := by
  rw [←Nat.cast_lt (α := ℕ∞), ht.cast_ncard_eq, (ht.subset h.subset).cast_ncard_eq]
  -- ⊢ encard s < encard t
  exact ht.encard_lt_encard h
  -- 🎉 no goals
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
  -- ⊢ Finset.card (Finite.toFinset hs) = n
  apply Finset.card_eq_of_bijective
  all_goals simpa
  -- 🎉 no goals
#align set.ncard_eq_of_bijective Set.ncard_eq_of_bijective

theorem ncard_congr {t : Set β} (f : ∀ a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
    (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) :
    s.ncard = t.ncard := by
  set f' : s → t := fun x ↦ ⟨f x.1 x.2, h₁ _ _⟩
  -- ⊢ ncard s = ncard t
  have hbij : f'.Bijective := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [Subtype.mk.injEq] at hxy ⊢
      exact h₂ _ _ hx hy hxy
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := h₃ y hy
    simp only [Subtype.mk.injEq, Subtype.exists]
    exact ⟨_, ha, rfl⟩
  simp_rw [←Nat.card_coe_set_eq]
  -- ⊢ Nat.card ↑s = Nat.card ↑t
  exact Nat.card_congr (Equiv.ofBijective f' hbij)
  -- 🎉 no goals
#align set.ncard_congr Set.ncard_congr

theorem ncard_le_ncard_of_injOn {t : Set β} (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (f_inj : InjOn f s)
    (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ t.ncard := by
  have hle := encard_le_encard_of_injOn hf f_inj
  -- ⊢ ncard s ≤ ncard t
  to_encard_tac; rwa [ht.cast_ncard_eq, (ht.finite_of_encard_le hle).cast_ncard_eq]
  -- ⊢ ↑(ncard s) ≤ ↑(ncard t)
                 -- 🎉 no goals
#align set.ncard_le_ncard_of_inj_on Set.ncard_le_ncard_of_injOn

theorem exists_ne_map_eq_of_ncard_lt_of_maps_to {t : Set β} (hc : t.ncard < s.ncard) {f : α → β}
  (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Finite := by toFinite_tac) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  by_contra h'
  -- ⊢ False
  simp only [Ne.def, exists_prop, not_exists, not_and, not_imp_not] at h'
  -- ⊢ False
  exact (ncard_le_ncard_of_injOn f hf h' ht).not_lt hc
  -- 🎉 no goals
#align set.exists_ne_map_eq_of_ncard_lt_of_maps_to Set.exists_ne_map_eq_of_ncard_lt_of_maps_to

theorem le_ncard_of_inj_on_range {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
  (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) (hs : s.Finite := by toFinite_tac) :
    n ≤ s.ncard := by
  rw [ncard_eq_toFinset_card _ hs]
  -- ⊢ n ≤ Finset.card (Finite.toFinset hs)
  apply Finset.le_card_of_inj_on_range <;> simpa
                                           -- 🎉 no goals
                                           -- 🎉 no goals
#align set.le_ncard_of_inj_on_range Set.le_ncard_of_inj_on_range

theorem surj_on_of_inj_on_of_ncard_le {t : Set β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
  (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : t.ncard ≤ s.ncard)
  (ht : t.Finite := by toFinite_tac) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  intro b hb
  -- ⊢ ∃ a ha, b = f a ha
  set f' : s → t := fun x ↦ ⟨f x.1 x.2, hf _ _⟩
  -- ⊢ ∃ a ha, b = f a ha
  have finj : f'.Injective := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk.injEq] at hxy ⊢
    apply hinj _ _ hx hy hxy
  have hft := ht.fintype
  -- ⊢ ∃ a ha, b = f a ha
  have hft' := Fintype.ofInjective f' finj
  -- ⊢ ∃ a ha, b = f a ha
  set f'' : ∀ a, a ∈ s.toFinset → β := fun a h ↦ f a (by simpa using h)
  -- ⊢ ∃ a ha, b = f a ha
  convert @Finset.surj_on_of_inj_on_of_card_le _ _ _ t.toFinset f'' _ _ _ _ (by simpa)
  · simp
    -- 🎉 no goals
  · simp [hf]
    -- 🎉 no goals
  · intros a₁ a₂ ha₁ ha₂ h
    -- ⊢ a₁ = a₂
    rw [mem_toFinset] at ha₁ ha₂
    -- ⊢ a₁ = a₂
    exact hinj _ _ ha₁ ha₂ h
    -- 🎉 no goals
  rwa [←ncard_eq_toFinset_card', ←ncard_eq_toFinset_card']
  -- 🎉 no goals
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
  to_encard_tac; rw [hs.cast_ncard_eq, ht.cast_ncard_eq, (hs.union ht).cast_ncard_eq,
  -- ⊢ ↑(ncard (s ∪ t)) + ↑(ncard (s ∩ t)) = ↑(ncard s) + ↑(ncard t)
    (hs.subset (inter_subset_left _ _)).cast_ncard_eq, encard_union_add_encard_inter]
#align set.ncard_union_add_ncard_inter Set.ncard_union_add_ncard_inter

theorem ncard_inter_add_ncard_union (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∩ t).ncard + (s ∪ t).ncard = s.ncard + t.ncard := by
  rw [add_comm, ncard_union_add_ncard_inter _ _ hs ht]
  -- 🎉 no goals
#align set.ncard_inter_add_ncard_union Set.ncard_inter_add_ncard_union

theorem ncard_union_le (s t : Set α) : (s ∪ t).ncard ≤ s.ncard + t.ncard := by
  obtain (h | h) := (s ∪ t).finite_or_infinite
  -- ⊢ ncard (s ∪ t) ≤ ncard s + ncard t
  · to_encard_tac
    -- ⊢ ↑(ncard (s ∪ t)) ≤ ↑(ncard s) + ↑(ncard t)
    rw [h.cast_ncard_eq, (h.subset (subset_union_left _ _)).cast_ncard_eq,
      (h.subset (subset_union_right _ _)).cast_ncard_eq]
    apply encard_union_le
    -- 🎉 no goals
  rw [h.ncard]
  -- ⊢ 0 ≤ ncard s + ncard t
  apply zero_le
  -- 🎉 no goals
#align set.ncard_union_le Set.ncard_union_le

theorem ncard_union_eq (h : Disjoint s t) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∪ t).ncard = s.ncard + t.ncard := by
  to_encard_tac
  -- ⊢ ↑(ncard (s ∪ t)) = ↑(ncard s) + ↑(ncard t)
  rw [hs.cast_ncard_eq, ht.cast_ncard_eq, (hs.union ht).cast_ncard_eq, encard_union_eq h]
  -- 🎉 no goals
#align set.ncard_union_eq Set.ncard_union_eq

theorem ncard_diff_add_ncard_of_subset (h : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    (t \ s).ncard + s.ncard = t.ncard := by
  to_encard_tac
  -- ⊢ ↑(ncard (t \ s)) + ↑(ncard s) = ↑(ncard t)
  rw [ht.cast_ncard_eq, (ht.subset h).cast_ncard_eq, (ht.diff _).cast_ncard_eq,
    encard_diff_add_encard_of_subset h]
#align set.ncard_diff_add_ncard_eq_ncard Set.ncard_diff_add_ncard_of_subset

theorem ncard_diff (h : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    (t \ s).ncard = t.ncard - s.ncard := by
  rw [← ncard_diff_add_ncard_of_subset h ht, add_tsub_cancel_right]
  -- 🎉 no goals
#align set.ncard_diff Set.ncard_diff

theorem ncard_le_ncard_diff_add_ncard (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ (s \ t).ncard + t.ncard := by
  cases' s.finite_or_infinite with hs hs
  -- ⊢ ncard s ≤ ncard (s \ t) + ncard t
  · to_encard_tac
    -- ⊢ ↑(ncard s) ≤ ↑(ncard (s \ t)) + ↑(ncard t)
    rw [ht.cast_ncard_eq, hs.cast_ncard_eq, (hs.diff _).cast_ncard_eq]
    -- ⊢ encard s ≤ encard (s \ t) + encard t
    apply encard_le_encard_diff_add_encard
    -- 🎉 no goals
  convert Nat.zero_le _
  -- ⊢ ncard s = 0
  rw [hs.ncard]
  -- 🎉 no goals
#align set.ncard_le_ncard_diff_add_ncard Set.ncard_le_ncard_diff_add_ncard

theorem le_ncard_diff (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    t.ncard - s.ncard ≤ (t \ s).ncard :=
  tsub_le_iff_left.mpr (by rw [add_comm]; apply ncard_le_ncard_diff_add_ncard _ _ hs)
                           -- ⊢ ncard t ≤ ncard (t \ s) + ncard s
                                          -- 🎉 no goals
#align set.le_ncard_diff Set.le_ncard_diff

theorem ncard_diff_add_ncard (s t : Set α) (hs : s.Finite := by toFinite_tac)
  (ht : t.Finite := by toFinite_tac) :
    (s \ t).ncard + t.ncard = (s ∪ t).ncard := by
  rw [←ncard_union_eq disjoint_sdiff_left (hs.diff _) ht, diff_union_self]
  -- 🎉 no goals
#align set.ncard_diff_add_ncard Set.ncard_diff_add_ncard

theorem diff_nonempty_of_ncard_lt_ncard (h : s.ncard < t.ncard) (hs : s.Finite := by toFinite_tac) :
    (t \ s).Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Ne.def, diff_eq_empty]
  -- ⊢ ¬t ⊆ s
  exact fun h' ↦ h.not_le (ncard_le_of_subset h' hs)
  -- 🎉 no goals
#align set.diff_nonempty_of_ncard_lt_ncard Set.diff_nonempty_of_ncard_lt_ncard

theorem exists_mem_not_mem_of_ncard_lt_ncard (h : s.ncard < t.ncard)
  (hs : s.Finite := by toFinite_tac) : ∃ e, e ∈ t ∧ e ∉ s :=
  diff_nonempty_of_ncard_lt_ncard h hs
#align set.exists_mem_not_mem_of_ncard_lt_ncard Set.exists_mem_not_mem_of_ncard_lt_ncard

@[simp] theorem ncard_inter_add_ncard_diff_eq_ncard (s t : Set α)
    (hs : s.Finite := by toFinite_tac) : (s ∩ t).ncard + (s \ t).ncard = s.ncard := by
  rw [←ncard_union_eq (disjoint_of_subset_left (inter_subset_right _ _) disjoint_sdiff_right)
    (hs.inter_of_left _) (hs.diff _), union_comm, diff_union_inter]
#align set.ncard_inter_add_ncard_diff_eq_ncard Set.ncard_inter_add_ncard_diff_eq_ncard

theorem ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard = t.ncard ↔ (s \ t).ncard = (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_right_inj]
#align set.ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff
  Set.ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff

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
#align set.ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff
  Set.ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff

theorem ncard_add_ncard_compl (s : Set α) (hs : s.Finite := by toFinite_tac)
    (hsc : sᶜ.Finite := by toFinite_tac) : s.ncard + sᶜ.ncard = Nat.card α := by
  rw [← ncard_univ, ← ncard_union_eq (@disjoint_compl_right _ _ s) hs hsc, union_compl_self]
  -- 🎉 no goals
#align set.ncard_add_ncard_compl Set.ncard_add_ncard_compl

end Lattice

/-- Given a set `t` and a set `s` inside it, we can shrink `t` to any appropriate size, and keep `s`
    inside it. -/
theorem exists_intermediate_Set (i : ℕ) (h₁ : i + s.ncard ≤ t.ncard) (h₂ : s ⊆ t) :
    ∃ r : Set α, s ⊆ r ∧ r ⊆ t ∧ r.ncard = i + s.ncard := by
  cases' t.finite_or_infinite with ht ht
  -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ ncard r = i + ncard s
  · rw [ncard_eq_toFinset_card _ (ht.subset h₂)] at h₁ ⊢
    -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ ncard r = i + Finset.card (Finite.toFinset (_ : Set.Fin …
    rw [ncard_eq_toFinset_card t ht] at h₁
    -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ ncard r = i + Finset.card (Finite.toFinset (_ : Set.Fin …
    obtain ⟨r', hsr', hr't, hr'⟩ := Finset.exists_intermediate_set _ h₁ (by simpa)
    -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ ncard r = i + Finset.card (Finite.toFinset (_ : Set.Fin …
    exact ⟨r', by simpa using hsr', by simpa using hr't, by rw [← hr', ncard_coe_Finset]⟩
    -- 🎉 no goals
  rw [ht.ncard] at h₁
  -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ ncard r = i + ncard s
  have h₁' := Nat.eq_zero_of_le_zero h₁
  -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ ncard r = i + ncard s
  rw [add_eq_zero_iff] at h₁'
  -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ ncard r = i + ncard s
  refine' ⟨t, h₂, rfl.subset, _⟩
  -- ⊢ ncard t = i + ncard s
  rw [h₁'.2, h₁'.1, ht.ncard, add_zero]
  -- 🎉 no goals
#align set.exists_intermediate_set Set.exists_intermediate_Set

theorem exists_intermediate_set' {m : ℕ} (hs : s.ncard ≤ m) (ht : m ≤ t.ncard) (h : s ⊆ t) :
    ∃ r : Set α, s ⊆ r ∧ r ⊆ t ∧ r.ncard = m := by
  obtain ⟨r, hsr, hrt, hc⟩ :=
    exists_intermediate_Set (m - s.ncard) (by rwa [tsub_add_cancel_of_le hs]) h
  rw [tsub_add_cancel_of_le hs] at hc
  -- ⊢ ∃ r, s ⊆ r ∧ r ⊆ t ∧ ncard r = m
  exact ⟨r, hsr, hrt, hc⟩
  -- 🎉 no goals
#align set.exists_intermediate_set' Set.exists_intermediate_set'

/-- We can shrink `s` to any smaller size. -/
theorem exists_smaller_set (s : Set α) (i : ℕ) (h₁ : i ≤ s.ncard) :
    ∃ t : Set α, t ⊆ s ∧ t.ncard = i :=
  (exists_intermediate_Set i (by simpa) (empty_subset s)).imp fun t ht ↦
                                 -- 🎉 no goals
    ⟨ht.2.1, by simpa using ht.2.2⟩
                -- 🎉 no goals
#align set.exists_smaller_set Set.exists_smaller_set

theorem Infinite.exists_subset_ncard_eq {s : Set α} (hs : s.Infinite) (k : ℕ) :
    ∃ t, t ⊆ s ∧ t.Finite ∧ t.ncard = k := by
  have := hs.to_subtype
  -- ⊢ ∃ t, t ⊆ s ∧ Set.Finite t ∧ Set.ncard t = k
  obtain ⟨t', -, rfl⟩ := @Infinite.exists_subset_card_eq s univ infinite_univ k
  -- ⊢ ∃ t, t ⊆ s ∧ Set.Finite t ∧ Set.ncard t = Finset.card t'
  refine' ⟨Subtype.val '' (t' : Set s), by simp, Finite.image _ (by simp), _⟩
  -- ⊢ Set.ncard (Subtype.val '' ↑t') = Finset.card t'
  rw [ncard_image_of_injective _ Subtype.coe_injective]
  -- ⊢ Set.ncard ↑t' = Finset.card t'
  simp
  -- 🎉 no goals
#align set.Infinite.exists_subset_ncard_eq Set.Infinite.exists_subset_ncard_eq

theorem Infinite.exists_supset_ncard_eq {s t : Set α} (ht : t.Infinite) (hst : s ⊆ t)
    (hs : s.Finite) {k : ℕ} (hsk : s.ncard ≤ k) : ∃ s', s ⊆ s' ∧ s' ⊆ t ∧ s'.ncard = k := by
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.diff hs).exists_subset_ncard_eq (k - s.ncard)
  -- ⊢ ∃ s', s ⊆ s' ∧ s' ⊆ t ∧ Set.ncard s' = k
  refine' ⟨s ∪ s₁, subset_union_left _ _, union_subset hst (hs₁.trans (diff_subset _ _)), _⟩
  -- ⊢ Set.ncard (s ∪ s₁) = k
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
  -- ⊢ ∃ a, s = {a}
  have hft := (finite_of_ncard_ne_zero (ne_zero_of_eq_one h)).fintype
  -- ⊢ ∃ a, s = {a}
  simp_rw [ncard_eq_toFinset_card', @Finset.card_eq_one _ (toFinset s)] at h
  -- ⊢ ∃ a, s = {a}
  refine' h.imp fun a ha ↦ _
  -- ⊢ s = {a}
  simp_rw [Set.ext_iff, mem_singleton_iff]
  -- ⊢ ∀ (x : α), x ∈ s ↔ x = a
  simp only [Finset.ext_iff, mem_toFinset, Finset.mem_singleton] at ha
  -- ⊢ ∀ (x : α), x ∈ s ↔ x = a
  exact ha
  -- 🎉 no goals
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
  -- 🎉 no goals
#align set.ncard_le_one Set.ncard_le_one

theorem ncard_le_one_iff (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by
  rw [ncard_le_one hs]
  -- ⊢ (∀ (a : α), a ∈ s → ∀ (b : α), b ∈ s → a = b) ↔ ∀ {a b : α}, a ∈ s → b ∈ s → …
  tauto
  -- 🎉 no goals
#align set.ncard_le_one_iff Set.ncard_le_one_iff

theorem ncard_le_one_iff_eq (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ s = ∅ ∨ ∃ a, s = {a} := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  -- ⊢ ncard ∅ ≤ 1 ↔ ∅ = ∅ ∨ ∃ a, ∅ = {a}
  · exact iff_of_true (by simp) (Or.inl rfl)
    -- 🎉 no goals
  rw [ncard_le_one_iff hs]
  -- ⊢ (∀ {a b : α}, a ∈ s → b ∈ s → a = b) ↔ s = ∅ ∨ ∃ a, s = {a}
  refine' ⟨fun h ↦ Or.inr ⟨x, (singleton_subset_iff.mpr hx).antisymm' fun y hy ↦ h hy hx⟩, _⟩
  -- ⊢ (s = ∅ ∨ ∃ a, s = {a}) → ∀ {a b : α}, a ∈ s → b ∈ s → a = b
  rintro (rfl | ⟨a, rfl⟩)
  -- ⊢ ∀ {a b : α}, a ∈ ∅ → b ∈ ∅ → a = b
  · exact (not_mem_empty _ hx).elim
    -- 🎉 no goals
  simp_rw [mem_singleton_iff] at hx ⊢; subst hx
  -- ⊢ ∀ {a_1 b : α}, a_1 = a → b = a → a_1 = b
                                       -- ⊢ ∀ {a b : α}, a = x → b = x → a = b
  simp only [forall_eq_apply_imp_iff', imp_self, implies_true]
  -- 🎉 no goals
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
  -- ⊢ Finset.card (Finite.toFinset (_ : Set.Finite s)) ≤ 1
  exact Finset.card_le_one_of_subsingleton _
  -- 🎉 no goals
#align ncard_le_one_of_subsingleton Set.ncard_le_one_of_subsingleton

theorem one_lt_ncard (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.one_lt_card, Finite.mem_toFinset]
  -- 🎉 no goals
#align set.one_lt_ncard Set.one_lt_ncard

theorem one_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b :=   by
  rw [one_lt_ncard hs]
  -- ⊢ (∃ a, a ∈ s ∧ ∃ b, b ∈ s ∧ a ≠ b) ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b
  simp only [exists_prop, exists_and_left]
  -- 🎉 no goals
#align set.one_lt_ncard_iff Set.one_lt_ncard_iff

theorem two_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.two_lt_card_iff, Finite.mem_toFinset]
  -- 🎉 no goals
#align set.two_lt_ncard_iff Set.two_lt_ncard_iff

theorem two_lt_ncard (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp only [two_lt_ncard_iff hs, exists_and_left, exists_prop]
  -- 🎉 no goals
#align set.two_lt_card Set.two_lt_ncard

theorem exists_ne_of_one_lt_ncard (hs : 1 < s.ncard) (a : α) : ∃ b, b ∈ s ∧ b ≠ a := by
  have hsf := (finite_of_ncard_ne_zero (zero_lt_one.trans hs).ne.symm)
  -- ⊢ ∃ b, b ∈ s ∧ b ≠ a
  rw [ncard_eq_toFinset_card _ hsf] at hs
  -- ⊢ ∃ b, b ∈ s ∧ b ≠ a
  simpa only [Finite.mem_toFinset] using Finset.exists_ne_of_one_lt_card hs a
  -- 🎉 no goals
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
  -- ⊢ (∃ a t, ¬a ∈ t ∧ insert a t = s ∧ ncard t = n) → ncard s = n + 1
  rintro ⟨a, t, hat, h, rfl⟩
  -- ⊢ ncard s = ncard t + 1
  rw [← h, ncard_insert_of_not_mem hat (hs.subset ((subset_insert a t).trans_eq h))]
  -- 🎉 no goals
#align set.ncard_eq_succ Set.ncard_eq_succ

theorem ncard_eq_two : s.ncard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  rw [←encard_eq_two, ncard_def, ←Nat.cast_inj (R := ℕ∞), Nat.cast_ofNat]
  -- ⊢ ↑(↑ENat.toNat (encard s)) = 2 ↔ encard s = 2
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  -- ⊢ encard s = 2
  · rwa [ENat.coe_toNat] at h; rintro h'; simp [h'] at h
    -- ⊢ encard s ≠ ⊤
                               -- ⊢ False
                                          -- 🎉 no goals
  simp [h]; exact Iff.mp ENat.coe_toNat_eq_self rfl
  -- ⊢ ¬2 = ⊤
            -- 🎉 no goals
#align set.ncard_eq_two Set.ncard_eq_two

theorem ncard_eq_three : s.ncard = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  rw [←encard_eq_three, ncard_def, ←Nat.cast_inj (R := ℕ∞), Nat.cast_ofNat]
  -- ⊢ ↑(↑ENat.toNat (encard s)) = 3 ↔ encard s = 3
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  -- ⊢ encard s = 3
  · rwa [ENat.coe_toNat] at h; rintro h'; simp [h'] at h
    -- ⊢ encard s ≠ ⊤
                               -- ⊢ False
                                          -- 🎉 no goals
  simp [h]; exact Iff.mp ENat.coe_toNat_eq_self rfl
  -- ⊢ ¬3 = ⊤
            -- 🎉 no goals
#align set.ncard_eq_three Set.ncard_eq_three

end ncard
