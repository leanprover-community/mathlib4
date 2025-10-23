/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Finite.Powerset

/-!
# Noncomputable Set Cardinality

We define the cardinality of set `s` as a term `Set.encard s : ℕ∞` and a term `Set.ncard s : ℕ`.
The latter takes the junk value of zero if `s` is infinite. Both functions are noncomputable, and
are defined in terms of `ENat.card` (which takes a type as its argument); this file can be seen
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

namespace Set

variable {α β : Type*} {s t : Set α}

/-- The cardinality of a set as a term in `ℕ∞` -/
noncomputable def encard (s : Set α) : ℕ∞ := ENat.card s

@[simp] theorem encard_univ (α : Type*) :
    encard (univ : Set α) = ENat.card α := by
  rw [encard, ENat.card_congr (Equiv.Set.univ α)]

@[simp] theorem _root_.ENat.card_coe_set_eq (s : Set α) : ENat.card s = s.encard := rfl

@[deprecated "Use simp" (since := "2025-09-23")]
theorem encard_univ_coe (s : Set α) : encard (univ : Set s) = encard s := by simp

theorem Finite.encard_eq_coe_toFinset_card (h : s.Finite) : s.encard = h.toFinset.card := by
  have := h.fintype
  rw [encard, ENat.card_eq_coe_fintype_card, toFinite_toFinset, toFinset_card]

theorem encard_eq_coe_toFinset_card (s : Set α) [Fintype s] : encard s = s.toFinset.card := by
  have h := toFinite s
  rw [h.encard_eq_coe_toFinset_card, toFinite_toFinset]

@[simp] theorem toENat_cardinalMk (s : Set α) : (Cardinal.mk s).toENat = s.encard := rfl

theorem toENat_cardinalMk_subtype (P : α → Prop) :
    (Cardinal.mk {x // P x}).toENat = {x | P x}.encard :=
  rfl

@[simp] theorem coe_fintypeCard (s : Set α) [Fintype s] : Fintype.card s = s.encard := by
  simp [encard_eq_coe_toFinset_card]

@[simp, norm_cast] theorem encard_coe_eq_coe_finsetCard (s : Finset α) :
    encard (s : Set α) = s.card := by
  rw [Finite.encard_eq_coe_toFinset_card (Finset.finite_toSet s)]; simp

@[simp] theorem Infinite.encard_eq {s : Set α} (h : s.Infinite) : s.encard = ⊤ := by
  have := h.to_subtype
  rw [encard, ENat.card_eq_top_of_infinite]

@[simp] theorem encard_eq_zero : s.encard = 0 ↔ s = ∅ := by
  rw [encard, ENat.card_eq_zero_iff_empty, isEmpty_subtype, eq_empty_iff_forall_notMem]

@[simp] theorem encard_empty : (∅ : Set α).encard = 0 := by
  rw [encard_eq_zero]

theorem nonempty_of_encard_ne_zero (h : s.encard ≠ 0) : s.Nonempty := by
  rwa [nonempty_iff_ne_empty, Ne, ← encard_eq_zero]

theorem encard_ne_zero : s.encard ≠ 0 ↔ s.Nonempty := by
  rw [ne_eq, encard_eq_zero, nonempty_iff_ne_empty]

@[simp] theorem encard_pos : 0 < s.encard ↔ s.Nonempty := by
  rw [pos_iff_ne_zero, encard_ne_zero]

protected alias ⟨_, Nonempty.encard_pos⟩ := encard_pos

@[simp] theorem encard_singleton (e : α) : ({e} : Set α).encard = 1 := by
  rw [encard, ENat.card_eq_coe_fintype_card, Fintype.card_ofSubsingleton, Nat.cast_one]

theorem encard_union_eq (h : Disjoint s t) : (s ∪ t).encard = s.encard + t.encard := by
  classical
  unfold encard
  simp [ENat.card_congr (Equiv.Set.union h)]

theorem encard_ne_add_one (a : α) :
    ({x | x ≠ a}).encard + 1 = ENat.card α := by
  have : Disjoint {x | x ≠ a} {a} := disjoint_singleton_right.mpr <| by simp
  replace this := (Set.encard_union_eq this).symm
  have aux : {x | x ≠ a} ∪ {a} = univ := by ext x; simp [eq_or_ne x a]
  rwa [encard_singleton, aux, encard_univ] at this

theorem encard_insert_of_notMem {a : α} (has : a ∉ s) : (insert a s).encard = s.encard + 1 := by
  rw [← union_singleton, encard_union_eq (by simpa), encard_singleton]

@[deprecated (since := "2025-05-23")] alias encard_insert_of_not_mem := encard_insert_of_notMem

theorem Finite.encard_lt_top (h : s.Finite) : s.encard < ⊤ := by
  induction s, h using Set.Finite.induction_on with
  | empty => simp
  | insert hat _ ht' =>
    rw [encard_insert_of_notMem hat]
    exact lt_tsub_iff_right.1 ht'

theorem Finite.encard_eq_coe (h : s.Finite) : s.encard = ENat.toNat s.encard :=
  (ENat.coe_toNat h.encard_lt_top.ne).symm

theorem Finite.exists_encard_eq_coe (h : s.Finite) : ∃ (n : ℕ), s.encard = n :=
  ⟨_, h.encard_eq_coe⟩

@[simp] theorem encard_lt_top_iff : s.encard < ⊤ ↔ s.Finite :=
  ⟨fun h ↦ by_contra fun h' ↦ h.ne (Infinite.encard_eq h'), Finite.encard_lt_top⟩

@[simp] theorem encard_eq_top_iff : s.encard = ⊤ ↔ s.Infinite := by
  rw [← not_iff_not, ← Ne, ← lt_top_iff_ne_top, encard_lt_top_iff, not_infinite]

alias ⟨_, encard_eq_top⟩ := encard_eq_top_iff

theorem encard_ne_top_iff : s.encard ≠ ⊤ ↔ s.Finite := by
  simp

theorem finite_of_encard_le_coe {k : ℕ} (h : s.encard ≤ k) : s.Finite := by
  rw [← encard_lt_top_iff]; exact h.trans_lt (WithTop.coe_lt_top _)

theorem finite_of_encard_eq_coe {k : ℕ} (h : s.encard = k) : s.Finite :=
  finite_of_encard_le_coe h.le

theorem encard_le_coe_iff {k : ℕ} : s.encard ≤ k ↔ s.Finite ∧ ∃ (n₀ : ℕ), s.encard = n₀ ∧ n₀ ≤ k :=
  ⟨fun h ↦ ⟨finite_of_encard_le_coe h, by rwa [ENat.le_coe_iff] at h⟩,
    fun ⟨_,⟨n₀,hs, hle⟩⟩ ↦ by rwa [hs, Nat.cast_le]⟩

@[simp]
theorem encard_prod {s : Set α} {t : Set β} : (s ×ˢ t).encard = s.encard * t.encard := by
  unfold encard
  simp [ENat.card_congr (Equiv.Set.prod ..)]

section Lattice

theorem encard_le_encard (h : s ⊆ t) : s.encard ≤ t.encard := by
  rw [← union_diff_cancel h, encard_union_eq disjoint_sdiff_right]; exact le_self_add

theorem encard_mono {α : Type*} : Monotone (encard : Set α → ℕ∞) :=
  fun _ _ ↦ encard_le_encard

theorem encard_diff_add_encard_of_subset (h : s ⊆ t) : (t \ s).encard + s.encard = t.encard := by
  rw [← encard_union_eq disjoint_sdiff_left, diff_union_self, union_eq_self_of_subset_right h]

@[simp] theorem one_le_encard_iff_nonempty : 1 ≤ s.encard ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, Ne, ← encard_eq_zero, ENat.one_le_iff_ne_zero]

theorem encard_diff_add_encard_inter (s t : Set α) :
    (s \ t).encard + (s ∩ t).encard = s.encard := by
  rw [← encard_union_eq (disjoint_of_subset_right inter_subset_right disjoint_sdiff_left),
    diff_union_inter]

theorem encard_union_add_encard_inter (s t : Set α) :
    (s ∪ t).encard + (s ∩ t).encard = s.encard + t.encard := by
  rw [← diff_union_self, encard_union_eq disjoint_sdiff_left, add_right_comm,
    encard_diff_add_encard_inter]

theorem encard_eq_encard_iff_encard_diff_eq_encard_diff (h : (s ∩ t).Finite) :
    s.encard = t.encard ↔ (s \ t).encard = (t \ s).encard := by
  rw [← encard_diff_add_encard_inter s t, ← encard_diff_add_encard_inter t s, inter_comm t s,
    WithTop.add_right_inj h.encard_lt_top.ne]

theorem encard_le_encard_iff_encard_diff_le_encard_diff (h : (s ∩ t).Finite) :
    s.encard ≤ t.encard ↔ (s \ t).encard ≤ (t \ s).encard := by
  rw [← encard_diff_add_encard_inter s t, ← encard_diff_add_encard_inter t s, inter_comm t s,
    WithTop.add_le_add_iff_right h.encard_lt_top.ne]

theorem encard_lt_encard_iff_encard_diff_lt_encard_diff (h : (s ∩ t).Finite) :
    s.encard < t.encard ↔ (s \ t).encard < (t \ s).encard := by
  rw [← encard_diff_add_encard_inter s t, ← encard_diff_add_encard_inter t s, inter_comm t s,
    WithTop.add_lt_add_iff_right h.encard_lt_top.ne]

theorem encard_union_le (s t : Set α) : (s ∪ t).encard ≤ s.encard + t.encard := by
  rw [← encard_union_add_encard_inter]; exact le_self_add

theorem finite_iff_finite_of_encard_eq_encard (h : s.encard = t.encard) : s.Finite ↔ t.Finite := by
  rw [← encard_lt_top_iff, ← encard_lt_top_iff, h]

theorem infinite_iff_infinite_of_encard_eq_encard (h : s.encard = t.encard) :
    s.Infinite ↔ t.Infinite := by rw [← encard_eq_top_iff, h, encard_eq_top_iff]

theorem Finite.finite_of_encard_le {s : Set α} {t : Set β} (hs : s.Finite)
    (h : t.encard ≤ s.encard) : t.Finite :=
  encard_lt_top_iff.1 (h.trans_lt hs.encard_lt_top)

lemma Finite.eq_of_subset_of_encard_le' (ht : t.Finite) (hst : s ⊆ t) (hts : t.encard ≤ s.encard) :
    s = t := by
  rw [← zero_add (a := encard s), ← encard_diff_add_encard_of_subset hst] at hts
  have hdiff := WithTop.le_of_add_le_add_right (ht.subset hst).encard_lt_top.ne hts
  rw [nonpos_iff_eq_zero, encard_eq_zero, diff_eq_empty] at hdiff
  exact hst.antisymm hdiff

theorem Finite.eq_of_subset_of_encard_le (hs : s.Finite) (hst : s ⊆ t)
    (hts : t.encard ≤ s.encard) : s = t :=
  (hs.finite_of_encard_le hts).eq_of_subset_of_encard_le' hst hts

theorem Finite.encard_lt_encard (hs : s.Finite) (h : s ⊂ t) : s.encard < t.encard :=
  (encard_mono h.subset).lt_of_ne fun he ↦ h.ne (hs.eq_of_subset_of_encard_le h.subset he.symm.le)

theorem encard_strictMono [Finite α] : StrictMono (encard : Set α → ℕ∞) :=
  fun _ _ h ↦ (toFinite _).encard_lt_encard h

theorem encard_diff_add_encard (s t : Set α) : (s \ t).encard + t.encard = (s ∪ t).encard := by
  rw [← encard_union_eq disjoint_sdiff_left, diff_union_self]

theorem encard_le_encard_diff_add_encard (s t : Set α) : s.encard ≤ (s \ t).encard + t.encard :=
  (encard_mono subset_union_left).trans_eq (encard_diff_add_encard _ _).symm

theorem tsub_encard_le_encard_diff (s t : Set α) : s.encard - t.encard ≤ (s \ t).encard := by
  rw [tsub_le_iff_left, add_comm]; apply encard_le_encard_diff_add_encard

theorem encard_add_encard_compl (s : Set α) : s.encard + sᶜ.encard = (univ : Set α).encard := by
  rw [← encard_union_eq disjoint_compl_right, union_compl_self]

end Lattice

section InsertErase

variable {a b : α}

theorem encard_insert_le (s : Set α) (x : α) : (insert x s).encard ≤ s.encard + 1 := by
  rw [← union_singleton, ← encard_singleton x]; apply encard_union_le

theorem encard_singleton_inter (s : Set α) (x : α) : ({x} ∩ s).encard ≤ 1 := by
  rw [← encard_singleton x]; exact encard_le_encard inter_subset_left

theorem encard_diff_singleton_add_one (h : a ∈ s) :
    (s \ {a}).encard + 1 = s.encard := by
  rw [← encard_insert_of_notMem (fun h ↦ h.2 rfl), insert_diff_singleton, insert_eq_of_mem h]

theorem encard_diff_singleton_of_mem (h : a ∈ s) :
    (s \ {a}).encard = s.encard - 1 := by
  rw [← encard_diff_singleton_add_one h, ← WithTop.add_right_inj WithTop.one_ne_top,
    tsub_add_cancel_of_le (self_le_add_left _ _)]

theorem encard_tsub_one_le_encard_diff_singleton (s : Set α) (x : α) :
    s.encard - 1 ≤ (s \ {x}).encard := by
  rw [← encard_singleton x]; apply tsub_encard_le_encard_diff

theorem encard_exchange (ha : a ∉ s) (hb : b ∈ s) : (insert a (s \ {b})).encard = s.encard := by
  rw [encard_insert_of_notMem, encard_diff_singleton_add_one hb]
  simp_all only [mem_diff, mem_singleton_iff, false_and, not_false_eq_true]

theorem encard_exchange' (ha : a ∉ s) (hb : b ∈ s) : (insert a s \ {b}).encard = s.encard := by
  rw [← insert_diff_singleton_comm (by rintro rfl; exact ha hb), encard_exchange ha hb]

theorem encard_eq_add_one_iff {k : ℕ∞} :
    s.encard = k + 1 ↔ (∃ a t, a ∉ t ∧ insert a t = s ∧ t.encard = k) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty_of_encard_ne_zero (s := s) (by simp [h])
    refine ⟨a, s \ {a}, fun h ↦ h.2 rfl, by rwa [insert_diff_singleton, insert_eq_of_mem], ?_⟩
    rw [← WithTop.add_right_inj WithTop.one_ne_top, ← h,
      encard_diff_singleton_add_one ha]
  rintro ⟨a, t, h, rfl, rfl⟩
  rw [encard_insert_of_notMem h]

/-- Every set is either empty, infinite, or can have its `encard` reduced by a removal. Intended
  for well-founded induction on the value of `encard`. -/
theorem eq_empty_or_encard_eq_top_or_encard_diff_singleton_lt (s : Set α) :
    s = ∅ ∨ s.encard = ⊤ ∨ ∃ a ∈ s, (s \ {a}).encard < s.encard := by
  refine s.eq_empty_or_nonempty.elim Or.inl (Or.inr ∘ fun ⟨a,ha⟩ ↦
    (s.finite_or_infinite.elim (fun hfin ↦ Or.inr ⟨a, ha, ?_⟩) (Or.inl ∘ Infinite.encard_eq)))
  rw [← encard_diff_singleton_add_one ha]; nth_rw 1 [← add_zero (encard _)]
  exact WithTop.add_lt_add_left hfin.diff.encard_lt_top.ne zero_lt_one

end InsertErase

section SmallSets

theorem encard_pair {x y : α} (hne : x ≠ y) : ({x, y} : Set α).encard = 2 := by
  rw [encard_insert_of_notMem (by simpa), ← one_add_one_eq_two,
    WithTop.add_right_inj WithTop.one_ne_top, encard_singleton]

theorem encard_eq_one : s.encard = 1 ↔ ∃ x, s = {x} := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ by rw [hx, encard_singleton]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  exact ⟨x, ((finite_singleton x).eq_of_subset_of_encard_le (by simpa) (by simp [h])).symm⟩

theorem encard_le_one_iff_eq : s.encard ≤ 1 ↔ s = ∅ ∨ ∃ x, s = {x} := by
  rw [le_iff_lt_or_eq, lt_iff_not_ge, ENat.one_le_iff_ne_zero, not_not, encard_eq_zero,
    encard_eq_one]

theorem encard_le_one_iff : s.encard ≤ 1 ↔ ∀ a b, a ∈ s → b ∈ s → a = b := by
  rw [encard_le_one_iff_eq, or_iff_not_imp_left, ← Ne, ← nonempty_iff_ne_empty]
  refine ⟨fun h a b has hbs ↦ ?_,
    fun h ⟨x, hx⟩ ↦ ⟨x, ((singleton_subset_iff.2 hx).antisymm' (fun y hy ↦ h _ _ hy hx))⟩⟩
  obtain ⟨x, rfl⟩ := h ⟨_, has⟩
  rw [(has : a = x), (hbs : b = x)]

theorem encard_le_one_iff_subsingleton : s.encard ≤ 1 ↔ s.Subsingleton := by
  rw [encard_le_one_iff, Set.Subsingleton]
  tauto

theorem one_lt_encard_iff_nontrivial : 1 < s.encard ↔ s.Nontrivial := by
  rw [← not_iff_not, not_lt, Set.not_nontrivial_iff, ← encard_le_one_iff_subsingleton]

theorem one_lt_encard_iff : 1 < s.encard ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  rw [← not_iff_not, not_exists, not_lt, encard_le_one_iff]; aesop

theorem exists_ne_of_one_lt_encard (h : 1 < s.encard) (a : α) : ∃ b ∈ s, b ≠ a := by
  by_contra! h'
  obtain ⟨b, b', hb, hb', hne⟩ := one_lt_encard_iff.1 h
  apply hne
  rw [h' b hb, h' b' hb']

theorem encard_eq_two : s.encard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  refine ⟨fun h ↦ ?_, fun ⟨x, y, hne, hs⟩ ↦ by rw [hs, encard_pair hne]⟩
  obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
  rw [← insert_eq_of_mem hx, ← insert_diff_singleton, encard_insert_of_notMem (fun h ↦ h.2 rfl),
    ← one_add_one_eq_two, WithTop.add_right_inj (WithTop.one_ne_top), encard_eq_one] at h
  obtain ⟨y, h⟩ := h
  refine ⟨x, y, by rintro rfl; exact (h.symm.subset rfl).2 rfl, ?_⟩
  rw [← h, insert_diff_singleton, insert_eq_of_mem hx]

theorem encard_eq_three {α : Type u_1} {s : Set α} :
    encard s = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  refine ⟨fun h ↦ ?_, fun ⟨x, y, z, hxy, hyz, hxz, hs⟩ ↦ ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
    rw [← insert_eq_of_mem hx, ← insert_diff_singleton,
      encard_insert_of_notMem (fun h ↦ h.2 rfl), (by exact rfl : (3 : ℕ∞) = 2 + 1),
      WithTop.add_right_inj WithTop.one_ne_top, encard_eq_two] at h
    obtain ⟨y, z, hne, hs⟩ := h
    refine ⟨x, y, z, ?_, ?_, hne, ?_⟩
    · rintro rfl; exact (hs.symm.subset (Or.inl rfl)).2 rfl
    · rintro rfl; exact (hs.symm.subset (Or.inr rfl)).2 rfl
    rw [← hs, insert_diff_singleton, insert_eq_of_mem hx]
  rw [hs, encard_insert_of_notMem, encard_insert_of_notMem, encard_singleton] <;> aesop

theorem encard_eq_four {α : Type u_1} {s : Set α} :
    encard s = 4 ↔ ∃ x y z w, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧ s = {x, y, z, w} := by
  refine ⟨fun h ↦ ?_, fun ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hs⟩ ↦ ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_encard_ne_zero (s := s) (by rw [h]; simp)
    rw [← insert_eq_of_mem hx, ← insert_diff_singleton,
      encard_insert_of_notMem (fun h ↦ h.2 rfl), (by exact rfl : (4 : ℕ∞) = 3 + 1),
      WithTop.add_right_inj WithTop.one_ne_top, encard_eq_three] at h
    obtain ⟨y, z, w, hyz, hyw, hzw, hs⟩ := h
    refine ⟨x, y, z, w, ?_, ?_, ?_, hyz, hyw, hzw, ?_⟩
    · rintro rfl; exact (hs.symm.subset (Or.inl rfl)).2 rfl
    · rintro rfl; exact (hs.symm.subset (Or.inr (Or.inl rfl))).2 rfl
    · rintro rfl; exact (hs.symm.subset (Or.inr (Or.inr rfl))).2 rfl
    rw [← hs, insert_diff_singleton, insert_eq_of_mem hx]
  rw [hs, encard_insert_of_notMem, encard_insert_of_notMem, encard_insert_of_notMem,
    encard_singleton] <;> aesop

theorem Nat.encard_range (k : ℕ) : {i | i < k}.encard = k := by
  convert encard_coe_eq_coe_finsetCard (Finset.range k) using 1
  · rw [Finset.coe_range, Iio_def]
  rw [Finset.card_range]

end SmallSets

theorem Finite.eq_insert_of_subset_of_encard_eq_succ (hs : s.Finite) (h : s ⊆ t)
    (hst : t.encard = s.encard + 1) : ∃ a, t = insert a s := by
  rw [← encard_diff_add_encard_of_subset h, add_comm, WithTop.add_left_inj hs.encard_lt_top.ne,
    encard_eq_one] at hst
  obtain ⟨x, hx⟩ := hst; use x; rw [← diff_union_of_subset h, hx, singleton_union]

theorem exists_subset_encard_eq {k : ℕ∞} (hk : k ≤ s.encard) : ∃ t, t ⊆ s ∧ t.encard = k := by
  induction k using ENat.nat_induction with
  | zero => exact ⟨∅, empty_subset _, by simp⟩
  | succ n IH =>
    obtain ⟨t₀, ht₀s, ht₀⟩ := IH (le_trans (by simp) hk)
    simp only [Nat.cast_succ] at *
    have hne : t₀ ≠ s := by
      rintro rfl; rw [ht₀, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le] at hk; simp at hk
    obtain ⟨x, hx⟩ := exists_of_ssubset (ht₀s.ssubset_of_ne hne)
    exact ⟨insert x t₀, insert_subset hx.1 ht₀s, by rw [encard_insert_of_notMem hx.2, ht₀]⟩
  | top => rw [top_le_iff] at hk; exact ⟨s, Subset.rfl, hk⟩

theorem exists_superset_subset_encard_eq {k : ℕ∞}
    (hst : s ⊆ t) (hsk : s.encard ≤ k) (hkt : k ≤ t.encard) :
    ∃ r, s ⊆ r ∧ r ⊆ t ∧ r.encard = k := by
  obtain (hs | hs) := eq_or_ne s.encard ⊤
  · rw [hs, top_le_iff] at hsk; subst hsk; exact ⟨s, Subset.rfl, hst, hs⟩
  obtain ⟨k, rfl⟩ := exists_add_of_le hsk
  obtain ⟨k', hk'⟩ := exists_add_of_le hkt
  have hk : k ≤ encard (t \ s) := by
    rw [← encard_diff_add_encard_of_subset hst, add_comm] at hkt
    exact WithTop.le_of_add_le_add_right hs hkt
  obtain ⟨r', hr', rfl⟩ := exists_subset_encard_eq hk
  refine ⟨s ∪ r', subset_union_left, union_subset hst (hr'.trans diff_subset), ?_⟩
  rw [encard_union_eq (disjoint_of_subset_right hr' disjoint_sdiff_right)]

section Function

variable {s : Set α} {t : Set β} {f : α → β}

theorem InjOn.encard_image (h : InjOn f s) : (f '' s).encard = s.encard := by
  rw [encard, ENat.card_image_of_injOn h, encard]

theorem encard_congr (e : s ≃ t) : s.encard = t.encard := ENat.card_congr e

theorem _root_.Function.Injective.encard_image (hf : f.Injective) (s : Set α) :
    (f '' s).encard = s.encard :=
  hf.injOn.encard_image

theorem _root_.Function.Injective.encard_range (hf : f.Injective) :
    ENat.card α ≤ (range f).encard := by
  rw [← image_univ, hf.encard_image, encard_univ]

theorem _root_.Function.Embedding.encard_le (e : s ↪ t) : s.encard ≤ t.encard :=
  ENat.card_le_card_of_injective e.injective

theorem encard_image_le (f : α → β) (s : Set α) : (f '' s).encard ≤ s.encard := by
  obtain (h | h) := isEmpty_or_nonempty α
  · rw [s.eq_empty_of_isEmpty]; simp
  rw [← (f.invFunOn_injOn_image s).encard_image]
  apply encard_le_encard
  exact f.invFunOn_image_image_subset s

theorem Finite.injOn_of_encard_image_eq (hs : s.Finite) (h : (f '' s).encard = s.encard) :
    InjOn f s := by
  obtain (h' | hne) := isEmpty_or_nonempty α
  · simp
  rw [← (f.invFunOn_injOn_image s).encard_image] at h
  rw [injOn_iff_invFunOn_image_image_eq_self]
  exact hs.eq_of_subset_of_encard_le' (f.invFunOn_image_image_subset s) h.symm.le

theorem encard_preimage_of_injective_subset_range (hf : f.Injective) (ht : t ⊆ range f) :
    (f ⁻¹' t).encard = t.encard := by
  rw [← hf.encard_image, image_preimage_eq_inter_range, inter_eq_self_of_subset_left ht]

lemma encard_preimage_of_bijective (hf : f.Bijective) (t : Set β) : (f ⁻¹' t).encard = t.encard :=
  encard_preimage_of_injective_subset_range hf.injective (by simp [hf.surjective.range_eq])

theorem encard_le_encard_of_injOn (hf : MapsTo f s t) (f_inj : InjOn f s) :
    s.encard ≤ t.encard := by
  rw [← f_inj.encard_image]; apply encard_le_encard; rintro _ ⟨x, hx, rfl⟩; exact hf hx

open Notation in
lemma encard_preimage_val_le_encard_left (P Q : Set α) : (P ↓∩ Q).encard ≤ P.encard :=
  (Function.Embedding.subtype _).encard_le

open Notation in
lemma encard_preimage_val_le_encard_right (P Q : Set α) : (P ↓∩ Q).encard ≤ Q.encard :=
  Function.Embedding.encard_le ⟨fun ⟨⟨x, _⟩, hx⟩ ↦ ⟨x, hx⟩, fun _ _ h ↦ by
    simpa [Subtype.coe_inj] using h⟩

theorem Finite.exists_injOn_of_encard_le [Nonempty β] {s : Set α} {t : Set β} (hs : s.Finite)
    (hle : s.encard ≤ t.encard) : ∃ (f : α → β), s ⊆ f ⁻¹' t ∧ InjOn f s := by
  classical
  obtain (rfl | h | ⟨a, has, -⟩) := s.eq_empty_or_encard_eq_top_or_encard_diff_singleton_lt
  · simp
  · exact (encard_ne_top_iff.mpr hs h).elim
  obtain ⟨b, hbt⟩ := encard_pos.1 ((encard_pos.2 ⟨_, has⟩).trans_le hle)
  have hle' : (s \ {a}).encard ≤ (t \ {b}).encard := by
    rwa [← WithTop.add_le_add_iff_right WithTop.one_ne_top,
    encard_diff_singleton_add_one has, encard_diff_singleton_add_one hbt]
  obtain ⟨f₀, hf₀s, hinj⟩ := exists_injOn_of_encard_le hs.diff hle'
  simp only [preimage_diff, subset_def, mem_diff, mem_singleton_iff, mem_preimage, and_imp] at hf₀s
  use Function.update f₀ a b
  rw [← insert_eq_of_mem has, ← insert_diff_singleton, injOn_insert (fun h ↦ h.2 rfl)]
  simp only [mem_diff, mem_singleton_iff, insert_diff_singleton, subset_def,
    mem_insert_iff, mem_preimage, Function.update_apply, forall_eq_or_imp, ite_true, and_imp,
    mem_image, ite_eq_left_iff, not_exists, not_and, not_forall, exists_prop, and_iff_right hbt]
  refine ⟨?_, ?_, fun x hxs hxa ↦ ⟨hxa, (hf₀s x hxs hxa).2⟩⟩
  · rintro x hx; split_ifs with h
    · assumption
    · exact (hf₀s x hx h).1
  exact InjOn.congr hinj (fun x ⟨_, hxa⟩ ↦ by rwa [Function.update_of_ne])
termination_by encard s

theorem Finite.exists_bijOn_of_encard_eq [Nonempty β] (hs : s.Finite) (h : s.encard = t.encard) :
    ∃ (f : α → β), BijOn f s t := by
  obtain ⟨f, hf, hinj⟩ := hs.exists_injOn_of_encard_le h.le; use f
  convert hinj.bijOn_image
  rw [(hs.image f).eq_of_subset_of_encard_le (image_subset_iff.mpr hf)
    (h.symm.trans hinj.encard_image.symm).le]

/-- A version of the pigeonhole principle for `Set`s rather than `Finset`s.

See also `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` and
`Set.exists_ne_map_eq_of_ncard_lt_of_maps_to`. -/
lemma exists_ne_map_eq_of_encard_lt_of_maps_to (hc : t.encard < s.encard) (hf : MapsTo f s t) :
    ∃ᵉ (a₁ ∈ s) (a₂ ∈ s), a₁ ≠ a₂ ∧ f a₁ = f a₂ := by
  contrapose! hc
  suffices Function.Injective (hf.restrict f) by
    let f' : s ↪ t := ⟨hf.restrict, this⟩
    exact f'.encard_le
  simpa only [hf.restrict_inj, not_imp_not] using hc

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
      simp only [← Nat.cast_le (α := ℕ∞), ← Nat.cast_inj (R := ℕ∞), Nat.cast_add, Nat.cast_one])


/-- The cardinality of `s : Set α` . Has the junk value `0` if `s` is infinite -/
noncomputable def ncard (s : Set α) : ℕ := ENat.toNat s.encard

theorem ncard_def (s : Set α) : s.ncard = ENat.toNat s.encard := rfl

theorem Finite.cast_ncard_eq (hs : s.Finite) : s.ncard = s.encard := by
  rwa [ncard, ENat.coe_toNat_eq_self, ne_eq, encard_eq_top_iff, Set.Infinite, not_not]

lemma ncard_le_encard (s : Set α) : s.ncard ≤ s.encard := ENat.coe_toNat_le_self _

@[simp] theorem _root_.Nat.card_coe_set_eq (s : Set α) : Nat.card s = s.ncard := rfl

@[deprecated (since := "2025-07-05")] alias Nat.card_coe_set_eq := _root_.Nat.card_coe_set_eq

theorem ncard_eq_toFinset_card (s : Set α) (hs : s.Finite := by toFinite_tac) :
    s.ncard = hs.toFinset.card := by
  rw [← _root_.Nat.card_coe_set_eq, @Nat.card_eq_fintype_card _ hs.fintype,
    @Finite.card_toFinset _ _ hs.fintype hs]

theorem ncard_eq_toFinset_card' (s : Set α) [Fintype s] :
    s.ncard = s.toFinset.card := by
  simp [← _root_.Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

lemma cast_ncard {s : Set α} (hs : s.Finite) :
    (s.ncard : Cardinal) = Cardinal.mk s := @Nat.cast_card _ hs

theorem encard_le_coe_iff_finite_ncard_le {k : ℕ} : s.encard ≤ k ↔ s.Finite ∧ s.ncard ≤ k := by
  rw [encard_le_coe_iff, and_congr_right_iff]
  exact fun hfin ↦ ⟨fun ⟨n₀, hn₀, hle⟩ ↦ by rwa [ncard_def, hn₀, ENat.toNat_coe],
    fun h ↦ ⟨s.ncard, by rw [hfin.cast_ncard_eq], h⟩⟩

theorem Infinite.ncard (hs : s.Infinite) : s.ncard = 0 := by
  rw [← _root_.Nat.card_coe_set_eq, @Nat.card_eq_zero_of_infinite _ hs.to_subtype]

@[gcongr]
theorem ncard_le_ncard (hst : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ t.ncard := by
  rw [← Nat.cast_le (α := ℕ∞), ht.cast_ncard_eq, (ht.subset hst).cast_ncard_eq]
  exact encard_mono hst

theorem ncard_mono [Finite α] : @Monotone (Set α) _ _ _ ncard := fun _ _ ↦ ncard_le_ncard

@[simp] theorem ncard_eq_zero (hs : s.Finite := by toFinite_tac) :
    s.ncard = 0 ↔ s = ∅ := by
  rw [← Nat.cast_inj (R := ℕ∞), hs.cast_ncard_eq, Nat.cast_zero, encard_eq_zero]

@[simp, norm_cast] theorem ncard_coe_finset (s : Finset α) : (s : Set α).ncard = s.card := by
  rw [ncard_eq_toFinset_card _, Finset.finite_toSet_toFinset]

@[deprecated (since := "2025-07-05")] alias ncard_coe_Finset := ncard_coe_finset

@[simp] theorem ncard_univ (α : Type*) : (univ : Set α).ncard = Nat.card α := Nat.card_univ

theorem ncard_le_card [Finite α] (s : Set α) : s.ncard ≤ Nat.card α :=
  ncard_univ α ▸ ncard_le_ncard s.subset_univ

@[simp] theorem ncard_empty (α : Type*) : (∅ : Set α).ncard = 0 := by
  rw [ncard_eq_zero]

theorem ncard_pos (hs : s.Finite := by toFinite_tac) : 0 < s.ncard ↔ s.Nonempty := by
  rw [pos_iff_ne_zero, Ne, ncard_eq_zero hs, nonempty_iff_ne_empty]

protected alias ⟨_, Nonempty.ncard_pos⟩ := ncard_pos

theorem ncard_ne_zero_of_mem {a : α} (h : a ∈ s) (hs : s.Finite := by toFinite_tac) : s.ncard ≠ 0 :=
  ((ncard_pos hs).mpr ⟨a, h⟩).ne.symm

theorem finite_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.Finite :=
  s.finite_or_infinite.elim id fun h ↦ (hs h.ncard).elim

theorem finite_of_ncard_pos (hs : 0 < s.ncard) : s.Finite :=
  finite_of_ncard_ne_zero hs.ne.symm

theorem nonempty_of_ncard_ne_zero (hs : s.ncard ≠ 0) : s.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; simp at hs

@[simp] theorem ncard_singleton (a : α) : ({a} : Set α).ncard = 1 := by
  simp [ncard]

theorem ncard_singleton_inter (a : α) (s : Set α) : ({a} ∩ s).ncard ≤ 1 := by
  rw [← Nat.cast_le (α := ℕ∞), (toFinite _).cast_ncard_eq, Nat.cast_one]
  apply encard_singleton_inter

@[simp]
theorem ncard_prod {s : Set α} {t : Set β} : (s ×ˢ t).ncard = s.ncard * t.ncard := by
  simp [ncard, ENat.toNat_mul]

@[simp]
theorem ncard_powerset (s : Set α) (hs : s.Finite := by toFinite_tac) :
    (𝒫 s).ncard = 2 ^ s.ncard := by
  have h := Cardinal.mk_powerset s
  rw [← cast_ncard hs.powerset, ← cast_ncard hs] at h
  norm_cast at h

section InsertErase

@[simp] theorem ncard_insert_of_notMem {a : α} (h : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    (insert a s).ncard = s.ncard + 1 := by
  rw [← Nat.cast_inj (R := ℕ∞), (hs.insert a).cast_ncard_eq, Nat.cast_add, Nat.cast_one,
    hs.cast_ncard_eq, encard_insert_of_notMem h]

@[deprecated (since := "2025-05-23")] alias ncard_insert_of_not_mem := ncard_insert_of_notMem

theorem ncard_insert_of_mem {a : α} (h : a ∈ s) : ncard (insert a s) = s.ncard := by
  rw [insert_eq_of_mem h]

theorem ncard_insert_le (a : α) (s : Set α) : (insert a s).ncard ≤ s.ncard + 1 := by
  obtain hs | hs := s.finite_or_infinite
  · to_encard_tac; rw [hs.cast_ncard_eq, (hs.insert _).cast_ncard_eq]; apply encard_insert_le
  rw [(hs.mono (subset_insert a s)).ncard]
  exact Nat.zero_le _

theorem ncard_insert_eq_ite {a : α} [Decidable (a ∈ s)] (hs : s.Finite := by toFinite_tac) :
    ncard (insert a s) = if a ∈ s then s.ncard else s.ncard + 1 := by
  by_cases h : a ∈ s
  · rw [ncard_insert_of_mem h, if_pos h]
  · rw [ncard_insert_of_notMem h hs, if_neg h]

theorem ncard_le_ncard_insert (a : α) (s : Set α) : s.ncard ≤ (insert a s).ncard := by
  classical
  refine
    s.finite_or_infinite.elim (fun h ↦ ?_) (fun h ↦ by (rw [h.ncard]; exact Nat.zero_le _))
  rw [ncard_insert_eq_ite h]; split_ifs <;> simp

theorem ncard_pair {a b : α} (h : a ≠ b) : ({a, b} : Set α).ncard = 2 := by
  simp [h]

-- removing `@[simp]` because the LHS is not in simp normal form
theorem ncard_diff_singleton_add_one {a : α} (h : a ∈ s)
    (hs : s.Finite := by toFinite_tac) : (s \ {a}).ncard + 1 = s.ncard := by
  to_encard_tac
  rw [hs.cast_ncard_eq, hs.diff.cast_ncard_eq, encard_diff_singleton_add_one h]

@[simp] theorem ncard_diff_singleton_of_mem {a : α} (h : a ∈ s) :
    (s \ {a}).ncard = s.ncard - 1 := by
  rcases s.infinite_or_finite with hs | hs
  · simp_all [ncard, Infinite.diff hs (finite_singleton a)]
  · exact eq_tsub_of_add_eq (ncard_diff_singleton_add_one h hs)

theorem ncard_diff_singleton_lt_of_mem {a : α} (h : a ∈ s) (hs : s.Finite := by toFinite_tac) :
    (s \ {a}).ncard < s.ncard := by
  rw [← ncard_diff_singleton_add_one h hs]; apply lt_add_one

theorem ncard_diff_singleton_le (s : Set α) (a : α) : (s \ {a}).ncard ≤ s.ncard := by
  obtain hs | hs := s.finite_or_infinite
  · apply ncard_le_ncard diff_subset hs
  convert zero_le (α := ℕ) _
  exact (hs.diff (by simp : Set.Finite {a})).ncard

theorem pred_ncard_le_ncard_diff_singleton (s : Set α) (a : α) : s.ncard - 1 ≤ (s \ {a}).ncard := by
  by_cases h : a ∈ s
  · rw [ncard_diff_singleton_of_mem h]
  rw [diff_singleton_eq_self h]
  apply Nat.pred_le

theorem ncard_exchange {a b : α} (ha : a ∉ s) (hb : b ∈ s) : (insert a (s \ {b})).ncard = s.ncard :=
  congr_arg ENat.toNat <| encard_exchange ha hb

theorem ncard_exchange' {a b : α} (ha : a ∉ s) (hb : b ∈ s) :
    (insert a s \ {b}).ncard = s.ncard := by
  rw [← ncard_exchange ha hb, ← singleton_union, ← singleton_union, union_diff_distrib,
    diff_singleton_eq_self fun h ↦ ha (by rwa [← mem_singleton_iff.mp h])]

lemma odd_card_insert_iff {a : α} (ha : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    Odd (insert a s).ncard ↔ Even s.ncard := by
  rw [ncard_insert_of_notMem ha hs, Nat.odd_add]
  simp only [← Nat.not_even_iff_odd, Nat.not_even_one, iff_false, Decidable.not_not]

lemma even_card_insert_iff {a : α} (ha : a ∉ s) (hs : s.Finite := by toFinite_tac) :
    Even (insert a s).ncard ↔ Odd s.ncard := by
  rw [ncard_insert_of_notMem ha hs, Nat.even_add_one, Nat.not_even_iff_odd]

end InsertErase

variable {f : α → β}

theorem ncard_image_le (hs : s.Finite := by toFinite_tac) : (f '' s).ncard ≤ s.ncard := by
  to_encard_tac; rw [hs.cast_ncard_eq, (hs.image _).cast_ncard_eq]; apply encard_image_le

theorem ncard_image_of_injOn (H : Set.InjOn f s) : (f '' s).ncard = s.ncard :=
  congr_arg ENat.toNat <| H.encard_image

theorem injOn_of_ncard_image_eq (h : (f '' s).ncard = s.ncard) (hs : s.Finite := by toFinite_tac) :
    Set.InjOn f s := by
  rw [← Nat.cast_inj (R := ℕ∞), hs.cast_ncard_eq, (hs.image _).cast_ncard_eq] at h
  exact hs.injOn_of_encard_image_eq h

theorem ncard_image_iff (hs : s.Finite := by toFinite_tac) :
    (f '' s).ncard = s.ncard ↔ Set.InjOn f s :=
  ⟨fun h ↦ injOn_of_ncard_image_eq h hs, ncard_image_of_injOn⟩

theorem ncard_image_of_injective (s : Set α) (H : f.Injective) : (f '' s).ncard = s.ncard :=
  ncard_image_of_injOn fun _ _ _ _ h ↦ H h

theorem ncard_preimage_of_injective_subset_range {s : Set β} (H : f.Injective)
    (hs : s ⊆ Set.range f) :
    (f ⁻¹' s).ncard = s.ncard := by
  rw [← ncard_image_of_injective _ H, image_preimage_eq_iff.mpr hs]

theorem fiber_ncard_ne_zero_iff_mem_image {y : β} (hs : s.Finite := by toFinite_tac) :
    { x ∈ s | f x = y }.ncard ≠ 0 ↔ y ∈ f '' s := by
  refine ⟨nonempty_of_ncard_ne_zero, ?_⟩
  rintro ⟨z, hz, rfl⟩
  exact @ncard_ne_zero_of_mem _ ({ x ∈ s | f x = f z }) z (mem_sep hz rfl)
    (hs.subset (sep_subset _ _))

@[simp] theorem ncard_map (f : α ↪ β) : (f '' s).ncard = s.ncard :=
  ncard_image_of_injective _ f.inj'

@[simp] theorem ncard_subtype (P : α → Prop) (s : Set α) :
    { x : Subtype P | (x : α) ∈ s }.ncard = (s ∩ setOf P).ncard := by
  convert (ncard_image_of_injective _ (@Subtype.coe_injective _ P)).symm
  ext x
  simp [← and_assoc, exists_eq_right]

theorem ncard_inter_le_ncard_left (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    (s ∩ t).ncard ≤ s.ncard :=
  ncard_le_ncard inter_subset_left hs

theorem ncard_inter_le_ncard_right (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    (s ∩ t).ncard ≤ t.ncard :=
  ncard_le_ncard inter_subset_right ht

theorem eq_of_subset_of_ncard_le (h : s ⊆ t) (h' : t.ncard ≤ s.ncard)
    (ht : t.Finite := by toFinite_tac) : s = t :=
  ht.eq_of_subset_of_encard_le' h
    (by rwa [← Nat.cast_le (α := ℕ∞), ht.cast_ncard_eq, (ht.subset h).cast_ncard_eq] at h')

theorem subset_iff_eq_of_ncard_le (h : t.ncard ≤ s.ncard) (ht : t.Finite := by toFinite_tac) :
    s ⊆ t ↔ s = t :=
  ⟨fun hst ↦ eq_of_subset_of_ncard_le hst h ht, Eq.subset'⟩

theorem map_eq_of_subset {f : α ↪ α} (h : f '' s ⊆ s) (hs : s.Finite := by toFinite_tac) :
    f '' s = s :=
  eq_of_subset_of_ncard_le h (ncard_map _).ge hs

theorem sep_of_ncard_eq {a : α} {P : α → Prop} (h : { x ∈ s | P x }.ncard = s.ncard) (ha : a ∈ s)
    (hs : s.Finite := by toFinite_tac) : P a :=
  sep_eq_self_iff_mem_true.mp (eq_of_subset_of_ncard_le (by simp) h.symm.le hs) _ ha

theorem ncard_lt_ncard (h : s ⊂ t) (ht : t.Finite := by toFinite_tac) :
    s.ncard < t.ncard := by
  rw [← Nat.cast_lt (α := ℕ∞), ht.cast_ncard_eq, (ht.subset h.subset).cast_ncard_eq]
  exact (ht.subset h.subset).encard_lt_encard h

theorem ncard_lt_card [Finite α] (h : s ≠ univ) : s.ncard < Nat.card α :=
  ncard_univ α ▸ ncard_lt_ncard (ssubset_univ_iff.mpr h)

theorem ncard_strictMono [Finite α] : @StrictMono (Set α) _ _ _ ncard :=
  fun _ _ h ↦ ncard_lt_ncard h

theorem ncard_eq_of_bijective {n : ℕ} (f : ∀ i, i < n → α)
    (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a) (hf' : ∀ (i) (h : i < n), f i h ∈ s)
    (f_inj : ∀ (i j) (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) : s.ncard = n := by
  let f' : Fin n → α := fun i ↦ f i.val i.is_lt
  suffices himage : s = f' '' Set.univ by
    rw [← Fintype.card_fin n, ← Nat.card_eq_fintype_card, ← Set.ncard_univ, himage]
    exact ncard_image_of_injOn <| fun i _hi j _hj h ↦ Fin.ext <| f_inj i.val j.val i.is_lt j.is_lt h
  ext x
  simp only [image_univ, mem_range]
  refine ⟨fun hx ↦ ?_, fun ⟨⟨i, hi⟩, hx⟩ ↦ hx ▸ hf' i hi⟩
  obtain ⟨i, hi, rfl⟩ := hf x hx
  use ⟨i, hi⟩

theorem ncard_congr {t : Set β} (f : ∀ a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
    (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) :
    s.ncard = t.ncard := by
  set f' : s → t := fun x ↦ ⟨f x.1 x.2, h₁ _ _⟩
  have hbij : f'.Bijective := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [f', Subtype.mk.injEq] at hxy ⊢
      exact h₂ _ _ hx hy hxy
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := h₃ y hy
    simp only [Subtype.exists]
    exact ⟨_, ha, rfl⟩
  simp_rw [← _root_.Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.ofBijective f' hbij)

theorem ncard_le_ncard_of_injOn {t : Set β} (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (f_inj : InjOn f s)
    (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ t.ncard := by
  have hle := encard_le_encard_of_injOn hf f_inj
  to_encard_tac; rwa [ht.cast_ncard_eq, (ht.finite_of_encard_le hle).cast_ncard_eq]

theorem ncard_range_of_injective (hf : Function.Injective f) :
    (range f).ncard = Nat.card α := by
  rw [← image_univ, ncard_image_of_injective univ hf, ncard_univ]

/-- A version of the pigeonhole principle for `Set`s rather than `Finset`s.

See also `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` and
`Set.exists_ne_map_eq_of_encard_lt_of_maps_to`. -/
theorem exists_ne_map_eq_of_ncard_lt_of_maps_to {t : Set β} (hc : t.ncard < s.ncard) {f : α → β}
    (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Finite := by toFinite_tac) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  by_contra h'
  simp only [Ne, not_exists, not_and, not_imp_not] at h'
  exact (ncard_le_ncard_of_injOn f hf h' ht).not_gt hc

theorem le_ncard_of_inj_on_range {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) (hs : s.Finite := by toFinite_tac) :
    n ≤ s.ncard := by
  rw [ncard_eq_toFinset_card _ hs]
  apply Finset.le_card_of_inj_on_range <;> simpa

theorem surj_on_of_inj_on_of_ncard_le {t : Set β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : t.ncard ≤ s.ncard)
    (ht : t.Finite := by toFinite_tac) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  intro b hb
  set f' : s → t := fun x ↦ ⟨f x.1 x.2, hf _ _⟩
  have finj : f'.Injective := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [f', Subtype.mk.injEq] at hxy ⊢
    apply hinj _ _ hx hy hxy
  have hft := ht.fintype
  have hft' := Fintype.ofInjective f' finj
  set f'' : ∀ a, a ∈ s.toFinset → β := fun a h ↦ f a (by simpa using h)
  convert @Finset.surj_on_of_inj_on_of_card_le _ _ _ t.toFinset f'' _ _ _ _ (by simpa) using 1
  · simp [f'']
  · simp [f'', hf]
  · intro a₁ a₂ ha₁ ha₂ h
    rw [mem_toFinset] at ha₁ ha₂
    exact hinj _ _ ha₁ ha₂ h
  rwa [← ncard_eq_toFinset_card', ← ncard_eq_toFinset_card']

theorem inj_on_of_surj_on_of_ncard_le {t : Set β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀ b ∈ t, ∃ a ha, f a ha = b) (hst : s.ncard ≤ t.ncard) ⦃a₁⦄ (ha₁ : a₁ ∈ s) ⦃a₂⦄
    (ha₂ : a₂ ∈ s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) (hs : s.Finite := by toFinite_tac) :
    a₁ = a₂ := by
  classical
  set f' : s → t := fun x ↦ ⟨f x.1 x.2, hf _ _⟩
  have hsurj : f'.Surjective := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := hsurj y hy
    simp only [Subtype.exists]
    exact ⟨_, ha, rfl⟩
  haveI := hs.fintype
  haveI := Fintype.ofSurjective _ hsurj
  set f'' : ∀ a, a ∈ s.toFinset → β := fun a h ↦ f a (by simpa using h)
  exact
    @Finset.inj_on_of_surj_on_of_card_le _ _ _ t.toFinset f''
      (fun a ha ↦ by { rw [mem_toFinset] at ha ⊢; exact hf a ha }) (by simpa)
      (by { rwa [← ncard_eq_toFinset_card', ← ncard_eq_toFinset_card'] }) a₁
      (by simpa) a₂ (by simpa) (by simpa)

theorem ncard_coe {α : Type*} (s : Set α) :
    Set.ncard (Set.univ : Set (Set.Elem s)) = s.ncard := by simp

@[simp] lemma ncard_graphOn (s : Set α) (f : α → β) : (s.graphOn f).ncard = s.ncard := by
  rw [← ncard_image_of_injOn fst_injOn_graph, image_fst_graphOn]

section Lattice

theorem ncard_union_add_ncard_inter (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∪ t).ncard + (s ∩ t).ncard = s.ncard + t.ncard := by
  to_encard_tac; rw [hs.cast_ncard_eq, ht.cast_ncard_eq, (hs.union ht).cast_ncard_eq,
    (hs.subset inter_subset_left).cast_ncard_eq, encard_union_add_encard_inter]

theorem ncard_inter_add_ncard_union (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∩ t).ncard + (s ∪ t).ncard = s.ncard + t.ncard := by
  rw [add_comm, ncard_union_add_ncard_inter _ _ hs ht]

theorem ncard_union_le (s t : Set α) : (s ∪ t).ncard ≤ s.ncard + t.ncard := by
  obtain (h | h) := (s ∪ t).finite_or_infinite
  · to_encard_tac
    rw [h.cast_ncard_eq, (h.subset subset_union_left).cast_ncard_eq,
      (h.subset subset_union_right).cast_ncard_eq]
    apply encard_union_le
  rw [h.ncard]
  apply zero_le

theorem ncard_union_eq (h : Disjoint s t) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∪ t).ncard = s.ncard + t.ncard := by
  to_encard_tac
  rw [hs.cast_ncard_eq, ht.cast_ncard_eq, (hs.union ht).cast_ncard_eq, encard_union_eq h]

theorem ncard_union_eq_iff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : (s ∪ t).ncard = s.ncard + t.ncard ↔ Disjoint s t := by
  rw [← ncard_union_add_ncard_inter s t hs ht, left_eq_add,
    ncard_eq_zero (hs.inter_of_left t), disjoint_iff_inter_eq_empty]

theorem ncard_union_lt (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) (h : ¬ Disjoint s t) :
    (s ∪ t).ncard < s.ncard + t.ncard :=
  (ncard_union_le s t).lt_of_ne (mt (ncard_union_eq_iff hs ht).mp h)

theorem ncard_diff_add_ncard_of_subset (h : s ⊆ t) (ht : t.Finite := by toFinite_tac) :
    (t \ s).ncard + s.ncard = t.ncard := by
  to_encard_tac
  rw [ht.cast_ncard_eq, (ht.subset h).cast_ncard_eq, ht.diff.cast_ncard_eq,
    encard_diff_add_encard_of_subset h]

theorem ncard_diff (hst : s ⊆ t) (hs : s.Finite := by toFinite_tac) :
    (t \ s).ncard = t.ncard - s.ncard := by
  obtain ht | ht := t.finite_or_infinite
  · rw [← ncard_diff_add_ncard_of_subset hst ht, add_tsub_cancel_right]
  · rw [ht.ncard, Nat.zero_sub, (ht.diff hs).ncard]

lemma cast_ncard_sdiff {R : Type*} [AddGroupWithOne R] (hst : s ⊆ t) (ht : t.Finite) :
    ((t \ s).ncard : R) = t.ncard - s.ncard := by
  rw [ncard_diff hst (ht.subset hst), Nat.cast_sub (ncard_le_ncard hst ht)]

theorem ncard_le_ncard_diff_add_ncard (s t : Set α) (ht : t.Finite := by toFinite_tac) :
    s.ncard ≤ (s \ t).ncard + t.ncard := by
  rcases s.finite_or_infinite with hs | hs
  · to_encard_tac
    rw [ht.cast_ncard_eq, hs.cast_ncard_eq, hs.diff.cast_ncard_eq]
    apply encard_le_encard_diff_add_encard
  convert Nat.zero_le _
  rw [hs.ncard]

theorem le_ncard_diff (s t : Set α) (hs : s.Finite := by toFinite_tac) :
    t.ncard - s.ncard ≤ (t \ s).ncard :=
  tsub_le_iff_left.mpr (by rw [add_comm]; apply ncard_le_ncard_diff_add_ncard _ _ hs)

theorem ncard_diff_add_ncard (s t : Set α) (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) :
    (s \ t).ncard + t.ncard = (s ∪ t).ncard := by
  rw [← ncard_union_eq disjoint_sdiff_left hs.diff ht, diff_union_self]

theorem diff_nonempty_of_ncard_lt_ncard (h : s.ncard < t.ncard) (hs : s.Finite := by toFinite_tac) :
    (t \ s).Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Ne, diff_eq_empty]
  exact fun h' ↦ h.not_ge (ncard_le_ncard h' hs)

theorem exists_mem_notMem_of_ncard_lt_ncard (h : s.ncard < t.ncard)
    (hs : s.Finite := by toFinite_tac) : ∃ e, e ∈ t ∧ e ∉ s :=
  diff_nonempty_of_ncard_lt_ncard h hs

@[deprecated (since := "2025-05-23")]
alias exists_mem_not_mem_of_ncard_lt_ncard := exists_mem_notMem_of_ncard_lt_ncard

@[simp] theorem ncard_inter_add_ncard_diff_eq_ncard (s t : Set α)
    (hs : s.Finite := by toFinite_tac) : (s ∩ t).ncard + (s \ t).ncard = s.ncard := by
  rw [← ncard_union_eq (disjoint_of_subset_left inter_subset_right disjoint_sdiff_right)
    (hs.inter_of_left _) hs.diff, union_comm, diff_union_inter]

theorem ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard = t.ncard ↔ (s \ t).ncard = (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_right_inj]

theorem ncard_le_ncard_iff_ncard_diff_le_ncard_diff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard ≤ t.ncard ↔ (s \ t).ncard ≤ (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_le_add_iff_left]

theorem ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff (hs : s.Finite := by toFinite_tac)
    (ht : t.Finite := by toFinite_tac) : s.ncard < t.ncard ↔ (s \ t).ncard < (t \ s).ncard := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard s t hs, ← ncard_inter_add_ncard_diff_eq_ncard t s ht,
    inter_comm, add_lt_add_iff_left]

theorem ncard_add_ncard_compl (s : Set α) (hs : s.Finite := by toFinite_tac)
    (hsc : sᶜ.Finite := by toFinite_tac) : s.ncard + sᶜ.ncard = Nat.card α := by
  rw [← ncard_univ, ← ncard_union_eq (@disjoint_compl_right _ _ s) hs hsc, union_compl_self]

theorem eq_univ_iff_ncard [Finite α] (s : Set α) :
    s = univ ↔ ncard s = Nat.card α := by
  rw [← compl_empty_iff, ← ncard_eq_zero, ← ncard_add_ncard_compl s, left_eq_add]

lemma even_ncard_compl_iff [Finite α] (heven : Even (Nat.card α)) (s : Set α) :
    Even sᶜ.ncard ↔ Even s.ncard := by
  rwa [iff_comm, ← Nat.even_add, ncard_add_ncard_compl]

lemma odd_ncard_compl_iff [Finite α] (heven : Even (Nat.card α)) (s : Set α) :
    Odd sᶜ.ncard ↔ Odd s.ncard := by
  rw [← Nat.not_even_iff_odd, even_ncard_compl_iff heven, Nat.not_even_iff_odd]

theorem nonempty_inter_of_lt_ncard_add_ncard [Finite α]
    (h : Nat.card α < s.ncard + t.ncard) : (s ∩ t).Nonempty := by
  rw [← ncard_union_add_ncard_inter s t] at h
  replace h := (s ∪ t).ncard_le_card.trans_lt h
  rwa [lt_add_iff_pos_right, ncard_pos] at h

theorem nonempty_inter_of_le_ncard_add_ncard [Finite α]
    (h' : Nat.card α ≤ s.ncard + t.ncard) (h : s ∪ t ≠ univ) :
    (s ∩ t).Nonempty := by
  rw [← ncard_union_add_ncard_inter s t] at h'
  replace h := (ncard_lt_card h).trans_le h'
  rwa [lt_add_iff_pos_right, ncard_pos] at h

theorem union_ne_univ_of_ncard_add_ncard_lt
    (h : s.ncard + t.ncard < Nat.card α) : s ∪ t ≠ univ := by
  contrapose! h
  rw [← ncard_univ, ← h]
  exact ncard_union_le s t

theorem nonempty_inter_compl_of_ncard_add_ncard_lt
    (h : s.ncard + t.ncard < Nat.card α) : (sᶜ ∩ tᶜ).Nonempty := by
  rw [← compl_union, nonempty_compl]
  exact union_ne_univ_of_ncard_add_ncard_lt h

end Lattice

/-- Given a subset `s` of a set `t`, of sizes at most and at least `n` respectively, there exists a
set `u` of size `n` which is both a superset of `s` and a subset of `t`. -/
lemma exists_subsuperset_card_eq {n : ℕ} (hst : s ⊆ t) (hsn : s.ncard ≤ n) (hnt : n ≤ t.ncard) :
    ∃ u, s ⊆ u ∧ u ⊆ t ∧ u.ncard = n := by
  obtain ht | ht := t.infinite_or_finite
  · rw [ht.ncard, Nat.le_zero, ← ht.ncard] at hnt
    exact ⟨t, hst, Subset.rfl, hnt.symm⟩
  lift s to Finset α using ht.subset hst
  lift t to Finset α using ht
  obtain ⟨u, hsu, hut, hu⟩ := Finset.exists_subsuperset_card_eq (mod_cast hst) (by simpa using hsn)
    (mod_cast hnt)
  exact ⟨u, mod_cast hsu, mod_cast hut, mod_cast hu⟩

/-- We can shrink a set to any smaller size. -/
lemma exists_subset_card_eq {n : ℕ} (hns : n ≤ s.ncard) : ∃ t ⊆ s, t.ncard = n := by
  simpa using exists_subsuperset_card_eq s.empty_subset (by simp) hns

theorem Infinite.exists_subset_ncard_eq {s : Set α} (hs : s.Infinite) (k : ℕ) :
    ∃ t, t ⊆ s ∧ t.Finite ∧ t.ncard = k := by
  have := hs.to_subtype
  obtain ⟨t', -, rfl⟩ := @Infinite.exists_subset_card_eq s univ infinite_univ k
  refine ⟨Subtype.val '' (t' : Set s), by simp, Finite.image _ (by simp), ?_⟩
  rw [ncard_image_of_injective _ Subtype.coe_injective]
  simp

theorem Infinite.exists_superset_ncard_eq {s t : Set α} (ht : t.Infinite) (hst : s ⊆ t)
    (hs : s.Finite) {k : ℕ} (hsk : s.ncard ≤ k) : ∃ s', s ⊆ s' ∧ s' ⊆ t ∧ s'.ncard = k := by
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.diff hs).exists_subset_ncard_eq (k - s.ncard)
  refine ⟨s ∪ s₁, subset_union_left, union_subset hst (hs₁.trans diff_subset), ?_⟩
  rwa [ncard_union_eq (disjoint_of_subset_right hs₁ disjoint_sdiff_right) hs hs₁fin, hs₁card,
    add_tsub_cancel_of_le]

theorem exists_subset_or_subset_of_two_mul_lt_ncard {n : ℕ} (hst : 2 * n < (s ∪ t).ncard) :
    ∃ r : Set α, n < r.ncard ∧ (r ⊆ s ∨ r ⊆ t) := by
  classical
  have hu := finite_of_ncard_ne_zero ((Nat.zero_le _).trans_lt hst).ne.symm
  rw [ncard_eq_toFinset_card _ hu,
    Finite.toFinset_union (hu.subset subset_union_left)
      (hu.subset subset_union_right)] at hst
  obtain ⟨r', hnr', hr'⟩ := Finset.exists_subset_or_subset_of_two_mul_lt_card hst
  exact ⟨r', by simpa, by simpa using hr'⟩

lemma _root_.Finset.exists_not_mem_of_card_lt_enatCard {s : Finset α} (hs : s.card < ENat.card α) :
    ∃ a, a ∉ s := by
  contrapose! hs; simp [← Set.encard_coe_eq_coe_finsetCard, Set.eq_univ_of_forall (s := s.toSet) hs]

/-! ### Explicit description of a set from its cardinality -/

@[simp] theorem ncard_eq_one : s.ncard = 1 ↔ ∃ a, s = {a} := by
  refine ⟨fun h ↦ ?_, by rintro ⟨a, rfl⟩; rw [ncard_singleton]⟩
  have hft := (finite_of_ncard_ne_zero (ne_zero_of_eq_one h)).fintype
  simp_rw [ncard_eq_toFinset_card', @Finset.card_eq_one _ (toFinset s)] at h
  refine h.imp fun a ha ↦ ?_
  simp_rw [Set.ext_iff, mem_singleton_iff]
  simp only [Finset.ext_iff, mem_toFinset, Finset.mem_singleton] at ha
  exact ha

theorem exists_eq_insert_iff_ncard (hs : s.Finite := by toFinite_tac) :
    (∃ a ∉ s, insert a s = t) ↔ s ⊆ t ∧ s.ncard + 1 = t.ncard := by
  classical
  rcases t.finite_or_infinite with ht | ht
  · rw [ncard_eq_toFinset_card _ hs, ncard_eq_toFinset_card _ ht,
      ← @Finite.toFinset_subset_toFinset _ _ _ hs ht, ← Finset.exists_eq_insert_iff]
    convert Iff.rfl using 2; simp only [Finite.mem_toFinset]
    ext x
    simp [Finset.ext_iff, Set.ext_iff]
  simp only [ht.ncard, add_eq_zero, and_false, iff_false, not_exists, not_and,
    reduceCtorEq]
  rintro x - rfl
  exact ht (hs.insert x)

theorem ncard_le_one (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one, Finite.mem_toFinset]

@[simp] theorem ncard_le_one_iff_subsingleton [Finite s] :
    s.ncard ≤ 1 ↔ s.Subsingleton :=
  ncard_le_one <| inferInstanceAs (Finite s)

theorem ncard_le_one_iff (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by
  rw [ncard_le_one hs]
  tauto

theorem ncard_le_one_iff_eq (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ s = ∅ ∨ ∃ a, s = {a} := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact iff_of_true (by simp) (Or.inl rfl)
  rw [ncard_le_one_iff hs]
  refine ⟨fun h ↦ Or.inr ⟨x, (singleton_subset_iff.mpr hx).antisymm' fun y hy ↦ h hy hx⟩, ?_⟩
  grind

theorem ncard_le_one_iff_subset_singleton [Nonempty α]
    (hs : s.Finite := by toFinite_tac) :
    s.ncard ≤ 1 ↔ ∃ x : α, s ⊆ {x} := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.card_le_one_iff_subset_singleton,
    Finite.toFinset_subset, Finset.coe_singleton]

/-- A `Set` of a subsingleton type has cardinality at most one. -/
theorem ncard_le_one_of_subsingleton [Subsingleton α] (s : Set α) : s.ncard ≤ 1 := by
  rw [ncard_eq_toFinset_card]
  exact Finset.card_le_one_of_subsingleton _

theorem one_lt_ncard (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.one_lt_card, Finite.mem_toFinset]

theorem one_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    1 < s.ncard ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  rw [one_lt_ncard hs]
  simp only [exists_and_left]

lemma one_lt_ncard_of_nonempty_of_even (hs : Set.Finite s) (hn : Set.Nonempty s := by toFinite_tac)
    (he : Even (s.ncard)) : 1 < s.ncard := by
  rw [← Set.ncard_pos hs] at hn
  have : s.ncard ≠ 1 := fun h ↦ by simp [h] at he
  cutsat

theorem two_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.two_lt_card_iff, Finite.mem_toFinset]

theorem two_lt_ncard (hs : s.Finite := by toFinite_tac) :
    2 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp only [two_lt_ncard_iff hs, exists_and_left]

theorem three_lt_ncard_iff (hs : s.Finite := by toFinite_tac) :
    3 < s.ncard ↔
    ∃ a b c d, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp_rw [ncard_eq_toFinset_card _ hs, Finset.three_lt_card_iff, Finite.mem_toFinset]

theorem three_lt_ncard (hs : s.Finite := by toFinite_tac) :
    3 < s.ncard ↔
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp only [three_lt_ncard_iff hs, exists_and_left]

theorem exists_ne_of_one_lt_ncard (hs : 1 < s.ncard) (a : α) : ∃ b, b ∈ s ∧ b ≠ a := by
  have hsf := finite_of_ncard_ne_zero (zero_lt_one.trans hs).ne.symm
  rw [ncard_eq_toFinset_card _ hsf] at hs
  simpa only [Finite.mem_toFinset] using Finset.exists_mem_ne hs a

theorem eq_insert_of_ncard_eq_succ {n : ℕ} (h : s.ncard = n + 1) :
    ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  classical
  have hsf := finite_of_ncard_pos (n.zero_lt_succ.trans_eq h.symm)
  rw [ncard_eq_toFinset_card _ hsf, Finset.card_eq_succ] at h
  obtain ⟨a, t, hat, hts, rfl⟩ := h
  simp only [Finset.ext_iff, Finset.mem_insert, Finite.mem_toFinset] at hts
  refine ⟨a, t, hat, ?_, ?_⟩
  · simp [Set.ext_iff, hts]
  · simp

theorem ncard_eq_succ {n : ℕ} (hs : s.Finite := by toFinite_tac) :
    s.ncard = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ t.ncard = n := by
  refine ⟨eq_insert_of_ncard_eq_succ, ?_⟩
  rintro ⟨a, t, hat, h, rfl⟩
  rw [← h, ncard_insert_of_notMem hat (hs.subset ((subset_insert a t).trans_eq h))]

theorem ncard_eq_two : s.ncard = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  rw [← encard_eq_two, ncard_def]
  simp

theorem ncard_eq_three : s.ncard = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  rw [← encard_eq_three, ncard_def]
  simp

theorem ncard_eq_four : s.ncard = 4 ↔
    ∃ x y z w, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧ s = {x, y, z, w} := by
  rw [← encard_eq_four, ncard_def]
  simp

end ncard
end Set
