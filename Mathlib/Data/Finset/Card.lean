/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.Data.Finset.Image

#align_import data.finset.card from "leanprover-community/mathlib"@"65a1391a0106c9204fe45bc73a039f056558cb83"

/-!
# Cardinality of a finite set

This defines the cardinality of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.card`: `s.card : ℕ` returns the cardinality of `s : Finset α`.

### Induction principles

* `Finset.strongInduction`: Strong induction
* `Finset.strongInductionOn`
* `Finset.strongDownwardInduction`
* `Finset.strongDownwardInductionOn`
* `Finset.case_strong_induction_on`
* `Finset.Nonempty.strong_induction`
-/

assert_not_exists MonoidWithZero
-- TODO: After a lot more work,
-- assert_not_exists OrderedCommMonoid

open Function Multiset Nat

variable {α β R : Type*}

namespace Finset

variable {s t : Finset α} {a b : α}

/-- `s.card` is the number of elements of `s`, aka its cardinality. -/
def card (s : Finset α) : ℕ :=
  Multiset.card s.1
#align finset.card Finset.card

theorem card_def (s : Finset α) : s.card = Multiset.card s.1 :=
  rfl
#align finset.card_def Finset.card_def

@[simp] lemma card_val (s : Finset α) : Multiset.card s.1 = s.card := rfl
#align finset.card_val Finset.card_val

@[simp]
theorem card_mk {m nodup} : (⟨m, nodup⟩ : Finset α).card = Multiset.card m :=
  rfl
#align finset.card_mk Finset.card_mk

@[simp]
theorem card_empty : card (∅ : Finset α) = 0 :=
  rfl
#align finset.card_empty Finset.card_empty

@[gcongr]
theorem card_le_card : s ⊆ t → s.card ≤ t.card :=
  Multiset.card_le_card ∘ val_le_iff.mpr
#align finset.card_le_of_subset Finset.card_le_card

@[mono]
theorem card_mono : Monotone (@card α) := by apply card_le_card
#align finset.card_mono Finset.card_mono

@[simp] lemma card_eq_zero : s.card = 0 ↔ s = ∅ := card_eq_zero.trans val_eq_zero
lemma card_ne_zero : s.card ≠ 0 ↔ s.Nonempty := card_eq_zero.ne.trans nonempty_iff_ne_empty.symm
lemma card_pos : 0 < s.card ↔ s.Nonempty := Nat.pos_iff_ne_zero.trans card_ne_zero
#align finset.card_eq_zero Finset.card_eq_zero
#align finset.card_pos Finset.card_pos

alias ⟨_, Nonempty.card_pos⟩ := card_pos
alias ⟨_, Nonempty.card_ne_zero⟩ := card_ne_zero
#align finset.nonempty.card_pos Finset.Nonempty.card_pos

theorem card_ne_zero_of_mem (h : a ∈ s) : s.card ≠ 0 :=
  (not_congr card_eq_zero).2 <| ne_empty_of_mem h
#align finset.card_ne_zero_of_mem Finset.card_ne_zero_of_mem

@[simp]
theorem card_singleton (a : α) : card ({a} : Finset α) = 1 :=
  Multiset.card_singleton _
#align finset.card_singleton Finset.card_singleton

theorem card_singleton_inter [DecidableEq α] : ({a} ∩ s).card ≤ 1 := by
  cases' Finset.decidableMem a s with h h
  · simp [Finset.singleton_inter_of_not_mem h]
  · simp [Finset.singleton_inter_of_mem h]
#align finset.card_singleton_inter Finset.card_singleton_inter

@[simp]
theorem card_cons (h : a ∉ s) : (s.cons a h).card = s.card + 1 :=
  Multiset.card_cons _ _
#align finset.card_cons Finset.card_cons

section InsertErase

variable [DecidableEq α]

@[simp]
theorem card_insert_of_not_mem (h : a ∉ s) : (insert a s).card = s.card + 1 := by
  rw [← cons_eq_insert _ _ h, card_cons]
#align finset.card_insert_of_not_mem Finset.card_insert_of_not_mem

theorem card_insert_of_mem (h : a ∈ s) : card (insert a s) = s.card := by rw [insert_eq_of_mem h]
#align finset.card_insert_of_mem Finset.card_insert_of_mem

theorem card_insert_le (a : α) (s : Finset α) : card (insert a s) ≤ s.card + 1 := by
  by_cases h : a ∈ s
  · rw [insert_eq_of_mem h]
    exact Nat.le_succ _
  · rw [card_insert_of_not_mem h]
#align finset.card_insert_le Finset.card_insert_le

section

variable {a b c d e f : α}

theorem card_le_two : card {a, b} ≤ 2 := card_insert_le _ _

theorem card_le_three : card {a, b, c} ≤ 3 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_two)

theorem card_le_four : card {a, b, c, d} ≤ 4 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_three)

theorem card_le_five : card {a, b, c, d, e} ≤ 5 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_four)

theorem card_le_six : card {a, b, c, d, e, f} ≤ 6 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_five)

end

/-- If `a ∈ s` is known, see also `Finset.card_insert_of_mem` and `Finset.card_insert_of_not_mem`.
-/
theorem card_insert_eq_ite : card (insert a s) = if a ∈ s then s.card else s.card + 1 := by
  by_cases h : a ∈ s
  · rw [card_insert_of_mem h, if_pos h]
  · rw [card_insert_of_not_mem h, if_neg h]
#align finset.card_insert_eq_ite Finset.card_insert_eq_ite

@[simp]
theorem card_pair_eq_one_or_two : ({a,b} : Finset α).card = 1 ∨ ({a,b} : Finset α).card = 2 := by
  simp [card_insert_eq_ite]
  tauto

@[simp]
theorem card_pair (h : a ≠ b) : ({a, b} : Finset α).card = 2 := by
  rw [card_insert_of_not_mem (not_mem_singleton.2 h), card_singleton]
#align finset.card_doubleton Finset.card_pair

@[deprecated (since := "2024-01-04")] alias card_doubleton := Finset.card_pair

/-- $\#(s \setminus \{a\}) = \#s - 1$ if $a \in s$. -/
@[simp]
theorem card_erase_of_mem : a ∈ s → (s.erase a).card = s.card - 1 :=
  Multiset.card_erase_of_mem
#align finset.card_erase_of_mem Finset.card_erase_of_mem

/-- $\#(s \setminus \{a\}) = \#s - 1$ if $a \in s$.
  This result is casted to any additive group with 1,
  so that we don't have to work with `ℕ`-subtraction. -/
@[simp]
theorem cast_card_erase_of_mem {R} [AddGroupWithOne R] {s : Finset α} (hs : a ∈ s) :
    ((s.erase a).card : R) = s.card - 1 := by
  rw [card_erase_of_mem hs, Nat.cast_sub, Nat.cast_one]
  rw [Nat.add_one_le_iff, Finset.card_pos]
  exact ⟨a, hs⟩

@[simp]
theorem card_erase_add_one : a ∈ s → (s.erase a).card + 1 = s.card :=
  Multiset.card_erase_add_one
#align finset.card_erase_add_one Finset.card_erase_add_one

theorem card_erase_lt_of_mem : a ∈ s → (s.erase a).card < s.card :=
  Multiset.card_erase_lt_of_mem
#align finset.card_erase_lt_of_mem Finset.card_erase_lt_of_mem

theorem card_erase_le : (s.erase a).card ≤ s.card :=
  Multiset.card_erase_le
#align finset.card_erase_le Finset.card_erase_le

theorem pred_card_le_card_erase : s.card - 1 ≤ (s.erase a).card := by
  by_cases h : a ∈ s
  · exact (card_erase_of_mem h).ge
  · rw [erase_eq_of_not_mem h]
    exact Nat.sub_le _ _
#align finset.pred_card_le_card_erase Finset.pred_card_le_card_erase

/-- If `a ∈ s` is known, see also `Finset.card_erase_of_mem` and `Finset.erase_eq_of_not_mem`. -/
theorem card_erase_eq_ite : (s.erase a).card = if a ∈ s then s.card - 1 else s.card :=
  Multiset.card_erase_eq_ite
#align finset.card_erase_eq_ite Finset.card_erase_eq_ite

end InsertErase

@[simp]
theorem card_range (n : ℕ) : (range n).card = n :=
  Multiset.card_range n
#align finset.card_range Finset.card_range

@[simp]
theorem card_attach : s.attach.card = s.card :=
  Multiset.card_attach
#align finset.card_attach Finset.card_attach

end Finset

section ToMLListultiset

variable [DecidableEq α] (m : Multiset α) (l : List α)

theorem Multiset.card_toFinset : m.toFinset.card = Multiset.card m.dedup :=
  rfl
#align multiset.card_to_finset Multiset.card_toFinset

theorem Multiset.toFinset_card_le : m.toFinset.card ≤ Multiset.card m :=
  card_le_card <| dedup_le _
#align multiset.to_finset_card_le Multiset.toFinset_card_le

theorem Multiset.toFinset_card_of_nodup {m : Multiset α} (h : m.Nodup) :
    m.toFinset.card = Multiset.card m :=
  congr_arg card <| Multiset.dedup_eq_self.mpr h
#align multiset.to_finset_card_of_nodup Multiset.toFinset_card_of_nodup

theorem Multiset.dedup_card_eq_card_iff_nodup {m : Multiset α} :
    card m.dedup = card m ↔ m.Nodup :=
  .trans ⟨fun h ↦ eq_of_le_of_card_le (dedup_le m) h.ge, congr_arg _⟩ dedup_eq_self

theorem Multiset.toFinset_card_eq_card_iff_nodup {m : Multiset α} :
    m.toFinset.card = card m ↔ m.Nodup := dedup_card_eq_card_iff_nodup

theorem List.card_toFinset : l.toFinset.card = l.dedup.length :=
  rfl
#align list.card_to_finset List.card_toFinset

theorem List.toFinset_card_le : l.toFinset.card ≤ l.length :=
  Multiset.toFinset_card_le ⟦l⟧
#align list.to_finset_card_le List.toFinset_card_le

theorem List.toFinset_card_of_nodup {l : List α} (h : l.Nodup) : l.toFinset.card = l.length :=
  Multiset.toFinset_card_of_nodup h
#align list.to_finset_card_of_nodup List.toFinset_card_of_nodup

end ToMLListultiset

namespace Finset

variable {s t u : Finset α} {f : α → β} {n : ℕ}

@[simp]
theorem length_toList (s : Finset α) : s.toList.length = s.card := by
  rw [toList, ← Multiset.coe_card, Multiset.coe_toList, card_def]
#align finset.length_to_list Finset.length_toList

theorem card_image_le [DecidableEq β] : (s.image f).card ≤ s.card := by
  simpa only [card_map] using (s.1.map f).toFinset_card_le
#align finset.card_image_le Finset.card_image_le

theorem card_image_of_injOn [DecidableEq β] (H : Set.InjOn f s) : (s.image f).card = s.card := by
  simp only [card, image_val_of_injOn H, card_map]
#align finset.card_image_of_inj_on Finset.card_image_of_injOn

theorem injOn_of_card_image_eq [DecidableEq β] (H : (s.image f).card = s.card) : Set.InjOn f s := by
  rw [card_def, card_def, image, toFinset] at H
  dsimp only at H
  have : (s.1.map f).dedup = s.1.map f := by
    refine Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) ?_
    simp only [H, Multiset.card_map, le_rfl]
  rw [Multiset.dedup_eq_self] at this
  exact inj_on_of_nodup_map this
#align finset.inj_on_of_card_image_eq Finset.injOn_of_card_image_eq

theorem card_image_iff [DecidableEq β] : (s.image f).card = s.card ↔ Set.InjOn f s :=
  ⟨injOn_of_card_image_eq, card_image_of_injOn⟩
#align finset.card_image_iff Finset.card_image_iff

theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
    (s.image f).card = s.card :=
  card_image_of_injOn fun _ _ _ _ h => H h
#align finset.card_image_of_injective Finset.card_image_of_injective

theorem fiber_card_ne_zero_iff_mem_image (s : Finset α) (f : α → β) [DecidableEq β] (y : β) :
    (s.filter fun x => f x = y).card ≠ 0 ↔ y ∈ s.image f := by
  rw [← Nat.pos_iff_ne_zero, card_pos, fiber_nonempty_iff_mem_image]
#align finset.fiber_card_ne_zero_iff_mem_image Finset.fiber_card_ne_zero_iff_mem_image

lemma card_filter_le_iff (s : Finset α) (P : α → Prop) [DecidablePred P] (n : ℕ) :
    (s.filter P).card ≤ n ↔ ∀ s' ⊆ s, n < s'.card → ∃ a ∈ s', ¬ P a :=
  (s.1.card_filter_le_iff P n).trans ⟨fun H s' hs' h ↦ H s'.1 (by aesop) h,
    fun H s' hs' h ↦ H ⟨s', nodup_of_le hs' s.2⟩ (fun x hx ↦ subset_of_le hs' hx) h⟩

@[simp]
theorem card_map (f : α ↪ β) : (s.map f).card = s.card :=
  Multiset.card_map _ _
#align finset.card_map Finset.card_map

@[simp]
theorem card_subtype (p : α → Prop) [DecidablePred p] (s : Finset α) :
    (s.subtype p).card = (s.filter p).card := by simp [Finset.subtype]
#align finset.card_subtype Finset.card_subtype

theorem card_filter_le (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card ≤ s.card :=
  card_le_card <| filter_subset _ _
#align finset.card_filter_le Finset.card_filter_le

theorem eq_of_subset_of_card_le {s t : Finset α} (h : s ⊆ t) (h₂ : t.card ≤ s.card) : s = t :=
  eq_of_veq <| Multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂
#align finset.eq_of_subset_of_card_le Finset.eq_of_subset_of_card_le

theorem eq_of_superset_of_card_ge (hst : s ⊆ t) (hts : t.card ≤ s.card) : t = s :=
  (eq_of_subset_of_card_le hst hts).symm
#align finset.eq_of_superset_of_card_ge Finset.eq_of_superset_of_card_ge

theorem subset_iff_eq_of_card_le (h : t.card ≤ s.card) : s ⊆ t ↔ s = t :=
  ⟨fun hst => eq_of_subset_of_card_le hst h, Eq.subset'⟩
#align finset.subset_iff_eq_of_card_le Finset.subset_iff_eq_of_card_le

theorem map_eq_of_subset {f : α ↪ α} (hs : s.map f ⊆ s) : s.map f = s :=
  eq_of_subset_of_card_le hs (card_map _).ge
#align finset.map_eq_of_subset Finset.map_eq_of_subset

theorem filter_card_eq {p : α → Prop} [DecidablePred p] (h : (s.filter p).card = s.card) (x : α)
    (hx : x ∈ s) : p x := by
  rw [← eq_of_subset_of_card_le (s.filter_subset p) h.ge, mem_filter] at hx
  exact hx.2
#align finset.filter_card_eq Finset.filter_card_eq

nonrec lemma card_lt_card (h : s ⊂ t) : s.card < t.card := card_lt_card <| val_lt_iff.2 h
#align finset.card_lt_card Finset.card_lt_card

lemma card_strictMono : StrictMono (card : Finset α → ℕ) := fun _ _ ↦ card_lt_card

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

section bij
variable {t : Finset β}

/-- Reorder a finset.

The difference with `Finset.card_bij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.card_nbij` is that the bijection is allowed to use membership of the
domain, rather than being a non-dependent function. -/
lemma card_bij (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) : s.card = t.card := by
  classical
  calc
    s.card = s.attach.card := card_attach.symm
    _      = (s.attach.image fun a : { a // a ∈ s } => i a.1 a.2).card := Eq.symm ?_
    _      = t.card := ?_
  · apply card_image_of_injective
    intro ⟨_, _⟩ ⟨_, _⟩ h
    simpa using i_inj _ _ _ _ h
  · congr 1
    ext b
    constructor <;> intro h
    · obtain ⟨_, _, rfl⟩ := mem_image.1 h; apply hi
    · obtain ⟨a, ha, rfl⟩ := i_surj b h; exact mem_image.2 ⟨⟨a, ha⟩, by simp⟩
#align finset.card_bij Finset.card_bij

@[deprecated (since := "2024-05-04")] alias card_congr := card_bij

/-- Reorder a finset.

The difference with `Finset.card_bij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.card_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains, rather than being non-dependent functions. -/
lemma card_bij' (i : ∀ a ∈ s, β) (j : ∀ a ∈ t, α) (hi : ∀ a ha, i a ha ∈ t)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) : s.card = t.card := by
  refine card_bij i hi (fun a1 h1 a2 h2 eq ↦ ?_) (fun b hb ↦ ⟨_, hj b hb, right_inv b hb⟩)
  rw [← left_inv a1 h1, ← left_inv a2 h2]
  simp only [eq]

/-- Reorder a finset.

The difference with `Finset.card_nbij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.card_bij` is that the bijection is a non-dependent function, rather than
being allowed to use membership of the domain. -/
lemma card_nbij (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (i_inj : (s : Set α).InjOn i)
    (i_surj : (s : Set α).SurjOn i t) : s.card = t.card :=
  card_bij (fun a _ ↦ i a) hi i_inj (by simpa using i_surj)

/-- Reorder a finset.

The difference with `Finset.card_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.card_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains.

The difference with `Finset.card_equiv` is that bijectivity is only required to hold on the domains,
rather than on the entire types. -/
lemma card_nbij' (i : α → β) (j : β → α) (hi : ∀ a ∈ s, i a ∈ t) (hj : ∀ a ∈ t, j a ∈ s)
    (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a) : s.card = t.card :=
  card_bij' (fun a _ ↦ i a) (fun b _ ↦ j b) hi hj left_inv right_inv

/-- Specialization of `Finset.card_nbij'` that automatically fills in most arguments.

See `Fintype.card_equiv` for the version where `s` and `t` are `univ`. -/
lemma card_equiv (e : α ≃ β) (hst : ∀ i, i ∈ s ↔ e i ∈ t) : s.card = t.card := by
  refine card_nbij' e e.symm ?_ ?_ ?_ ?_ <;> simp [hst]

/-- Specialization of `Finset.card_nbij` that automatically fills in most arguments.

See `Fintype.card_bijective` for the version where `s` and `t` are `univ`. -/
lemma card_bijective (e : α → β) (he : e.Bijective) (hst : ∀ i, i ∈ s ↔ e i ∈ t) :
    s.card = t.card := card_equiv (.ofBijective e he) hst

lemma card_le_card_of_injOn (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (f_inj : (s : Set α).InjOn f) :
    s.card ≤ t.card := by
  classical
  calc
    s.card = (s.image f).card := (card_image_of_injOn f_inj).symm
    _      ≤ t.card           := card_le_card <| image_subset_iff.2 hf
@[deprecated (since := "2024-06-01")] alias card_le_card_of_inj_on := card_le_card_of_injOn

lemma card_le_card_of_surjOn (f : α → β) (hf : Set.SurjOn f s t) : t.card ≤ s.card := by
  classical unfold Set.SurjOn at hf; exact (card_le_card (mod_cast hf)).trans card_image_le

/-- If there are more pigeons than pigeonholes, then there are two pigeons in the same pigeonhole.
-/
theorem exists_ne_map_eq_of_card_lt_of_maps_to {t : Finset β} (hc : t.card < s.card) {f : α → β}
    (hf : ∀ a ∈ s, f a ∈ t) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  classical
  by_contra! hz
  refine hc.not_le (card_le_card_of_injOn f hf ?_)
  intro x hx y hy
  contrapose
  exact hz x hx y hy
#align finset.exists_ne_map_eq_of_card_lt_of_maps_to Finset.exists_ne_map_eq_of_card_lt_of_maps_to

lemma le_card_of_inj_on_range (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ s.card :=
  calc
    n = card (range n) := (card_range n).symm
    _ ≤ s.card := card_le_card_of_injOn f (by simpa only [mem_range]) (by simpa)
#align finset.le_card_of_inj_on_range Finset.le_card_of_inj_on_range

lemma surj_on_of_inj_on_of_card_le (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : t.card ≤ s.card) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  classical
  have h : (s.attach.image fun a : { a // a ∈ s } => f a a.prop).card = s.card := by
    rw [← @card_attach _ s, card_image_of_injective]
    intro ⟨_, _⟩ ⟨_, _⟩ h
    exact Subtype.eq <| hinj _ _ _ _ h
  obtain rfl : image (fun a : { a // a ∈ s } => f a a.prop) s.attach = t :=
    eq_of_subset_of_card_le (image_subset_iff.2 $ by simpa) (by simp [hst, h])
  simp only [mem_image, mem_attach, true_and, Subtype.exists, forall_exists_index]
  exact fun b a ha hb ↦ ⟨a, ha, hb.symm⟩
#align finset.surj_on_of_inj_on_of_card_le Finset.surj_on_of_inj_on_of_card_le

theorem inj_on_of_surj_on_of_card_le (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀ b ∈ t, ∃ a ha, f a ha = b) (hst : s.card ≤ t.card) ⦃a₁⦄ (ha₁ : a₁ ∈ s) ⦃a₂⦄
    (ha₂ : a₂ ∈ s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) : a₁ = a₂ :=
  haveI : Inhabited { x // x ∈ s } := ⟨⟨a₁, ha₁⟩⟩
  let f' : { x // x ∈ s } → { x // x ∈ t } := fun x => ⟨f x.1 x.2, hf x.1 x.2⟩
  let g : { x // x ∈ t } → { x // x ∈ s } :=
    @surjInv _ _ f' fun x =>
      let ⟨y, hy₁, hy₂⟩ := hsurj x.1 x.2
      ⟨⟨y, hy₁⟩, Subtype.eq hy₂⟩
  have hg : Injective g := injective_surjInv _
  have hsg : Surjective g := fun x =>
    let ⟨y, hy⟩ :=
      surj_on_of_inj_on_of_card_le (fun (x : { x // x ∈ t }) (_ : x ∈ t.attach) => g x)
        (fun x _ => show g x ∈ s.attach from mem_attach _ _) (fun x y _ _ hxy => hg hxy) (by simpa)
        x (mem_attach _ _)
    ⟨y, hy.snd.symm⟩
  have hif : Injective f' :=
    (leftInverse_of_surjective_of_rightInverse hsg (rightInverse_surjInv _)).injective
  Subtype.ext_iff_val.1 (@hif ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ (Subtype.eq ha₁a₂))
#align finset.inj_on_of_surj_on_of_card_le Finset.inj_on_of_surj_on_of_card_le

end bij

@[simp]
theorem card_disjUnion (s t : Finset α) (h) : (s.disjUnion t h).card = s.card + t.card :=
  Multiset.card_add _ _
#align finset.card_disj_union Finset.card_disjUnion

/-! ### Lattice structure -/


section Lattice

variable [DecidableEq α]

theorem card_union_add_card_inter (s t : Finset α) :
    (s ∪ t).card + (s ∩ t).card = s.card + t.card :=
  Finset.induction_on t (by simp) fun a r har h => by by_cases a ∈ s <;>
    simp [*, ← add_assoc, add_right_comm _ 1]
#align finset.card_union_add_card_inter Finset.card_union_add_card_inter

theorem card_inter_add_card_union (s t : Finset α) :
    (s ∩ t).card + (s ∪ t).card = s.card + t.card := by rw [add_comm, card_union_add_card_inter]
#align finset.card_inter_add_card_union Finset.card_inter_add_card_union

lemma card_union (s t : Finset α) : (s ∪ t).card = s.card + t.card - (s ∩ t).card := by
  rw [← card_union_add_card_inter, Nat.add_sub_cancel]

lemma card_inter (s t : Finset α) : (s ∩ t).card = s.card + t.card - (s ∪ t).card := by
  rw [← card_inter_add_card_union, Nat.add_sub_cancel]

theorem card_union_le (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card :=
  card_union_add_card_inter s t ▸ Nat.le_add_right _ _
#align finset.card_union_le Finset.card_union_le

lemma card_union_eq_card_add_card : (s ∪ t).card = s.card + t.card ↔ Disjoint s t := by
  rw [← card_union_add_card_inter]; simp [disjoint_iff_inter_eq_empty]

@[simp] alias ⟨_, card_union_of_disjoint⟩ := card_union_eq_card_add_card
#align finset.card_union_eq Finset.card_union_of_disjoint
#align finset.card_disjoint_union Finset.card_union_of_disjoint

@[deprecated (since := "2024-02-09")] alias card_union_eq := card_union_of_disjoint
@[deprecated (since := "2024-02-09")] alias card_disjoint_union := card_union_of_disjoint

lemma cast_card_inter [AddGroupWithOne R] :
    ((s ∩ t).card : R) = s.card + t.card - (s ∪ t).card := by
  rw [eq_sub_iff_add_eq, ← cast_add, card_inter_add_card_union, cast_add]

lemma cast_card_union [AddGroupWithOne R] :
    ((s ∪ t).card : R) = s.card + t.card - (s ∩ t).card := by
  rw [eq_sub_iff_add_eq, ← cast_add, card_union_add_card_inter, cast_add]

theorem card_sdiff (h : s ⊆ t) : card (t \ s) = t.card - s.card := by
  suffices card (t \ s) = card (t \ s ∪ s) - s.card by rwa [sdiff_union_of_subset h] at this
  rw [card_union_of_disjoint sdiff_disjoint, Nat.add_sub_cancel_right]
#align finset.card_sdiff Finset.card_sdiff

lemma cast_card_sdiff [AddGroupWithOne R] (h : s ⊆ t) : ((t \ s).card : R) = t.card - s.card := by
  rw [card_sdiff h, Nat.cast_sub (card_mono h)]

theorem card_sdiff_add_card_eq_card {s t : Finset α} (h : s ⊆ t) : card (t \ s) + card s = card t :=
  ((Nat.sub_eq_iff_eq_add (card_le_card h)).mp (card_sdiff h).symm).symm
#align finset.card_sdiff_add_card_eq_card Finset.card_sdiff_add_card_eq_card

theorem le_card_sdiff (s t : Finset α) : t.card - s.card ≤ card (t \ s) :=
  calc
    card t - card s ≤ card t - card (s ∩ t) :=
      Nat.sub_le_sub_left (card_le_card inter_subset_left) _
    _ = card (t \ (s ∩ t)) := (card_sdiff inter_subset_right).symm
    _ ≤ card (t \ s) := by rw [sdiff_inter_self_right t s]
#align finset.le_card_sdiff Finset.le_card_sdiff

theorem card_le_card_sdiff_add_card : s.card ≤ (s \ t).card + t.card :=
  Nat.sub_le_iff_le_add.1 <| le_card_sdiff _ _
#align finset.card_le_card_sdiff_add_card Finset.card_le_card_sdiff_add_card

theorem card_sdiff_add_card : (s \ t).card + t.card = (s ∪ t).card := by
  rw [← card_union_of_disjoint sdiff_disjoint, sdiff_union_self_eq_union]
#align finset.card_sdiff_add_card Finset.card_sdiff_add_card

lemma card_sdiff_comm (h : s.card = t.card) : (s \ t).card = (t \ s).card :=
  add_left_injective t.card <| by
    simp_rw [card_sdiff_add_card, ← h, card_sdiff_add_card, union_comm]

@[simp]
lemma card_sdiff_add_card_inter (s t : Finset α) :
    (s \ t).card + (s ∩ t).card = s.card := by
  rw [← card_union_of_disjoint (disjoint_sdiff_inter _ _), sdiff_union_inter]

@[simp]
lemma card_inter_add_card_sdiff (s t : Finset α) :
    (s ∩ t).card + (s \ t).card = s.card := by
  rw [add_comm, card_sdiff_add_card_inter]

/-- **Pigeonhole principle** for two finsets inside an ambient finset. -/
theorem inter_nonempty_of_card_lt_card_add_card (hts : t ⊆ s) (hus : u ⊆ s)
    (hstu : s.card < t.card + u.card) : (t ∩ u).Nonempty := by
  contrapose! hstu
  calc
    _ = (t ∪ u).card := by simp [← card_union_add_card_inter, not_nonempty_iff_eq_empty.1 hstu]
    _ ≤ s.card := by gcongr; exact union_subset hts hus

end Lattice

theorem filter_card_add_filter_neg_card_eq_card
    (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] :
    (s.filter p).card + (s.filter (fun a => ¬ p a)).card = s.card := by
  classical
  rw [← card_union_of_disjoint (disjoint_filter_filter_neg _ _ _), filter_union_filter_neg_eq]
#align finset.filter_card_add_filter_neg_card_eq_card Finset.filter_card_add_filter_neg_card_eq_card

/-- Given a set `A` and a set `B` inside it, we can shrink `A` to any appropriate size, and keep `B`
inside it. -/
theorem exists_intermediate_set {A B : Finset α} (i : ℕ) (h₁ : i + card B ≤ card A) (h₂ : B ⊆ A) :
    ∃ C : Finset α, B ⊆ C ∧ C ⊆ A ∧ card C = i + card B := by
  classical
    rcases Nat.le.dest h₁ with ⟨k, h⟩
    clear h₁
    induction' k with k ih generalizing A
    · exact ⟨A, h₂, Subset.refl _, h.symm⟩
    obtain ⟨a, ha⟩ : (A \ B).Nonempty := by rw [← card_pos, card_sdiff h₂]; omega
    have z : i + card B + k = card (erase A a) := by
      rw [card_erase_of_mem (mem_sdiff.1 ha).1, ← h,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr k.succ_ne_zero), ← pred_eq_sub_one,
        k.pred_succ]
    have : B ⊆ A.erase a := by
      rintro t th
      apply mem_erase_of_ne_of_mem _ (h₂ th)
      rintro rfl
      exact not_mem_sdiff_of_mem_right th ha
    rcases ih this z with ⟨B', hB', B'subA', cards⟩
    exact ⟨B', hB', B'subA'.trans (erase_subset _ _), cards⟩
#align finset.exists_intermediate_set Finset.exists_intermediate_set

/-- We can shrink `A` to any smaller size. -/
theorem exists_smaller_set (A : Finset α) (i : ℕ) (h₁ : i ≤ card A) :
    ∃ B : Finset α, B ⊆ A ∧ card B = i :=
  let ⟨B, _, x₁, x₂⟩ := exists_intermediate_set i (by simpa) (empty_subset A)
  ⟨B, x₁, x₂⟩
#align finset.exists_smaller_set Finset.exists_smaller_set

theorem le_card_iff_exists_subset_card : n ≤ s.card ↔ ∃ t ⊆ s, t.card = n := by
  refine ⟨fun h => ?_, fun ⟨t, hst, ht⟩ => ht ▸ card_le_card hst⟩
  exact exists_smaller_set s n h

theorem exists_subset_or_subset_of_two_mul_lt_card [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < (X ∪ Y).card) : ∃ C : Finset α, n < C.card ∧ (C ⊆ X ∨ C ⊆ Y) := by
  have h₁ : (X ∩ (Y \ X)).card = 0 := Finset.card_eq_zero.mpr (Finset.inter_sdiff_self X Y)
  have h₂ : (X ∪ Y).card = X.card + (Y \ X).card := by
    rw [← card_union_add_card_inter X (Y \ X), Finset.union_sdiff_self_eq_union, h₁, add_zero]
  rw [h₂, Nat.two_mul] at hXY
  obtain h | h : n < X.card ∨ n < (Y \ X).card := by contrapose! hXY; omega
  · exact ⟨X, h, Or.inl (Finset.Subset.refl X)⟩
  · exact ⟨Y \ X, h, Or.inr sdiff_subset⟩
#align finset.exists_subset_or_subset_of_two_mul_lt_card Finset.exists_subset_or_subset_of_two_mul_lt_card

/-! ### Explicit description of a finset from its card -/


theorem card_eq_one : s.card = 1 ↔ ∃ a, s = {a} := by
  cases s
  simp only [Multiset.card_eq_one, Finset.card, ← val_inj, singleton_val]
#align finset.card_eq_one Finset.card_eq_one

theorem _root_.Multiset.toFinset_card_eq_one_iff [DecidableEq α] (s : Multiset α) :
    s.toFinset.card = 1 ↔ Multiset.card s ≠ 0 ∧ ∃ a : α, s = Multiset.card s • {a} := by
  simp_rw [card_eq_one, Multiset.toFinset_eq_singleton_iff, exists_and_left]

theorem exists_eq_insert_iff [DecidableEq α] {s t : Finset α} :
    (∃ a ∉ s, insert a s = t) ↔ s ⊆ t ∧ s.card + 1 = t.card := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨subset_insert _ _, (card_insert_of_not_mem ha).symm⟩
  · rintro ⟨hst, h⟩
    obtain ⟨a, ha⟩ : ∃ a, t \ s = {a} :=
      card_eq_one.1 (by rw [card_sdiff hst, ← h, Nat.add_sub_cancel_left])
    refine
      ⟨a, fun hs => (?_ : a ∉ {a}) <| mem_singleton_self _, by
        rw [insert_eq, ← ha, sdiff_union_of_subset hst]⟩
    rw [← ha]
    exact not_mem_sdiff_of_mem_right hs
#align finset.exists_eq_insert_iff Finset.exists_eq_insert_iff

theorem card_le_one : s.card ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  refine (Nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)).le_iff_eq.trans (card_eq_one.trans ⟨?_, ?_⟩)
  · rintro ⟨y, rfl⟩
    simp
  · exact fun h => ⟨x, eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => h _ hy _ hx⟩⟩
#align finset.card_le_one Finset.card_le_one

theorem card_le_one_iff : s.card ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by
  rw [card_le_one]
  tauto
#align finset.card_le_one_iff Finset.card_le_one_iff

theorem card_le_one_iff_subsingleton_coe : s.card ≤ 1 ↔ Subsingleton (s : Type _) :=
  card_le_one.trans (s : Set α).subsingleton_coe.symm

theorem card_le_one_iff_subset_singleton [Nonempty α] : s.card ≤ 1 ↔ ∃ x : α, s ⊆ {x} := by
  refine ⟨fun H => ?_, ?_⟩
  · obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
    · exact ⟨Classical.arbitrary α, empty_subset _⟩
    · exact ⟨x, fun y hy => by rw [card_le_one.1 H y hy x hx, mem_singleton]⟩
  · rintro ⟨x, hx⟩
    rw [← card_singleton x]
    exact card_le_card hx
#align finset.card_le_one_iff_subset_singleton Finset.card_le_one_iff_subset_singleton

lemma exists_mem_ne (hs : 1 < s.card) (a : α) : ∃ b ∈ s, b ≠ a := by
  have : Nonempty α := ⟨a⟩
  by_contra!
  exact hs.not_le (card_le_one_iff_subset_singleton.2 ⟨a, subset_singleton_iff'.2 this⟩)
#align finset.exists_mem_ne Finset.exists_mem_ne

/-- A `Finset` of a subsingleton type has cardinality at most one. -/
theorem card_le_one_of_subsingleton [Subsingleton α] (s : Finset α) : s.card ≤ 1 :=
  Finset.card_le_one_iff.2 fun {_ _ _ _} => Subsingleton.elim _ _
#align finset.card_le_one_of_subsingleton Finset.card_le_one_of_subsingleton

theorem one_lt_card : 1 < s.card ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  rw [← not_iff_not]
  push_neg
  exact card_le_one
#align finset.one_lt_card Finset.one_lt_card

theorem one_lt_card_iff : 1 < s.card ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  rw [one_lt_card]
  simp only [exists_prop, exists_and_left]
#align finset.one_lt_card_iff Finset.one_lt_card_iff

theorem one_lt_card_iff_nontrivial : 1 < s.card ↔ s.Nontrivial := by
  rw [← not_iff_not, not_lt, Finset.Nontrivial, ← Set.nontrivial_coe_sort,
    not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton_coe, coe_sort_coe]

@[deprecated (since := "2024-02-05")]
alias one_lt_card_iff_nontrivial_coe := one_lt_card_iff_nontrivial

theorem exists_ne_of_one_lt_card (hs : 1 < s.card) (a : α) : ∃ b, b ∈ s ∧ b ≠ a := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hs
  by_cases ha : y = a
  · exact ⟨x, hx, ne_of_ne_of_eq hxy ha⟩
  · exact ⟨y, hy, ha⟩
#align finset.exists_ne_of_one_lt_card Finset.exists_ne_of_one_lt_card

/-- If a Finset in a Pi type is nontrivial (has at least two elements), then
  its projection to some factor is nontrivial, and the fibers of the projection
  are proper subsets. -/
lemma exists_of_one_lt_card_pi {ι : Type*} {α : ι → Type*} [∀ i, DecidableEq (α i)]
    {s : Finset (∀ i, α i)} (h : 1 < s.card) :
    ∃ i, 1 < (s.image (· i)).card ∧ ∀ ai, s.filter (· i = ai) ⊂ s := by
  simp_rw [one_lt_card_iff, Function.ne_iff] at h ⊢
  obtain ⟨a1, a2, h1, h2, i, hne⟩ := h
  refine ⟨i, ⟨_, _, mem_image_of_mem _ h1, mem_image_of_mem _ h2, hne⟩, fun ai => ?_⟩
  rw [filter_ssubset]
  obtain rfl | hne := eq_or_ne (a2 i) ai
  exacts [⟨a1, h1, hne⟩, ⟨a2, h2, hne⟩]

section DecidableEq
variable [DecidableEq α]

theorem card_eq_succ : s.card = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ t.card = n :=
  ⟨fun h =>
    let ⟨a, has⟩ := card_pos.mp (h.symm ▸ Nat.zero_lt_succ _ : 0 < s.card)
    ⟨a, s.erase a, s.not_mem_erase a, insert_erase has, by
      simp only [h, card_erase_of_mem has, Nat.add_sub_cancel_right]⟩,
    fun ⟨a, t, hat, s_eq, n_eq⟩ => s_eq ▸ n_eq ▸ card_insert_of_not_mem hat⟩
#align finset.card_eq_succ Finset.card_eq_succ

theorem card_eq_two : s.card = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  constructor
  · rw [card_eq_succ]
    simp_rw [card_eq_one]
    rintro ⟨a, _, hab, rfl, b, rfl⟩
    exact ⟨a, b, not_mem_singleton.1 hab, rfl⟩
  · rintro ⟨x, y, h, rfl⟩
    exact card_pair h
#align finset.card_eq_two Finset.card_eq_two

theorem card_eq_three : s.card = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  constructor
  · rw [card_eq_succ]
    simp_rw [card_eq_two]
    rintro ⟨a, _, abc, rfl, b, c, bc, rfl⟩
    rw [mem_insert, mem_singleton, not_or] at abc
    exact ⟨a, b, c, abc.1, abc.2, bc, rfl⟩
  · rintro ⟨x, y, z, xy, xz, yz, rfl⟩
    simp only [xy, xz, yz, mem_insert, card_insert_of_not_mem, not_false_iff, mem_singleton,
      or_self_iff, card_singleton]
#align finset.card_eq_three Finset.card_eq_three

end DecidableEq

theorem two_lt_card_iff : 2 < s.card ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
    simp_rw [lt_iff_add_one_le, le_card_iff_exists_subset_card, reduceAdd, card_eq_three,
      ← exists_and_left, exists_comm (α := Finset α)]
    constructor
    · rintro ⟨a, b, c, t, hsub, hab, hac, hbc, rfl⟩
      exact ⟨a, b, c, by simp_all [insert_subset_iff]⟩
    · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
      exact ⟨a, b, c, {a, b, c}, by simp_all [insert_subset_iff]⟩
#align finset.two_lt_card_iff Finset.two_lt_card_iff

theorem two_lt_card : 2 < s.card ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [two_lt_card_iff, exists_and_left]
#align finset.two_lt_card Finset.two_lt_card

/-! ### Inductions -/


/-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
define an object on `s`. Then one can inductively define an object on all finsets, starting from
the empty set and iterating. This can be used either to define data, or to prove properties. -/
def strongInduction {p : Finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
    ∀ s : Finset α, p s
  | s =>
    H s fun t h =>
      have : t.card < s.card := card_lt_card h
      strongInduction H t
  termination_by s => Finset.card s
#align finset.strong_induction Finset.strongInduction

@[nolint unusedHavesSuffices] -- Porting note: false positive
theorem strongInduction_eq {p : Finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s)
    (s : Finset α) : strongInduction H s = H s fun t _ => strongInduction H t := by
  rw [strongInduction]
#align finset.strong_induction_eq Finset.strongInduction_eq

/-- Analogue of `strongInduction` with order of arguments swapped. -/
@[elab_as_elim]
def strongInductionOn {p : Finset α → Sort*} (s : Finset α) :
    (∀ s, (∀ t ⊂ s, p t) → p s) → p s := fun H => strongInduction H s
#align finset.strong_induction_on Finset.strongInductionOn

@[nolint unusedHavesSuffices] -- Porting note: false positive
theorem strongInductionOn_eq {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
    s.strongInductionOn H = H s fun t _ => t.strongInductionOn H := by
  dsimp only [strongInductionOn]
  rw [strongInduction]
#align finset.strong_induction_on_eq Finset.strongInductionOn_eq

@[elab_as_elim]
theorem case_strong_induction_on [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h₀ : p ∅)
    (h₁ : ∀ a s, a ∉ s → (∀ t ⊆ s, p t) → p (insert a s)) : p s :=
  Finset.strongInductionOn s fun s =>
    Finset.induction_on s (fun _ => h₀) fun a s n _ ih =>
      (h₁ a s n) fun t ss => ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)
#align finset.case_strong_induction_on Finset.case_strong_induction_on

/-- Suppose that, given objects defined on all nonempty strict subsets of any nontrivial finset `s`,
one knows how to define an object on `s`. Then one can inductively define an object on all finsets,
starting from singletons and iterating.

TODO: Currently this can only be used to prove properties.
Replace `Finset.Nonempty.exists_eq_singleton_or_nontrivial` with computational content
in order to let `p` be `Sort`-valued. -/
@[elab_as_elim]
protected lemma Nonempty.strong_induction {p : ∀ s, s.Nonempty → Prop}
    (h₀ : ∀ a, p {a} (singleton_nonempty _))
    (h₁ : ∀ ⦃s⦄ (hs : s.Nontrivial), (∀ t ht, t ⊂ s → p t ht) → p s hs.nonempty) :
    ∀ ⦃s : Finset α⦄ (hs), p s hs
  | s, hs => by
    obtain ⟨a, rfl⟩ | hs := hs.exists_eq_singleton_or_nontrivial
    · exact h₀ _
    · refine h₁ hs fun t ht hts ↦ ?_
      have := card_lt_card hts
      exact ht.strong_induction h₀ h₁
termination_by s => Finset.card s

/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all finsets `s` of
cardinality less than `n`, starting from finsets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
def strongDownwardInduction {p : Finset α → Sort*} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    ∀ s : Finset α, s.card ≤ n → p s
  | s =>
    H s fun {t} ht h =>
      have := Finset.card_lt_card h
      have : n - t.card < n - s.card := by omega
      strongDownwardInduction H t ht
  termination_by s => n - s.card
#align finset.strong_downward_induction Finset.strongDownwardInduction

@[nolint unusedHavesSuffices] -- Porting note: false positive
theorem strongDownwardInduction_eq {p : Finset α → Sort*}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁)
    (s : Finset α) :
    strongDownwardInduction H s = H s fun {t} ht _ => strongDownwardInduction H t ht := by
  rw [strongDownwardInduction]
#align finset.strong_downward_induction_eq Finset.strongDownwardInduction_eq

/-- Analogue of `strongDownwardInduction` with order of arguments swapped. -/
@[elab_as_elim]
def strongDownwardInductionOn {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    s.card ≤ n → p s :=
  strongDownwardInduction H s
#align finset.strong_downward_induction_on Finset.strongDownwardInductionOn

@[nolint unusedHavesSuffices] -- Porting note: false positive
theorem strongDownwardInductionOn_eq {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    s.strongDownwardInductionOn H = H s fun {t} ht _ => t.strongDownwardInductionOn H ht := by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]
#align finset.strong_downward_induction_on_eq Finset.strongDownwardInductionOn_eq

theorem lt_wf {α} : WellFounded (@LT.lt (Finset α) _) :=
  have H : Subrelation (@LT.lt (Finset α) _) (InvImage (· < ·) card) := fun {_ _} hxy =>
    card_lt_card hxy
  Subrelation.wf H <| InvImage.wf _ <| (Nat.lt_wfRel).2
#align finset.lt_wf Finset.lt_wf

@[deprecated (since := "2023-12-27")] alias card_le_of_subset := card_le_card

end Finset
