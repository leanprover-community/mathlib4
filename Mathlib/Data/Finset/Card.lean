/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Cardinality of a finite set

This defines the cardinality of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.card`: `#s : ℕ` returns the cardinality of `s : Finset α`.

### Induction principles

* `Finset.strongInduction`: Strong induction
* `Finset.strongInductionOn`
* `Finset.strongDownwardInduction`
* `Finset.strongDownwardInductionOn`
* `Finset.case_strong_induction_on`
* `Finset.Nonempty.strong_induction`
* `Finset.eraseInduction`
-/

@[expose] public section

assert_not_exists Monoid

open Function Multiset Nat

variable {α β R : Type*}

namespace Finset

variable {s t : Finset α} {a b : α}

/-- `s.card` is the number of elements of `s`, aka its cardinality.

The notation `#s` can be accessed in the `Finset` locale. -/
def card (s : Finset α) : ℕ :=
  Multiset.card s.1

@[inherit_doc] scoped prefix:arg "#" => Finset.card

theorem card_def (s : Finset α) : #s = Multiset.card s.1 :=
  rfl

@[simp] lemma card_val (s : Finset α) : Multiset.card s.1 = #s := rfl

@[simp]
theorem card_mk {m nodup} : #(⟨m, nodup⟩ : Finset α) = Multiset.card m :=
  rfl

@[simp, grind =]
theorem card_empty : #(∅ : Finset α) = 0 :=
  rfl

@[gcongr]
theorem card_le_card : s ⊆ t → #s ≤ #t :=
  Multiset.card_le_card ∘ val_le_iff.mpr

-- This pattern is unreasonable to use generally, but it's convenient in this file.
-- (Note that we turn it on again later in this file.)
local grind_pattern card_le_card => #s, #t

@[mono]
theorem card_mono : Monotone (@card α) := by apply card_le_card

@[simp] lemma card_eq_zero : #s = 0 ↔ s = ∅ := Multiset.card_eq_zero.trans val_eq_zero
lemma card_ne_zero : #s ≠ 0 ↔ s.Nonempty := card_eq_zero.ne.trans nonempty_iff_ne_empty.symm
@[simp] lemma card_pos : 0 < #s ↔ s.Nonempty := Nat.pos_iff_ne_zero.trans card_ne_zero
@[simp] lemma one_le_card : 1 ≤ #s ↔ s.Nonempty := card_pos

alias ⟨_, Nonempty.card_pos⟩ := card_pos
alias ⟨_, Nonempty.card_ne_zero⟩ := card_ne_zero

theorem card_ne_zero_of_mem (h : a ∈ s) : #s ≠ 0 :=
  (not_congr card_eq_zero).2 <| ne_empty_of_mem h

grind_pattern card_ne_zero_of_mem => a ∈ s, #s

@[simp, grind =]
theorem card_singleton (a : α) : #{a} = 1 :=
  Multiset.card_singleton _

theorem card_singleton_inter [DecidableEq α] : #({a} ∩ s) ≤ 1 := by grind

@[simp, grind =]
theorem card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1 :=
  Multiset.card_cons _ _

section InsertErase

variable [DecidableEq α]

@[simp, grind =]
theorem card_insert_of_notMem (h : a ∉ s) : #(insert a s) = #s + 1 := by
  grind [=_ cons_eq_insert]

theorem card_insert_of_mem (h : a ∈ s) : #(insert a s) = #s := by rw [insert_eq_of_mem h]

theorem card_insert_le (a : α) (s : Finset α) : #(insert a s) ≤ #s + 1 := by grind

section

variable {a b c d e f : α}

theorem card_le_two : #{a, b} ≤ 2 := card_insert_le _ _

theorem card_le_three : #{a, b, c} ≤ 3 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_two)

theorem card_le_four : #{a, b, c, d} ≤ 4 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_three)

theorem card_le_five : #{a, b, c, d, e} ≤ 5 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_four)

theorem card_le_six : #{a, b, c, d, e, f} ≤ 6 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ card_le_five)

end

/-- If `a ∈ s` is known, see also `Finset.card_insert_of_mem` and `Finset.card_insert_of_notMem`.
-/
theorem card_insert_eq_ite : #(insert a s) = if a ∈ s then #s else #s + 1 := by grind

@[simp]
theorem card_pair_eq_one_or_two : #{a, b} = 1 ∨ #{a, b} = 2 := by grind

theorem card_pair (h : a ≠ b) : #{a, b} = 2 := by
  simp [h]

/-- $\#(s \setminus \{a\}) = \#s - 1$ if $a \in s$. -/
@[simp, grind =]
theorem card_erase_of_mem : a ∈ s → #(s.erase a) = #s - 1 :=
  Multiset.card_erase_of_mem

-- @[simp] -- removed because LHS is not in simp normal form
theorem card_erase_add_one : a ∈ s → #(s.erase a) + 1 = #s :=
  Multiset.card_erase_add_one

theorem card_erase_lt_of_mem : a ∈ s → #(s.erase a) < #s :=
  Multiset.card_erase_lt_of_mem

theorem card_erase_le : #(s.erase a) ≤ #s :=
  Multiset.card_erase_le

theorem pred_card_le_card_erase : #s - 1 ≤ #(s.erase a) := by grind

/-- If `a ∈ s` is known, see also `Finset.card_erase_of_mem` and `Finset.erase_eq_of_notMem`. -/
theorem card_erase_eq_ite : #(s.erase a) = if a ∈ s then #s - 1 else #s :=
  Multiset.card_erase_eq_ite

end InsertErase

@[simp, grind =]
theorem card_range (n : ℕ) : #(range n) = n :=
  Multiset.card_range n

@[simp, grind =]
theorem card_attach : #s.attach = #s :=
  Multiset.card_attach

end Finset

open scoped Finset

section ToMultiset

variable [DecidableEq α] (m : Multiset α) (l : List α)

theorem Multiset.card_toFinset : #m.toFinset = Multiset.card m.dedup :=
  rfl

theorem Multiset.toFinset_card_le : #m.toFinset ≤ Multiset.card m :=
  card_le_card <| dedup_le _

theorem Multiset.toFinset_card_of_nodup {m : Multiset α} (h : m.Nodup) :
    #m.toFinset = Multiset.card m :=
  congr_arg card <| Multiset.dedup_eq_self.mpr h

theorem Multiset.dedup_card_eq_card_iff_nodup {m : Multiset α} :
    card m.dedup = card m ↔ m.Nodup :=
  .trans ⟨fun h ↦ eq_of_le_of_card_le (dedup_le m) h.ge, congr_arg _⟩ dedup_eq_self

theorem Multiset.toFinset_card_eq_card_iff_nodup {m : Multiset α} :
    #m.toFinset = card m ↔ m.Nodup := dedup_card_eq_card_iff_nodup

theorem List.card_toFinset : #l.toFinset = l.dedup.length :=
  rfl

theorem List.toFinset_card_le : #l.toFinset ≤ l.length :=
  Multiset.toFinset_card_le ⟦l⟧

theorem List.toFinset_card_of_nodup {l : List α} (h : l.Nodup) : #l.toFinset = l.length :=
  Multiset.toFinset_card_of_nodup h

end ToMultiset

namespace Finset

variable {s t u : Finset α} {f : α → β} {n : ℕ}

@[simp, grind =]
theorem length_toList (s : Finset α) : s.toList.length = #s := by
  rw [toList, ← Multiset.coe_card, Multiset.coe_toList, card_def]

theorem card_image_le [DecidableEq β] : #(s.image f) ≤ #s := by
  simpa only [card_map] using (s.1.map f).toFinset_card_le

grind_pattern card_image_le => #(s.image f)
grind_pattern card_image_le => s.image f, #s

theorem card_image_of_injOn [DecidableEq β] (H : Set.InjOn f s) : #(s.image f) = #s := by
  simp only [card, image_val_of_injOn H, card_map]

theorem injOn_of_card_image_eq [DecidableEq β] (H : #(s.image f) = #s) : Set.InjOn f s := by
  rw [card_def, card_def, image, toFinset] at H
  dsimp only at H
  have : (s.1.map f).dedup = s.1.map f := by
    refine Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) ?_
    simp only [H, Multiset.card_map, le_rfl]
  rw [Multiset.dedup_eq_self] at this
  exact inj_on_of_nodup_map this

theorem card_image_iff [DecidableEq β] : #(s.image f) = #s ↔ Set.InjOn f s :=
  ⟨injOn_of_card_image_eq, card_image_of_injOn⟩

grind_pattern card_image_iff => #(s.image f)
grind_pattern card_image_iff => s.image f, #s

theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
    #(s.image f) = #s :=
  card_image_of_injOn fun _ _ _ _ h => H h

theorem fiber_card_ne_zero_iff_mem_image (s : Finset α) (f : α → β) [DecidableEq β] (y : β) :
    #(s.filter fun x ↦ f x = y) ≠ 0 ↔ y ∈ s.image f := by
  rw [← Nat.pos_iff_ne_zero, card_pos, fiber_nonempty_iff_mem_image]

lemma card_filter_le_iff (s : Finset α) (P : α → Prop) [DecidablePred P] (n : ℕ) :
    #(s.filter P) ≤ n ↔ ∀ s' ⊆ s, n < #s' → ∃ a ∈ s', ¬ P a :=
  (s.1.card_filter_le_iff P n).trans ⟨fun H s' hs' h ↦ H s'.1 (by simp_all) h,
    fun H s' hs' h ↦ H ⟨s', nodup_of_le hs' s.2⟩ (fun _ hx ↦ Multiset.subset_of_le hs' hx) h⟩

@[simp, grind =]
theorem card_map (f : α ↪ β) : #(s.map f) = #s :=
  Multiset.card_map _ _

@[simp, grind =]
theorem card_subtype (p : α → Prop) [DecidablePred p] (s : Finset α) :
    #(s.subtype p) = #(s.filter p) := by simp [Finset.subtype]

theorem card_filter_le (s : Finset α) (p : α → Prop) [DecidablePred p] :
    #(s.filter p) ≤ #s :=
  card_le_card <| filter_subset _ _

grind_pattern card_filter_le => #(s.filter p)
grind_pattern card_filter_le => s.filter p, #s

theorem eq_of_subset_of_card_le {s t : Finset α} (h : s ⊆ t) (h₂ : #t ≤ #s) : s = t :=
  eq_of_veq <| Multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂

theorem eq_iff_card_le_of_subset (hst : s ⊆ t) : #t ≤ #s ↔ s = t :=
  ⟨eq_of_subset_of_card_le hst, (ge_of_eq <| congr_arg _ ·)⟩

theorem eq_of_superset_of_card_ge (hst : s ⊆ t) (hts : #t ≤ #s) : t = s :=
  (eq_of_subset_of_card_le hst hts).symm

theorem eq_iff_card_ge_of_superset (hst : s ⊆ t) : #t ≤ #s ↔ t = s :=
  (eq_iff_card_le_of_subset hst).trans eq_comm

theorem subset_iff_eq_of_card_le (h : #t ≤ #s) : s ⊆ t ↔ s = t :=
  ⟨fun hst => eq_of_subset_of_card_le hst h, Eq.subset⟩

theorem map_eq_of_subset {f : α ↪ α} (hs : s.map f ⊆ s) : s.map f = s :=
  eq_of_subset_of_card_le hs (card_map _).ge

theorem card_filter_eq_iff {p : α → Prop} [DecidablePred p] :
    #(s.filter p) = #s ↔ ∀ x ∈ s, p x := by
  rw [← (card_filter_le s p).ge_iff_eq, eq_iff_card_le_of_subset (filter_subset p s),
    filter_eq_self]

alias ⟨filter_card_eq, _⟩ := card_filter_eq_iff

theorem card_filter_eq_zero_iff {p : α → Prop} [DecidablePred p] :
    #(s.filter p) = 0 ↔ ∀ x ∈ s, ¬ p x := by
  rw [card_eq_zero, filter_eq_empty_iff]

@[gcongr]
nonrec lemma card_lt_card (h : s ⊂ t) : #s < #t := card_lt_card <| val_lt_iff.2 h

lemma card_strictMono : StrictMono (card : Finset α → ℕ) := fun _ _ ↦ card_lt_card

section bij

/--
See also `card_bij`.
TODO: consider deprecating, since this has been unused in mathlib for a long time and is just a
special case of `card_bij`.
-/
theorem card_eq_of_bijective (f : ∀ i, i < n → α) (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a)
    (hf' : ∀ i (h : i < n), f i h ∈ s)
    (f_inj : ∀ i j (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) : #s = n := by
  classical
  have : s = (range n).attach.image fun i => f i.1 (mem_range.1 i.2) := by
    ext a
    suffices _ : a ∈ s ↔ ∃ (i : _) (hi : i ∈ range n), f i (mem_range.1 hi) = a by
      simpa only [mem_image, mem_attach, true_and, Subtype.exists]
    constructor
    · intro ha; obtain ⟨i, hi, rfl⟩ := hf a ha; use i, mem_range.2 hi
    · rintro ⟨i, hi, rfl⟩; apply hf'
  calc
    #s = #((range n).attach.image fun i => f i.1 (mem_range.1 i.2)) := by rw [this]
    _ = #(range n).attach := ?_
    _ = #(range n) := card_attach
    _ = n := card_range n
  apply card_image_of_injective
  intro ⟨i, hi⟩ ⟨j, hj⟩ eq
  exact Subtype.ext <| f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq

variable {t : Finset β}

/-- Given a bijection from a finite set `s` to a finite set `t`, the cardinalities of `s` and `t`
are equal.

The difference with `Finset.card_bij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.card_nbij` is that the bijection is allowed to use membership of the
domain, rather than being a non-dependent function. -/
lemma card_bij (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) : #s = #t := by
  classical
  calc
    #s = #s.attach := card_attach.symm
    _ = #(s.attach.image fun a ↦ i a.1 a.2) := Eq.symm ?_
    _ = #t := ?_
  · apply card_image_of_injective
    intro ⟨_, _⟩ ⟨_, _⟩ h
    simpa using i_inj _ _ _ _ h
  · congr 1
    ext b
    constructor <;> intro h
    · obtain ⟨_, _, rfl⟩ := mem_image.1 h; apply hi
    · obtain ⟨a, ha, rfl⟩ := i_surj b h; exact mem_image.2 ⟨⟨a, ha⟩, by simp⟩

/-- Given a bijection from a finite set `s` to a finite set `t`, the cardinalities of `s` and `t`
are equal.

The difference with `Finset.card_bij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.card_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains, rather than being non-dependent functions. -/
lemma card_bij' (i : ∀ a ∈ s, β) (j : ∀ a ∈ t, α) (hi : ∀ a ha, i a ha ∈ t)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) : #s = #t := by
  refine card_bij i hi (fun a1 h1 a2 h2 eq ↦ ?_) (fun b hb ↦ ⟨_, hj b hb, right_inv b hb⟩)
  rw [← left_inv a1 h1, ← left_inv a2 h2]
  simp only [eq]

/-- Given a bijection from a finite set `s` to a finite set `t`, the cardinalities of `s` and `t`
are equal.

The difference with `Finset.card_nbij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.card_bij` is that the bijection is a non-dependent function, rather than
being allowed to use membership of the domain. -/
lemma card_nbij (i : α → β) (hi : Set.MapsTo i s t) (i_inj : (s : Set α).InjOn i)
    (i_surj : (s : Set α).SurjOn i t) : #s = #t :=
  card_bij (fun a _ ↦ i a) hi i_inj (by simpa using i_surj)

/-- Given a bijection from a finite set `s` to a finite set `t`, the cardinalities of `s` and `t`
are equal.

The difference with `Finset.card_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.card_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains.

The difference with `Finset.card_equiv` is that bijectivity is only required to hold on the domains,
rather than on the entire types. -/
lemma card_nbij' (i : α → β) (j : β → α) (hi : Set.MapsTo i s t) (hj : Set.MapsTo j t s)
    (left_inv : Set.LeftInvOn j i s) (right_inv : Set.RightInvOn j i t) : #s = #t :=
  card_bij' (fun a _ ↦ i a) (fun b _ ↦ j b) hi hj left_inv right_inv

/-- Specialization of `Finset.card_nbij'` that automatically fills in most arguments.

See `Fintype.card_equiv` for the version where `s` and `t` are `univ`. -/
lemma card_equiv (e : α ≃ β) (hst : ∀ i, i ∈ s ↔ e i ∈ t) : #s = #t := by
  refine card_nbij' e e.symm ?_ ?_ ?_ ?_ <;> simp [hst, Set.MapsTo, Set.LeftInvOn, Set.RightInvOn]

/-- Specialization of `Finset.card_nbij` that automatically fills in most arguments.

See `Fintype.card_bijective` for the version where `s` and `t` are `univ`. -/
lemma card_bijective (e : α → β) (he : e.Bijective) (hst : ∀ i, i ∈ s ↔ e i ∈ t) :
    #s = #t := card_equiv (.ofBijective e he) hst

lemma _root_.Set.BijOn.finsetCard_eq (e : α → β) (he : Set.BijOn e s t) : #s = #t :=
  card_nbij e he.mapsTo he.injOn he.surjOn

lemma card_le_card_of_injOn (f : α → β) (hf : Set.MapsTo f s t) (f_inj : (s : Set α).InjOn f) :
    #s ≤ #t := by
  classical
  calc
    #s = #(s.image f) := (card_image_of_injOn f_inj).symm
    _ ≤ #t := card_le_card <| image_subset_iff.2 hf

lemma card_le_card_of_injective {f : s → t} (hf : f.Injective) : #s ≤ #t := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  · classical
    let f' : α → β := fun a => f (if ha : a ∈ s then ⟨a, ha⟩ else ⟨a₀, ha₀⟩)
    apply card_le_card_of_injOn f'
    · aesop (add safe unfold Set.MapsTo)
    · intro a₁ ha₁ a₂ ha₂ haa
      rw [mem_coe] at ha₁ ha₂
      simp only [f', ha₁, ha₂, ← Subtype.ext_iff] at haa
      exact Subtype.ext_iff.mp (hf haa)

grind_pattern card_le_card_of_injective => f.Injective, #s
grind_pattern card_le_card_of_injective => f.Injective, #t

lemma card_le_card_of_surjOn (f : α → β) (hf : Set.SurjOn f s t) : #t ≤ #s := by
  classical unfold Set.SurjOn at hf; exact (card_le_card (mod_cast hf)).trans card_image_le

/-- If there are more pigeons than pigeonholes, then there are two pigeons in the same pigeonhole.

See also `Set.exists_ne_map_eq_of_encard_lt_of_maps_to` and
`Set.exists_ne_map_eq_of_ncard_lt_of_maps_to`. -/
theorem exists_ne_map_eq_of_card_lt_of_maps_to (hc : #t < #s) {f : α → β}
    (hf : Set.MapsTo f s t) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  classical
  by_contra! hz
  refine hc.not_ge (card_le_card_of_injOn f hf ?_)
  intro x hx y hy
  contrapose
  exact hz x hx y hy

/-- a special case of `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` where `t` is `s.image f` -/
theorem exists_ne_map_eq_of_card_image_lt [DecidableEq β] {f : α → β} (hc : #(s.image f) < #s) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y :=
  exists_ne_map_eq_of_card_lt_of_maps_to hc (coe_image (β := β) ▸ Set.mapsTo_image f s)

/-- a variant of `Finset.exists_ne_map_eq_of_card_image_lt` using `Set.InjOn` -/
theorem not_injOn_of_card_image_lt [DecidableEq β] {f : α → β} (hc : #(s.image f) < #s) :
    ¬ Set.InjOn f s :=
  mt card_image_of_injOn hc.ne

/--
See also `Finset.card_le_card_of_injOn`, which is a more general version of this lemma.
TODO: consider deprecating, since this is just a special case of `Finset.card_le_card_of_injOn`.
-/
lemma le_card_of_inj_on_range (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ #s :=
  calc
    n = #(range n) := (card_range n).symm
    _ ≤ #s := card_le_card_of_injOn f (by simpa [Set.MapsTo, mem_range] using hf) (by simpa)

/--
Given an injective map `f` from a finite set `s` to another finite set `t`, if `t` is no larger
than `s`, then `f` is surjective to `t` when restricted to `s`.
See `Finset.surj_on_of_inj_on_of_card_le` for the version where `f` is a dependent function.
-/
lemma surjOn_of_injOn_of_card_le (f : α → β) (hf : Set.MapsTo f s t) (hinj : Set.InjOn f s)
    (hst : #t ≤ #s) : Set.SurjOn f s t := by
  classical
  suffices s.image f = t by simp [← this, Set.SurjOn]
  have : s.image f ⊆ t := by aesop (add simp Finset.subset_iff)
  exact eq_of_subset_of_card_le this (hst.trans_eq (card_image_of_injOn hinj).symm)

/--
Given an injective map `f` defined on a finite set `s` to another finite set `t`, if `t` is no
larger than `s`, then `f` is surjective to `t` when restricted to `s`.
See `Finset.surjOn_of_injOn_of_card_le` for the version where `f` is a non-dependent function.
-/
lemma surj_on_of_inj_on_of_card_le (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : #t ≤ #s) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  let f' : s → β := fun a ↦ f a a.2
  have hinj' : Set.InjOn f' s.attach := fun x hx y hy hxy ↦ Subtype.ext (hinj _ _ x.2 y.2 hxy)
  have hmapsto' : Set.MapsTo f' s.attach t := fun x hx ↦ hf _ _
  intro b hb
  obtain ⟨a, ha, rfl⟩ := surjOn_of_injOn_of_card_le _ hmapsto' hinj' (by rwa [card_attach]) hb
  exact ⟨a, a.2, rfl⟩

/--
Given a surjective map `f` from a finite set `s` to another finite set `t`, if `s` is no larger
than `t`, then `f` is injective when restricted to `s`.
See `Finset.inj_on_of_surj_on_of_card_le` for the version where `f` is a dependent function.
-/
lemma injOn_of_surjOn_of_card_le (f : α → β) (hf : Set.MapsTo f s t) (hsurj : Set.SurjOn f s t)
    (hst : #s ≤ #t) : Set.InjOn f s := by
  classical
  have : s.image f = t := Finset.coe_injective <| by simp [hsurj.image_eq_of_mapsTo hf]
  have : #(s.image f) = #t := by rw [this]
  have : #(s.image f) ≤ #s := card_image_le
  rw [← card_image_iff]
  lia

/--
Given a surjective map `f` defined on a finite set `s` to another finite set `t`, if `s` is no
larger than `t`, then `f` is injective when restricted to `s`.
See `Finset.injOn_of_surjOn_of_card_le` for the version where `f` is a non-dependent function.
-/
theorem inj_on_of_surj_on_of_card_le (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀ b ∈ t, ∃ a ha, f a ha = b) (hst : #s ≤ #t) ⦃a₁⦄ (ha₁ : a₁ ∈ s) ⦃a₂⦄
    (ha₂ : a₂ ∈ s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) : a₁ = a₂ := by
  let f' : s → β := fun a ↦ f a a.2
  have hsurj' : Set.SurjOn f' s.attach t := fun x hx ↦ by simpa [f'] using hsurj x hx
  have hinj' := injOn_of_surjOn_of_card_le f' (fun x hx ↦ hf _ _) hsurj' (by simpa)
  exact congrArg Subtype.val (@hinj' ⟨a₁, ha₁⟩ (by simp) ⟨a₂, ha₂⟩ (by simp) ha₁a₂)

end bij

@[simp, grind =]
theorem card_disjUnion (s t : Finset α) (h) : #(s.disjUnion t h) = #s + #t :=
  Multiset.card_add _ _

/-! ### Lattice structure -/

-- This pattern is unreasonable to use generally, but it's convenient in this file.
-- (Note that we've already turned it on earlier in this file, but need to redo it now.)
local grind_pattern card_le_card => #s, #t

section Lattice

variable [DecidableEq α]

theorem card_union_add_card_inter (s t : Finset α) :
    #(s ∪ t) + #(s ∩ t) = #s + #t :=
  Finset.induction_on t (by simp) (by grind)

grind_pattern card_union_add_card_inter => #(s ∪ t), s ∩ t
grind_pattern card_union_add_card_inter => s ∪ t, #(s ∩ t)
grind_pattern card_union_add_card_inter => #(s ∪ t), #s
grind_pattern card_union_add_card_inter => #(s ∪ t), #t
grind_pattern card_union_add_card_inter => #(s ∩ t), #s
grind_pattern card_union_add_card_inter => #(s ∩ t), #t

theorem card_inter_add_card_union (s t : Finset α) :
    #(s ∩ t) + #(s ∪ t) = #s + #t := by grind

lemma card_union (s t : Finset α) : #(s ∪ t) = #s + #t - #(s ∩ t) := by grind

lemma card_inter (s t : Finset α) : #(s ∩ t) = #s + #t - #(s ∪ t) := by grind

theorem card_union_le (s t : Finset α) : #(s ∪ t) ≤ #s + #t := by grind

lemma card_union_eq_card_add_card : #(s ∪ t) = #s + #t ↔ Disjoint s t := by
  rw [← card_union_add_card_inter]; simp [disjoint_iff_inter_eq_empty]

@[simp] alias ⟨_, card_union_of_disjoint⟩ := card_union_eq_card_add_card

@[grind =]
theorem card_sdiff_of_subset (h : s ⊆ t) : #(t \ s) = #t - #s := by
  suffices #(t \ s) = #(t \ s ∪ s) - #s by rwa [sdiff_union_of_subset h] at this
  rw [card_union_of_disjoint sdiff_disjoint, Nat.add_sub_cancel_right]

@[grind =]
theorem card_sdiff : #(t \ s) = #t - #(s ∩ t) := by
  rw [← card_sdiff_of_subset] <;> grind

theorem card_sdiff_add_card_eq_card {s t : Finset α} (h : s ⊆ t) : #(t \ s) + #s = #t := by grind

lemma card_sub_card_eq (s t : Finset α) : #t - #s = #(t \ s) - #(s \ t) :=
  calc
    #t - #s = #t - #(s ∩ t) - #(s \ t) := by grind
    _ = #(t \ (s ∩ t)) - #(s \ t) := by grind
    _ = #(t \ s) - #(s \ t) := by grind

theorem le_card_sdiff (s t : Finset α) : #t - #s ≤ #(t \ s) := by grind

grind_pattern le_card_sdiff => #(t \ s), #t
grind_pattern le_card_sdiff => #(t \ s), #s

theorem card_le_card_sdiff_add_card : #s ≤ #(s \ t) + #t := by grind

theorem card_sdiff_add_card (s t : Finset α) : #(s \ t) + #t = #(s ∪ t) := by
  rw [← card_union_of_disjoint sdiff_disjoint, sdiff_union_self_eq_union]

theorem sdiff_nonempty_of_card_lt_card (h : #s < #t) : (t \ s).Nonempty := by
  grind

omit [DecidableEq α] in
theorem exists_mem_notMem_of_card_lt_card (h : #s < #t) : ∃ e, e ∈ t ∧ e ∉ s := by
  classical simpa [Finset.Nonempty] using sdiff_nonempty_of_card_lt_card h

@[simp]
lemma card_sdiff_add_card_inter (s t : Finset α) :
    #(s \ t) + #(s ∩ t) = #s := by
  rw [← card_union_of_disjoint (disjoint_sdiff_inter _ _), sdiff_union_inter]

grind_pattern card_sdiff_add_card_inter => #(s \ t), #(s ∩ t)
grind_pattern card_sdiff_add_card_inter => #(s \ t), #s

@[simp]
lemma card_inter_add_card_sdiff (s t : Finset α) :
    #(s ∩ t) + #(s \ t) = #s := by grind

lemma card_sdiff_le_card_sdiff_iff : #(s \ t) ≤ #(t \ s) ↔ #s ≤ #t := by grind

lemma card_sdiff_lt_card_sdiff_iff : #(s \ t) < #(t \ s) ↔ #s < #t := by grind

lemma card_sdiff_eq_card_sdiff_iff : #(s \ t) = #(t \ s) ↔ #s = #t := by grind

alias ⟨_, card_sdiff_comm⟩ := card_sdiff_eq_card_sdiff_iff

/-- **Pigeonhole principle** for two finsets inside an ambient finset. -/
theorem inter_nonempty_of_card_lt_card_add_card (hts : t ⊆ s) (hus : u ⊆ s)
    (hstu : #s < #t + #u) : (t ∩ u).Nonempty := by
  contrapose! hstu
  calc
    _ = #(t ∪ u) := by simp [← card_union_add_card_inter, hstu]
    _ ≤ #s := by gcongr; exact union_subset hts hus

end Lattice

theorem card_filter_add_card_filter_not
    (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] :
    #(s.filter p) + #(s.filter fun a ↦ ¬ p a) = #s := by
  classical
  rw [← card_union_of_disjoint (disjoint_filter_filter_not _ _ _), filter_union_filter_not_eq]

@[deprecated (since := "2025-12-12")]
alias filter_card_add_filter_neg_card_eq_card := card_filter_add_card_filter_not

/-- Given a subset `s` of a set `t`, of sizes at most and at least `n` respectively, there exists a
set `u` of size `n` which is both a superset of `s` and a subset of `t`. -/
lemma exists_subsuperset_card_eq (hst : s ⊆ t) (hsn : #s ≤ n) (hnt : n ≤ #t) :
    ∃ u, s ⊆ u ∧ u ⊆ t ∧ #u = n := by
  classical
  refine Nat.decreasingInduction' ?_ hnt ⟨t, by simp [hst]⟩
  intro k _ hnk ⟨u, hu₁, hu₂, hu₃⟩
  obtain ⟨a, ha⟩ : (u \ s).Nonempty := by grind
  exact ⟨u.erase a, by grind⟩

/-- We can shrink a set to any smaller size. -/
lemma exists_subset_card_eq (hns : n ≤ #s) : ∃ t ⊆ s, #t = n := by
  simpa using exists_subsuperset_card_eq s.empty_subset (by simp) hns

theorem le_card_iff_exists_subset_card : n ≤ #s ↔ ∃ t ⊆ s, #t = n := by
  refine ⟨fun h => ?_, fun ⟨t, hst, ht⟩ => ht ▸ card_le_card hst⟩
  exact exists_subset_card_eq h

theorem exists_subset_or_subset_of_two_mul_lt_card [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) : ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind =>
    have : #(X ∪ Y) = #X + #(Y \ X)
    finish

/-! ### Explicit description of a finset from its card -/


theorem card_eq_one : #s = 1 ↔ ∃ a, s = {a} := by
  cases s
  simp only [Multiset.card_eq_one, Finset.card, ← val_inj, singleton_val]

theorem exists_eq_insert_iff [DecidableEq α] {s t : Finset α} :
    (∃ a ∉ s, insert a s = t) ↔ s ⊆ t ∧ #s + 1 = #t := by
  constructor
  · grind
  · rintro ⟨hst, h⟩
    obtain ⟨a, ha⟩ : ∃ a, t \ s = {a} := card_eq_one.mp (by grind)
    grind =>
      have : a ∈ t \ s
      have h : insert a s ⊆ t
      have := eq_of_subset_of_card_le h
      instantiate

theorem card_le_one : #s ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  refine (Nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)).ge_iff_eq'.trans (card_eq_one.trans ⟨?_, ?_⟩)
  · grind
  · exact fun h => ⟨x, by grind⟩

theorem card_le_one_iff : #s ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by
  grind [card_le_one]

theorem card_le_one_iff_subsingleton_coe : #s ≤ 1 ↔ Subsingleton (s : Type _) :=
  card_le_one.trans (s : Set α).subsingleton_coe.symm

/-- A finset has cardinality at most 1 iff its underlying set is subsingleton. -/
theorem card_le_one_iff_subsingleton : #s ≤ 1 ↔ (s : Set α).Subsingleton := by
  rw [card_le_one_iff_subsingleton_coe, ← Set.subsingleton_coe, SetLike.coe_sort_coe]

theorem card_le_one_iff_subset_singleton [Nonempty α] : #s ≤ 1 ↔ ∃ x : α, s ⊆ {x} := by
  refine ⟨fun H => ?_, ?_⟩
  · obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
    · exact ⟨Classical.arbitrary α, empty_subset _⟩
    · exact ⟨x, fun y hy => by rw [card_le_one.1 H y hy x hx, mem_singleton]⟩
  · rintro ⟨x, hx⟩
    rw [← card_singleton x]
    exact card_le_card hx

lemma exists_mem_ne (hs : 1 < #s) (a : α) : ∃ b ∈ s, b ≠ a := by
  have : Nonempty α := ⟨a⟩
  by_contra!
  exact hs.not_ge (card_le_one_iff_subset_singleton.2 ⟨a, subset_singleton_iff'.2 this⟩)

/-- A `Finset` of a subsingleton type has cardinality at most one. -/
theorem card_le_one_of_subsingleton [Subsingleton α] (s : Finset α) : #s ≤ 1 :=
  Finset.card_le_one_iff.2 fun {_ _ _ _} => Subsingleton.elim _ _

theorem one_lt_card : 1 < #s ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  contrapose!; exact card_le_one

theorem one_lt_card_iff : 1 < #s ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  rw [one_lt_card]
  simp only [exists_and_left]

theorem one_lt_card_iff_nontrivial : 1 < #s ↔ s.Nontrivial := by
  rw [← not_iff_not, not_lt, Finset.Nontrivial, ← Set.nontrivial_coe_sort,
    not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton_coe, coe_sort_coe]

/-- If a Finset in a Pi type is nontrivial (has at least two elements), then
  its projection to some factor is nontrivial, and the fibers of the projection
  are proper subsets. -/
lemma exists_of_one_lt_card_pi {ι : Type*} {α : ι → Type*} [∀ i, DecidableEq (α i)]
    {s : Finset (∀ i, α i)} (h : 1 < #s) :
    ∃ i, 1 < #(s.image (· i)) ∧ ∀ ai, s.filter (· i = ai) ⊂ s := by
  simp_rw [one_lt_card_iff, Function.ne_iff] at h ⊢
  obtain ⟨a1, a2, h1, h2, i, hne⟩ := h
  refine ⟨i, ⟨_, _, mem_image_of_mem _ h1, mem_image_of_mem _ h2, hne⟩, fun ai => ?_⟩
  rw [filter_ssubset]
  obtain rfl | hne := eq_or_ne (a2 i) ai
  exacts [⟨a1, h1, hne⟩, ⟨a2, h2, hne⟩]

theorem card_eq_succ_iff_cons :
    #s = n + 1 ↔ ∃ a t, ∃ (h : a ∉ t), cons a t h = s ∧ #t = n :=
  ⟨cons_induction_on s (by simp) fun a s _ _ _ => ⟨a, s, by simp_all⟩,
   fun ⟨a, t, _, hs, _⟩ => by simpa [← hs]⟩

section DecidableEq
variable [DecidableEq α]

theorem card_eq_succ : #s = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ #t = n :=
  ⟨fun h =>
    let ⟨a, has⟩ := card_pos.mp (h.symm ▸ Nat.zero_lt_succ _ : 0 < #s)
    ⟨a, s.erase a, s.notMem_erase a, insert_erase has, by
      simp only [h, card_erase_of_mem has, Nat.add_sub_cancel_right]⟩,
    fun ⟨_, _, hat, s_eq, n_eq⟩ => s_eq ▸ n_eq ▸ card_insert_of_notMem hat⟩

theorem card_eq_two : #s = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_one]
  · grind

theorem card_eq_three : #s = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_two]
  · grind

theorem card_eq_four : #s = 4 ↔
    ∃ x y z w, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧ s = {x, y, z, w} := by
  constructor
  · rw [card_eq_succ]
    grind [card_eq_three]
  · grind

end DecidableEq

theorem two_lt_card_iff : 2 < #s ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
    simp_rw [lt_iff_add_one_le, le_card_iff_exists_subset_card, reduceAdd, card_eq_three,
      ← exists_and_left, exists_comm (α := Finset α)]
    constructor
    · rintro ⟨a, b, c, t, hsub, hab, hac, hbc, rfl⟩
      exact ⟨a, b, c, by simp_all [insert_subset_iff]⟩
    · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
      exact ⟨a, b, c, {a, b, c}, by simp_all [insert_subset_iff]⟩

theorem two_lt_card : 2 < #s ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [two_lt_card_iff, exists_and_left]

theorem three_lt_card_iff : 3 < #s ↔
    ∃ a b c d, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
    simp_rw [lt_iff_add_one_le, le_card_iff_exists_subset_card, reduceAdd, card_eq_four,
      ← exists_and_left, exists_comm (α := Finset α)]
    constructor
    · rintro ⟨a, b, c, d, t, hsub, hab, hac, had, hbc, hbd, hcd, rfl⟩
      exact ⟨a, b, c, d, by simp_all [insert_subset_iff]⟩
    · rintro ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩
      exact ⟨a, b, c, d, {a, b, c, d}, by simp_all [insert_subset_iff]⟩

theorem three_lt_card : 3 < #s ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp_rw [three_lt_card_iff, exists_and_left]

/-! ### Inductions -/


/-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
define an object on `s`. Then one can inductively define an object on all finsets, starting from
the empty set and iterating. This can be used either to define data, or to prove properties. -/
def strongInduction {p : Finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
    ∀ s : Finset α, p s
  | s =>
    H s fun t h =>
      have : #t < #s := card_lt_card h
      strongInduction H t
  termination_by s => #s

theorem strongInduction_eq {p : Finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s)
    (s : Finset α) : strongInduction H s = H s fun t _ => strongInduction H t := by
  rw [strongInduction]

/-- Analogue of `strongInduction` with order of arguments swapped. -/
@[elab_as_elim]
def strongInductionOn {p : Finset α → Sort*} (s : Finset α) :
    (∀ s, (∀ t ⊂ s, p t) → p s) → p s := fun H => strongInduction H s

theorem strongInductionOn_eq {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
    s.strongInductionOn H = H s fun t _ => t.strongInductionOn H := by
  dsimp only [strongInductionOn]
  rw [strongInduction]

@[elab_as_elim]
theorem case_strong_induction_on [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h₀ : p ∅)
    (h₁ : ∀ a s, a ∉ s → (∀ t ⊆ s, p t) → p (insert a s)) : p s :=
  Finset.strongInductionOn s fun s =>
    Finset.induction_on s (fun _ => h₀) fun a s n _ ih =>
      (h₁ a s n) fun t ss => ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)

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
termination_by s => #s

/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all finsets `s` of
cardinality less than `n`, starting from finsets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
def strongDownwardInduction {p : Finset α → Sort*} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, #t₂ ≤ n → t₁ ⊂ t₂ → p t₂) → #t₁ ≤ n → p t₁) :
    ∀ s : Finset α, #s ≤ n → p s
  | s =>
    H s fun {t} ht h =>
      have := Finset.card_lt_card h
      have : n - #t < n - #s := by lia
      strongDownwardInduction H t ht
  termination_by s => n - #s

theorem strongDownwardInduction_eq {p : Finset α → Sort*}
    (H : ∀ t₁, (∀ {t₂ : Finset α}, #t₂ ≤ n → t₁ ⊂ t₂ → p t₂) → #t₁ ≤ n → p t₁)
    (s : Finset α) :
    strongDownwardInduction H s = H s fun {t} ht _ => strongDownwardInduction H t ht := by
  rw [strongDownwardInduction]

/-- Analogue of `strongDownwardInduction` with order of arguments swapped. -/
@[elab_as_elim]
def strongDownwardInductionOn {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, #t₂ ≤ n → t₁ ⊂ t₂ → p t₂) → #t₁ ≤ n → p t₁) :
    #s ≤ n → p s :=
  strongDownwardInduction H s

theorem strongDownwardInductionOn_eq {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, #t₂ ≤ n → t₁ ⊂ t₂ → p t₂) → #t₁ ≤ n → p t₁) :
    s.strongDownwardInductionOn H = H s fun {t} ht _ => t.strongDownwardInductionOn H ht := by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]

theorem lt_wf {α} : WellFounded (@LT.lt (Finset α) _) :=
  have H : Subrelation (@LT.lt (Finset α) _) (InvImage (· < ·) card) := fun {_ _} hxy =>
    card_lt_card hxy
  Subrelation.wf H <| InvImage.wf _ <| (Nat.lt_wfRel).2

/--
To prove a proposition for an arbitrary `Finset α`,
it suffices to prove that for any `S : Finset α`, the following is true:
the property is true for S with any element `s` removed, then the property holds for `S`.

This is a weaker version of `Finset.strongInduction`.
But it can be more precise when the induction argument
only requires removing single elements at a time.
-/
theorem eraseInduction [DecidableEq α] {p : Finset α → Prop}
    (H : (S : Finset α) → (∀ s ∈ S, p (S.erase s)) → p S) (S : Finset α) : p S :=
  S.strongInduction fun S ih => H S fun _ hs => ih _ (erase_ssubset hs)

/--
Given a function `f` which sends the finite set `s` to itself, the sequence of images of `s` under
iterates of `f` is eventually constant. Furthermore, the sequence of images stabilises in fewer
than `#s` steps.
-/
theorem image_iterate_stabilises_lt_card [DecidableEq α] {f : α → α} {s : Finset α}
    (hs : Set.MapsTo f s s) (hs₀ : s.Nonempty) :
    ∃ n < #s, ∀ m, n ≤ m → s.image f^[m] = s.image f^[n] := by
  let g (i : ℕ) : Finset α := s.image f^[i]
  have (i : ℕ) : 0 < #(g i) := (hs₀.image _).card_pos
  have hg : Antitone g := antitone_nat_of_succ_le <| fun i ↦ by
    simp_rw [le_iff_subset, g, Function.iterate_succ, ← image_image]
    grw [hs.finsetImage_subset]
  have eq_iff (i j : ℕ) : #(g i) - 1 = #(g j) - 1 ↔ g i = g j := by
    wlog hij : j ≤ i generalizing i j
    · grind
    exact ⟨fun h ↦ eq_of_subset_of_card_le (hg hij) (by grind), by grind⟩
  have hG : Antitone (fun i ↦ #(g i) - 1) := fun i j h ↦ by dsimp; gcongr #?_ - 1; exact hg h
  rcases Nat.stabilises_of_antitone hG (by grind [=_ image_image, iterate_succ']) with ⟨n, hn, hn'⟩
  exact ⟨n, by grind⟩

/--
Given a function `f` which sends the finite set `s` to itself, the sequence of images of `s` under
iterates of `f` is eventually constant. Furthermore, the sequence of images stabilises in at most
`#s` steps.
-/
theorem image_iterate_stabilises_le_card [DecidableEq α] {f : α → α} {s : Finset α}
    (hs : Set.MapsTo f s s) :
    ∃ n ≤ #s, ∀ m, n ≤ m → s.image f^[m] = s.image f^[n] := by
  obtain rfl | hs₀ := s.eq_empty_or_nonempty
  · simp
  obtain ⟨n, hn', hn⟩ := image_iterate_stabilises_lt_card hs hs₀
  exact ⟨n, hn'.le, hn⟩

end Finset
