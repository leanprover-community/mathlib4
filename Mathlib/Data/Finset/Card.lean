/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.Data.Finset.Image

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
-/

assert_not_exists MonoidWithZero
assert_not_exists OrderedCommMonoid

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

@[simp]
theorem card_empty : #(∅ : Finset α) = 0 :=
  rfl

@[gcongr]
theorem card_le_card : s ⊆ t → #s ≤ #t :=
  Multiset.card_le_card ∘ val_le_iff.mpr

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

@[simp]
theorem card_singleton (a : α) : #{a} = 1 :=
  Multiset.card_singleton _

theorem card_singleton_inter [DecidableEq α] : #({a} ∩ s) ≤ 1 := by
  cases' Finset.decidableMem a s with h h
  · simp [Finset.singleton_inter_of_not_mem h]
  · simp [Finset.singleton_inter_of_mem h]

@[simp]
theorem card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1 :=
  Multiset.card_cons _ _

section InsertErase

variable [DecidableEq α]

@[simp]
theorem card_insert_of_not_mem (h : a ∉ s) : #(insert a s) = #s + 1 := by
  rw [← cons_eq_insert _ _ h, card_cons]

theorem card_insert_of_mem (h : a ∈ s) : #(insert a s) = #s := by rw [insert_eq_of_mem h]

theorem card_insert_le (a : α) (s : Finset α) : #(insert a s) ≤ #s + 1 := by
  by_cases h : a ∈ s
  · rw [insert_eq_of_mem h]
    exact Nat.le_succ _
  · rw [card_insert_of_not_mem h]

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

/-- If `a ∈ s` is known, see also `Finset.card_insert_of_mem` and `Finset.card_insert_of_not_mem`.
-/
theorem card_insert_eq_ite : #(insert a s) = if a ∈ s then #s else #s + 1 := by
  by_cases h : a ∈ s
  · rw [card_insert_of_mem h, if_pos h]
  · rw [card_insert_of_not_mem h, if_neg h]

@[simp]
theorem card_pair_eq_one_or_two : #{a, b} = 1 ∨ #{a, b} = 2 := by
  simp [card_insert_eq_ite]
  tauto

@[simp]
theorem card_pair (h : a ≠ b) : #{a, b} = 2 := by
  rw [card_insert_of_not_mem (not_mem_singleton.2 h), card_singleton]

/-- $\#(s \setminus \{a\}) = \#s - 1$ if $a \in s$. -/
@[simp]
theorem card_erase_of_mem : a ∈ s → #(s.erase a) = #s - 1 :=
  Multiset.card_erase_of_mem

/-- $\#(s \setminus \{a\}) = \#s - 1$ if $a \in s$.
  This result is casted to any additive group with 1,
  so that we don't have to work with `ℕ`-subtraction. -/
@[simp]
theorem cast_card_erase_of_mem {R} [AddGroupWithOne R] {s : Finset α} (hs : a ∈ s) :
    (#(s.erase a) : R) = #s - 1 := by
  rw [card_erase_of_mem hs, Nat.cast_sub, Nat.cast_one]
  rw [Nat.add_one_le_iff, Finset.card_pos]
  exact ⟨a, hs⟩

@[simp]
theorem card_erase_add_one : a ∈ s → #(s.erase a) + 1 = #s :=
  Multiset.card_erase_add_one

theorem card_erase_lt_of_mem : a ∈ s → #(s.erase a) < #s :=
  Multiset.card_erase_lt_of_mem

theorem card_erase_le : #(s.erase a) ≤ #s :=
  Multiset.card_erase_le

theorem pred_card_le_card_erase : #s - 1 ≤ #(s.erase a) := by
  by_cases h : a ∈ s
  · exact (card_erase_of_mem h).ge
  · rw [erase_eq_of_not_mem h]
    exact Nat.sub_le _ _

/-- If `a ∈ s` is known, see also `Finset.card_erase_of_mem` and `Finset.erase_eq_of_not_mem`. -/
theorem card_erase_eq_ite : #(s.erase a) = if a ∈ s then #s - 1 else #s :=
  Multiset.card_erase_eq_ite

end InsertErase

@[simp]
theorem card_range (n : ℕ) : #(range n) = n :=
  Multiset.card_range n

@[simp]
theorem card_attach : #s.attach = #s :=
  Multiset.card_attach

end Finset

open scoped Finset

section ToMLListultiset

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

end ToMLListultiset

namespace Finset

variable {s t u : Finset α} {f : α → β} {n : ℕ}

@[simp]
theorem length_toList (s : Finset α) : s.toList.length = #s := by
  rw [toList, ← Multiset.coe_card, Multiset.coe_toList, card_def]

theorem card_image_le [DecidableEq β] : #(s.image f) ≤ #s := by
  simpa only [card_map] using (s.1.map f).toFinset_card_le

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

theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
    #(s.image f) = #s :=
  card_image_of_injOn fun _ _ _ _ h => H h

theorem fiber_card_ne_zero_iff_mem_image (s : Finset α) (f : α → β) [DecidableEq β] (y : β) :
    #(s.filter fun x ↦ f x = y) ≠ 0 ↔ y ∈ s.image f := by
  rw [← Nat.pos_iff_ne_zero, card_pos, fiber_nonempty_iff_mem_image]

lemma card_filter_le_iff (s : Finset α) (P : α → Prop) [DecidablePred P] (n : ℕ) :
    #(s.filter P) ≤ n ↔ ∀ s' ⊆ s, n < #s' → ∃ a ∈ s', ¬ P a :=
  (s.1.card_filter_le_iff P n).trans ⟨fun H s' hs' h ↦ H s'.1 (by aesop) h,
    fun H s' hs' h ↦ H ⟨s', nodup_of_le hs' s.2⟩ (fun _ hx ↦ Multiset.subset_of_le hs' hx) h⟩

@[simp]
theorem card_map (f : α ↪ β) : #(s.map f) = #s :=
  Multiset.card_map _ _

@[simp]
theorem card_subtype (p : α → Prop) [DecidablePred p] (s : Finset α) :
    #(s.subtype p) = #(s.filter p) := by simp [Finset.subtype]

theorem card_filter_le (s : Finset α) (p : α → Prop) [DecidablePred p] :
    #(s.filter p) ≤ #s :=
  card_le_card <| filter_subset _ _

theorem eq_of_subset_of_card_le {s t : Finset α} (h : s ⊆ t) (h₂ : #t ≤ #s) : s = t :=
  eq_of_veq <| Multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂

theorem eq_iff_card_le_of_subset (hst : s ⊆ t) : #t ≤ #s ↔ s = t :=
  ⟨eq_of_subset_of_card_le hst, (ge_of_eq <| congr_arg _ ·)⟩

theorem eq_of_superset_of_card_ge (hst : s ⊆ t) (hts : #t ≤ #s) : t = s :=
  (eq_of_subset_of_card_le hst hts).symm

theorem eq_iff_card_ge_of_superset (hst : s ⊆ t) : #t ≤ #s ↔ t = s :=
  (eq_iff_card_le_of_subset hst).trans eq_comm

theorem subset_iff_eq_of_card_le (h : #t ≤ #s) : s ⊆ t ↔ s = t :=
  ⟨fun hst => eq_of_subset_of_card_le hst h, Eq.subset'⟩

theorem map_eq_of_subset {f : α ↪ α} (hs : s.map f ⊆ s) : s.map f = s :=
  eq_of_subset_of_card_le hs (card_map _).ge

theorem card_filter_eq_iff {p : α → Prop} [DecidablePred p] :
    #(s.filter p) = #s ↔ ∀ x ∈ s, p x := by
  rw [(card_filter_le s p).eq_iff_not_lt, not_lt, eq_iff_card_le_of_subset (filter_subset p s),
    filter_eq_self]

alias ⟨filter_card_eq, _⟩ := card_filter_eq_iff

theorem card_filter_eq_zero_iff {p : α → Prop} [DecidablePred p] :
    #(s.filter p) = 0 ↔ ∀ x ∈ s, ¬ p x := by
  rw [card_eq_zero, filter_eq_empty_iff]

nonrec lemma card_lt_card (h : s ⊂ t) : #s < #t := card_lt_card <| val_lt_iff.2 h

lemma card_strictMono : StrictMono (card : Finset α → ℕ) := fun _ _ ↦ card_lt_card

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
  exact Subtype.eq <| f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq

section bij
variable {t : Finset β}

/-- Reorder a finset.

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

@[deprecated (since := "2024-05-04")] alias card_congr := card_bij

/-- Reorder a finset.

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

/-- Reorder a finset.

The difference with `Finset.card_nbij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.card_bij` is that the bijection is a non-dependent function, rather than
being allowed to use membership of the domain. -/
lemma card_nbij (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (i_inj : (s : Set α).InjOn i)
    (i_surj : (s : Set α).SurjOn i t) : #s = #t :=
  card_bij (fun a _ ↦ i a) hi i_inj (by simpa using i_surj)

/-- Reorder a finset.

The difference with `Finset.card_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.card_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains.

The difference with `Finset.card_equiv` is that bijectivity is only required to hold on the domains,
rather than on the entire types. -/
lemma card_nbij' (i : α → β) (j : β → α) (hi : ∀ a ∈ s, i a ∈ t) (hj : ∀ a ∈ t, j a ∈ s)
    (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a) : #s = #t :=
  card_bij' (fun a _ ↦ i a) (fun b _ ↦ j b) hi hj left_inv right_inv

/-- Specialization of `Finset.card_nbij'` that automatically fills in most arguments.

See `Fintype.card_equiv` for the version where `s` and `t` are `univ`. -/
lemma card_equiv (e : α ≃ β) (hst : ∀ i, i ∈ s ↔ e i ∈ t) : #s = #t := by
  refine card_nbij' e e.symm ?_ ?_ ?_ ?_ <;> simp [hst]

/-- Specialization of `Finset.card_nbij` that automatically fills in most arguments.

See `Fintype.card_bijective` for the version where `s` and `t` are `univ`. -/
lemma card_bijective (e : α → β) (he : e.Bijective) (hst : ∀ i, i ∈ s ↔ e i ∈ t) :
    #s = #t := card_equiv (.ofBijective e he) hst

lemma card_le_card_of_injOn (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (f_inj : (s : Set α).InjOn f) :
    #s ≤ #t := by
  classical
  calc
    #s = #(s.image f) := (card_image_of_injOn f_inj).symm
    _  ≤ #t           := card_le_card <| image_subset_iff.2 hf
@[deprecated (since := "2024-06-01")] alias card_le_card_of_inj_on := card_le_card_of_injOn

lemma card_le_card_of_surjOn (f : α → β) (hf : Set.SurjOn f s t) : #t ≤ #s := by
  classical unfold Set.SurjOn at hf; exact (card_le_card (mod_cast hf)).trans card_image_le

/-- If there are more pigeons than pigeonholes, then there are two pigeons in the same pigeonhole.
-/
theorem exists_ne_map_eq_of_card_lt_of_maps_to {t : Finset β} (hc : #t < #s) {f : α → β}
    (hf : ∀ a ∈ s, f a ∈ t) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  classical
  by_contra! hz
  refine hc.not_le (card_le_card_of_injOn f hf ?_)
  intro x hx y hy
  contrapose
  exact hz x hx y hy

lemma le_card_of_inj_on_range (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ #s :=
  calc
    n = #(range n) := (card_range n).symm
    _ ≤ #s := card_le_card_of_injOn f (by simpa only [mem_range]) (by simpa)

lemma surj_on_of_inj_on_of_card_le (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : #t ≤ #s) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  classical
  have h : #(s.attach.image fun a : s ↦ f a a.2) = #s := by
    rw [← @card_attach _ s, card_image_of_injective]
    intro ⟨_, _⟩ ⟨_, _⟩ h
    exact Subtype.eq <| hinj _ _ _ _ h
  obtain rfl : image (fun a : { a // a ∈ s } => f a a.prop) s.attach = t :=
    eq_of_subset_of_card_le (image_subset_iff.2 <| by simpa) (by simp [hst, h])
  simp only [mem_image, mem_attach, true_and, Subtype.exists, forall_exists_index]
  exact fun b a ha hb ↦ ⟨a, ha, hb.symm⟩

theorem inj_on_of_surj_on_of_card_le (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hsurj : ∀ b ∈ t, ∃ a ha, f a ha = b) (hst : #s ≤ #t) ⦃a₁⦄ (ha₁ : a₁ ∈ s) ⦃a₂⦄
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
        (fun x _ => show g x ∈ s.attach from mem_attach _ _) (fun _ _ _ _ hxy => hg hxy) (by simpa)
        x (mem_attach _ _)
    ⟨y, hy.snd.symm⟩
  have hif : Injective f' :=
    (leftInverse_of_surjective_of_rightInverse hsg (rightInverse_surjInv _)).injective
  Subtype.ext_iff_val.1 (@hif ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ (Subtype.eq ha₁a₂))

end bij

@[simp]
theorem card_disjUnion (s t : Finset α) (h) : #(s.disjUnion t h) = #s + #t :=
  Multiset.card_add _ _

/-! ### Lattice structure -/


section Lattice

variable [DecidableEq α]

theorem card_union_add_card_inter (s t : Finset α) :
    #(s ∪ t) + #(s ∩ t) = #s + #t :=
  Finset.induction_on t (by simp) fun a r har h => by by_cases a ∈ s <;>
    simp [*, ← add_assoc, add_right_comm _ 1]

theorem card_inter_add_card_union (s t : Finset α) :
    #(s ∩ t) + #(s ∪ t) = #s + #t := by rw [add_comm, card_union_add_card_inter]

lemma card_union (s t : Finset α) : #(s ∪ t) = #s + #t - #(s ∩ t) := by
  rw [← card_union_add_card_inter, Nat.add_sub_cancel]

lemma card_inter (s t : Finset α) : #(s ∩ t) = #s + #t - #(s ∪ t) := by
  rw [← card_inter_add_card_union, Nat.add_sub_cancel]

theorem card_union_le (s t : Finset α) : #(s ∪ t) ≤ #s + #t :=
  card_union_add_card_inter s t ▸ Nat.le_add_right _ _

lemma card_union_eq_card_add_card : #(s ∪ t) = #s + #t ↔ Disjoint s t := by
  rw [← card_union_add_card_inter]; simp [disjoint_iff_inter_eq_empty]

@[simp] alias ⟨_, card_union_of_disjoint⟩ := card_union_eq_card_add_card

@[deprecated (since := "2024-02-09")] alias card_union_eq := card_union_of_disjoint
@[deprecated (since := "2024-02-09")] alias card_disjoint_union := card_union_of_disjoint

lemma cast_card_inter [AddGroupWithOne R] :
    (#(s ∩ t) : R) = #s + #t - #(s ∪ t) := by
  rw [eq_sub_iff_add_eq, ← cast_add, card_inter_add_card_union, cast_add]

lemma cast_card_union [AddGroupWithOne R] :
    (#(s ∪ t) : R) = #s + #t - #(s ∩ t) := by
  rw [eq_sub_iff_add_eq, ← cast_add, card_union_add_card_inter, cast_add]

theorem card_sdiff (h : s ⊆ t) : #(t \ s) = #t - #s := by
  suffices #(t \ s) = #(t \ s ∪ s) - #s by rwa [sdiff_union_of_subset h] at this
  rw [card_union_of_disjoint sdiff_disjoint, Nat.add_sub_cancel_right]

lemma cast_card_sdiff [AddGroupWithOne R] (h : s ⊆ t) : (#(t \ s) : R) = #t - #s := by
  rw [card_sdiff h, Nat.cast_sub (card_mono h)]

theorem card_sdiff_add_card_eq_card {s t : Finset α} (h : s ⊆ t) : #(t \ s) + #s = #t :=
  ((Nat.sub_eq_iff_eq_add (card_le_card h)).mp (card_sdiff h).symm).symm

theorem le_card_sdiff (s t : Finset α) : #t - #s ≤ #(t \ s) :=
  calc
    #t - #s ≤ #t - #(s ∩ t) :=
      Nat.sub_le_sub_left (card_le_card inter_subset_left) _
    _ = #(t \ (s ∩ t)) := (card_sdiff inter_subset_right).symm
    _ ≤ #(t \ s) := by rw [sdiff_inter_self_right t s]

theorem card_le_card_sdiff_add_card : #s ≤ #(s \ t) + #t :=
  Nat.sub_le_iff_le_add.1 <| le_card_sdiff _ _

theorem card_sdiff_add_card (s t : Finset α) : #(s \ t) + #t = #(s ∪ t) := by
  rw [← card_union_of_disjoint sdiff_disjoint, sdiff_union_self_eq_union]

lemma card_sdiff_comm (h : #s = #t) : #(s \ t) = #(t \ s) :=
  add_left_injective #t <| by
    simp_rw [card_sdiff_add_card, ← h, card_sdiff_add_card, union_comm]

@[simp]
lemma card_sdiff_add_card_inter (s t : Finset α) :
    #(s \ t) + #(s ∩ t) = #s := by
  rw [← card_union_of_disjoint (disjoint_sdiff_inter _ _), sdiff_union_inter]

@[simp]
lemma card_inter_add_card_sdiff (s t : Finset α) :
    #(s ∩ t) + #(s \ t) = #s := by
  rw [add_comm, card_sdiff_add_card_inter]

/-- **Pigeonhole principle** for two finsets inside an ambient finset. -/
theorem inter_nonempty_of_card_lt_card_add_card (hts : t ⊆ s) (hus : u ⊆ s)
    (hstu : #s < #t + #u) : (t ∩ u).Nonempty := by
  contrapose! hstu
  calc
    _ = #(t ∪ u) := by simp [← card_union_add_card_inter, not_nonempty_iff_eq_empty.1 hstu]
    _ ≤ #s := by gcongr; exact union_subset hts hus

end Lattice

theorem filter_card_add_filter_neg_card_eq_card
    (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] :
    #(s.filter p) + #(s.filter fun a ↦ ¬ p a) = #s := by
  classical
  rw [← card_union_of_disjoint (disjoint_filter_filter_neg _ _ _), filter_union_filter_neg_eq]

/-- Given a subset `s` of a set `t`, of sizes at most and at least `n` respectively, there exists a
set `u` of size `n` which is both a superset of `s` and a subset of `t`. -/
lemma exists_subsuperset_card_eq (hst : s ⊆ t) (hsn : #s ≤ n) (hnt : n ≤ #t) :
    ∃ u, s ⊆ u ∧ u ⊆ t ∧ #u = n := by
  classical
  refine Nat.decreasingInduction' ?_ hnt ⟨t, by simp [hst]⟩
  intro k _ hnk ⟨u, hu₁, hu₂, hu₃⟩
  obtain ⟨a, ha⟩ : (u \ s).Nonempty := by rw [← card_pos, card_sdiff hu₁]; omega
  simp only [mem_sdiff] at ha
  exact ⟨u.erase a, by simp [subset_erase, erase_subset_iff_of_mem (hu₂ _), *]⟩

/-- We can shrink a set to any smaller size. -/
lemma exists_subset_card_eq (hns : n ≤ #s) : ∃ t ⊆ s, #t = n := by
  simpa using exists_subsuperset_card_eq s.empty_subset (by simp) hns

/-- Given a set `A` and a set `B` inside it, we can shrink `A` to any appropriate size, and keep `B`
inside it. -/
@[deprecated exists_subsuperset_card_eq (since := "2024-06-23")]
theorem exists_intermediate_set {A B : Finset α} (i : ℕ) (h₁ : i + #B ≤ #A) (h₂ : B ⊆ A) :
    ∃ C : Finset α, B ⊆ C ∧ C ⊆ A ∧ #C = i + #B :=
  exists_subsuperset_card_eq h₂ (Nat.le_add_left ..) h₁

/-- We can shrink `A` to any smaller size. -/
@[deprecated exists_subset_card_eq (since := "2024-06-23")]
theorem exists_smaller_set (A : Finset α) (i : ℕ) (h₁ : i ≤ #A) :
    ∃ B : Finset α, B ⊆ A ∧ #B = i := exists_subset_card_eq h₁

theorem le_card_iff_exists_subset_card : n ≤ #s ↔ ∃ t ⊆ s, #t = n := by
  refine ⟨fun h => ?_, fun ⟨t, hst, ht⟩ => ht ▸ card_le_card hst⟩
  exact exists_subset_card_eq h

theorem exists_subset_or_subset_of_two_mul_lt_card [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) : ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  have h₁ : #(X ∩ (Y \ X)) = 0 := Finset.card_eq_zero.mpr (Finset.inter_sdiff_self X Y)
  have h₂ : #(X ∪ Y) = #X + #(Y \ X) := by
    rw [← card_union_add_card_inter X (Y \ X), Finset.union_sdiff_self_eq_union, h₁, add_zero]
  rw [h₂, Nat.two_mul] at hXY
  obtain h | h : n < #X ∨ n < #(Y \ X) := by contrapose! hXY; omega
  · exact ⟨X, h, Or.inl (Finset.Subset.refl X)⟩
  · exact ⟨Y \ X, h, Or.inr sdiff_subset⟩

/-! ### Explicit description of a finset from its card -/


theorem card_eq_one : #s = 1 ↔ ∃ a, s = {a} := by
  cases s
  simp only [Multiset.card_eq_one, Finset.card, ← val_inj, singleton_val]

theorem _root_.Multiset.toFinset_card_eq_one_iff [DecidableEq α] (s : Multiset α) :
    #s.toFinset = 1 ↔ Multiset.card s ≠ 0 ∧ ∃ a : α, s = Multiset.card s • {a} := by
  simp_rw [card_eq_one, Multiset.toFinset_eq_singleton_iff, exists_and_left]

theorem exists_eq_insert_iff [DecidableEq α] {s t : Finset α} :
    (∃ a ∉ s, insert a s = t) ↔ s ⊆ t ∧ #s + 1 = #t := by
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

theorem card_le_one : #s ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b := by
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  refine (Nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)).le_iff_eq.trans (card_eq_one.trans ⟨?_, ?_⟩)
  · rintro ⟨y, rfl⟩
    simp
  · exact fun h => ⟨x, eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => h _ hy _ hx⟩⟩

theorem card_le_one_iff : #s ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by
  rw [card_le_one]
  tauto

theorem card_le_one_iff_subsingleton_coe : #s ≤ 1 ↔ Subsingleton (s : Type _) :=
  card_le_one.trans (s : Set α).subsingleton_coe.symm

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
  exact hs.not_le (card_le_one_iff_subset_singleton.2 ⟨a, subset_singleton_iff'.2 this⟩)

/-- A `Finset` of a subsingleton type has cardinality at most one. -/
theorem card_le_one_of_subsingleton [Subsingleton α] (s : Finset α) : #s ≤ 1 :=
  Finset.card_le_one_iff.2 fun {_ _ _ _} => Subsingleton.elim _ _

theorem one_lt_card : 1 < #s ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  rw [← not_iff_not]
  push_neg
  exact card_le_one

theorem one_lt_card_iff : 1 < #s ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  rw [one_lt_card]
  simp only [exists_prop, exists_and_left]

theorem one_lt_card_iff_nontrivial : 1 < #s ↔ s.Nontrivial := by
  rw [← not_iff_not, not_lt, Finset.Nontrivial, ← Set.nontrivial_coe_sort,
    not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton_coe, coe_sort_coe]

@[deprecated (since := "2024-02-05")]
alias one_lt_card_iff_nontrivial_coe := one_lt_card_iff_nontrivial

theorem exists_ne_of_one_lt_card (hs : 1 < #s) (a : α) : ∃ b, b ∈ s ∧ b ≠ a := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hs
  by_cases ha : y = a
  · exact ⟨x, hx, ne_of_ne_of_eq hxy ha⟩
  · exact ⟨y, hy, ha⟩

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
    ⟨a, s.erase a, s.not_mem_erase a, insert_erase has, by
      simp only [h, card_erase_of_mem has, Nat.add_sub_cancel_right]⟩,
    fun ⟨_, _, hat, s_eq, n_eq⟩ => s_eq ▸ n_eq ▸ card_insert_of_not_mem hat⟩

theorem card_eq_two : #s = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} := by
  constructor
  · rw [card_eq_succ]
    simp_rw [card_eq_one]
    rintro ⟨a, _, hab, rfl, b, rfl⟩
    exact ⟨a, b, not_mem_singleton.1 hab, rfl⟩
  · rintro ⟨x, y, h, rfl⟩
    exact card_pair h

theorem card_eq_three : #s = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} := by
  constructor
  · rw [card_eq_succ]
    simp_rw [card_eq_two]
    rintro ⟨a, _, abc, rfl, b, c, bc, rfl⟩
    rw [mem_insert, mem_singleton, not_or] at abc
    exact ⟨a, b, c, abc.1, abc.2, bc, rfl⟩
  · rintro ⟨x, y, z, xy, xz, yz, rfl⟩
    simp only [xy, xz, yz, mem_insert, card_insert_of_not_mem, not_false_iff, mem_singleton,
      or_self_iff, card_singleton]

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

@[nolint unusedHavesSuffices] -- Porting note: false positive
theorem strongInduction_eq {p : Finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s)
    (s : Finset α) : strongInduction H s = H s fun t _ => strongInduction H t := by
  rw [strongInduction]

/-- Analogue of `strongInduction` with order of arguments swapped. -/
@[elab_as_elim]
def strongInductionOn {p : Finset α → Sort*} (s : Finset α) :
    (∀ s, (∀ t ⊂ s, p t) → p s) → p s := fun H => strongInduction H s

@[nolint unusedHavesSuffices] -- Porting note: false positive
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
      have : n - #t < n - #s := by omega
      strongDownwardInduction H t ht
  termination_by s => n - #s

@[nolint unusedHavesSuffices] -- Porting note: false positive
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

@[nolint unusedHavesSuffices] -- Porting note: false positive
theorem strongDownwardInductionOn_eq {p : Finset α → Sort*} (s : Finset α)
    (H : ∀ t₁, (∀ {t₂ : Finset α}, #t₂ ≤ n → t₁ ⊂ t₂ → p t₂) → #t₁ ≤ n → p t₁) :
    s.strongDownwardInductionOn H = H s fun {t} ht _ => t.strongDownwardInductionOn H ht := by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]

theorem lt_wf {α} : WellFounded (@LT.lt (Finset α) _) :=
  have H : Subrelation (@LT.lt (Finset α) _) (InvImage (· < ·) card) := fun {_ _} hxy =>
    card_lt_card hxy
  Subrelation.wf H <| InvImage.wf _ <| (Nat.lt_wfRel).2

end Finset
