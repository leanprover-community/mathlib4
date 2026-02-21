/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Antoine Chambert-Loir
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Finite.Card
public import Mathlib.Data.Set.Card

/-! # Combinations

Combinations in a type are finite subsets of given cardinality.

* `Set.powersetCard α n` is the set of all `Finset α` with cardinality `n`.
  The name is chosen in relation with `Finset.powersetCard` which corresponds to
  the analogous structure for subsets of given cardinality of a given `Finset`, as a `Finset`.

* `Set.powersetCard.card` proves that the `Nat.card`-cardinality
  of this set is equal to `(Nat.card α).choose n`.

-/

@[expose] public section

variable (α : Type*)

/-- The type of combinations of `n` elements of a type `α`.

See also `Finset.powersetCard`. -/
def Set.powersetCard (n : ℕ) := {s : Finset α | s.card = n}

variable {α} {n : ℕ}

namespace Set.powersetCard

open Finset Set Function

@[simp]
theorem mem_iff {s : Finset α} :
    s ∈ powersetCard α n ↔ s.card = n := by
  rw [powersetCard, Set.mem_setOf_eq]

instance : SetLike (powersetCard α n) α := SetLike.instSubtype

instance : PartialOrder (Set.powersetCard α n) := .ofSetLike (Set.powersetCard α n) α

@[simp]
theorem coe_coe {s : powersetCard α n} :
    ((s : Finset α) : Set α) = s := rfl

theorem mem_coe_iff {s : Set.powersetCard α n} {a : α} : a ∈ (s : Finset α) ↔ a ∈ s := .rfl

@[simp]
theorem card_eq (s : Set.powersetCard α n) : (s : Finset α).card = n := s.prop

@[simp]
theorem ncard_eq (s : Set.powersetCard α n) : (s : Set α).ncard = n := by
  rw [← coe_coe, Set.ncard_coe_finset, s.prop]

theorem coe_nonempty_iff {s : Set.powersetCard α n} :
    (s : Set α).Nonempty ↔ 1 ≤ n := by
  rw [← Set.powersetCard.coe_coe, Finset.coe_nonempty, ← one_le_card, s.prop]

theorem coe_nontrivial_iff {s : Set.powersetCard α n} :
    (s : Set α).Nontrivial ↔ 1 < n := by
  rw [← coe_coe, Finset.nontrivial_coe, ← one_lt_card_iff_nontrivial, card_eq]

theorem eq_iff_subset {s t : Set.powersetCard α n} : s = t ↔ (s : Finset α) ⊆ (t : Finset α) := by
  rw [Finset.subset_iff_eq_of_card_le (t.prop.trans_le s.prop.ge), Subtype.ext_iff]

set_option backward.isDefEq.respectTransparency false in
theorem exists_mem_notMem (hn : 1 ≤ n) (hα : n < ENat.card α) {a b : α} (hab : a ≠ b) :
    ∃ s : powersetCard α n, a ∈ s ∧ b ∉ s := by
  have ha' : n ≤ Set.encard {b}ᶜ := by
    rwa [← (Set.encard_add_encard_compl {b}).trans (Set.encard_univ α), Set.encard_singleton,
      add_comm, ENat.lt_add_one_iff' (ENat.coe_ne_top n)] at hα
  obtain ⟨s, has, has', hs⟩ :=
    Set.exists_superset_subset_encard_eq (s := {a}) (by simp [Ne.symm hab]) (by simpa) ha'
  have : Set.Finite s := Set.finite_of_encard_eq_coe hs
  exact ⟨⟨Set.Finite.toFinset this, by
    rwa [mem_iff, ← ENat.coe_inj, ← this.encard_eq_coe_toFinset_card]⟩,
      by simpa using has, by simpa using has'⟩

theorem exists_mem_notMem_iff_ne (s t : Set.powersetCard α n) : s ≠ t ↔ ∃ a ∈ s, a ∉ t := by
  contrapose!
  rw [eq_iff_subset]
  rfl

section map

variable (n) {β : Type*}

/-- The map `powersetCard α n → powersetCard β n` induced by embedding `f : α ↪ β`. -/
def map (f : α ↪ β) (s : powersetCard α n) : powersetCard β n :=
    ⟨Finset.map f s, by rw [mem_iff, card_map, s.prop]⟩

set_option backward.isDefEq.respectTransparency false in
lemma mem_map_iff_mem_range (f : α ↪ β) (s : powersetCard α n) (b : β) :
    b ∈ map n f s ↔ b ∈ f '' s := by
  simp [map]
  rfl

@[simp]
lemma coe_map (f : α ↪ β) (s : powersetCard α n) : SetLike.coe (map n f s) = f '' s := by
  ext
  simp [mem_map_iff_mem_range]

@[simp]
lemma val_map (f : α ↪ β) (s : powersetCard α n) : Subtype.val (map n f s) = s.val.map f := rfl

end map

section of

/-- The coercion of a finite set to its corresponding element of `Set.powersetCard`. -/
def ofCard {s : Finset α} (s_card : s.card = n) : powersetCard α n := ⟨s, mem_iff.mpr s_card⟩

@[simp]
lemma val_ofCard {s : Finset α} (s_card : s.card = n) : Subtype.val (ofCard s_card) = s := rfl

/-- The equivalence sending `a : α` to the singleton `{a}`. -/
noncomputable def ofSingleton : α ≃ powersetCard α 1 where
  toFun a := ⟨{a}, Finset.card_singleton a⟩
  invFun s := (Finset.card_eq_one.mp s.prop).choose
  left_inv a := by simp
  right_inv s := by rw [← Subtype.val_inj, (Finset.card_eq_one.mp s.prop).choose_spec]

variable (n) (β : Type*)

/-- The image of an embedding `f : Fin n ↪ β` as an element of `powersetCard β n`. -/
def ofFinEmb (f : Fin n ↪ β) : powersetCard β n :=
  map n f ⟨Finset.univ, by rw [mem_iff, Finset.card_univ, Fintype.card_fin]⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma mem_ofFinEmb_iff_mem_range (f : Fin n ↪ β) (b : β) :
    b ∈ ofFinEmb n β f ↔ b ∈ Set.range f := by
  simp [ofFinEmb, mem_map_iff_mem_range]

@[simp]
lemma coe_ofFinEmb (f : Fin n ↪ β) : SetLike.coe (ofFinEmb n β f) = Set.range f := by
  ext
  simp [mem_ofFinEmb_iff_mem_range]

@[simp]
lemma val_ofFinEmb (f : Fin n ↪ β) :
    Subtype.val (ofFinEmb n β f) = Finset.univ.map f := by
  simp [← coe_inj, coe_ofFinEmb]

theorem ofFinEmb_surjective :
    Function.Surjective (ofFinEmb n β) := by
  intro ⟨s, hs⟩
  obtain ⟨f : Fin n ↪ β, hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (by rw [hs, Fintype.card_fin])
  exact ⟨f, Subtype.ext hf⟩

end of

section compl

variable [DecidableEq α] [Fintype α] {m : ℕ} (hm : m + n = Fintype.card α)

/-- Complement of `Finset`s as an equivalence on `Set.powersetCard`. -/
def compl : powersetCard α n ≃ powersetCard α m where
  toFun s := ⟨(sᶜ : Finset α), by simp [Finset.card_compl, mem_iff.mp s.2]; omega⟩
  invFun t := ⟨(tᶜ : Finset α), by simp [Finset.card_compl, mem_iff.mp t.2]; omega⟩
  left_inv s := by simp
  right_inv t := by simp

variable {hm}

@[simp]
theorem coe_compl {s : powersetCard α n} :
    (compl hm s : Finset α) = (s : Finset α)ᶜ :=
  rfl

@[simp]
theorem mem_compl {s : powersetCard α n} {a : α} :
    a ∈ compl hm s ↔ a ∉ s :=
  Finset.mem_compl

theorem compl_symm : (compl hm).symm = compl ((n.add_comm m).trans hm) := rfl

end compl

section disjUnion

variable {m : ℕ} {s : powersetCard α m} {t : powersetCard α n} (hst : Disjoint s.val t.val)

/-- The disjoint union of two `powersetCard`s. -/
def disjUnion : powersetCard α (m + n) :=
  ⟨s.val.disjUnion t hst, by rw [mem_iff, Finset.card_disjUnion, card_eq s, card_eq t]⟩

variable {hst}

@[simp]
theorem coe_disjUnion : (disjUnion hst : Finset α) = s.val.disjUnion t hst := rfl

@[simp]
theorem mem_disjUnion {a : α} : a ∈ disjUnion hst ↔ a ∈ s ∨ a ∈ t :=
  Finset.mem_disjUnion (h := hst)

end disjUnion

variable (α n)

set_option backward.isDefEq.respectTransparency false in
theorem coe_finset [Fintype α] :
    powersetCard α n = Finset.powersetCard n (Finset.univ : Finset α) := by
  ext; simp

instance [Fintype α] : Fintype (powersetCard α n) := by
  rw [coe_finset]
  infer_instance

instance [Finite α] : Finite (powersetCard α n) := by
  have : Fintype α := Fintype.ofFinite α
  simpa [coe_finset] using Subtype.finite

lemma exist_mem_powersetCard_of_inf (h : 0 < n) [Infinite α] (a : α) :
    ∃ s ∈ powersetCard α n, a ∈ s := by
  obtain ⟨s, a_mem, s_card⟩ := Infinite.exists_superset_card_eq ({a} : Finset α) n
    (by rw [Finset.card_singleton]; exact h)
  use ↑s
  exact ⟨mem_iff.mp s_card, by simpa using a_mem⟩

instance instInfinite [NeZero n] [Infinite α] : Infinite (powersetCard α n) := by
  rw [← not_finite_iff_infinite]
  by_contra finite
  suffices ⋃₀ (SetLike.coe '' powersetCard α n) = Set.univ by
    apply Finite.false (α := α)
    rw [← Set.finite_univ_iff, ← this]
    apply Set.Finite.sUnion (Finite.image SetLike.coe finite)
    aesop
  rw [sUnion_eq_univ_iff]
  intro a
  obtain ⟨s, s_mem, mem_s⟩ := exist_mem_powersetCard_of_inf α n (Nat.pos_of_neZero n) a
  exact ⟨↑s, mem_image_of_mem SetLike.coe s_mem, mem_coe.mpr mem_s⟩

protected theorem card :
    Nat.card (powersetCard α n) = (Nat.card α).choose n := by
  classical
  cases fintypeOrInfinite α
  · simp [coe_finset]
  · rcases n with _ | n
    · simp [powersetCard]
    · rw [Nat.card_eq_zero_of_infinite (α := α), Nat.choose_zero_succ]
      exact Nat.card_eq_zero_of_infinite

variable {α n}

/-- If `0 < n < ENat.card α`, then `powersetCard α n` is nontrivial. -/
theorem nontrivial (h1 : 0 < n) (h2 : n < ENat.card α) :
    Nontrivial (powersetCard α n) := by
  cases fintypeOrInfinite α
  · rw [Set.nontrivial_coe_sort, ← Set.one_lt_ncard_iff_nontrivial, ← Nat.card_coe_set_eq,
      powersetCard.card]
    by_contra!
    rw [Nat.le_one_iff_eq_zero_or_eq_one] at this
    rw [ENat.card_eq_coe_natCard] at h2
    norm_cast at h2
    rcases this with h | h
    · rw [Nat.choose_eq_zero_iff] at h
      exact (lt_self_iff_false n).mp (lt_trans h2 h)
    · rw [Nat.choose_eq_one_iff] at h
      aesop
  · have : NeZero n := NeZero.of_pos h1
    infer_instance

/-- A variant of `Set.powersetCard.nontrivial` that uses `Nat.card`. -/
theorem nontrivial' (h1 : 0 < n) (h2 : n < Nat.card α) :
    Nontrivial (powersetCard α n) := by
  have : Finite α := Nat.finite_of_card_ne_zero (ne_zero_of_lt h2)
  apply nontrivial h1
  simp [ENat.card_eq_coe_natCard α, h2]

@[simp]
theorem eq_empty_iff [Finite α] :
    powersetCard α n = ∅ ↔ Nat.card α < n := by
  rw [← Set.ncard_eq_zero, ← _root_.Nat.card_coe_set_eq, powersetCard.card, Nat.choose_eq_zero_iff]

theorem nontrivial_iff [Finite α] :
    Nontrivial (powersetCard α n) ↔ 0 < n ∧ n < Nat.card α := by
  rw [← Finite.one_lt_card_iff_nontrivial, powersetCard.card, Nat.one_lt_iff_ne_zero_and_ne_one,
    ne_eq, Nat.choose_eq_zero_iff, ne_eq, Nat.choose_eq_one_iff]
  grind

/-- The bijection between the product of `(n : ℕ)` and the finsets of `α` of cardinality `n` and
`Finset α`. -/
def prodEquiv : (n : ℕ) × (powersetCard α n) ≃ Finset α where
  toFun x := x.2
  invFun x := ⟨x.card, ⟨x, rfl⟩⟩
  left_inv x := by ext <;> simp

@[simp]
lemma prodEquiv_apply (x : (n : ℕ) × (powersetCard α n)) : prodEquiv x = x.2 := rfl

@[simp]
lemma prodEquiv_symm_apply (s : Finset α) : prodEquiv.symm s = ⟨s.card, ⟨s, rfl⟩⟩ := rfl

end Set.powersetCard
