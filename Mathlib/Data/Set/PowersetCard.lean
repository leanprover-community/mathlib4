/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups

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

theorem card_eq (s : Set.powersetCard α n) : (s : Finset α).card = n := s.prop

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

section map

variable (n) {β : Type*}

def map (f : α ↪ β) (s : powersetCard α n) : powersetCard β n :=
    ⟨Finset.map f s, by rw [mem_iff, card_map, s.prop]⟩

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

def ofSingleton (a : α) : powersetCard α 1 := ⟨{a}, Finset.card_singleton a⟩

lemma ofSingleton_bijective : Bijective (ofSingleton (α := α)) := by
  refine ⟨fun a b h ↦ Finset.singleton_injective congr($h.1), fun ⟨s, hs⟩ ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
  exact ⟨a, rfl⟩

noncomputable def singletonEquiv : α ≃ powersetCard α 1 where
  toFun := ofSingleton
  invFun s := (Finset.card_eq_one.mp s.prop).choose
  left_inv a := by simp [ofSingleton]
  right_inv s := by rw [ofSingleton, ← Subtype.val_inj, (Finset.card_eq_one.mp s.prop).choose_spec]

lemma coe_singletonEquiv : ⇑(singletonEquiv (α := α)) = ofSingleton := rfl

lemma singletonEquiv_apply (a : α) : singletonEquiv a = ofSingleton a := rfl

variable (n) (β : Type*)

def ofFinEmb (f : Fin n ↪ β) : powersetCard β n :=
  map n f ⟨Finset.univ, by rw [mem_iff, Finset.card_univ, Fintype.card_fin]⟩

lemma mem_ofFinEmb_iff_mem_range (f : Fin n ↪ β) (b : β) :
    b ∈ ofFinEmb n β f ↔ b ∈ Set.range f := by
  simp [ofFinEmb, mem_map_iff_mem_range]

lemma coe_ofFinEmb (f : Fin n ↪ β) : SetLike.coe (ofFinEmb n β f) = Set.range f := by
  ext
  simp [mem_ofFinEmb_iff_mem_range]

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

variable (α)

variable [DecidableEq α] [Fintype α] {m : ℕ} (hm : m + n = Fintype.card α)
include hm

/-- The complement of a combination. -/
def compl (s : powersetCard α n) : powersetCard α m :=
    ⟨(sᶜ : Finset α), by rw [mem_iff, Finset.card_compl]; have := mem_iff.mp s.2; omega⟩

variable {hm} in
theorem coe_compl {s : powersetCard α n} :
    (compl α hm s : Finset α) = (s : Finset α)ᶜ :=
  rfl

variable {hm} in
theorem mem_compl {s : powersetCard α n} {a : α} :
    a ∈ compl α hm s ↔ a ∉ s :=
  Finset.mem_compl

theorem compl_compl :
    (compl α <| (n.add_comm m).trans hm).comp (compl α hm) = id := by
  ext s a
  change a ∈ (compl α _).comp (compl α hm) s ↔ a ∈ s
  simp [mem_compl]

theorem compl_bijective :
    Function.Bijective (compl α hm) :=
  Function.bijective_iff_has_inverse.mpr ⟨compl α ((n.add_comm m).trans hm),
    leftInverse_iff_comp.mpr (compl_compl α hm), rightInverse_iff_comp.mpr (compl_compl α _)⟩

end compl

variable (α n)

theorem coe_finset [Fintype α] :
    powersetCard α n = Finset.powersetCard n (Finset.univ : Finset α) := by
  ext; simp

instance [Finite α] : Finite (powersetCard α n) := by
  have : Fintype α := Fintype.ofFinite α
  simpa [coe_finset] using Subtype.finite

lemma exist_mem_powersetCard_of_inf (h : 0 < n) [Infinite α] (a : α) :
    ∃ s ∈ powersetCard α n, a ∈ s := by
  obtain ⟨s, a_mem, s_card⟩ := Infinite.exists_superset_card_eq ({a} : Finset α) n
    (by rw [Finset.card_singleton]; exact h)
  use ↑s
  exact ⟨mem_iff.mp s_card, by simpa using a_mem⟩

instance instInfinite (h : 0 < n) [Infinite α] : Infinite (powersetCard α n) := by
  rw [← not_finite_iff_infinite]
  by_contra finite
  suffices ⋃₀ (SetLike.coe '' powersetCard α n) = Set.univ by
    apply Finite.false (α := α)
    rw [← Set.finite_univ_iff, ← this]
    apply Set.Finite.sUnion (Finite.image SetLike.coe finite)
    aesop
  rw [sUnion_eq_univ_iff]
  intro a
  obtain ⟨s, s_mem, mem_s⟩ := exist_mem_powersetCard_of_inf α n h a
  exact ⟨↑s, mem_image_of_mem SetLike.coe s_mem, mem_coe.mpr mem_s⟩

protected theorem card :
    Nat.card (powersetCard α n) = (Nat.card α).choose n := by
  classical
  cases fintypeOrInfinite α
  · simp [coe_finset]
  · rcases n with _ | n
    · simp [powersetCard]
    · rw [Nat.card_eq_zero_of_infinite (α := α), Nat.choose_zero_succ]
      have : Infinite (powersetCard α (n+1)) := instInfinite _ _ (Nat.zero_lt_succ n)
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
  · have : Infinite (powersetCard α n) := instInfinite _ _ h1
    infer_instance

/-- A variant of `Set.powersetCard.nontrivial` that uses `Nat.card`. -/
theorem nontrivial' (h1 : 0 < n) (h2 : n < Nat.card α) :
    Nontrivial (powersetCard α n) := by
  have : Finite α := Nat.finite_of_card_ne_zero (ne_zero_of_lt h2)
  apply nontrivial h1
  simp [ENat.card_eq_coe_natCard α, h2]

theorem eq_empty_iff [Finite α] :
    powersetCard α n = ∅ ↔ Nat.card α < n := by
  rw [← Set.ncard_eq_zero, ← _root_.Nat.card_coe_set_eq, powersetCard.card, Nat.choose_eq_zero_iff]

theorem nontrivial_iff [Finite α] :
    Nontrivial (powersetCard α n) ↔ 0 < n ∧ n < Nat.card α := by
  rw [← Finite.one_lt_card_iff_nontrivial, powersetCard.card, Nat.one_lt_iff_ne_zero_and_ne_one,
    ne_eq, Nat.choose_eq_zero_iff, ne_eq, Nat.choose_eq_one_iff]
  grind

end Set.powersetCard
