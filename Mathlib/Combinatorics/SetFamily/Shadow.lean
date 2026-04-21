/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Sups
public import Mathlib.Logic.Function.Iterate

/-!
# Shadows

This file defines shadows of a set family. The shadow of a set family is the set family of sets we
get by removing any element from any set of the original family. If one pictures `Finset α` as a big
hypercube (each dimension being membership of a given element), then taking the shadow corresponds
to projecting each finset down once in all available directions.

## Main definitions

* `Finset.shadow`: The shadow of a set family. Everything we can get by removing a new element from
  some set.
* `Finset.upShadow`: The upper shadow of a set family. Everything we can get by adding an element
  to some set.

## Notation

We define notation in scope `FinsetFamily`:
* `∂ 𝒜`: Shadow of `𝒜`.
* `∂⁺ 𝒜`: Upper shadow of `𝒜`.

We also maintain the convention that `a, b : α` are elements of the ground type, `s, t : Finset α`
are finsets, and `𝒜, ℬ : Finset (Finset α)` are finset families.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, set family
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open Finset Nat

variable {α : Type*}

namespace Finset

section Shadow

variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s t : Finset α} {a : α} {k r : ℕ}

/-- The shadow of a set family `𝒜` is all sets we can get by removing one element from any set in
`𝒜`, and the (`k` times) iterated shadow (`shadow^[k]`) is all sets we can get by removing `k`
elements from any set in `𝒜`. -/
def shadow (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.sup fun s => s.image (erase s)

@[inherit_doc] scoped[FinsetFamily] notation:max "∂" => Finset.shadow

open FinsetFamily

/-- The shadow of the empty set is empty. -/
@[simp]
theorem shadow_empty : ∂ (∅ : Finset (Finset α)) = ∅ :=
  rfl

@[simp] lemma shadow_iterate_empty (k : ℕ) : ∂^[k] (∅ : Finset (Finset α)) = ∅ := by
  induction k <;> simp [*, shadow_empty]

@[simp]
theorem shadow_singleton_empty : ∂ ({∅} : Finset (Finset α)) = ∅ :=
  rfl

@[simp]
theorem shadow_singleton (a : α) : ∂ {{a}} = {∅} := by
  simp [shadow]

/-- The shadow is monotone. -/
@[mono]
theorem shadow_monotone : Monotone (shadow : Finset (Finset α) → Finset (Finset α)) := fun _ _ =>
  sup_mono

@[gcongr] lemma shadow_mono (h𝒜ℬ : 𝒜 ⊆ ℬ) : ∂ 𝒜 ⊆ ∂ ℬ := shadow_monotone h𝒜ℬ

/-- `t` is in the shadow of `𝒜` iff there is a `s ∈ 𝒜` from which we can remove one element to
get `t`. -/
lemma mem_shadow_iff : t ∈ ∂ 𝒜 ↔ ∃ s ∈ 𝒜, ∃ a ∈ s, erase s a = t := by
  simp only [shadow, mem_sup, mem_image]

theorem erase_mem_shadow (hs : s ∈ 𝒜) (ha : a ∈ s) : erase s a ∈ ∂ 𝒜 :=
  mem_shadow_iff.2 ⟨s, hs, a, ha, rfl⟩

/-- `t ∈ ∂𝒜` iff `t` is exactly one element less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_mem_card_add_one`. -/
lemma mem_shadow_iff_exists_sdiff : t ∈ ∂ 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ #(s \ t) = 1 := by
  simp_rw [mem_shadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]

/-- `t` is in the shadow of `𝒜` iff we can add an element to it so that the resulting finset is in
`𝒜`. -/
lemma mem_shadow_iff_insert_mem : t ∈ ∂ 𝒜 ↔ ∃ a ∉ t, insert a t ∈ 𝒜 := by
  simp_rw [mem_shadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]
  aesop

/-- `s ∈ ∂ 𝒜` iff `s` is exactly one element less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_sdiff`. -/
lemma mem_shadow_iff_exists_mem_card_add_one : t ∈ ∂ 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ #s = #t + 1 := by
  refine mem_shadow_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff_of_subset hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst

lemma mem_shadow_iterate_iff_exists_card :
    t ∈ ∂^[k] 𝒜 ↔ ∃ u : Finset α, #u = k ∧ Disjoint t u ∧ t ∪ u ∈ 𝒜 := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    simp only [mem_shadow_iff_insert_mem, ih, Function.iterate_succ_apply', card_eq_succ]
    aesop

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_mem_card_add`. -/
lemma mem_shadow_iterate_iff_exists_sdiff : t ∈ ∂^[k] 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ #(s \ t) = k := by
  rw [mem_shadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, htu, hsuA⟩
    exact ⟨_, hsuA, subset_union_left, by rw [union_sdiff_cancel_left htu]⟩
  · rintro ⟨s, hs, hts, rfl⟩
    refine ⟨s \ t, rfl, disjoint_sdiff, ?_⟩
    rwa [union_sdiff_self_eq_union, union_eq_right.2 hts]

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`.

See also `Finset.mem_shadow_iterate_iff_exists_sdiff`. -/
lemma mem_shadow_iterate_iff_exists_mem_card_add :
    t ∈ ∂^[k] 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ #s = #t + k := by
  refine mem_shadow_iterate_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff_of_subset hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst

/-- The shadow of a family of `r`-sets is a family of `r - 1`-sets. -/
protected theorem _root_.Set.Sized.shadow (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂ 𝒜 : Set (Finset α)).Sized (r - 1) := by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_shadow_iff.1 h
  rw [card_erase_of_mem hi, h𝒜 hA]

/-- The `k`-th shadow of a family of `r`-sets is a family of `r - k`-sets. -/
lemma _root_.Set.Sized.shadow_iterate (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂^[k] 𝒜 : Set (Finset α)).Sized (r - k) := by
  simp_rw [Set.Sized, mem_coe, mem_shadow_iterate_iff_exists_sdiff]
  rintro t ⟨s, hs, hts, rfl⟩
  rw [card_sdiff_of_subset hts, ← h𝒜 hs, Nat.sub_sub_self (card_le_card hts)]

theorem sized_shadow_iff (h : ∅ ∉ 𝒜) :
    (∂ 𝒜 : Set (Finset α)).Sized r ↔ (𝒜 : Set (Finset α)).Sized (r + 1) := by
  refine ⟨fun h𝒜 s hs => ?_, Set.Sized.shadow⟩
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hs h)
  rw [← h𝒜 (erase_mem_shadow hs ha), card_erase_add_one ha]

/-- Being in the shadow of `𝒜` means we have a superset in `𝒜`. -/
lemma exists_subset_of_mem_shadow (hs : t ∈ ∂ 𝒜) : ∃ s ∈ 𝒜, t ⊆ s :=
  let ⟨t, ht, hst⟩ := mem_shadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hst.1⟩

end Shadow

open FinsetFamily

section UpShadow

variable [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {s t : Finset α} {a : α} {k r : ℕ}

/-- The upper shadow of a set family `𝒜` is all sets we can get by adding one element to any set in
`𝒜`, and the (`k` times) iterated upper shadow (`upShadow^[k]`) is all sets we can get by adding
`k` elements from any set in `𝒜`. -/
def upShadow (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.sup fun s => sᶜ.image fun a => insert a s

@[inherit_doc] scoped[FinsetFamily] notation:max "∂⁺ " => Finset.upShadow

/-- The upper shadow of the empty set is empty. -/
@[simp]
theorem upShadow_empty : ∂⁺ (∅ : Finset (Finset α)) = ∅ :=
  rfl

/-- The upper shadow is monotone. -/
@[mono]
theorem upShadow_monotone : Monotone (upShadow : Finset (Finset α) → Finset (Finset α)) :=
  fun _ _ => sup_mono

/-- `t` is in the upper shadow of `𝒜` iff there is a `s ∈ 𝒜` from which we can remove one element
to get `t`. -/
lemma mem_upShadow_iff : t ∈ ∂⁺ 𝒜 ↔ ∃ s ∈ 𝒜, ∃ a ∉ s, insert a s = t := by
  simp_rw [upShadow, mem_sup, mem_image, mem_compl]

theorem insert_mem_upShadow (hs : s ∈ 𝒜) (ha : a ∉ s) : insert a s ∈ ∂⁺ 𝒜 :=
  mem_upShadow_iff.2 ⟨s, hs, a, ha, rfl⟩

/-- `t` is in the upper shadow of `𝒜` iff `t` is exactly one element more than something from `𝒜`.

See also `Finset.mem_upShadow_iff_exists_mem_card_add_one`. -/
lemma mem_upShadow_iff_exists_sdiff : t ∈ ∂⁺ 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ #(t \ s) = 1 := by
  simp_rw [mem_upShadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]

/-- `t` is in the upper shadow of `𝒜` iff we can remove an element from it so that the resulting
finset is in `𝒜`. -/
lemma mem_upShadow_iff_erase_mem : t ∈ ∂⁺ 𝒜 ↔ ∃ a, a ∈ t ∧ erase t a ∈ 𝒜 := by
  simp_rw [mem_upShadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]
  aesop

/-- `t` is in the upper shadow of `𝒜` iff `t` is exactly one element less than something from `𝒜`.

See also `Finset.mem_upShadow_iff_exists_sdiff`. -/
lemma mem_upShadow_iff_exists_mem_card_add_one :
    t ∈ ∂⁺ 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ #t = #s + 1 := by
  refine mem_upShadow_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff_of_subset hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst

lemma mem_upShadow_iterate_iff_exists_card :
    t ∈ ∂⁺^[k] 𝒜 ↔ ∃ u : Finset α, #u = k ∧ u ⊆ t ∧ t \ u ∈ 𝒜 := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    simp only [mem_upShadow_iff_erase_mem, ih, Function.iterate_succ_apply', card_eq_succ,
      subset_erase, erase_sdiff_comm, ← sdiff_insert]
    constructor
    · rintro ⟨a, hat, u, rfl, ⟨hut, hau⟩, htu⟩
      exact ⟨_, ⟨_, _, hau, rfl, rfl⟩, insert_subset hat hut, htu⟩
    · rintro ⟨_, ⟨a, u, hau, rfl, rfl⟩, hut, htu⟩
      rw [insert_subset_iff] at hut
      exact ⟨a, hut.1, _, rfl, ⟨hut.2, hau⟩, htu⟩

/-- `t` is in the upper shadow of `𝒜` iff `t` is exactly `k` elements less than something from `𝒜`.

See also `Finset.mem_upShadow_iff_exists_mem_card_add`. -/
lemma mem_upShadow_iterate_iff_exists_sdiff : t ∈ ∂⁺^[k] 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ #(t \ s) = k := by
  rw [mem_upShadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, hut, htu⟩
    exact ⟨_, htu, sdiff_subset, by rw [sdiff_sdiff_eq_self hut]⟩
  · rintro ⟨s, hs, hst, rfl⟩
    exact ⟨_, rfl, sdiff_subset, by rwa [sdiff_sdiff_eq_self hst]⟩

/-- `t ∈ ∂⁺^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`.

See also `Finset.mem_upShadow_iterate_iff_exists_sdiff`. -/
lemma mem_upShadow_iterate_iff_exists_mem_card_add :
    t ∈ ∂⁺^[k] 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ #t = #s + k := by
  refine mem_upShadow_iterate_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff_of_subset hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst

/-- The upper shadow of a family of `r`-sets is a family of `r + 1`-sets. -/
protected lemma _root_.Set.Sized.upShadow (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂⁺ 𝒜 : Set (Finset α)).Sized (r + 1) := by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_upShadow_iff.1 h
  rw [card_insert_of_notMem hi, h𝒜 hA]

/-- Being in the upper shadow of `𝒜` means we have a superset in `𝒜`. -/
theorem exists_subset_of_mem_upShadow (hs : s ∈ ∂⁺ 𝒜) : ∃ t ∈ 𝒜, t ⊆ s :=
  let ⟨t, ht, hts, _⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hts⟩

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements more than something in `𝒜`. -/
theorem mem_upShadow_iff_exists_mem_card_add :
    s ∈ ∂⁺ ^[k] 𝒜 ↔ ∃ t ∈ 𝒜, t ⊆ s ∧ #t + k = #s := by
  induction k generalizing 𝒜 s with
  | zero =>
    refine ⟨fun hs => ⟨s, hs, Subset.refl _, rfl⟩, ?_⟩
    rintro ⟨t, ht, hst, hcard⟩
    rwa [← eq_of_subset_of_card_le hst hcard.ge]
  | succ k ih =>
    simp only [Function.comp_apply, Function.iterate_succ]
    refine ih.trans ?_
    clear ih
    constructor
    · rintro ⟨t, ht, hts, hcardst⟩
      obtain ⟨u, hu, hut, hcardtu⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 ht
      refine ⟨u, hu, hut.trans hts, ?_⟩
      rw [← hcardst, hcardtu, add_right_comm]
      rfl
    · rintro ⟨t, ht, hts, hcard⟩
      obtain ⟨u, htu, hus, hu⟩ := Finset.exists_subsuperset_card_eq hts (Nat.le_add_right _ 1)
        (by lia)
      refine ⟨u, mem_upShadow_iff_exists_mem_card_add_one.2 ⟨t, ht, htu, hu⟩, hus, ?_⟩
      rw [hu, ← hcard, add_right_comm]
      rfl

@[simp] lemma shadow_compls : ∂ 𝒜ᶜˢ = (∂⁺ 𝒜)ᶜˢ := by
  ext s
  simp only [mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]

@[simp] lemma upShadow_compls : ∂⁺ 𝒜ᶜˢ = (∂ 𝒜)ᶜˢ := by
  ext s
  simp only [mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]

end UpShadow

end Finset
