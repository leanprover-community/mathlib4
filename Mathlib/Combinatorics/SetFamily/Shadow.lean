/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import Mathlib.Data.Finset.Grade
import Mathlib.Data.Finset.Sups
import Mathlib.Logic.Function.Iterate

#align_import combinatorics.set_family.shadow from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

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

We define notation in locale `FinsetFamily`:
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


open Finset Nat

variable {α : Type*}

namespace Finset

section Shadow

variable [DecidableEq α] {𝒜 : Finset (Finset α)} {s t : Finset α} {a : α} {k r : ℕ}

/-- The shadow of a set family `𝒜` is all sets we can get by removing one element from any set in
`𝒜`, and the (`k` times) iterated shadow (`shadow^[k]`) is all sets we can get by removing `k`
elements from any set in `𝒜`. -/
def shadow (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.sup fun s => s.image (erase s)
#align finset.shadow Finset.shadow

-- Porting note: added `inherit_doc` to calm linter
@[inherit_doc] scoped[FinsetFamily] notation:max "∂ " => Finset.shadow
-- Porting note: had to open FinsetFamily
open FinsetFamily

/-- The shadow of the empty set is empty. -/
@[simp]
theorem shadow_empty : ∂ (∅ : Finset (Finset α)) = ∅ :=
  rfl
#align finset.shadow_empty Finset.shadow_empty

@[simp] lemma shadow_iterate_empty (k : ℕ) : ∂^[k] (∅ : Finset (Finset α)) = ∅ := by
  induction' k <;> simp [*, shadow_empty]

@[simp]
theorem shadow_singleton_empty : ∂ ({∅} : Finset (Finset α)) = ∅ :=
  rfl
#align finset.shadow_singleton_empty Finset.shadow_singleton_empty

--TODO: Prove `∂ {{a}} = {∅}` quickly using `covers` and `GradeOrder`
/-- The shadow is monotone. -/
@[mono]
theorem shadow_monotone : Monotone (shadow : Finset (Finset α) → Finset (Finset α)) := fun _ _ =>
  sup_mono
#align finset.shadow_monotone Finset.shadow_monotone

/-- `t` is in the shadow of `𝒜` iff there is a `s ∈ 𝒜` from which we can remove one element to
get `t`. -/
lemma mem_shadow_iff : t ∈ ∂ 𝒜 ↔ ∃ s ∈ 𝒜, ∃ a ∈ s, erase s a = t := by
  simp only [shadow, mem_sup, mem_image]
#align finset.mem_shadow_iff Finset.mem_shadow_iff

theorem erase_mem_shadow (hs : s ∈ 𝒜) (ha : a ∈ s) : erase s a ∈ ∂ 𝒜 :=
  mem_shadow_iff.2 ⟨s, hs, a, ha, rfl⟩
#align finset.erase_mem_shadow Finset.erase_mem_shadow

/-- `t ∈ ∂𝒜` iff `t` is exactly one element less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_mem_card_add_one`. -/
lemma mem_shadow_iff_exists_sdiff : t ∈ ∂ 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ (s \ t).card = 1 := by
  simp_rw [mem_shadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]

/-- `t` is in the shadow of `𝒜` iff we can add an element to it so that the resulting finset is in
`𝒜`. -/
lemma mem_shadow_iff_insert_mem : t ∈ ∂ 𝒜 ↔ ∃ a ∉ t, insert a t ∈ 𝒜 := by
  simp_rw [mem_shadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]
  aesop
#align finset.mem_shadow_iff_insert_mem Finset.mem_shadow_iff_insert_mem

/-- `s ∈ ∂ 𝒜` iff `s` is exactly one element less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_sdiff`. -/
lemma mem_shadow_iff_exists_mem_card_add_one :
    t ∈ ∂ 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ s.card = t.card + 1 := by
  refine mem_shadow_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst
#align finset.mem_shadow_iff_exists_mem_card_add_one Finset.mem_shadow_iff_exists_mem_card_add_one

lemma mem_shadow_iterate_iff_exists_card :
    t ∈ ∂^[k] 𝒜 ↔ ∃ u : Finset α, u.card = k ∧ Disjoint t u ∧ t ∪ u ∈ 𝒜 := by
  induction' k with k ih generalizing t
  · simp
  set_option tactic.skipAssignedInstances false in
  simp only [mem_shadow_iff_insert_mem, ih, Function.iterate_succ_apply', card_eq_succ]
  aesop

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something from `𝒜`.

See also `Finset.mem_shadow_iff_exists_mem_card_add`. -/
lemma mem_shadow_iterate_iff_exists_sdiff : t ∈ ∂^[k] 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ (s \ t).card = k := by
  rw [mem_shadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, htu, hsuA⟩
    exact ⟨_, hsuA, subset_union_left _ _, by rw [union_sdiff_cancel_left htu]⟩
  · rintro ⟨s, hs, hts, rfl⟩
    refine ⟨s \ t, rfl, disjoint_sdiff, ?_⟩
    rwa [union_sdiff_self_eq_union, union_eq_right.2 hts]

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`.

See also `Finset.mem_shadow_iterate_iff_exists_sdiff`. -/
lemma mem_shadow_iterate_iff_exists_mem_card_add :
    t ∈ ∂^[k] 𝒜 ↔ ∃ s ∈ 𝒜, t ⊆ s ∧ s.card = t.card + k := by
  refine mem_shadow_iterate_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst
#align finset.mem_shadow_iff_exists_mem_card_add Finset.mem_shadow_iterate_iff_exists_mem_card_add

/-- The shadow of a family of `r`-sets is a family of `r - 1`-sets. -/
protected theorem _root_.Set.Sized.shadow (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂ 𝒜 : Set (Finset α)).Sized (r - 1) := by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_shadow_iff.1 h
  rw [card_erase_of_mem hi, h𝒜 hA]
#align finset.set.sized.shadow Set.Sized.shadow

/-- The `k`-th shadow of a family of `r`-sets is a family of `r - k`-sets. -/
lemma _root_.Set.Sized.shadow_iterate (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂^[k] 𝒜 : Set (Finset α)).Sized (r - k) := by
  simp_rw [Set.Sized, mem_coe, mem_shadow_iterate_iff_exists_sdiff]
  rintro t ⟨s, hs, hts, rfl⟩
  rw [card_sdiff hts, ← h𝒜 hs, Nat.sub_sub_self (card_le_card hts)]

theorem sized_shadow_iff (h : ∅ ∉ 𝒜) :
    (∂ 𝒜 : Set (Finset α)).Sized r ↔ (𝒜 : Set (Finset α)).Sized (r + 1) := by
  refine ⟨fun h𝒜 s hs => ?_, Set.Sized.shadow⟩
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hs h)
  rw [← h𝒜 (erase_mem_shadow hs ha), card_erase_add_one ha]
#align finset.sized_shadow_iff Finset.sized_shadow_iff

/-- Being in the shadow of `𝒜` means we have a superset in `𝒜`. -/
lemma exists_subset_of_mem_shadow (hs : t ∈ ∂ 𝒜) : ∃ s ∈ 𝒜, t ⊆ s :=
  let ⟨t, ht, hst⟩ := mem_shadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hst.1⟩
#align finset.exists_subset_of_mem_shadow Finset.exists_subset_of_mem_shadow

end Shadow

open FinsetFamily

section UpShadow

variable [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {s t : Finset α} {a : α} {k r : ℕ}

/-- The upper shadow of a set family `𝒜` is all sets we can get by adding one element to any set in
`𝒜`, and the (`k` times) iterated upper shadow (`upShadow^[k]`) is all sets we can get by adding
`k` elements from any set in `𝒜`. -/
def upShadow (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.sup fun s => sᶜ.image fun a => insert a s
#align finset.up_shadow Finset.upShadow

-- Porting note: added `inherit_doc` to calm linter
@[inherit_doc] scoped[FinsetFamily] notation:max "∂⁺ " => Finset.upShadow

/-- The upper shadow of the empty set is empty. -/
@[simp]
theorem upShadow_empty : ∂⁺ (∅ : Finset (Finset α)) = ∅ :=
  rfl
#align finset.up_shadow_empty Finset.upShadow_empty

/-- The upper shadow is monotone. -/
@[mono]
theorem upShadow_monotone : Monotone (upShadow : Finset (Finset α) → Finset (Finset α)) :=
  fun _ _ => sup_mono
#align finset.up_shadow_monotone Finset.upShadow_monotone

/-- `t` is in the upper shadow of `𝒜` iff there is a `s ∈ 𝒜` from which we can remove one element
to get `t`. -/
lemma mem_upShadow_iff : t ∈ ∂⁺ 𝒜 ↔ ∃ s ∈ 𝒜, ∃ a ∉ s, insert a s = t := by
  simp_rw [upShadow, mem_sup, mem_image, mem_compl]
#align finset.mem_up_shadow_iff Finset.mem_upShadow_iff

theorem insert_mem_upShadow (hs : s ∈ 𝒜) (ha : a ∉ s) : insert a s ∈ ∂⁺ 𝒜 :=
  mem_upShadow_iff.2 ⟨s, hs, a, ha, rfl⟩
#align finset.insert_mem_up_shadow Finset.insert_mem_upShadow

/-- `t` is in the upper shadow of `𝒜` iff `t` is exactly one element more than something from `𝒜`.

See also `Finset.mem_upShadow_iff_exists_mem_card_add_one`. -/
lemma mem_upShadow_iff_exists_sdiff : t ∈ ∂⁺ 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ (t \ s).card = 1 := by
  simp_rw [mem_upShadow_iff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_insert]

/-- `t` is in the upper shadow of `𝒜` iff we can remove an element from it so that the resulting
finset is in `𝒜`. -/
lemma mem_upShadow_iff_erase_mem : t ∈ ∂⁺ 𝒜 ↔ ∃ a, a ∈ t ∧ erase t a ∈ 𝒜 := by
  simp_rw [mem_upShadow_iff_exists_sdiff, ← covBy_iff_card_sdiff_eq_one, covBy_iff_exists_erase]
  aesop
#align finset.mem_up_shadow_iff_erase_mem Finset.mem_upShadow_iff_erase_mem

/-- `t` is in the upper shadow of `𝒜` iff `t` is exactly one element less than something from `𝒜`.

See also `Finset.mem_upShadow_iff_exists_sdiff`. -/
lemma mem_upShadow_iff_exists_mem_card_add_one :
    t ∈ ∂⁺ 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ t.card = s.card + 1 := by
  refine mem_upShadow_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst
#align finset.mem_up_shadow_iff_exists_mem_card_add_one Finset.mem_upShadow_iff_exists_mem_card_add_one

lemma mem_upShadow_iterate_iff_exists_card :
    t ∈ ∂⁺^[k] 𝒜 ↔ ∃ u : Finset α, u.card = k ∧ u ⊆ t ∧ t \ u ∈ 𝒜 := by
  induction' k with k ih generalizing t
  · simp
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
lemma mem_upShadow_iterate_iff_exists_sdiff :
    t ∈ ∂⁺^[k] 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ (t \ s).card = k := by
  rw [mem_upShadow_iterate_iff_exists_card]
  constructor
  · rintro ⟨u, rfl, hut, htu⟩
    exact ⟨_, htu, sdiff_subset _ _, by rw [sdiff_sdiff_eq_self hut]⟩
  · rintro ⟨s, hs, hst, rfl⟩
    exact ⟨_, rfl, sdiff_subset _ _, by rwa [sdiff_sdiff_eq_self hst]⟩

/-- `t ∈ ∂⁺^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`.

See also `Finset.mem_upShadow_iterate_iff_exists_sdiff`. -/
lemma mem_upShadow_iterate_iff_exists_mem_card_add :
    t ∈ ∂⁺^[k] 𝒜 ↔ ∃ s ∈ 𝒜, s ⊆ t ∧ t.card = s.card + k := by
  refine mem_upShadow_iterate_iff_exists_sdiff.trans <| exists_congr fun t ↦ and_congr_right fun _ ↦
    and_congr_right fun hst ↦ ?_
  rw [card_sdiff hst, tsub_eq_iff_eq_add_of_le, add_comm]
  exact card_mono hst

/-- The upper shadow of a family of `r`-sets is a family of `r + 1`-sets. -/
protected lemma _root_.Set.Sized.upShadow (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂⁺ 𝒜 : Set (Finset α)).Sized (r + 1) := by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_upShadow_iff.1 h
  rw [card_insert_of_not_mem hi, h𝒜 hA]
#align finset.set.sized.up_shadow Set.Sized.upShadow

/-- Being in the upper shadow of `𝒜` means we have a superset in `𝒜`. -/
theorem exists_subset_of_mem_upShadow (hs : s ∈ ∂⁺ 𝒜) : ∃ t ∈ 𝒜, t ⊆ s :=
  let ⟨t, ht, hts, _⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hts⟩
#align finset.exists_subset_of_mem_up_shadow Finset.exists_subset_of_mem_upShadow

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements more than something in `𝒜`. -/
theorem mem_upShadow_iff_exists_mem_card_add :
    s ∈ ∂⁺ ^[k] 𝒜 ↔ ∃ t ∈ 𝒜, t ⊆ s ∧ t.card + k = s.card := by
  induction' k with k ih generalizing 𝒜 s
  · refine ⟨fun hs => ⟨s, hs, Subset.refl _, rfl⟩, ?_⟩
    rintro ⟨t, ht, hst, hcard⟩
    rwa [← eq_of_subset_of_card_le hst hcard.ge]
  simp only [exists_prop, Function.comp_apply, Function.iterate_succ]
  refine ih.trans ?_
  clear ih
  constructor
  · rintro ⟨t, ht, hts, hcardst⟩
    obtain ⟨u, hu, hut, hcardtu⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 ht
    refine ⟨u, hu, hut.trans hts, ?_⟩
    rw [← hcardst, hcardtu, add_right_comm]
    rfl
  · rintro ⟨t, ht, hts, hcard⟩
    obtain ⟨u, htu, hus, hu⟩ :=
      Finset.exists_intermediate_set 1
        (by
          rw [add_comm, ← hcard]
          exact add_le_add_left (succ_le_of_lt (zero_lt_succ _)) _)
        hts
    rw [add_comm] at hu
    refine ⟨u, mem_upShadow_iff_exists_mem_card_add_one.2 ⟨t, ht, htu, hu⟩, hus, ?_⟩
    rw [hu, ← hcard, add_right_comm]
    rfl
#align finset.mem_up_shadow_iff_exists_mem_card_add Finset.mem_upShadow_iff_exists_mem_card_add

@[simp] lemma shadow_compls : ∂ 𝒜ᶜˢ = (∂⁺ 𝒜)ᶜˢ := by
  ext s
  simp only [mem_image, exists_prop, mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]
#align finset.up_shadow_image_compl Finset.shadow_compls

@[simp] lemma upShadow_compls : ∂⁺ 𝒜ᶜˢ = (∂ 𝒜)ᶜˢ := by
  ext s
  simp only [mem_image, exists_prop, mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [← compl_involutive.eq_iff]
#align finset.shadow_image_compl Finset.upShadow_compls

end UpShadow

end Finset
