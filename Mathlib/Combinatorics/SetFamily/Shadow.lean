/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
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

/-- `s` is in the shadow of `𝒜` iff there is a `t ∈ 𝒜` from which we can remove one element to
get `s`. -/
theorem mem_shadow_iff : s ∈ ∂ 𝒜 ↔ ∃ t ∈ 𝒜, ∃ a ∈ t, erase t a = s := by
  simp only [shadow, mem_sup, mem_image]
#align finset.mem_shadow_iff Finset.mem_shadow_iff

theorem erase_mem_shadow (hs : s ∈ 𝒜) (ha : a ∈ s) : erase s a ∈ ∂ 𝒜 :=
  mem_shadow_iff.2 ⟨s, hs, a, ha, rfl⟩
#align finset.erase_mem_shadow Finset.erase_mem_shadow

/-- `t` is in the shadow of `𝒜` iff we can add an element to it so that the resulting finset is in
`𝒜`. -/
theorem mem_shadow_iff_insert_mem : s ∈ ∂ 𝒜 ↔ ∃ (a : _) (_ : a ∉ s), insert a s ∈ 𝒜 := by
  refine' mem_shadow_iff.trans ⟨_, _⟩
  · rintro ⟨s, hs, a, ha, rfl⟩
    refine' ⟨a, not_mem_erase a s, _⟩
    rwa [insert_erase ha]
  · rintro ⟨a, ha, hs⟩
    exact ⟨insert a s, hs, a, mem_insert_self _ _, erase_insert ha⟩
#align finset.mem_shadow_iff_insert_mem Finset.mem_shadow_iff_insert_mem

/-- The shadow of a family of `r`-sets is a family of `r - 1`-sets. -/
protected theorem Set.Sized.shadow (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂ 𝒜 : Set (Finset α)).Sized (r - 1) := by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_shadow_iff.1 h
  rw [card_erase_of_mem hi, h𝒜 hA]
#align finset.set.sized.shadow Finset.Set.Sized.shadow

theorem sized_shadow_iff (h : ∅ ∉ 𝒜) :
    (∂ 𝒜 : Set (Finset α)).Sized r ↔ (𝒜 : Set (Finset α)).Sized (r + 1) := by
  refine' ⟨fun h𝒜 s hs => _, Set.Sized.shadow⟩
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hs h)
  rw [← h𝒜 (erase_mem_shadow hs ha), card_erase_add_one ha]
#align finset.sized_shadow_iff Finset.sized_shadow_iff

/-- `s ∈ ∂ 𝒜` iff `s` is exactly one element less than something from `𝒜` -/
theorem mem_shadow_iff_exists_mem_card_add_one :
    s ∈ ∂ 𝒜 ↔ ∃ t ∈ 𝒜, s ⊆ t ∧ t.card = s.card + 1 := by
  refine' mem_shadow_iff_insert_mem.trans ⟨_, _⟩
  · rintro ⟨a, ha, hs⟩
    exact ⟨insert a s, hs, subset_insert _ _, card_insert_of_not_mem ha⟩
  · rintro ⟨t, ht, hst, h⟩
    obtain ⟨a, ha⟩ : ∃ a, t \ s = {a} :=
      card_eq_one.1 (by rw [card_sdiff hst, h, add_tsub_cancel_left])
    exact
      ⟨a, fun hat => not_mem_sdiff_of_mem_right hat (ha.superset <| mem_singleton_self a),
       by rwa [insert_eq a s, ← ha, sdiff_union_of_subset hst]⟩
#align finset.mem_shadow_iff_exists_mem_card_add_one Finset.mem_shadow_iff_exists_mem_card_add_one

/-- Being in the shadow of `𝒜` means we have a superset in `𝒜`. -/
theorem exists_subset_of_mem_shadow (hs : s ∈ ∂ 𝒜) : ∃ t ∈ 𝒜, s ⊆ t :=
  let ⟨t, ht, hst⟩ := mem_shadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hst.1⟩
#align finset.exists_subset_of_mem_shadow Finset.exists_subset_of_mem_shadow

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`. -/
theorem mem_shadow_iff_exists_mem_card_add :
    s ∈ ∂ ^[k] 𝒜 ↔ ∃ t ∈ 𝒜, s ⊆ t ∧ t.card = s.card + k := by
  induction' k with k ih generalizing 𝒜 s
  · refine' ⟨fun hs => ⟨s, hs, Subset.refl _, rfl⟩, _⟩
    rintro ⟨t, ht, hst, hcard⟩
    rwa [eq_of_subset_of_card_le hst hcard.le]
  simp only [exists_prop, Function.comp_apply, Function.iterate_succ]
  refine' ih.trans _
  clear ih
  constructor
  · rintro ⟨t, ht, hst, hcardst⟩
    obtain ⟨u, hu, htu, hcardtu⟩ := mem_shadow_iff_exists_mem_card_add_one.1 ht
    refine' ⟨u, hu, hst.trans htu, _⟩
    rw [hcardtu, hcardst]
    rfl
  · rintro ⟨t, ht, hst, hcard⟩
    obtain ⟨u, hsu, hut, hu⟩ :=
      Finset.exists_intermediate_set k
        (by
          rw [add_comm, hcard]
          exact le_succ _)
        hst
    rw [add_comm] at hu
    refine' ⟨u, mem_shadow_iff_exists_mem_card_add_one.2 ⟨t, ht, hut, _⟩, hsu, hu⟩
    rw [hcard, hu]
    rfl
#align finset.mem_shadow_iff_exists_mem_card_add Finset.mem_shadow_iff_exists_mem_card_add

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

/-- `s` is in the upper shadow of `𝒜` iff there is a `t ∈ 𝒜` from which we can remove one element
to get `s`. -/
theorem mem_upShadow_iff : s ∈ ∂⁺ 𝒜 ↔ ∃ t ∈ 𝒜, ∃ (a : _) (_ : a ∉ t), insert a t = s := by
  simp_rw [upShadow, mem_sup, mem_image, exists_prop, mem_compl]
#align finset.mem_up_shadow_iff Finset.mem_upShadow_iff

theorem insert_mem_upShadow (hs : s ∈ 𝒜) (ha : a ∉ s) : insert a s ∈ ∂⁺ 𝒜 :=
  mem_upShadow_iff.2 ⟨s, hs, a, ha, rfl⟩
#align finset.insert_mem_up_shadow Finset.insert_mem_upShadow

/-- The upper shadow of a family of `r`-sets is a family of `r + 1`-sets. -/
protected theorem Set.Sized.upShadow (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (∂⁺ 𝒜 : Set (Finset α)).Sized (r + 1) := by
  intro A h
  obtain ⟨A, hA, i, hi, rfl⟩ := mem_upShadow_iff.1 h
  rw [card_insert_of_not_mem hi, h𝒜 hA]
#align finset.set.sized.up_shadow Finset.Set.Sized.upShadow

/-- `t` is in the upper shadow of `𝒜` iff we can remove an element from it so that the resulting
finset is in `𝒜`. -/
theorem mem_upShadow_iff_erase_mem : s ∈ ∂⁺ 𝒜 ↔ ∃ a ∈ s, s.erase a ∈ 𝒜 := by
  refine' mem_upShadow_iff.trans ⟨_, _⟩
  · rintro ⟨s, hs, a, ha, rfl⟩
    refine' ⟨a, mem_insert_self a s, _⟩
    rwa [erase_insert ha]
  · rintro ⟨a, ha, hs⟩
    exact ⟨s.erase a, hs, a, not_mem_erase _ _, insert_erase ha⟩
#align finset.mem_up_shadow_iff_erase_mem Finset.mem_upShadow_iff_erase_mem

/-- `s ∈ ∂⁺ 𝒜` iff `s` is exactly one element less than something from `𝒜`. -/
theorem mem_upShadow_iff_exists_mem_card_add_one :
    s ∈ ∂⁺ 𝒜 ↔ ∃ t ∈ 𝒜, t ⊆ s ∧ t.card + 1 = s.card := by
  refine' mem_upShadow_iff_erase_mem.trans ⟨_, _⟩
  · rintro ⟨a, ha, hs⟩
    exact ⟨s.erase a, hs, erase_subset _ _, card_erase_add_one ha⟩
  · rintro ⟨t, ht, hts, h⟩
    obtain ⟨a, ha⟩ : ∃ a, s \ t = {a} :=
      card_eq_one.1 (by rw [card_sdiff hts, ← h, add_tsub_cancel_left])
    refine' ⟨a, sdiff_subset _ _ ((ha.ge : _ ⊆ _) <| mem_singleton_self a), _⟩
    rwa [← sdiff_singleton_eq_erase, ← ha, sdiff_sdiff_eq_self hts]
#align finset.mem_up_shadow_iff_exists_mem_card_add_one Finset.mem_upShadow_iff_exists_mem_card_add_one

/-- Being in the upper shadow of `𝒜` means we have a superset in `𝒜`. -/
theorem exists_subset_of_mem_upShadow (hs : s ∈ ∂⁺ 𝒜) : ∃ t ∈ 𝒜, t ⊆ s :=
  let ⟨t, ht, hts, _⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 hs
  ⟨t, ht, hts⟩
#align finset.exists_subset_of_mem_up_shadow Finset.exists_subset_of_mem_upShadow

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements more than something in `𝒜`. -/
theorem mem_upShadow_iff_exists_mem_card_add :
    s ∈ ∂⁺ ^[k] 𝒜 ↔ ∃ t ∈ 𝒜, t ⊆ s ∧ t.card + k = s.card := by
  induction' k with k ih generalizing 𝒜 s
  · refine' ⟨fun hs => ⟨s, hs, Subset.refl _, rfl⟩, _⟩
    rintro ⟨t, ht, hst, hcard⟩
    rwa [← eq_of_subset_of_card_le hst hcard.ge]
  simp only [exists_prop, Function.comp_apply, Function.iterate_succ]
  refine' ih.trans _
  clear ih
  constructor
  · rintro ⟨t, ht, hts, hcardst⟩
    obtain ⟨u, hu, hut, hcardtu⟩ := mem_upShadow_iff_exists_mem_card_add_one.1 ht
    refine' ⟨u, hu, hut.trans hts, _⟩
    rw [← hcardst, ← hcardtu, add_right_comm]
    rfl
  · rintro ⟨t, ht, hts, hcard⟩
    obtain ⟨u, htu, hus, hu⟩ :=
      Finset.exists_intermediate_set 1
        (by
          rw [add_comm, ← hcard]
          exact add_le_add_left (succ_le_of_lt (zero_lt_succ _)) _)
        hts
    rw [add_comm] at hu
    refine' ⟨u, mem_upShadow_iff_exists_mem_card_add_one.2 ⟨t, ht, htu, hu.symm⟩, hus, _⟩
    rw [hu, ← hcard, add_right_comm]
    rfl
#align finset.mem_up_shadow_iff_exists_mem_card_add Finset.mem_upShadow_iff_exists_mem_card_add

@[simp] lemma shadow_compls : ∂ 𝒜ᶜˢ = (∂⁺ 𝒜)ᶜˢ := by
  ext s
  simp only [mem_image, exists_prop, mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [←compl_involutive.eq_iff]
#align finset.up_shadow_image_compl Finset.shadow_compls

@[simp] lemma upShadow_compls : ∂⁺ 𝒜ᶜˢ = (∂ 𝒜)ᶜˢ := by
  ext s
  simp only [mem_image, exists_prop, mem_shadow_iff, mem_upShadow_iff, mem_compls]
  refine (compl_involutive.toPerm _).exists_congr_left.trans ?_
  simp [←compl_involutive.eq_iff]
#align finset.shadow_image_compl Finset.upShadow_compls

end UpShadow

end Finset
