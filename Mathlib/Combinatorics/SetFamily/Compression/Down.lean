/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Lattice

#align_import combinatorics.set_family.compression.down from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Down-compressions

This file defines down-compression.

Down-compressing `𝒜 : Finset (Finset α)` along `a : α` means removing `a` from the elements of `𝒜`,
when the resulting set is not already in `𝒜`.

## Main declarations

* `Finset.nonMemberSubfamily`: `𝒜.nonMemberSubfamily a` is the subfamily of sets not containing
  `a`.
* `Finset.memberSubfamily`: `𝒜.memberSubfamily a` is the image of the subfamily of sets containing
  `a` under removing `a`.
* `Down.compression`: Down-compression.

## Notation

`𝓓 a 𝒜` is notation for `Down.compress a 𝒜` in locale `SetFamily`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, down-compression
-/


variable {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s : Finset α} {a : α}

namespace Finset

/-- Elements of `𝒜` that do not contain `a`. -/
def nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.filter fun s => a ∉ s
#align finset.non_member_subfamily Finset.nonMemberSubfamily

/-- Image of the elements of `𝒜` which contain `a` under removing `a`. Finsets that do not contain
`a` such that `insert a s ∈ 𝒜`. -/
def memberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (𝒜.filter fun s => a ∈ s).image fun s => erase s a
#align finset.member_subfamily Finset.memberSubfamily

@[simp]
theorem mem_nonMemberSubfamily : s ∈ 𝒜.nonMemberSubfamily a ↔ s ∈ 𝒜 ∧ a ∉ s := by
  simp [nonMemberSubfamily]
#align finset.mem_non_member_subfamily Finset.mem_nonMemberSubfamily

@[simp]
theorem mem_memberSubfamily : s ∈ 𝒜.memberSubfamily a ↔ insert a s ∈ 𝒜 ∧ a ∉ s := by
  simp_rw [memberSubfamily, mem_image, mem_filter]
  refine ⟨?_, fun h => ⟨insert a s, ⟨h.1, by simp⟩, erase_insert h.2⟩⟩
  rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
  rw [insert_erase hs2]
  exact ⟨hs1, not_mem_erase _ _⟩
#align finset.mem_member_subfamily Finset.mem_memberSubfamily

theorem nonMemberSubfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∩ ℬ).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a ∩ ℬ.nonMemberSubfamily a :=
  filter_inter_distrib _ _ _
#align finset.non_member_subfamily_inter Finset.nonMemberSubfamily_inter

theorem memberSubfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∩ ℬ).memberSubfamily a = 𝒜.memberSubfamily a ∩ ℬ.memberSubfamily a := by
  unfold memberSubfamily
  rw [filter_inter_distrib, image_inter_of_injOn _ _ ((erase_injOn' _).mono _)]
  simp
#align finset.member_subfamily_inter Finset.memberSubfamily_inter

theorem nonMemberSubfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∪ ℬ).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a ∪ ℬ.nonMemberSubfamily a :=
  filter_union _ _ _
#align finset.non_member_subfamily_union Finset.nonMemberSubfamily_union

theorem memberSubfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∪ ℬ).memberSubfamily a = 𝒜.memberSubfamily a ∪ ℬ.memberSubfamily a := by
  simp_rw [memberSubfamily, filter_union, image_union]
#align finset.member_subfamily_union Finset.memberSubfamily_union

theorem card_memberSubfamily_add_card_nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) :
    (𝒜.memberSubfamily a).card + (𝒜.nonMemberSubfamily a).card = 𝒜.card := by
  rw [memberSubfamily, nonMemberSubfamily, card_image_of_injOn]
  · conv_rhs => rw [← filter_card_add_filter_neg_card_eq_card (fun s => (a ∈ s))]
  · apply (erase_injOn' _).mono
    simp
#align finset.card_member_subfamily_add_card_non_member_subfamily Finset.card_memberSubfamily_add_card_nonMemberSubfamily

theorem memberSubfamily_union_nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) :
    𝒜.memberSubfamily a ∪ 𝒜.nonMemberSubfamily a = 𝒜.image fun s => s.erase a := by
  ext s
  simp only [mem_union, mem_memberSubfamily, mem_nonMemberSubfamily, mem_image, exists_prop]
  constructor
  · rintro (h | h)
    · exact ⟨_, h.1, erase_insert h.2⟩
    · exact ⟨_, h.1, erase_eq_of_not_mem h.2⟩
  · rintro ⟨s, hs, rfl⟩
    by_cases ha : a ∈ s
    · exact Or.inl ⟨by rwa [insert_erase ha], not_mem_erase _ _⟩
    · exact Or.inr ⟨by rwa [erase_eq_of_not_mem ha], not_mem_erase _ _⟩
#align finset.member_subfamily_union_non_member_subfamily Finset.memberSubfamily_union_nonMemberSubfamily

@[simp]
theorem memberSubfamily_memberSubfamily : (𝒜.memberSubfamily a).memberSubfamily a = ∅ := by
  ext
  simp
#align finset.member_subfamily_member_subfamily Finset.memberSubfamily_memberSubfamily

@[simp]
theorem memberSubfamily_nonMemberSubfamily : (𝒜.nonMemberSubfamily a).memberSubfamily a = ∅ := by
  ext
  simp
#align finset.member_subfamily_non_member_subfamily Finset.memberSubfamily_nonMemberSubfamily

@[simp]
theorem nonMemberSubfamily_memberSubfamily :
    (𝒜.memberSubfamily a).nonMemberSubfamily a = 𝒜.memberSubfamily a := by
  ext
  simp
#align finset.non_member_subfamily_member_subfamily Finset.nonMemberSubfamily_memberSubfamily

@[simp]
theorem nonMemberSubfamily_nonMemberSubfamily :
    (𝒜.nonMemberSubfamily a).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a := by
  ext
  simp
#align finset.non_member_subfamily_non_member_subfamily Finset.nonMemberSubfamily_nonMemberSubfamily

lemma memberSubfamily_image_insert (h𝒜 : ∀ s ∈ 𝒜, a ∉ s) :
    (𝒜.image <| insert a).memberSubfamily a = 𝒜 := by
  ext s
  simp only [mem_memberSubfamily, mem_image]
  refine ⟨?_, fun hs ↦ ⟨⟨s, hs, rfl⟩, h𝒜 _ hs⟩⟩
  rintro ⟨⟨t, ht, hts⟩, hs⟩
  rwa [← insert_erase_invOn.2.injOn (h𝒜 _ ht) hs hts]

@[simp] lemma nonMemberSubfamily_image_insert : (𝒜.image <| insert a).nonMemberSubfamily a = ∅ := by
  simp [eq_empty_iff_forall_not_mem]

@[simp] lemma memberSubfamily_image_erase : (𝒜.image (erase · a)).memberSubfamily a = ∅ := by
  simp [eq_empty_iff_forall_not_mem,
    (ne_of_mem_of_not_mem' (mem_insert_self _ _) (not_mem_erase _ _)).symm]

lemma image_insert_memberSubfamily (𝒜 : Finset (Finset α)) (a : α) :
    (𝒜.memberSubfamily a).image (insert a) = 𝒜.filter (a ∈ ·) := by
  ext s
  simp only [mem_memberSubfamily, mem_image, mem_filter]
  refine ⟨?_, fun ⟨hs, ha⟩ ↦ ⟨erase s a, ⟨?_, not_mem_erase _ _⟩, insert_erase ha⟩⟩
  · rintro ⟨s, ⟨hs, -⟩, rfl⟩
    exact ⟨hs, mem_insert_self _ _⟩
  · rwa [insert_erase ha]

/-- Induction principle for finset families. To prove a statement for every finset family,
it suffices to prove it for
* the empty finset family.
* the finset family which only contains the empty finset.
* `ℬ ∪ {s ∪ {a} | s ∈ 𝒞}` assuming the property for `ℬ` and `𝒞`, where `a` is an element of the
  ground type and `𝒜` and `ℬ` are families of finsets not containing `a`.
  Note that instead of giving `ℬ` and `𝒞`, the `subfamily` case gives you
  `𝒜 = ℬ ∪ {s ∪ {a} | s ∈ 𝒞}`, so that `ℬ = 𝒜.nonMemberSubfamily` and `𝒞 = 𝒜.memberSubfamily`.

This is a way of formalising induction on `n` where `𝒜` is a finset family on `n` elements.

See also `Finset.family_induction_on.`-/
@[elab_as_elim]
lemma memberFamily_induction_on {p : Finset (Finset α) → Prop}
    (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {∅})
    (subfamily : ∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      p (𝒜.nonMemberSubfamily a) → p (𝒜.memberSubfamily a) → p 𝒜) : p 𝒜 := by
  set u := 𝒜.sup id
  have hu : ∀ s ∈ 𝒜, s ⊆ u := fun s ↦ le_sup (f := id)
  clear_value u
  induction' u using Finset.induction with a u _ ih generalizing 𝒜
  · simp_rw [subset_empty] at hu
    rw [← subset_singleton_iff', subset_singleton_iff] at hu
    obtain rfl | rfl := hu <;> assumption
  refine subfamily a (ih _ ?_) (ih _ ?_)
  · simp only [mem_nonMemberSubfamily, and_imp]
    exact fun s hs has ↦ (subset_insert_iff_of_not_mem has).1 <| hu _ hs
  · simp only [mem_memberSubfamily, and_imp]
    exact fun s hs ha ↦ (insert_subset_insert_iff ha).1 <| hu _ hs

/-- Induction principle for finset families. To prove a statement for every finset family,
it suffices to prove it for
* the empty finset family.
* the finset family which only contains the empty finset.
* `{s ∪ {a} | s ∈ 𝒜}` assuming the property for `𝒜` a family of finsets not containing `a`.
* `ℬ ∪ 𝒞` assuming the property for `ℬ` and `𝒞`, where `a` is an element of the ground type and
  `ℬ`is a family of finsets not containing `a` and `𝒞` a family of finsets containing `a`.
  Note that instead of giving `ℬ` and `𝒞`, the `subfamily` case gives you `𝒜 = ℬ ∪ 𝒞`, so that
  `ℬ = 𝒜.filter (a ∉ ·)` and `𝒞 = 𝒜.filter (a ∈ ·)`.

This is a way of formalising induction on `n` where `𝒜` is a finset family on `n` elements.

See also `Finset.memberFamily_induction_on.`-/
@[elab_as_elim]
protected lemma family_induction_on {p : Finset (Finset α) → Prop}
    (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {∅})
    (image_insert : ∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      (∀ s ∈ 𝒜, a ∉ s) → p 𝒜 → p (𝒜.image <| insert a))
    (subfamily : ∀ (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      p (𝒜.filter (a ∉ ·)) → p (𝒜.filter (a ∈ ·)) → p 𝒜) : p 𝒜 := by
  refine memberFamily_induction_on 𝒜 empty singleton_empty fun a 𝒜 h𝒜₀ h𝒜₁ ↦ subfamily a h𝒜₀ ?_
  rw [← image_insert_memberSubfamily]
  exact image_insert _ (by simp) h𝒜₁

end Finset

open Finset

-- The namespace is here to distinguish from other compressions.
namespace Down

/-- `a`-down-compressing `𝒜` means removing `a` from the elements of `𝒜` that contain it, when the
resulting Finset is not already in `𝒜`. -/
def compression (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (𝒜.filter fun s => erase s a ∈ 𝒜).disjUnion
      ((𝒜.image fun s => erase s a).filter fun s => s ∉ 𝒜) <|
    disjoint_left.2 fun s h₁ h₂ => by
      have := (mem_filter.1 h₂).2
      exact this (mem_filter.1 h₁).1
#align down.compression Down.compression

@[inherit_doc]
scoped[FinsetFamily] notation "𝓓 " => Down.compression
-- Porting note: had to open this
open FinsetFamily

/-- `a` is in the down-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
theorem mem_compression : s ∈ 𝓓 a 𝒜 ↔ s ∈ 𝒜 ∧ s.erase a ∈ 𝒜 ∨ s ∉ 𝒜 ∧ insert a s ∈ 𝒜 := by
  simp_rw [compression, mem_disjUnion, mem_filter, mem_image, and_comm (a := (¬ s ∈ 𝒜))]
  refine
    or_congr_right
      (and_congr_left fun hs =>
        ⟨?_, fun h => ⟨_, h, erase_insert <| insert_ne_self.1 <| ne_of_mem_of_not_mem h hs⟩⟩)
  rintro ⟨t, ht, rfl⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem ht hs).symm)]
#align down.mem_compression Down.mem_compression

theorem erase_mem_compression (hs : s ∈ 𝒜) : s.erase a ∈ 𝓓 a 𝒜 := by
  simp_rw [mem_compression, erase_idem, and_self_iff]
  refine (em _).imp_right fun h => ⟨h, ?_⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem hs h).symm)]
#align down.erase_mem_compression Down.erase_mem_compression

-- This is a special case of `erase_mem_compression` once we have `compression_idem`.
theorem erase_mem_compression_of_mem_compression : s ∈ 𝓓 a 𝒜 → s.erase a ∈ 𝓓 a 𝒜 := by
  simp_rw [mem_compression, erase_idem]
  refine Or.imp (fun h => ⟨h.2, h.2⟩) fun h => ?_
  rwa [erase_eq_of_not_mem (insert_ne_self.1 <| ne_of_mem_of_not_mem h.2 h.1)]
#align down.erase_mem_compression_of_mem_compression Down.erase_mem_compression_of_mem_compression

theorem mem_compression_of_insert_mem_compression (h : insert a s ∈ 𝓓 a 𝒜) : s ∈ 𝓓 a 𝒜 := by
  by_cases ha : a ∈ s
  · rwa [insert_eq_of_mem ha] at h
  · rw [← erase_insert ha]
    exact erase_mem_compression_of_mem_compression h
#align down.mem_compression_of_insert_mem_compression Down.mem_compression_of_insert_mem_compression

/-- Down-compressing a family is idempotent. -/
@[simp]
theorem compression_idem (a : α) (𝒜 : Finset (Finset α)) : 𝓓 a (𝓓 a 𝒜) = 𝓓 a 𝒜 := by
  ext s
  refine mem_compression.trans ⟨?_, fun h => Or.inl ⟨h, erase_mem_compression_of_mem_compression h⟩⟩
  rintro (h | h)
  · exact h.1
  · cases h.1 (mem_compression_of_insert_mem_compression h.2)
#align down.compression_idem Down.compression_idem

/-- Down-compressing a family doesn't change its size. -/
@[simp]
theorem card_compression (a : α) (𝒜 : Finset (Finset α)) : (𝓓 a 𝒜).card = 𝒜.card := by
  rw [compression, card_disjUnion, filter_image,
    card_image_of_injOn ((erase_injOn' _).mono fun s hs => _), ← card_union_of_disjoint]
  · conv_rhs => rw [← filter_union_filter_neg_eq (fun s => (erase s a ∈ 𝒜)) 𝒜]
  · exact disjoint_filter_filter_neg 𝒜 𝒜 (fun s => (erase s a ∈ 𝒜))
  intro s hs
  rw [mem_coe, mem_filter] at hs
  exact not_imp_comm.1 erase_eq_of_not_mem (ne_of_mem_of_not_mem hs.1 hs.2).symm
#align down.card_compression Down.card_compression

end Down
