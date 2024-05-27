/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Set.Finite
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Set.Subsingleton

#align_import data.set.countable from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

/-!
# Countable sets

In this file we define `Set.Countable s` as `Countable s`
and prove basic properties of this definition.

Note that this definition does not provide a computable encoding.
For a noncomputable conversion to `Encodable s`, use `Set.Countable.nonempty_encodable`.

## Keywords

sets, countable set
-/

noncomputable section

open scoped Classical
open Function Set Encodable

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

namespace Set

/-- A set `s` is countable if the corresponding subtype is countable,
i.e., there exists an injective map `f : s → ℕ`.

Note that this is an abbreviation, so `hs : Set.Countable s` in the proof context
is the same as an instance `Countable s`.
For a constructive version, see `Encodable`.
-/
protected def Countable (s : Set α) : Prop := Countable s
#align set.countable Set.Countable

@[simp]
theorem countable_coe_iff {s : Set α} : Countable s ↔ s.Countable := .rfl
#align set.countable_coe_iff Set.countable_coe_iff

/-- Prove `Set.Countable` from a `Countable` instance on the subtype. -/
theorem to_countable (s : Set α) [Countable s] : s.Countable := ‹_›
#align set.to_countable Set.to_countable

/-- Restate `Set.Countable` as a `Countable` instance. -/
alias ⟨_root_.Countable.to_set, Countable.to_subtype⟩ := countable_coe_iff
#align countable.to_set Countable.to_set
#align set.countable.to_subtype Set.Countable.to_subtype

protected theorem countable_iff_exists_injective {s : Set α} :
    s.Countable ↔ ∃ f : s → ℕ, Injective f :=
  countable_iff_exists_injective s
#align set.countable_iff_exists_injective Set.countable_iff_exists_injective

/-- A set `s : Set α` is countable if and only if there exists a function `α → ℕ` injective
on `s`. -/
theorem countable_iff_exists_injOn {s : Set α} : s.Countable ↔ ∃ f : α → ℕ, InjOn f s :=
  Set.countable_iff_exists_injective.trans exists_injOn_iff_injective.symm
#align set.countable_iff_exists_inj_on Set.countable_iff_exists_injOn

theorem countable_iff_nonempty_encodable {s : Set α} : s.Countable ↔ Nonempty (Encodable s) :=
  Encodable.nonempty_encodable.symm

alias ⟨Countable.nonempty_encodable, _⟩ := countable_iff_nonempty_encodable

/-- Convert `Set.Countable s` to `Encodable s` (noncomputable). -/
protected def Countable.toEncodable {s : Set α} (hs : s.Countable) : Encodable s :=
  Classical.choice hs.nonempty_encodable
#align set.countable.to_encodable Set.Countable.toEncodable

section Enumerate

/-- Noncomputably enumerate elements in a set. The `default` value is used to extend the domain to
all of `ℕ`. -/
def enumerateCountable {s : Set α} (h : s.Countable) (default : α) : ℕ → α := fun n =>
  match @Encodable.decode s h.toEncodable n with
  | some y => y
  | none => default
#align set.enumerate_countable Set.enumerateCountable

theorem subset_range_enumerate {s : Set α} (h : s.Countable) (default : α) :
    s ⊆ range (enumerateCountable h default) := fun x hx =>
  ⟨@Encodable.encode s h.toEncodable ⟨x, hx⟩, by
    letI := h.toEncodable
    simp [enumerateCountable, Encodable.encodek]⟩
#align set.subset_range_enumerate Set.subset_range_enumerate

lemma range_enumerateCountable_subset {s : Set α} (h : s.Countable) (default : α) :
    range (enumerateCountable h default) ⊆ insert default s := by
  refine range_subset_iff.mpr (fun n ↦ ?_)
  rw [enumerateCountable]
  match @decode s (Countable.toEncodable h) n with
  | none => exact mem_insert _ _
  | some val => simp

lemma range_enumerateCountable_of_mem {s : Set α} (h : s.Countable) {default : α}
    (h_mem : default ∈ s) :
    range (enumerateCountable h default) = s :=
  subset_antisymm ((range_enumerateCountable_subset h _).trans_eq (insert_eq_of_mem h_mem))
    (subset_range_enumerate h default)

lemma enumerateCountable_mem {s : Set α} (h : s.Countable) {default : α} (h_mem : default ∈ s)
    (n : ℕ) :
    enumerateCountable h default n ∈ s := by
  conv_rhs => rw [← range_enumerateCountable_of_mem h h_mem]
  exact mem_range_self n

end Enumerate

theorem Countable.mono {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) (hs : s₂.Countable) : s₁.Countable :=
  have := hs.to_subtype; (inclusion_injective h).countable
#align set.countable.mono Set.Countable.mono

theorem countable_range [Countable ι] (f : ι → β) : (range f).Countable :=
  surjective_onto_range.countable.to_set
#align set.countable_range Set.countable_range

theorem countable_iff_exists_subset_range [Nonempty α] {s : Set α} :
    s.Countable ↔ ∃ f : ℕ → α, s ⊆ range f :=
  ⟨fun h => by
    inhabit α
    exact ⟨enumerateCountable h default, subset_range_enumerate _ _⟩, fun ⟨f, hsf⟩ =>
    (countable_range f).mono hsf⟩
#align set.countable_iff_exists_subset_range Set.countable_iff_exists_subset_range

/-- A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
protected theorem countable_iff_exists_surjective {s : Set α} (hs : s.Nonempty) :
    s.Countable ↔ ∃ f : ℕ → s, Surjective f :=
  @countable_iff_exists_surjective s hs.to_subtype
#align set.countable_iff_exists_surjective Set.countable_iff_exists_surjective

alias ⟨Countable.exists_surjective, _⟩ := Set.countable_iff_exists_surjective
#align set.countable.exists_surjective Set.Countable.exists_surjective

theorem countable_univ [Countable α] : (univ : Set α).Countable :=
  to_countable univ
#align set.countable_univ Set.countable_univ

theorem countable_univ_iff : (univ : Set α).Countable ↔ Countable α :=
  countable_coe_iff.symm.trans (Equiv.Set.univ _).countable_iff

/-- If `s : Set α` is a nonempty countable set, then there exists a map
`f : ℕ → α` such that `s = range f`. -/
theorem Countable.exists_eq_range {s : Set α} (hc : s.Countable) (hs : s.Nonempty) :
    ∃ f : ℕ → α, s = range f := by
  rcases hc.exists_surjective hs with ⟨f, hf⟩
  refine ⟨(↑) ∘ f, ?_⟩
  rw [hf.range_comp, Subtype.range_coe]
#align set.countable.exists_eq_range Set.Countable.exists_eq_range

@[simp] theorem countable_empty : (∅ : Set α).Countable := to_countable _
#align set.countable_empty Set.countable_empty

@[simp] theorem countable_singleton (a : α) : ({a} : Set α).Countable := to_countable _
#align set.countable_singleton Set.countable_singleton

theorem Countable.image {s : Set α} (hs : s.Countable) (f : α → β) : (f '' s).Countable := by
  rw [image_eq_range]
  have := hs.to_subtype
  apply countable_range
#align set.countable.image Set.Countable.image

theorem MapsTo.countable_of_injOn {s : Set α} {t : Set β} {f : α → β} (hf : MapsTo f s t)
    (hf' : InjOn f s) (ht : t.Countable) : s.Countable :=
  have := ht.to_subtype
  have : Injective (hf.restrict f s t) := (injOn_iff_injective.1 hf').codRestrict _
  this.countable
#align set.maps_to.countable_of_inj_on Set.MapsTo.countable_of_injOn

theorem Countable.preimage_of_injOn {s : Set β} (hs : s.Countable) {f : α → β}
    (hf : InjOn f (f ⁻¹' s)) : (f ⁻¹' s).Countable :=
  (mapsTo_preimage f s).countable_of_injOn hf hs
#align set.countable.preimage_of_inj_on Set.Countable.preimage_of_injOn

protected theorem Countable.preimage {s : Set β} (hs : s.Countable) {f : α → β} (hf : Injective f) :
    (f ⁻¹' s).Countable :=
  hs.preimage_of_injOn (hf.injOn _)
#align set.countable.preimage Set.Countable.preimage

theorem exists_seq_iSup_eq_top_iff_countable [CompleteLattice α] {p : α → Prop} (h : ∃ x, p x) :
    (∃ s : ℕ → α, (∀ n, p (s n)) ∧ ⨆ n, s n = ⊤) ↔
      ∃ S : Set α, S.Countable ∧ (∀ s ∈ S, p s) ∧ sSup S = ⊤ := by
  constructor
  · rintro ⟨s, hps, hs⟩
    refine ⟨range s, countable_range s, forall_mem_range.2 hps, ?_⟩
    rwa [sSup_range]
  · rintro ⟨S, hSc, hps, hS⟩
    rcases eq_empty_or_nonempty S with (rfl | hne)
    · rw [sSup_empty] at hS
      haveI := subsingleton_of_bot_eq_top hS
      rcases h with ⟨x, hx⟩
      exact ⟨fun _ => x, fun _ => hx, Subsingleton.elim _ _⟩
    · rcases (Set.countable_iff_exists_surjective hne).1 hSc with ⟨s, hs⟩
      refine ⟨fun n => s n, fun n => hps _ (s n).coe_prop, ?_⟩
      rwa [hs.iSup_comp, ← sSup_eq_iSup']
#align set.exists_seq_supr_eq_top_iff_countable Set.exists_seq_iSup_eq_top_iff_countable

theorem exists_seq_cover_iff_countable {p : Set α → Prop} (h : ∃ s, p s) :
    (∃ s : ℕ → Set α, (∀ n, p (s n)) ∧ ⋃ n, s n = univ) ↔
      ∃ S : Set (Set α), S.Countable ∧ (∀ s ∈ S, p s) ∧ ⋃₀ S = univ :=
  exists_seq_iSup_eq_top_iff_countable h
#align set.exists_seq_cover_iff_countable Set.exists_seq_cover_iff_countable

theorem countable_of_injective_of_countable_image {s : Set α} {f : α → β} (hf : InjOn f s)
    (hs : (f '' s).Countable) : s.Countable :=
  (mapsTo_image _ _).countable_of_injOn hf hs
#align set.countable_of_injective_of_countable_image Set.countable_of_injective_of_countable_image

theorem countable_iUnion {t : ι → Set α} [Countable ι] (ht : ∀ i, (t i).Countable) :
    (⋃ i, t i).Countable := by
  have := fun i ↦ (ht i).to_subtype
  rw [iUnion_eq_range_psigma]
  apply countable_range
#align set.countable_Union Set.countable_iUnion

@[simp]
theorem countable_iUnion_iff [Countable ι] {t : ι → Set α} :
    (⋃ i, t i).Countable ↔ ∀ i, (t i).Countable :=
  ⟨fun h _ => h.mono <| subset_iUnion _ _, countable_iUnion⟩
#align set.countable_Union_iff Set.countable_iUnion_iff

theorem Countable.biUnion_iff {s : Set α} {t : ∀ a ∈ s, Set β} (hs : s.Countable) :
    (⋃ a ∈ s, t a ‹_›).Countable ↔ ∀ a (ha : a ∈ s), (t a ha).Countable := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion, countable_iUnion_iff, SetCoe.forall']
#align set.countable.bUnion_iff Set.Countable.biUnion_iff

theorem Countable.sUnion_iff {s : Set (Set α)} (hs : s.Countable) :
    (⋃₀ s).Countable ↔ ∀ a ∈ s, a.Countable := by rw [sUnion_eq_biUnion, hs.biUnion_iff]
#align set.countable.sUnion_iff Set.Countable.sUnion_iff

alias ⟨_, Countable.biUnion⟩ := Countable.biUnion_iff
#align set.countable.bUnion Set.Countable.biUnion

alias ⟨_, Countable.sUnion⟩ := Countable.sUnion_iff
#align set.countable.sUnion Set.Countable.sUnion

@[simp]
theorem countable_union {s t : Set α} : (s ∪ t).Countable ↔ s.Countable ∧ t.Countable := by
  simp [union_eq_iUnion, and_comm]
#align set.countable_union Set.countable_union

theorem Countable.union {s t : Set α} (hs : s.Countable) (ht : t.Countable) : (s ∪ t).Countable :=
  countable_union.2 ⟨hs, ht⟩
#align set.countable.union Set.Countable.union

theorem Countable.of_diff {s t : Set α} (h : (s \ t).Countable) (ht : t.Countable) : s.Countable :=
  (h.union ht).mono (subset_diff_union _ _)

@[simp]
theorem countable_insert {s : Set α} {a : α} : (insert a s).Countable ↔ s.Countable := by
  simp only [insert_eq, countable_union, countable_singleton, true_and_iff]
#align set.countable_insert Set.countable_insert

protected theorem Countable.insert {s : Set α} (a : α) (h : s.Countable) : (insert a s).Countable :=
  countable_insert.2 h
#align set.countable.insert Set.Countable.insert

theorem Finite.countable {s : Set α} (hs : s.Finite) : s.Countable :=
  have := hs.to_subtype; s.to_countable
#align set.finite.countable Set.Finite.countable

@[nontriviality]
theorem Countable.of_subsingleton [Subsingleton α] (s : Set α) : s.Countable :=
  (Finite.of_subsingleton s).countable
#align set.countable.of_subsingleton Set.Countable.of_subsingleton

theorem Subsingleton.countable {s : Set α} (hs : s.Subsingleton) : s.Countable :=
  hs.finite.countable
#align set.subsingleton.countable Set.Subsingleton.countable

theorem countable_isTop (α : Type*) [PartialOrder α] : { x : α | IsTop x }.Countable :=
  (finite_isTop α).countable
#align set.countable_is_top Set.countable_isTop

theorem countable_isBot (α : Type*) [PartialOrder α] : { x : α | IsBot x }.Countable :=
  (finite_isBot α).countable
#align set.countable_is_bot Set.countable_isBot

/-- The set of finite subsets of a countable set is countable. -/
theorem countable_setOf_finite_subset {s : Set α} (hs : s.Countable) :
    { t | Set.Finite t ∧ t ⊆ s }.Countable := by
  have := hs.to_subtype
  refine (countable_range fun t : Finset s => Subtype.val '' (t : Set s)).mono ?_
  rintro t ⟨ht, hts⟩
  lift t to Set s using hts
  lift t to Finset s using ht.of_finite_image (Subtype.val_injective.injOn _)
  exact mem_range_self _
#align set.countable_set_of_finite_subset Set.countable_setOf_finite_subset

theorem countable_univ_pi {π : α → Type*} [Finite α] {s : ∀ a, Set (π a)}
    (hs : ∀ a, (s a).Countable) : (pi univ s).Countable :=
  have := fun a ↦ (hs a).to_subtype; .of_equiv _ (Equiv.Set.univPi s).symm
#align set.countable_univ_pi Set.countable_univ_pi

theorem countable_pi {π : α → Type*} [Finite α] {s : ∀ a, Set (π a)} (hs : ∀ a, (s a).Countable) :
    { f : ∀ a, π a | ∀ a, f a ∈ s a }.Countable := by
  simpa only [← mem_univ_pi] using countable_univ_pi hs
#align set.countable_pi Set.countable_pi

protected theorem Countable.prod {s : Set α} {t : Set β} (hs : s.Countable) (ht : t.Countable) :
    Set.Countable (s ×ˢ t) :=
  have := hs.to_subtype; have := ht.to_subtype; .of_equiv _ <| (Equiv.Set.prod _ _).symm
#align set.countable.prod Set.Countable.prod

theorem Countable.image2 {s : Set α} {t : Set β} (hs : s.Countable) (ht : t.Countable)
    (f : α → β → γ) : (image2 f s t).Countable := by
  rw [← image_prod]
  exact (hs.prod ht).image _
#align set.countable.image2 Set.Countable.image2

/-- If a family of disjoint sets is included in a countable set, then only countably many of
them are nonempty. -/
theorem countable_setOf_nonempty_of_disjoint {f : β → Set α}
    (hf : Pairwise (Disjoint on f)) {s : Set α} (h'f : ∀ t, f t ⊆ s) (hs : s.Countable) :
    Set.Countable {t | (f t).Nonempty} := by
  rw [← Set.countable_coe_iff] at hs ⊢
  have : ∀ t : {t // (f t).Nonempty}, ∃ x : s, x.1 ∈ f t := by
    rintro ⟨t, ⟨x, hx⟩⟩
    exact ⟨⟨x, (h'f t hx)⟩, hx⟩
  choose F hF using this
  have A : Injective F := by
    rintro ⟨t, ht⟩ ⟨t', ht'⟩ htt'
    have A : (f t ∩ f t').Nonempty := by
      refine ⟨F ⟨t, ht⟩, hF _, ?_⟩
      rw [htt']
      exact hF _
    simp only [Subtype.mk.injEq]
    by_contra H
    exact not_disjoint_iff_nonempty_inter.2 A (hf H)
  exact Injective.countable A

end Set

theorem Finset.countable_toSet (s : Finset α) : Set.Countable (↑s : Set α) :=
  s.finite_toSet.countable
#align finset.countable_to_set Finset.countable_toSet
