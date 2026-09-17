/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Data.Set.Subsingleton
public import Mathlib.InformationTheory.Coding.UniquelyDecodable

/-!
# Prefix-Free Codes

This file defines prefix-free codes and proves that every prefix-free code not containing the
empty word is uniquely decodable.

## Main definitions

* `IsPrefixFree`: a set of words is prefix-free if two words in the set cannot be distinct when
  one is a prefix of the other.

## Main results

* `IsPrefixFree.isUniquelyDecodable`: a prefix-free code not containing the empty word is uniquely
  decodable.
-/

@[expose] public section

namespace InformationTheory

variable {α : Type*} {S T : Set (List α)}

/-- A set of words is prefix-free if two words in the set cannot be distinct when one is a prefix
of the other. -/
def IsPrefixFree (S : Set (List α)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x <+: y → x = y

/-- A prefix-free set containing the empty word is the singleton containing the empty word. -/
lemma IsPrefixFree.eq_singleton_empty_of_empty_mem (hS : IsPrefixFree S) (hε : [] ∈ S) :
    S = {[]} := by
  rw [Set.eq_singleton_iff_unique_mem]
  exact ⟨hε, fun _ hx ↦ (hS _ hε _ hx List.nil_prefix).symm⟩

/-- Any subset of a prefix-free set is prefix-free. -/
lemma IsPrefixFree.anti (hS : IsPrefixFree S) (hTS : T ⊆ S) : IsPrefixFree T :=
  fun _ hx _ hy ↦ hS _ (hTS hx) _ (hTS hy)

/-- A prefix-free code not containing the empty word is uniquely decodable. -/
theorem IsPrefixFree.isUniquelyDecodable (hS : IsPrefixFree S) (hε : [] ∉ S) :
    IsUniquelyDecodable S := by
  intro L₁ L₂ hL₁ hL₂ hflatten
  induction L₁ generalizing L₂ with
  | nil =>
    cases L₂ with
    | nil => rfl
    | cons w L =>
      simp at hflatten
      grind
  | cons w₁ L₁ ih =>
    cases L₂ with
    | nil =>
      simp at hflatten
      grind
    | cons w₂ L₂ =>
      simp only [List.flatten_cons] at hflatten
      have hw : w₁ = w₂ := by
        rcases List.append_eq_append_iff.mp hflatten with
          ⟨t, hw₁, -⟩ | ⟨t, hw₂, -⟩
        · exact hS _ (hL₁ _ (.head ..)) _ (hL₂ _ (.head ..)) ⟨t, hw₁.symm⟩
        · exact (hS _ (hL₂ _ (.head ..)) _ (hL₁ _ (.head ..)) ⟨t, hw₂.symm⟩).symm
      subst w₂
      congr
      apply ih L₂
      · grind
      · grind
      · exact List.append_cancel_left hflatten

/-- A nontrivial prefix-free code is uniquely decodable. -/
theorem IsPrefixFree.isUniquelyDecodable_of_nontrivial (hS : IsPrefixFree S)
    (hS' : S.Nontrivial) : IsUniquelyDecodable S :=
  hS.isUniquelyDecodable fun hε ↦
    hS'.ne_singleton (hS.eq_singleton_empty_of_empty_mem hε)

end InformationTheory
