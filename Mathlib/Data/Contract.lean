/-
Copyright (c) 2024 Google. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
import Mathlib.Data.Setoid.Partition

/-!
# Contract
-/

open Relation

variable {α : Type*}

namespace Setoid

/--
Constructs a setoid from a collection of subsets `S`. Two values are related if they are in the same
subset.

This is similar to `Setoid.mkClasses S ..`, except that it doesn't require `S` to be a partition.
Instead, any overlapping subsets are merged, and any missing values are mapped to themselves.
-/
def fromSets (S : Set (Set α)) : Setoid α where
  r := ReflTransGen fun a b ↦ ∃ s ∈ S, a ∈ s ∧ b ∈ s
  iseqv := {
    refl := fun a ↦ ReflTransGen.refl
    trans := ReflTransGen.trans
    symm := fun h ↦ ReflTransGen.symmetric (by tauto) h
  }

theorem fromSets_r_iff (S : Set (Set α)) (h : S.PairwiseDisjoint id) (a b : α) :
    (fromSets S).r a b ↔ a = b ∨ ∃ s ∈ S, a ∈ s ∧ b ∈ s := by
  constructor
  · intro hr
    induction hr with
    | refl => exact .inl rfl
    | tail _ hs ih =>
      rcases ih with rfl | ht
      · exact .inr hs
      · right
        obtain ⟨s, hs, hbs, hcs⟩ := hs
        obtain ⟨t, ht, hat, hbt⟩ := ht
        have : s = t := h.elim_set hs ht _ hbs hbt
        exact ⟨s, hs, this ▸ hat, hcs⟩
  · rintro (rfl | hr)
    · exact .refl
    · exact .single hr

theorem fromSets_r_iff' (S : Set (Set α)) (hu : ⋃₀ S = Set.univ) (hd : S.PairwiseDisjoint id)
    (a b : α) : (fromSets S).r a b ↔ ∃ s ∈ S, a ∈ s ∧ b ∈ s := by
  rw [fromSets_r_iff S hd a b]
  constructor
  · rintro (rfl | _)
    · have := Set.mem_sUnion.mp <| hu.symm ▸ Set.mem_univ a
      tauto
    · assumption
  · tauto

theorem fromSets_r_iff'' (S : Set (Set α)) (H : ∀ a, ∃! (b : _) (_ : b ∈ S), a ∈ b)
    (a b : α) : (fromSets S).r a b ↔ ∃ s ∈ S, a ∈ s ∧ b ∈ s :=
  fromSets_r_iff' S (eqv_classes_sUnion_eq_univ H) (eqv_classes_disjoint H) a b

theorem fromSets_r_iff_mkClasses_r (S : Set (Set α)) (H : ∀ a, ∃! (b : _) (_ : b ∈ S), a ∈ b)
    (a b : α) : (fromSets S).r a b ↔ (mkClasses S H).r a b := by
  rw [fromSets_r_iff'' S H]
  obtain ⟨t, ⟨ht, hat, _⟩, hunique⟩ := H a
  dsimp at hunique
  constructor
  · rintro ⟨s, hs, has, hbs⟩ s' hs' has'
    rw [hunique s (.intro hs has fun _ _ => rfl)] at hbs
    rw [hunique s' (.intro hs' has' fun _ _ => rfl)]
    exact hbs
  · intro h
    exact ⟨t, ht, hat, h t ht hat⟩

/-- If `S` is a partition, then `Setoid.fromSets` and `Setoid.mkClasses` are equivalent. -/
theorem fromSets_eq_mkClasses (S : Set (Set α)) (H : ∀ a, ∃! (b : _) (_ : b ∈ S), a ∈ b) :
    fromSets S = mkClasses S H := by
  ext
  apply fromSets_r_iff_mkClasses_r

end Setoid

/--
Quotient by the equivalence classes induced by `S`. Two values are related if they are in the same
subset.

This is similar to `Quotient (Setoid.mkClasses S ..)`, except that it doesn't require `S` to be a
partition. Instead, any overlapping subsets are merged, and any missing values are mapped to
themselves.
-/
def Contract (S : Set (Set α)) := Quotient (Setoid.fromSets S)

/-- Constructor for `Contract`. -/
def Contract.mk (S : Set (Set α)) (a : α) : Contract S := Quotient.mk _ a

@[inherit_doc Contract.mk]
notation "⟦" S "|" a "⟧" => Contract.mk S a

namespace Contract

variable {S : Set (Set α)}

instance [Fintype α] [DecidableRel (Setoid.fromSets S).r] : Fintype (Contract S) :=
  inferInstanceAs <| Fintype (Quotient (Setoid.fromSets S))

theorem exists_rep (q : Contract S) : ∃ a, ⟦S|a⟧ = q :=
  Quotient.exists_rep q

protected theorem eq (a b : α) : ⟦S|a⟧ = ⟦S|b⟧ ↔ (Setoid.fromSets S).r a b :=
  letI := Setoid.fromSets S
  Quotient.eq

theorem fiber_of_mem (hd : S.PairwiseDisjoint id) {s : Set α} (hs : s ∈ S) {x : α} (hxs : x ∈ s) :
    Contract.mk S ⁻¹' {⟦S|x⟧} = s := by
  ext y
  change ⟦S|y⟧ = ⟦S|x⟧ ↔ y ∈ s
  rw [Contract.eq, Setoid.fromSets_r_iff S hd]
  constructor
  · rintro (rfl | ⟨t, ht, hyt, hxt⟩)
    · assumption
    · rwa [hd.elim_set hs ht x hxs hxt]
  · tauto

theorem fiber_of_mem' {s : Set α} {x : α} (hxs : x ∈ s) : Contract.mk {s} ⁻¹' {⟦{s}|x⟧} = s :=
  fiber_of_mem (Set.pairwiseDisjoint_singleton s id) (Set.mem_singleton s) hxs

theorem fiber_of_not_mem {x : α} (h : ∀ s ∈ S, x ∉ s) :
    Contract.mk S ⁻¹' {⟦S|x⟧} = {x} := by
  ext y
  change ⟦S|y⟧ = ⟦S|x⟧ ↔ _
  rw [Contract.eq]
  constructor
  · rintro (rfl | _)
    · rfl
    · tauto
  · rintro rfl
    exact .refl

theorem fiber_of_not_mem' {s : Set α} {x : α} (hxs : x ∉ s) : Contract.mk {s} ⁻¹' {⟦{s}|x⟧} = {x} :=
  fiber_of_not_mem fun _ hs => Set.eq_of_mem_singleton hs ▸ hxs

theorem card_le [Fintype α] [DecidableRel (Setoid.fromSets S).r] :
    Fintype.card (Contract S) ≤ Fintype.card α :=
  Fintype.card_quotient_le (Setoid.fromSets S)

theorem card_lt [Fintype α] [DecidableRel (Setoid.fromSets S).r] (h : ∃ s ∈ S, s.Nontrivial) :
    Fintype.card (Contract S) < Fintype.card α :=
  have ⟨s, hs, _, has, _, hbs, hab⟩ := h
  Fintype.card_quotient_lt hab <| .single ⟨s, hs, has, hbs⟩

/--
If `S` is a partition, then `Contract S` and `Quotient (Setoid.mkClasses S ..)` are equivalent.
-/
def equivMkClasses (S : Set (Set α)) (H : ∀ a, ∃! (b : _) (_ : b ∈ S), a ∈ b) :
    Contract S ≃ Quotient (Setoid.mkClasses S H) :=
  congrArg Quotient (Setoid.fromSets_eq_mkClasses S H) ▸ Equiv.refl (Contract S)

end Contract
