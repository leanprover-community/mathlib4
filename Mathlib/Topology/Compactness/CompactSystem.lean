/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact systems

This file defines compact systems of sets.

## Main definitions

* `IsCompactSystem`: A set of sets is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.
* `compactClosedSquareCylinders`: The square cylinders in a product space whose sides are
  compact and closed.

## Main results

* `isCompactSystem_insert_univ_iff`: A set system is a compact system iff inserting `univ`
  gives a compact system.
* `isCompactSystem_isCompact_isClosed`: The set of closed and compact sets is a compact system.
* `isCompactSystem_isCompact`: In a `T2Space`, the set of compact sets is a compact system.
* `IsCompactSystem.prod`, `IsCompactSystem.pi`: Products of sets from compact systems form a
  compact system.
* `isCompactSystem_compactClosedSquareCylinders`: Compact and closed square cylinders form a
  compact system.
-/

@[expose] public section

open Set Nat

variable {α : Type*} {S : Set (Set α)} {C : ℕ → Set α}

section definition

/-- A set of sets is a compact system if, whenever a countable subfamily has empty intersection,
then finitely many of them already have empty intersection. -/
def IsCompactSystem (S : Set (Set α)) : Prop :=
  ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → ⋂ i, C i = ∅ → ∃ (n : ℕ), dissipate C n = ∅

end definition

namespace IsCompactSystem

lemma of_nonempty_iInter
    (h : ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) :
    IsCompactSystem S := by
  intro C hC
  contrapose!
  exact h C hC

lemma nonempty_iInter (hp : IsCompactSystem S) {C : ℕ → Set α} (hC : ∀ i, C i ∈ S)
    (h_nonempty : ∀ n, (dissipate C n).Nonempty) :
    (⋂ i, C i).Nonempty := by
  revert h_nonempty
  contrapose!
  exact hp C hC

theorem iff_nonempty_iInter (S : Set (Set α)) :
    IsCompactSystem S ↔
      ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty :=
  ⟨nonempty_iInter, of_nonempty_iInter⟩

@[simp]
lemma of_IsEmpty [IsEmpty α] (S : Set (Set α)) : IsCompactSystem S :=
  fun s _ _ ↦ ⟨0, Set.eq_empty_of_isEmpty (dissipate s 0)⟩

/-- Any subset of a compact system is a compact system. -/
theorem mono {T : Set (Set α)} (hT : IsCompactSystem T) (hST : S ⊆ T) :
    IsCompactSystem S := fun C hC1 hC2 ↦ hT C (fun i ↦ hST (hC1 i)) hC2

/-- Inserting `∅` into a compact system gives a compact system. -/
lemma insert_empty (h : IsCompactSystem S) : IsCompactSystem (insert ∅ S) := by
  intro s h' hd
  by_cases! g : ∃ n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact (dissipate_subset le_rfl).trans g.choose_spec.le
  · exact h s (fun i ↦ (mem_of_mem_insert_of_ne (h' i) (g i).ne_empty)) hd

/-- Inserting `univ` into a compact system gives a compact system. -/
lemma insert_univ (h : IsCompactSystem S) : IsCompactSystem (insert univ S) := by
  rcases isEmpty_or_nonempty α with hα | _
  · simp
  rw [IsCompactSystem.iff_nonempty_iInter] at h ⊢
  intro s h' hd
  by_cases! h₀ : ∀ n, s n ∉ S
  · simp_all
  classical
  let n := Nat.find h₀
  let s' := fun i ↦ if s i ∈ S then s i else s n
  have h₁ : ∀ i, s' i ∈ S := by grind
  have h₂ : ⋂ i, s i = ⋂ i, s' i := by ext; simp; grind
  apply h₂ ▸ h s' h₁
  by_contra! ⟨j, hj⟩
  have h₃ (v : ℕ) (hv : n ≤ v) : dissipate s v = dissipate s' v := by ext; simp; grind
  have h₇ : dissipate s' (max j n) = ∅ := by
    rw [← subset_empty_iff] at hj ⊢
    exact (antitone_dissipate (Nat.le_max_left j n)).trans hj
  specialize h₃ (max j n) (Nat.le_max_right j n)
  specialize hd (max j n)
  simp [h₃, h₇] at hd

end IsCompactSystem

/-- In this equivalent formulation for a compact system,
note that we use `⋂ k < n, C k` rather than `⋂ k ≤ n, C k`. -/
lemma isCompactSystem_iff_nonempty_iInter_of_lt (S : Set (Set α)) :
    IsCompactSystem S ↔
      ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (⋂ k < n, C k).Nonempty) → (⋂ i, C i).Nonempty := by
  simp_rw [IsCompactSystem.iff_nonempty_iInter]
  refine ⟨fun h C hi h'↦ h C hi (fun n ↦ dissipate_eq_biInter_lt ▸ (h' (n + 1))),
    fun h C hi h' ↦ h C hi ?_⟩
  simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
  refine fun n g ↦ h' n ?_
  simp_rw [← subset_empty_iff, dissipate] at g ⊢
  exact le_trans (fun x ↦ by simp; grind) g

/-- A set system is a compact system iff adding `∅` gives a compact system. -/
lemma isCompactSystem_insert_empty_iff :
    IsCompactSystem (insert ∅ S) ↔ IsCompactSystem S :=
  ⟨fun h ↦ h.mono (subset_insert _ _), .insert_empty⟩

/-- A set system is a compact system iff adding `univ` gives a compact system. -/
lemma isCompactSystem_insert_univ_iff : IsCompactSystem (insert univ S) ↔ IsCompactSystem S :=
  ⟨fun h ↦ h.mono (subset_insert _ _), .insert_univ⟩

/-- To prove that a set of sets is a compact system, it suffices to consider directed families of
sets. -/
theorem isCompactSystem_iff_of_directed (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
      ∀ (C : ℕ → Set α), Directed (· ⊇ ·) C → (∀ i, C i ∈ S) → ⋂ i, C i = ∅ → ∃ n, C n = ∅ := by
  rw [← isCompactSystem_insert_empty_iff]
  refine ⟨fun h ↦ fun C hdi hi ↦ ?_, fun h C h1 h2 ↦ ?_⟩
  · rw [← exists_dissipate_eq_empty_iff_of_directed hdi]
    exact h C (by simp [hi])
  rw [← biInter_le_eq_iInter] at h2
  suffices (∀ n, dissipate C n ∈ S ∨ dissipate C n = ∅) ∧ (⋂ n, dissipate C n = ∅) by
    by_cases! f : ∀ n, dissipate C n ∈ S
    · exact h (dissipate C) directed_dissipate f this.2
    · obtain ⟨n, hn⟩ := f
      exact ⟨n, by simpa [hn] using this.1 n⟩
  refine ⟨fun n ↦ ?_, h2⟩
  by_cases g : (dissipate C n).Nonempty
  · simpa [or_comm] using hpi.insert_empty.dissipate_mem h1 n g
  · exact .inr (Set.not_nonempty_iff_eq_empty.mp g)

/-- To prove that a set of sets is a compact system, it suffices to consider directed families of
sets. -/
theorem isCompactSystem_iff_nonempty_iInter_of_directed (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
    ∀ (C : ℕ → Set α), (Directed (· ⊇ ·) C) → (∀ i, C i ∈ S) → (∀ n, (C n).Nonempty) →
      (⋂ i, C i).Nonempty := by
  rw [isCompactSystem_iff_of_directed hpi]
  refine ⟨fun h1 C h3 h4 ↦ ?_, fun h1 C h3 s ↦ ?_⟩ <;> contrapose!
  · exact h1 C h3 h4
  · exact h1 C h3 s

section IsCompactIsClosed

/-- The set of compact and closed sets is a compact system. -/
theorem isCompactSystem_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem {s : Set α | IsCompact s ∧ IsClosed s} := by
  refine IsCompactSystem.of_nonempty_iInter fun C hC_cc h_nonempty ↦ ?_
  rw [← iInter_dissipate]
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (Set.dissipate C)
    (fun n ↦ ?_) h_nonempty ?_ (fun n ↦ isClosed_biInter (fun i _ ↦ (hC_cc i).2))
  · exact Set.antitone_dissipate (by lia)
  · simpa using (hC_cc 0).1

/-- In a `T2Space` the set of compact sets is a compact system. -/
theorem isCompactSystem_isCompact (α : Type*) [TopologicalSpace α] [T2Space α] :
    IsCompactSystem {s : Set α | IsCompact s} := by
  convert! isCompactSystem_isCompact_isClosed α with s
  simpa using IsCompact.isClosed

/-- The set of sets which are either compact and closed, or `univ`, is a compact system. -/
theorem isCompactSystem_insert_univ_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem (insert univ {s : Set α | IsCompact s ∧ IsClosed s}) :=
  (isCompactSystem_isCompact_isClosed α).insert_univ

end IsCompactIsClosed

namespace IsCompactSystem

/-- Products of sets from two compact systems form a compact system. -/
theorem prod {β : Type*} {T : Set (Set β)} (hS : IsCompactSystem S) (hT : IsCompactSystem T) :
    IsCompactSystem (image2 (· ×ˢ ·) S T) := by
  intro u hu h_empty
  choose s hs t ht hst using hu
  obtain rfl : u = fun n ↦ s n ×ˢ t n := funext fun n ↦ (hst n).symm
  rw [← iInter_prod_iInter, prod_eq_empty_iff] at h_empty
  simp_rw [dissipate, ← iInter_prod_iInter, prod_eq_empty_iff]
  obtain h | h := h_empty
  · obtain ⟨n, hn⟩ := hS s hs h
    exact ⟨n, .inl hn⟩
  · obtain ⟨n, hn⟩ := hT t ht h
    exact ⟨n, .inr hn⟩

variable {ι : Type*} {α : ι → Type*}

/-- Boxes formed by compact systems form a compact system. -/
theorem pi {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsCompactSystem (C i)) :
    IsCompactSystem (univ.pi '' univ.pi C) := by
  intro S hS h_empty
  choose x hx hxS using hS
  obtain rfl : S = fun n ↦ univ.pi (x n) := funext fun n ↦ (hxS n).symm
  obtain ⟨i, hi⟩ := (iInter_univ_pi_eq_empty_iff x).mp h_empty
  obtain ⟨n, hn⟩ := hC i (fun n ↦ x n i) (fun n ↦ hx n i (mem_univ i)) hi
  exact ⟨n, (biInter_univ_pi_eq_empty_iff x _).mpr ⟨i, hn⟩⟩

end IsCompactSystem

/-- Products of two compact and closed sets form a compact system. -/
theorem isCompactSystem_prod_isCompact_isClosed (α β : Type*) [TopologicalSpace α]
    [TopologicalSpace β] :
    IsCompactSystem (image2 (· ×ˢ ·) {s : Set α | IsCompact s ∧ IsClosed s}
      {t : Set β | IsCompact t ∧ IsClosed t}) :=
  (isCompactSystem_isCompact_isClosed α).prod (isCompactSystem_isCompact_isClosed β)

section CompactClosedSquareCylinders

variable {ι : Type*} (α : ι → Type*) [∀ i, TopologicalSpace (α i)]

/-- The set of sets of the form `s.pi t`, where `s : Finset ι` and `t i` is both closed and
compact for all `i ∈ s`. -/
def compactClosedSquareCylinders : Set (Set (Π i, α i)) :=
  MeasureTheory.squareCylinders fun i ↦ {t : Set (α i) | IsCompact t ∧ IsClosed t}

/-- Boxes formed by compact and closed sets form a compact system. -/
theorem isCompactSystem_pi_isCompact_isClosed :
    IsCompactSystem (univ.pi '' univ.pi fun i ↦ {t : Set (α i) | IsCompact t ∧ IsClosed t}) :=
  IsCompactSystem.pi fun i ↦ isCompactSystem_isCompact_isClosed (α i)

/-- Boxes formed by sets that are either compact and closed, or `univ`, form a compact system. -/
theorem isCompactSystem_pi_insert_univ_isCompact_isClosed :
    IsCompactSystem
      (univ.pi '' univ.pi fun i ↦ insert univ {t : Set (α i) | IsCompact t ∧ IsClosed t}) :=
  IsCompactSystem.pi fun i ↦ isCompactSystem_insert_univ_isCompact_isClosed (α i)

/-- Compact and closed square cylinders form a compact system. -/
theorem isCompactSystem_compactClosedSquareCylinders :
    IsCompactSystem (compactClosedSquareCylinders α) :=
  (isCompactSystem_pi_insert_univ_isCompact_isClosed α).mono
    (MeasureTheory.squareCylinders_subset_image_pi_insert_univ _)

end CompactClosedSquareCylinders
