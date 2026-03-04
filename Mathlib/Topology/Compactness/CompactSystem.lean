/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Compact systems

This file defines compact systems of sets.

## Main definitions

* `IsCompactSystem`: A set of sets is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.

## Main results

* `isCompactSystem_insert_univ_iff`: A set system is a compact system iff inserting `univ`
  gives a compact system.
* `isCompactSystem_isCompact_isClosed`: The set of closed and compact sets is a compact system.
* `isCompactSystem_isCompact`: In a `T2Space`, the set of compact sets is a compact system.
-/

@[expose] public section

open Set Finset Nat

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
  by_cases g : ∃ n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact (dissipate_subset le_rfl).trans g.choose_spec.le
  · push_neg at g
    exact h s (fun i ↦ (mem_of_mem_insert_of_ne (h' i) (g i).ne_empty)) hd

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
  have h₁ : ∀ i, s' i ∈ S := by simp [s']; grind
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
  refine ⟨fun h1 C h3 h4 ↦ ?_, fun h1 C h3 s ↦ ?_⟩ <;> rw [← not_imp_not] <;> push_neg
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
  convert isCompactSystem_isCompact_isClosed α with s
  simpa using IsCompact.isClosed

/-- The set of sets which are either compact and closed, or `univ`, is a compact system. -/
theorem isCompactSystem_insert_univ_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem (insert univ {s : Set α | IsCompact s ∧ IsClosed s}) :=
  (isCompactSystem_isCompact_isClosed α).insert_univ

end IsCompactIsClosed

section pi

namespace Set

variable {ι : Type*} {α : ι → Type*}

/- In a product space, the intersection of square cylinders is empty iff there is a coordinate `i`
such that the projections to `i` have empty intersection. -/
theorem iInter_pi_empty_iff {β : Type*} (s : β → Set ι) (t : β → (i : ι) → Set (α i)) :
   (⋂ b, ((s b).pi (t b)) = ∅) ↔ (∃ i : ι, ⋂ (b : β) (_: i ∈ s b), (t b i) = ∅):= by
  rw [iInter_eq_empty_iff, not_iff_not.symm]
  push_neg
  simp only [Set.mem_pi, Set.nonempty_iInter, mem_iInter]
  refine ⟨fun ⟨x, hx⟩ i ↦ ?_, fun h ↦ ?_⟩
  · refine ⟨x i, fun j hi ↦ hx j i hi⟩
  · choose x hx using h
    refine ⟨x, fun i j hj ↦ hx j i hj⟩

theorem iInter_univ_pi_empty_iff {β : Type*} (t : β → (i : ι) → Set (α i)) :
   ( ⋂ b, (univ.pi (t b)) = ∅) ↔ (∃ i : ι, ⋂ (b : β), (t b i) = ∅):= by
  rw [iInter_pi_empty_iff]
  simp only [mem_univ, iInter_true]

theorem biInter_univ_pi_empty_iff {β : Type*} (t : β → (i : ι) → Set (α i)) (p : β → Prop) :
   ( ⋂ (b : β), ⋂ (_ : p b), (univ.pi (t b)) = ∅) ↔
      (∃ i : ι, ⋂ (b : β), ⋂ (_ : p b), (t b i) = ∅) := by
  have h :  ⋂ (b : β), ⋂ (_ : p b), (univ.pi (t b)) =
      ⋂ (b : { (b' : β) | p b' }), (univ.pi (t b.val)) := by
    exact biInter_eq_iInter p fun x h ↦ univ.pi (t x)
  have h' (i : ι) :  ⋂ (b : β), ⋂ (_ : p b), t b i =  ⋂ (b : { (b' : β) | p b' }), t b.val i := by
    exact biInter_eq_iInter p fun x h ↦ t x i
  simp_rw [h, h', iInter_univ_pi_empty_iff]

end Set

namespace IsCompactSystem

variable {ι : Type*} {α : ι → Type*}

theorem pi (C : (i : ι) → Set (Set (α i))) (hC : ∀ i, IsCompactSystem (C i)) :
    IsCompactSystem (univ.pi '' univ.pi C) := by
  intro S hS h_empty
  change ∀ i, S i ∈ univ.pi '' univ.pi C at hS
  simp only [mem_image, mem_pi, mem_univ, forall_const] at hS
  choose x hx1 hx2 using hS
  simp_rw [← hx2] at h_empty ⊢
  simp_rw [iInter_univ_pi_empty_iff x] at h_empty
  obtain ⟨i, hi⟩ := h_empty
  let y := (fun b ↦ x b i)
  have hy (b : ℕ) : y b ∈ C i := by
    simp only [y]
    exact hx1 b i
  have ⟨n, hn⟩ := (hC i) y hy hi
  use n
  simp_rw [dissipate, ← hx2] at hn ⊢
  rw [biInter_univ_pi_empty_iff x]
  use i

end IsCompactSystem

end pi

section ClosedCompactSquareCylinders

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, TopologicalSpace (α i)]

variable (α)
/-- The set of sets of the form `s.pi t`, where `s : Finset ι` and `t i` is both,
closed and compact, for all `i ∈ s`. -/
def compactClosedSquareCylinders : Set (Set (Π i, α i)) :=
  MeasureTheory.squareCylinders (fun i ↦ { t : Set (α i) | IsCompact t ∧ IsClosed t })

/-- Products of compact and closed sets form a compact system. -/
theorem IsCompactSystem.compactClosedPi :
    IsCompactSystem (univ.pi '' univ.pi (fun i ↦ { t : Set (α i) | IsCompact t ∧ IsClosed t })) :=
    IsCompactSystem.pi _ (fun _ ↦ isCompactSystem_isCompact_isClosed (α _))

theorem IsCompactSystem.compactClosedOrUnivPi :
    IsCompactSystem (univ.pi '' univ.pi (fun i ↦ insert univ { t :
    Set (α i) | IsCompact t ∧ IsClosed t })) :=
  IsCompactSystem.pi _ (fun i ↦ isCompactSystem_insert_univ_isCompact_isClosed (α i))

/-- Compact and closed square cylinders are a compact system. -/
theorem isCompactSystem.compactClosedSquareCylinders :
    IsCompactSystem (compactClosedSquareCylinders α) :=
    IsCompactSystem.mono (IsCompactSystem.compactClosedOrUnivPi _)
    (MeasureTheory.squareCylinders_subset_of_or_univ _)

end ClosedCompactSquareCylinders
