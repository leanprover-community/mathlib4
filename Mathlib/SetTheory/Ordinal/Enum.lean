/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Enumerating sets of ordinals by ordinals

The ordinals have the peculiar property that every subset bounded above is a small type, while
themselves not being small. As a consequence of this, every unbounded subset of `Ordinal` is order
isomorphic to `Ordinal`.

We define this correspondence as `enumOrd`, and use it to define an order isomorphism
`enumOrdOrderIso`.
-/

universe u

open Order Set

namespace Ordinal

variable {o a b : Ordinal.{u}}

theorem not_bddAbove_range_strictMono {f : Ordinal.{u} → Ordinal.{u}} (hf : StrictMono f) :
    ¬ BddAbove (range f) := by
  rintro ⟨a, ha⟩
  exact (((hf.id_le a).trans_lt (hf (lt_succ a))).trans_le <| ha (mem_range_self _)).false

/-- Enumerator function for an unbounded set of ordinals. -/
noncomputable def enumOrd (S : Set Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  sInf (S ∩ { b | ∀ c, c < o → enumOrd S c < b })
termination_by o

variable {S : Set Ordinal.{u}}

theorem enumOrd_le_of_forall_lt (ha : a ∈ S) (H : ∀ b < o, enumOrd S b < a) : enumOrd S o ≤ a := by
  rw [enumOrd]
  exact csInf_le' ⟨ha, H⟩

/-- The set in the definition of `enumOrd` is nonempty. -/
private theorem enumOrd_nonempty (hS : ¬ BddAbove S) (o : Ordinal) :
    (S ∩ { b | ∀ c, c < o → enumOrd S c < b }).Nonempty := by
  rw [not_bddAbove_iff] at hS
  obtain ⟨a, ha⟩ := bddAbove_of_small (enumOrd S '' Iio o)
  obtain ⟨b, hb, hba⟩ := hS a
  exact ⟨b, hb, fun c hc ↦ (ha (mem_image_of_mem _ hc)).trans_lt hba⟩

private theorem enumOrd_mem_aux (hS : ¬ BddAbove S) (o : Ordinal) :
    enumOrd S o ∈ S ∩ { b | ∀ c, c < o → enumOrd S c < b } := by
  rw [enumOrd]
  exact csInf_mem (enumOrd_nonempty hS o)

theorem enumOrd_mem (hS : ¬ BddAbove S) (o : Ordinal) : enumOrd S o ∈ S :=
  (enumOrd_mem_aux hS o).1

theorem enumOrd_strictMono (hS : ¬ BddAbove S) : StrictMono (enumOrd S) :=
  fun a b ↦ (enumOrd_mem_aux hS b).2 a

theorem enumOrd_succ_le (hS : ¬ BddAbove S) (ha : a ∈ S) (hb : enumOrd S b < a) :
    enumOrd S (succ b) ≤ a := by
  apply enumOrd_le_of_forall_lt ha
  intro c hc
  rw [lt_succ_iff] at hc
  exact ((enumOrd_strictMono hS).monotone hc).trans_lt hb

theorem range_enumOrd (hS : ¬ BddAbove S) : range (enumOrd S) = S := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact enumOrd_mem hS b
  · intro ha
    use sInf { b | a ≤ enumOrd S b }
    apply le_antisymm
    · apply enumOrd_le_of_forall_lt ha
      intro b hb
      by_contra! hb'
      exact hb.not_le (csInf_le' hb')
    · exact csInf_mem (s := { b | a ≤ enumOrd S b }) ⟨a, (enumOrd_strictMono hS).id_le a⟩

theorem enumOrd_surjective (hS : ¬ BddAbove S) {b : Ordinal} (hs : b ∈ S) :
    ∃ a, enumOrd S a = b := by
  rwa [← range_enumOrd hS] at hs

theorem enumOrd_le_enumOrd {S T : Set Ordinal} (hS : ¬ BddAbove S) (hST : S ⊆ T) :
    enumOrd T ≤ enumOrd S := by
  intro a
  rw [enumOrd, enumOrd]
  apply csInf_le_csInf' (enumOrd_nonempty hS a) (inter_subset_inter hST _)
  intro b hb c hc
  exact (enumOrd_le_enumOrd hS hST c).trans_lt <| hb c hc
termination_by a => a

/-- A characterization of `enumOrd`: it is the unique strict monotonic function with range `S`. -/
theorem eq_enumOrd (f : Ordinal → Ordinal) (hS : ¬ BddAbove S) :
    StrictMono f ∧ range f = S ↔ enumOrd S = f := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rwa [← StrictMono.range_inj (enumOrd_strictMono hS) h₁, range_enumOrd hS, eq_comm]
  · rintro rfl
    exact ⟨enumOrd_strictMono hS, range_enumOrd hS⟩

theorem enumOrd_range {f : Ordinal → Ordinal} (hf : StrictMono f) : enumOrd (range f) = f :=
  (eq_enumOrd _ (not_bddAbove_range_strictMono hf)).1 ⟨hf, rfl⟩

@[simp]
theorem enumOrd_univ : enumOrd Set.univ = id := by
  rw [← range_id]
  exact enumOrd_range strictMono_id

@[simp]
theorem enumOrd_zero : enumOrd S 0 = sInf S := by
  rw [enumOrd]
  simp [Ordinal.not_lt_zero]

/-- An order isomorphism between an unbounded set of ordinals and the ordinals. -/
noncomputable def enumOrdOrderIso (S : Set Ordinal) (hS : ¬ BddAbove S) : Ordinal ≃o S :=
  StrictMono.orderIsoOfSurjective (fun o => ⟨_, enumOrd_mem hS o⟩) (enumOrd_strictMono hS) fun s =>
    let ⟨a, ha⟩ := enumOrd_surjective hS s.prop
    ⟨a, Subtype.eq ha⟩

end Ordinal
