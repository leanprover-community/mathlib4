/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Family

/-!
# Enumerating sets of ordinals by ordinals

The ordinals have the peculiar property that every subset bounded above is a small type, while
themselves not being small. As a consequence of this, every unbounded subset of `Ordinal` is order
isomorphic to `Ordinal`.

We define this correspondence as `enumOrd`, and use it to then define an order isomorphism
`enumOrdOrderIso`.

This can be thought of as an ordinal analog of `Nat.nth`.
-/

universe u

open Order Set

namespace Ordinal

variable {o a b : Ordinal.{u}}

/-- Enumerator function for an unbounded set of ordinals. -/
noncomputable def enumOrd (s : Set Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  sInf (s ∩ { b | ∀ c, c < o → enumOrd s c < b })
termination_by o

variable {s : Set Ordinal.{u}}

theorem enumOrd_le_of_forall_lt (ha : a ∈ s) (H : ∀ b < o, enumOrd s b < a) : enumOrd s o ≤ a := by
  rw [enumOrd]
  exact csInf_le' ⟨ha, H⟩

/-- The set in the definition of `enumOrd` is nonempty. -/
private theorem enumOrd_nonempty (hs : ¬ BddAbove s) (o : Ordinal) :
    (s ∩ { b | ∀ c, c < o → enumOrd s c < b }).Nonempty := by
  rw [not_bddAbove_iff] at hs
  obtain ⟨a, ha⟩ := bddAbove_of_small (enumOrd s '' Iio o)
  obtain ⟨b, hb, hba⟩ := hs a
  exact ⟨b, hb, fun c hc ↦ (ha (mem_image_of_mem _ hc)).trans_lt hba⟩

private theorem enumOrd_mem_aux (hs : ¬ BddAbove s) (o : Ordinal) :
    enumOrd s o ∈ s ∩ { b | ∀ c, c < o → enumOrd s c < b } := by
  rw [enumOrd]
  exact csInf_mem (enumOrd_nonempty hs o)

theorem enumOrd_mem (hs : ¬ BddAbove s) (o : Ordinal) : enumOrd s o ∈ s :=
  (enumOrd_mem_aux hs o).1

theorem enumOrd_strictMono (hs : ¬ BddAbove s) : StrictMono (enumOrd s) :=
  fun a b ↦ (enumOrd_mem_aux hs b).2 a

theorem enumOrd_injective (hs : ¬ BddAbove s) : Function.Injective (enumOrd s) :=
  (enumOrd_strictMono hs).injective

theorem enumOrd_inj (hs : ¬ BddAbove s) {a b : Ordinal} : enumOrd s a = enumOrd s b ↔ a = b :=
  (enumOrd_injective hs).eq_iff

theorem enumOrd_le_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} :
    enumOrd s a ≤ enumOrd s b ↔ a ≤ b :=
  (enumOrd_strictMono hs).le_iff_le

theorem enumOrd_lt_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} :
    enumOrd s a < enumOrd s b ↔ a < b :=
  (enumOrd_strictMono hs).lt_iff_lt

theorem id_le_enumOrd (hs : ¬ BddAbove s) : id ≤ enumOrd s :=
  (enumOrd_strictMono hs).id_le

theorem le_enumOrd_self (hs : ¬ BddAbove s) {a} : a ≤ enumOrd s a :=
  (enumOrd_strictMono hs).le_apply

theorem enumOrd_succ_le (hs : ¬ BddAbove s) (ha : a ∈ s) (hb : enumOrd s b < a) :
    enumOrd s (succ b) ≤ a := by
  apply enumOrd_le_of_forall_lt ha
  intro c hc
  rw [lt_succ_iff] at hc
  exact ((enumOrd_strictMono hs).monotone hc).trans_lt hb

theorem range_enumOrd (hs : ¬ BddAbove s) : range (enumOrd s) = s := by
  ext a
  let t := { b | a ≤ enumOrd s b }
  constructor
  · rintro ⟨b, rfl⟩
    exact enumOrd_mem hs b
  · intro ha
    refine ⟨sInf t, (enumOrd_le_of_forall_lt ha ?_).antisymm ?_⟩
    · intro b hb
      by_contra! hb'
      exact hb.not_ge (csInf_le' hb')
    · exact csInf_mem (s := t) ⟨a, (enumOrd_strictMono hs).id_le a⟩

theorem enumOrd_surjective (hs : ¬ BddAbove s) {b : Ordinal} (hb : b ∈ s) :
    ∃ a, enumOrd s a = b := by
  rwa [← range_enumOrd hs] at hb

theorem enumOrd_le_of_subset {t : Set Ordinal} (hs : ¬ BddAbove s) (hst : s ⊆ t) :
    enumOrd t ≤ enumOrd s := by
  intro a
  rw [enumOrd, enumOrd]
  gcongr with b c
  exacts [enumOrd_nonempty hs a, enumOrd_le_of_subset hs hst c]
termination_by a => a

/-- A characterization of `enumOrd`: it is the unique strict monotonic function with range `s`. -/
theorem eq_enumOrd (f : Ordinal → Ordinal) (hs : ¬ BddAbove s) :
    enumOrd s = f ↔ StrictMono f ∧ range f = s := by
  constructor
  · rintro rfl
    exact ⟨enumOrd_strictMono hs, range_enumOrd hs⟩
  · rintro ⟨h₁, h₂⟩
    rwa [← (enumOrd_strictMono hs).range_inj h₁, range_enumOrd hs, eq_comm]

theorem enumOrd_range {f : Ordinal → Ordinal} (hf : StrictMono f) : enumOrd (range f) = f :=
  (eq_enumOrd _ hf.not_bddAbove_range_of_wellFoundedLT).2 ⟨hf, rfl⟩

/-- If `s` is closed under nonempty suprema, then its enumerator function is normal.
See also `enumOrd_isNormal_iff_isClosed`. -/
theorem isNormal_enumOrd (H : ∀ t ⊆ s, t.Nonempty → BddAbove t → sSup t ∈ s) (hs : ¬ BddAbove s) :
    IsNormal (enumOrd s) := by
  refine (isNormal_iff_strictMono_limit _).2 ⟨enumOrd_strictMono hs, fun o ho a ha ↦ ?_⟩
  trans ⨆ b : Iio o, enumOrd s b
  · refine enumOrd_le_of_forall_lt ?_ (fun b hb ↦ (enumOrd_strictMono hs (lt_succ b)).trans_le ?_)
    · have : Nonempty (Iio o) := ⟨0, ho.bot_lt⟩
      apply H _ _ (range_nonempty _) (bddAbove_of_small _)
      rintro _ ⟨c, rfl⟩
      exact enumOrd_mem hs c
    · exact Ordinal.le_iSup _ (⟨_, ho.succ_lt hb⟩ : Iio o)
  · exact Ordinal.iSup_le fun x ↦ ha _ x.2

@[simp]
theorem enumOrd_univ : enumOrd Set.univ = id := by
  rw [← range_id]
  exact enumOrd_range strictMono_id

@[simp]
theorem enumOrd_zero : enumOrd s 0 = sInf s := by
  rw [enumOrd]
  simp [Ordinal.not_lt_zero]

/-- An order isomorphism between an unbounded set of ordinals and the ordinals. -/
noncomputable def enumOrdOrderIso (s : Set Ordinal) (hs : ¬ BddAbove s) : Ordinal ≃o s :=
  StrictMono.orderIsoOfSurjective (fun o => ⟨_, enumOrd_mem hs o⟩) (enumOrd_strictMono hs) fun s =>
    let ⟨a, ha⟩ := enumOrd_surjective hs s.prop
    ⟨a, Subtype.eq ha⟩

end Ordinal
