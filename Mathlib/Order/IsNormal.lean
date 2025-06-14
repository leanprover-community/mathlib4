/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.SuccPred.InitialSeg

/-!
# Normal functions

A normal function between well-orders is a strictly monotonic continuous function. Normal functions
arise chiefly in the context of cardinal and ordinal-valued functions.

We opt for an equivalent definition that's both simpler and often more convenient: a normal function
is a strictly monotonic function `f` such that at successor limits `a`, `f a` is the least upper
bound of `f b` with `b < a`.

## TODO

* Prove the equivalence with the standard definition (in some other file).
* Replace `Ordinal.IsNormal` by this more general notion.
-/

open Order Set

variable {α β γ : Type*} {a b : α} {f : α → β} {g : β → γ}

namespace Order

/-- A normal function between well-orders is a strictly monotonic continuous function. -/
structure IsNormal [LinearOrder α] [LinearOrder β] (f : α → β) : Prop where
  strictMono : StrictMono f
  isLUB_image_Iio_of_isSuccLimit {a : α} (ha : IsSuccLimit a) : IsLUB (f '' Iio a) (f a)

namespace IsNormal

section LinearOrder
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- This condition is the LHS of the `IsLUB (f '' Iio a) (f a)` predicate. -/
theorem of_mem_lowerBounds_upperBounds {f : α → β} (hf : StrictMono f)
    (hl : ∀ {a}, IsSuccLimit a → f a ∈ lowerBounds (upperBounds (f '' Iio a))) : IsNormal f := by
  refine ⟨hf, fun {a} ha ↦ ⟨?_, hl ha⟩⟩
  rintro - ⟨b, hb, rfl⟩
  exact (hf hb).le

theorem of_succ_lt [SuccOrder α] [WellFoundedLT α]
    (hs : ∀ a, f a < f (succ a)) (hl : ∀ {a}, IsSuccLimit a → IsLUB (f '' Iio a) (f a)) :
    IsNormal f := by
  refine ⟨fun a b ↦ ?_, hl⟩
  induction b using SuccOrder.limitRecOn with
  | isMin b hb => exact hb.not_lt.elim
  | succ b hb IH =>
    intro hab
    obtain rfl | h := (lt_succ_iff_eq_or_lt_of_not_isMax hb).1 hab
    · exact hs a
    · exact (IH h).trans (hs b)
  | isSuccLimit b hb IH =>
    intro hab
    have hab' := hb.succ_lt hab
    exact (IH _ hab' (lt_succ_of_not_isMax hab.not_isMax)).trans_le
      ((hl hb).1 (mem_image_of_mem _ hab'))

theorem le_iff_forall_le (hf : IsNormal f) (ha : IsSuccLimit a) {b : β} :
    f a ≤ b ↔ ∀ a' < a, f a' ≤ b := by
  simpa [mem_upperBounds] using isLUB_le_iff (hf.isLUB_image_Iio_of_isSuccLimit ha)

theorem lt_iff_exists_lt (hf : IsNormal f) (ha : IsSuccLimit a) {b : β} :
    b < f a ↔ ∃ a' < a, b < f a' := by
  simpa [mem_upperBounds] using lt_isLUB_iff (hf.isLUB_image_Iio_of_isSuccLimit ha)

theorem map_isSuccLimit (hf : IsNormal f) (ha : IsSuccLimit a) : IsSuccLimit (f a) := by
  refine ⟨?_, fun b hb ↦ ?_⟩
  · obtain ⟨b, hb⟩ := not_isMin_iff.1 ha.not_isMin
    exact not_isMin_iff.2 ⟨_, hf.strictMono hb⟩
  · obtain ⟨c, hc, hc'⟩ := (hf.lt_iff_exists_lt ha).1 hb.lt
    have hc' := hb.ge_of_gt hc'
    rw [hf.strictMono.le_iff_le] at hc'
    exact hc.not_ge hc'

theorem map_isLUB (hf : IsNormal f) {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty) :
    IsLUB (f '' s) (f a) := by
  refine ⟨?_, fun b hb ↦ ?_⟩
  · simp_rw [mem_upperBounds, forall_mem_image, hf.strictMono.le_iff_le]
    exact hs.1
  · by_cases ha : a ∈ s
    · simp_rw [mem_upperBounds, forall_mem_image] at hb
      exact hb ha
    · have ha' := hs.isSuccLimit_of_notMem hs' ha
      rw [le_iff_forall_le hf ha']
      intro c hc
      obtain ⟨d, hd, hcd, hda⟩ := hs.exists_between hc
      simp_rw [mem_upperBounds, forall_mem_image] at hb
      exact (hf.strictMono hcd).le.trans (hb hd)

theorem _root_.InitialSeg.isNormal (f : α ≤i β) : IsNormal f where
  strictMono := f.strictMono
  isLUB_image_Iio_of_isSuccLimit ha := by
    rw [f.image_Iio]
    exact (f.map_isSuccLimit ha).isLUB_Iio

theorem _root_.PrincipalSeg.isNormal (f : α <i β) : IsNormal f :=
  (f : α ≤i β).isNormal

theorem _root_.OrderIso.isNormal (f : α ≃o β) : IsNormal f :=
  f.toInitialSeg.isNormal

protected theorem id : IsNormal (@id α) :=
  (OrderIso.refl _).isNormal

theorem comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal (g ∘ f) := by
  refine .of_mem_lowerBounds_upperBounds (hg.strictMono.comp hf.strictMono) fun ha b hb ↦ ?_
  simp_rw [Function.comp_apply, mem_upperBounds, forall_mem_image] at hb
  simpa [hg.le_iff_forall_le (hf.map_isSuccLimit ha), hf.lt_iff_exists_lt ha] using
    fun c d hd hc ↦ (hg.strictMono hc).le.trans (hb hd)

end LinearOrder

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [ConditionallyCompleteLinearOrder β]

theorem map_sSup (hf : IsNormal f) {s : Set α} (hs : s.Nonempty) (hs' : BddAbove s) :
    f (sSup s) = sSup (f '' s) :=
  ((hf.map_isLUB (isLUB_csSup hs hs') hs).csSup_eq (hs.image f)).symm

theorem map_iSup {ι} [Nonempty ι] {g : ι → α} (hf : IsNormal f) (hg : BddAbove (range g)) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  unfold iSup
  convert map_sSup hf (range_nonempty g) hg
  ext
  simp

end ConditionallyCompleteLinearOrder

end IsNormal

end Order
