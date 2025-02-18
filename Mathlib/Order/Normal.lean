/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.SuccPred.CompleteLinearOrder
import Mathlib.Order.SuccPred.InitialSeg

/-!
# Normal functions

A normal function between well-orders is a strictly monotonic continuous function. Normal functions
arise chiefly in the context of cardinal and ordinal-valued functions. Unfortunately, Mathlib places
these earlier in the import chain than the topological notion of continuity.

We instead opt for an alternate but equivalent definition: a normal function is a strictly monotonic
function `f` such that at successor limits `a`, `f a` is the least upper bound of `f b` with
`b < a`.

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
  /-- Combined with strict monotonicity, this condition implies that `f a` is the *least* upper
  bound for `f '' Iio a`. -/
  mem_lowerBounds_upperBounds {a : α} (ha : IsSuccLimit a) :
    f a ∈ lowerBounds (upperBounds (f '' Iio a))

namespace IsNormal

section LinearOrder
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

theorem of_succ_lt [SuccOrder α] [WellFoundedLT α]
    (hs : ∀ a, f a < f (succ a)) (hl : ∀ {a}, IsSuccLimit a → IsLUB (f '' Iio a) (f a)) :
    IsNormal f := by
  refine ⟨fun a b ↦ SuccOrder.limitRecOn b ?_ ?_ ?_ , fun ha ↦ (hl ha).2⟩
  · intro b hb hb'
    cases hb.not_lt hb'
  · intro b hb IH hab
    obtain rfl | h := (lt_succ_iff_eq_or_lt_of_not_isMax hb).1 hab
    · exact hs a
    · exact (IH h).trans (hs b)
  · intro b hb IH hab
    have hab' := hb.succ_lt hab
    exact (IH _ hab' (lt_succ_of_not_isMax hab.not_isMax)).trans_le
      ((hl hb).1 (mem_image_of_mem _ hab'))

theorem lt_iff_lt (hf : IsNormal f) : f a < f b ↔ a < b :=
  hf.strictMono.lt_iff_lt

theorem le_iff_le (hf : IsNormal f) : f a ≤ f b ↔ a ≤ b :=
  hf.strictMono.le_iff_le

theorem inj (hf : IsNormal f) : f a = f b ↔ a = b :=
  hf.strictMono.injective.eq_iff

theorem id_le {f : α → α} (hf : IsNormal f) [WellFoundedLT α] : id ≤ f :=
  hf.strictMono.id_le

theorem le_apply {f : α → α} (hf : IsNormal f) [WellFoundedLT α] : a ≤ f a :=
  hf.strictMono.le_apply

theorem isLUB_image_Iio_of_isSuccLimit (hf : IsNormal f) {a : α} (ha : IsSuccLimit a) :
    IsLUB (f '' Iio a) (f a) := by
  refine ⟨?_, mem_lowerBounds_upperBounds hf ha⟩
  rintro _ ⟨b, hb, rfl⟩
  exact (hf.strictMono hb).le

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
    rw [hf.le_iff_le] at hc'
    exact hc.not_le hc'

theorem map_isLUB (hf : IsNormal f) {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty) :
    IsLUB (f '' s) (f a) := by
  refine ⟨?_, fun b hb ↦ ?_⟩
  · simp_rw [mem_upperBounds, forall_mem_image, hf.le_iff_le]
    exact hs.1
  · by_cases ha : a ∈ s
    · simp_rw [mem_upperBounds, forall_mem_image] at hb
      exact hb ha
    · have ha' := hs.isSuccLimit_of_not_mem hs' ha
      rw [le_iff_forall_le hf ha']
      intro c hc
      obtain ⟨d, hd, hcd, hda⟩ := hs.exists_between hc
      simp_rw [mem_upperBounds, forall_mem_image] at hb
      exact (hf.strictMono hcd).le.trans (hb hd)

theorem _root_.InitialSeg.isNormal (f : α ≤i β) : IsNormal f where
  strictMono := f.strictMono
  mem_lowerBounds_upperBounds := by
    intro a ha
    rw [f.image_Iio]
    exact (f.map_isSuccLimit ha).isLUB_Iio.2

theorem _root_.PrincipalSeg.isNormal (f : α <i β) : IsNormal f :=
  (f : α ≤i β).isNormal

protected theorem id : IsNormal (@id α) :=
  (InitialSeg.refl _).isNormal

theorem trans (hg : IsNormal g) (hf : IsNormal f) : IsNormal (g ∘ f) where
  strictMono := hg.strictMono.comp hf.strictMono
  mem_lowerBounds_upperBounds := by
    intro a ha b hb
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
  ext; simp

end ConditionallyCompleteLinearOrder

end IsNormal

end Order
