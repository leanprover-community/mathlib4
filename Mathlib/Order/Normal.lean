/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.SuccPred.InitialSeg

/-!
# Normal functions

A normal function between well-orders is a strictly monotonic continuous function. Normal functions
arise chiefly in the context of cardinal and ordinal-valued functions. Unfortunately, Mathlib places
these earlier in the import chain than the topological notion of continuity.

We instead opt for an alternate but equivalent definition: a normal function is a strictly monotonic
function `f` such that at successor limits `a`, `f a` is the least upper bound of `f b` with
`b < a`.

TODO: replace `Ordinal.IsNormal` by this more general notion.
-/

open Order Set

variable {α β : Type*} {a b : α} [LinearOrder α] [LinearOrder β]

/-- A normal function between well-orders is a strictly monotonic continuous function. -/
structure IsNormal (f : α → β) : Prop where
  strictMono : StrictMono f
  /-- Combined with strict monotonicity, this condition implies that `f a` is the *least* upper
  bound for `f '' Iio a`. -/
  mem_lowerBounds_upperBounds {a : α} (ha : IsSuccLimit a) :
    f a ∈ lowerBounds (upperBounds (f '' Iio a))

namespace IsNormal
variable {f : α → β}

--theorem of_

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

theorem isLUB_of_isSuccLimit (hf : IsNormal f) {a : α} (ha : IsSuccLimit a) :
    IsLUB (f '' Iio a) (f a) := by
  refine ⟨?_, mem_lowerBounds_upperBounds hf ha⟩
  rintro _ ⟨b, hb, rfl⟩
  exact (hf.strictMono hb).le

theorem le_iff_forall_le (hf : IsNormal f) (ha : IsSuccLimit a) {b : β} :
    f a ≤ b ↔ ∀ a' < a, f a' ≤ b := by
  simpa [mem_upperBounds] using isLUB_le_iff (hf.isLUB_of_isSuccLimit ha)

theorem lf_iff_exists_lt (hf : IsNormal f) (ha : IsSuccLimit a) {b : β} :
    b < f a ↔ ∃ a' < a, b < f a' := by
  simpa [mem_upperBounds] using lt_isLUB_iff (hf.isLUB_of_isSuccLimit ha)

theorem _root_.InitialSeg.isNormal (f : α ≤i β) : IsNormal f where
  strictMono := f.strictMono
  mem_lowerBounds_upperBounds := by
    intro a ha b hb
    apply le_of_forall_lt
    intro c hc
    obtain ⟨c, rfl⟩ := f.mem_range_of_le hc.le
    rw [f.lt_iff_lt] at hc
    have := hb (mem_image_of_mem f hc)
    simp only [mem_upperBounds] at hb

    have := hb hc

protected theorem id : IsNormal (@id α) where
  strictMono := strictMono_id
  isLUB_of_isSuccLimit := by
    intro a ha
    simp
    refine isLUB_Iio

end IsNormal
