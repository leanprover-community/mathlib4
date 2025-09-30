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
@[mk_iff isNormal_iff']
structure IsNormal [LinearOrder α] [LinearOrder β] (f : α → β) : Prop where
  strictMono : StrictMono f
  /-- This condition is the RHS of the `IsLUB (f '' Iio a) (f a)` predicate, which is sufficient
  since the LHS is implied by monotonicity. -/
  mem_lowerBounds_upperBounds_of_isSuccLimit {a : α} (ha : IsSuccLimit a) :
    f a ∈ lowerBounds (upperBounds (f '' Iio a))

theorem isNormal_iff [LinearOrder α] [LinearOrder β] {f : α → β} :
    IsNormal f ↔ StrictMono f ∧ ∀ o, IsSuccLimit o → ∀ a, (∀ b < o, f b ≤ a) → f o ≤ a := by
  simp [isNormal_iff', mem_lowerBounds, mem_upperBounds]

namespace IsNormal

section LinearOrder
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

theorem isLUB_image_Iio_of_isSuccLimit {f : α → β} (hf : IsNormal f) {a : α} (ha : IsSuccLimit a) :
    IsLUB (f '' Iio a) (f a) := by
  refine ⟨?_, hf.2 ha⟩
  rintro - ⟨b, hb, rfl⟩
  exact (hf.1 hb).le

@[deprecated "use the default constructor of `IsNormal` directly" (since := "2025-07-08")]
theorem of_mem_lowerBounds_upperBounds {f : α → β} (hf : StrictMono f)
    (hl : ∀ {a}, IsSuccLimit a → f a ∈ lowerBounds (upperBounds (f '' Iio a))) : IsNormal f :=
  ⟨hf, hl⟩

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
  · simpa [mem_upperBounds, hf.strictMono.le_iff_le] using hs.1
  · by_cases ha : a ∈ s
    · simp_all [mem_upperBounds]
    · have ha' := hs.isSuccLimit_of_notMem hs' ha
      rw [le_iff_forall_le hf ha']
      intro c hc
      obtain ⟨d, hd, hcd, hda⟩ := hs.exists_between hc
      simp_rw [mem_upperBounds, forall_mem_image] at hb
      exact (hf.strictMono hcd).le.trans (hb hd)

theorem _root_.InitialSeg.isNormal (f : α ≤i β) : IsNormal f where
  strictMono := f.strictMono
  mem_lowerBounds_upperBounds_of_isSuccLimit ha := by
    rw [f.image_Iio]
    exact (f.map_isSuccLimit ha).isLUB_Iio.2

theorem _root_.PrincipalSeg.isNormal (f : α <i β) : IsNormal f :=
  (f : α ≤i β).isNormal

theorem _root_.OrderIso.isNormal (f : α ≃o β) : IsNormal f :=
  f.toInitialSeg.isNormal

protected theorem id : IsNormal (@id α) :=
  (OrderIso.refl _).isNormal

theorem comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal (g ∘ f) := by
  refine ⟨hg.strictMono.comp hf.strictMono, fun ha b hb ↦ ?_⟩
  simp_rw [Function.comp_apply, mem_upperBounds, forall_mem_image] at hb
  simpa [hg.le_iff_forall_le (hf.map_isSuccLimit ha), hf.lt_iff_exists_lt ha] using
    fun c d hd hc ↦ (hg.strictMono hc).le.trans (hb hd)

section WellFoundedLT
variable [WellFoundedLT α] [SuccOrder α]

theorem of_succ_lt
    (hs : ∀ a, f a < f (succ a)) (hl : ∀ {a}, IsSuccLimit a → IsLUB (f '' Iio a) (f a)) :
    IsNormal f := by
  refine ⟨fun a b ↦ ?_, fun ha ↦ (hl ha).2⟩
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

protected theorem ext [OrderBot α] {g : α → β} (hf : IsNormal f) (hg : IsNormal g) :
    f = g ↔ f ⊥ = g ⊥ ∧ ∀ a, f a = g a → f (succ a) = g (succ a) := by
  constructor
  · simp_all
  rintro ⟨H₁, H₂⟩
  ext a
  induction a using SuccOrder.limitRecOn with
  | isMin a ha => rw [ha.eq_bot, H₁]
  | succ a ha IH => exact H₂ a IH
  | isSuccLimit a ha IH =>
    apply (hf.isLUB_image_Iio_of_isSuccLimit ha).unique
    convert hg.isLUB_image_Iio_of_isSuccLimit ha using 1
    aesop

end WellFoundedLT
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

theorem preimage_Iic (hf : IsNormal f) {x : β}
    (h₁ : (f ⁻¹' Iic x).Nonempty) (h₂ : BddAbove (f ⁻¹' Iic x)) :
    f ⁻¹' Iic x = Iic (sSup (f ⁻¹' Iic x)) := by
  refine le_antisymm (fun _ ↦ le_csSup h₂) (fun y hy ↦ ?_)
  obtain hy | rfl := hy.lt_or_eq
  · rw [lt_csSup_iff h₂ h₁] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    exact (hf.strictMono hyz).le.trans hz
  · rw [mem_preimage, hf.map_sSup h₁ h₂]
    apply (csSup_le_csSup bddAbove_Iic _ (image_preimage_subset ..)).trans
    · rw [csSup_Iic]
    · simpa

end ConditionallyCompleteLinearOrder

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α] [ConditionallyCompleteLinearOrder β]

theorem apply_of_isSuccLimit (hf : IsNormal f) (ha : IsSuccLimit a) :
    f a = ⨆ b : Iio a, f b := by
  convert map_iSup hf _
  · exact ha.iSup_Iio.symm
  · exact ⟨⊥, ha.bot_lt⟩
  · use a
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact hx.le

end ConditionallyCompleteLinearOrderBot
end IsNormal
end Order
