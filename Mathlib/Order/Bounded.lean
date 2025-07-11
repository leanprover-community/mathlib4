/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.RelClasses
import Mathlib.Order.Interval.Set.Basic

/-!
# Bounded and unbounded sets
We prove miscellaneous lemmas about bounded and unbounded sets. Many of these are just variations on
the same ideas, or similar results with a few minor differences. The file is divided into these
different general ideas.
-/

assert_not_exists RelIso

namespace Set

variable {α : Type*} {r : α → α → Prop} {s t : Set α}

/-! ### Subsets of bounded and unbounded sets -/


theorem Bounded.mono (hst : s ⊆ t) (hs : Bounded r t) : Bounded r s :=
  hs.imp fun _ ha b hb => ha b (hst hb)

theorem Unbounded.mono (hst : s ⊆ t) (hs : Unbounded r s) : Unbounded r t := fun a =>
  let ⟨b, hb, hb'⟩ := hs a
  ⟨b, hst hb, hb'⟩

/-! ### Alternate characterizations of unboundedness on orders -/


theorem unbounded_le_of_forall_exists_lt [Preorder α] (h : ∀ a, ∃ b ∈ s, a < b) :
    Unbounded (· ≤ ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_gt hb'⟩

theorem unbounded_le_iff [LinearOrder α] : Unbounded (· ≤ ·) s ↔ ∀ a, ∃ b ∈ s, a < b := by
  simp only [Unbounded, not_le]

theorem unbounded_lt_of_forall_exists_le [Preorder α] (h : ∀ a, ∃ b ∈ s, a ≤ b) :
    Unbounded (· < ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => hba.not_ge hb'⟩

theorem unbounded_lt_iff [LinearOrder α] : Unbounded (· < ·) s ↔ ∀ a, ∃ b ∈ s, a ≤ b := by
  simp only [Unbounded, not_lt]

theorem unbounded_ge_of_forall_exists_gt [Preorder α] (h : ∀ a, ∃ b ∈ s, b < a) :
    Unbounded (· ≥ ·) s :=
  @unbounded_le_of_forall_exists_lt αᵒᵈ _ _ h

theorem unbounded_ge_iff [LinearOrder α] : Unbounded (· ≥ ·) s ↔ ∀ a, ∃ b ∈ s, b < a :=
  ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, lt_of_not_ge hba⟩,
    unbounded_ge_of_forall_exists_gt⟩

theorem unbounded_gt_of_forall_exists_ge [Preorder α] (h : ∀ a, ∃ b ∈ s, b ≤ a) :
    Unbounded (· > ·) s := fun a =>
  let ⟨b, hb, hb'⟩ := h a
  ⟨b, hb, fun hba => not_le_of_gt hba hb'⟩

theorem unbounded_gt_iff [LinearOrder α] : Unbounded (· > ·) s ↔ ∀ a, ∃ b ∈ s, b ≤ a :=
  ⟨fun h a =>
    let ⟨b, hb, hba⟩ := h a
    ⟨b, hb, le_of_not_gt hba⟩,
    unbounded_gt_of_forall_exists_ge⟩

/-! ### Relation between boundedness by strict and nonstrict orders. -/


/-! #### Less and less or equal -/


theorem Bounded.rel_mono {r' : α → α → Prop} (h : Bounded r s) (hrr' : r ≤ r') : Bounded r' s :=
  let ⟨a, ha⟩ := h
  ⟨a, fun b hb => hrr' b a (ha b hb)⟩

theorem bounded_le_of_bounded_lt [Preorder α] (h : Bounded (· < ·) s) : Bounded (· ≤ ·) s :=
  h.rel_mono fun _ _ => le_of_lt

theorem Unbounded.rel_mono {r' : α → α → Prop} (hr : r' ≤ r) (h : Unbounded r s) : Unbounded r' s :=
  fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (hr b a hba')⟩

theorem unbounded_lt_of_unbounded_le [Preorder α] (h : Unbounded (· ≤ ·) s) : Unbounded (· < ·) s :=
  h.rel_mono fun _ _ => le_of_lt

theorem bounded_le_iff_bounded_lt [Preorder α] [NoMaxOrder α] :
    Bounded (· ≤ ·) s ↔ Bounded (· < ·) s := by
  refine ⟨fun h => ?_, bounded_le_of_bounded_lt⟩
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := exists_gt a
  exact ⟨b, fun c hc => lt_of_le_of_lt (ha c hc) hb⟩

theorem unbounded_lt_iff_unbounded_le [Preorder α] [NoMaxOrder α] :
    Unbounded (· < ·) s ↔ Unbounded (· ≤ ·) s := by
  simp_rw [← not_bounded_iff, bounded_le_iff_bounded_lt]

/-! #### Greater and greater or equal -/


theorem bounded_ge_of_bounded_gt [Preorder α] (h : Bounded (· > ·) s) : Bounded (· ≥ ·) s :=
  let ⟨a, ha⟩ := h
  ⟨a, fun b hb => le_of_lt (ha b hb)⟩

theorem unbounded_gt_of_unbounded_ge [Preorder α] (h : Unbounded (· ≥ ·) s) : Unbounded (· > ·) s :=
  fun a =>
  let ⟨b, hb, hba⟩ := h a
  ⟨b, hb, fun hba' => hba (le_of_lt hba')⟩

theorem bounded_ge_iff_bounded_gt [Preorder α] [NoMinOrder α] :
    Bounded (· ≥ ·) s ↔ Bounded (· > ·) s :=
  @bounded_le_iff_bounded_lt αᵒᵈ _ _ _

theorem unbounded_gt_iff_unbounded_ge [Preorder α] [NoMinOrder α] :
    Unbounded (· > ·) s ↔ Unbounded (· ≥ ·) s :=
  @unbounded_lt_iff_unbounded_le αᵒᵈ _ _ _

/-! ### The universal set -/


theorem unbounded_le_univ [LE α] [NoTopOrder α] : Unbounded (· ≤ ·) (@Set.univ α) := fun a =>
  let ⟨b, hb⟩ := exists_not_le a
  ⟨b, ⟨⟩, hb⟩

theorem unbounded_lt_univ [Preorder α] [NoTopOrder α] : Unbounded (· < ·) (@Set.univ α) :=
  unbounded_lt_of_unbounded_le unbounded_le_univ

theorem unbounded_ge_univ [LE α] [NoBotOrder α] : Unbounded (· ≥ ·) (@Set.univ α) := fun a =>
  let ⟨b, hb⟩ := exists_not_ge a
  ⟨b, ⟨⟩, hb⟩

theorem unbounded_gt_univ [Preorder α] [NoBotOrder α] : Unbounded (· > ·) (@Set.univ α) :=
  unbounded_gt_of_unbounded_ge unbounded_ge_univ

/-! ### Bounded and unbounded intervals -/


theorem bounded_self (a : α) : Bounded r { b | r b a } :=
  ⟨a, fun _ => id⟩

/-! #### Half-open bounded intervals -/


theorem bounded_lt_Iio [Preorder α] (a : α) : Bounded (· < ·) (Iio a) :=
  bounded_self a

theorem bounded_le_Iio [Preorder α] (a : α) : Bounded (· ≤ ·) (Iio a) :=
  bounded_le_of_bounded_lt (bounded_lt_Iio a)

theorem bounded_le_Iic [Preorder α] (a : α) : Bounded (· ≤ ·) (Iic a) :=
  bounded_self a

theorem bounded_lt_Iic [Preorder α] [NoMaxOrder α] (a : α) : Bounded (· < ·) (Iic a) := by
  simp only [← bounded_le_iff_bounded_lt, bounded_le_Iic]

theorem bounded_gt_Ioi [Preorder α] (a : α) : Bounded (· > ·) (Ioi a) :=
  bounded_self a

theorem bounded_ge_Ioi [Preorder α] (a : α) : Bounded (· ≥ ·) (Ioi a) :=
  bounded_ge_of_bounded_gt (bounded_gt_Ioi a)

theorem bounded_ge_Ici [Preorder α] (a : α) : Bounded (· ≥ ·) (Ici a) :=
  bounded_self a

theorem bounded_gt_Ici [Preorder α] [NoMinOrder α] (a : α) : Bounded (· > ·) (Ici a) := by
  simp only [← bounded_ge_iff_bounded_gt, bounded_ge_Ici]

/-! #### Other bounded intervals -/


theorem bounded_lt_Ioo [Preorder α] (a b : α) : Bounded (· < ·) (Ioo a b) :=
  (bounded_lt_Iio b).mono Set.Ioo_subset_Iio_self

theorem bounded_lt_Ico [Preorder α] (a b : α) : Bounded (· < ·) (Ico a b) :=
  (bounded_lt_Iio b).mono Set.Ico_subset_Iio_self

theorem bounded_lt_Ioc [Preorder α] [NoMaxOrder α] (a b : α) : Bounded (· < ·) (Ioc a b) :=
  (bounded_lt_Iic b).mono Set.Ioc_subset_Iic_self

theorem bounded_lt_Icc [Preorder α] [NoMaxOrder α] (a b : α) : Bounded (· < ·) (Icc a b) :=
  (bounded_lt_Iic b).mono Set.Icc_subset_Iic_self

theorem bounded_le_Ioo [Preorder α] (a b : α) : Bounded (· ≤ ·) (Ioo a b) :=
  (bounded_le_Iio b).mono Set.Ioo_subset_Iio_self

theorem bounded_le_Ico [Preorder α] (a b : α) : Bounded (· ≤ ·) (Ico a b) :=
  (bounded_le_Iio b).mono Set.Ico_subset_Iio_self

theorem bounded_le_Ioc [Preorder α] (a b : α) : Bounded (· ≤ ·) (Ioc a b) :=
  (bounded_le_Iic b).mono Set.Ioc_subset_Iic_self

theorem bounded_le_Icc [Preorder α] (a b : α) : Bounded (· ≤ ·) (Icc a b) :=
  (bounded_le_Iic b).mono Set.Icc_subset_Iic_self

theorem bounded_gt_Ioo [Preorder α] (a b : α) : Bounded (· > ·) (Ioo a b) :=
  (bounded_gt_Ioi a).mono Set.Ioo_subset_Ioi_self

theorem bounded_gt_Ioc [Preorder α] (a b : α) : Bounded (· > ·) (Ioc a b) :=
  (bounded_gt_Ioi a).mono Set.Ioc_subset_Ioi_self

theorem bounded_gt_Ico [Preorder α] [NoMinOrder α] (a b : α) : Bounded (· > ·) (Ico a b) :=
  (bounded_gt_Ici a).mono Set.Ico_subset_Ici_self

theorem bounded_gt_Icc [Preorder α] [NoMinOrder α] (a b : α) : Bounded (· > ·) (Icc a b) :=
  (bounded_gt_Ici a).mono Set.Icc_subset_Ici_self

theorem bounded_ge_Ioo [Preorder α] (a b : α) : Bounded (· ≥ ·) (Ioo a b) :=
  (bounded_ge_Ioi a).mono Set.Ioo_subset_Ioi_self

theorem bounded_ge_Ioc [Preorder α] (a b : α) : Bounded (· ≥ ·) (Ioc a b) :=
  (bounded_ge_Ioi a).mono Set.Ioc_subset_Ioi_self

theorem bounded_ge_Ico [Preorder α] (a b : α) : Bounded (· ≥ ·) (Ico a b) :=
  (bounded_ge_Ici a).mono Set.Ico_subset_Ici_self

theorem bounded_ge_Icc [Preorder α] (a b : α) : Bounded (· ≥ ·) (Icc a b) :=
  (bounded_ge_Ici a).mono Set.Icc_subset_Ici_self

/-! #### Unbounded intervals -/


theorem unbounded_le_Ioi [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· ≤ ·) (Ioi a) := fun b =>
  let ⟨c, hc⟩ := exists_gt (a ⊔ b)
  ⟨c, le_sup_left.trans_lt hc, (le_sup_right.trans_lt hc).not_ge⟩

theorem unbounded_le_Ici [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· ≤ ·) (Ici a) :=
  (unbounded_le_Ioi a).mono Set.Ioi_subset_Ici_self

theorem unbounded_lt_Ioi [SemilatticeSup α] [NoMaxOrder α] (a : α) :
    Unbounded (· < ·) (Ioi a) :=
  unbounded_lt_of_unbounded_le (unbounded_le_Ioi a)

theorem unbounded_lt_Ici [SemilatticeSup α] (a : α) : Unbounded (· < ·) (Ici a) := fun b =>
  ⟨a ⊔ b, le_sup_left, le_sup_right.not_gt⟩

/-! ### Bounded initial segments -/


theorem bounded_inter_not (H : ∀ a b, ∃ m, ∀ c, r c a ∨ r c b → r c m) (a : α) :
    Bounded r (s ∩ { b | ¬r b a }) ↔ Bounded r s := by
  refine ⟨?_, Bounded.mono inter_subset_left⟩
  rintro ⟨b, hb⟩
  obtain ⟨m, hm⟩ := H a b
  exact ⟨m, fun c hc => hm c (or_iff_not_imp_left.2 fun hca => hb c ⟨hc, hca⟩)⟩

theorem unbounded_inter_not (H : ∀ a b, ∃ m, ∀ c, r c a ∨ r c b → r c m) (a : α) :
    Unbounded r (s ∩ { b | ¬r b a }) ↔ Unbounded r s := by
  simp_rw [← not_bounded_iff, bounded_inter_not H]

/-! #### Less or equal -/


theorem bounded_le_inter_not_le [SemilatticeSup α] (a : α) :
    Bounded (· ≤ ·) (s ∩ { b | ¬b ≤ a }) ↔ Bounded (· ≤ ·) s :=
  bounded_inter_not (fun x y => ⟨x ⊔ y, fun _ h => h.elim le_sup_of_le_left le_sup_of_le_right⟩) a

theorem unbounded_le_inter_not_le [SemilatticeSup α] (a : α) :
    Unbounded (· ≤ ·) (s ∩ { b | ¬b ≤ a }) ↔ Unbounded (· ≤ ·) s := by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_le_inter_not_le a

theorem bounded_le_inter_lt [LinearOrder α] (a : α) :
    Bounded (· ≤ ·) (s ∩ { b | a < b }) ↔ Bounded (· ≤ ·) s := by
  simp_rw [← not_le, bounded_le_inter_not_le]

theorem unbounded_le_inter_lt [LinearOrder α] (a : α) :
    Unbounded (· ≤ ·) (s ∩ { b | a < b }) ↔ Unbounded (· ≤ ·) s := by
  convert @unbounded_le_inter_not_le _ s _ a
  exact lt_iff_not_ge

theorem bounded_le_inter_le [LinearOrder α] (a : α) :
    Bounded (· ≤ ·) (s ∩ { b | a ≤ b }) ↔ Bounded (· ≤ ·) s := by
  refine ⟨?_, Bounded.mono Set.inter_subset_left⟩
  rw [← @bounded_le_inter_lt _ s _ a]
  exact Bounded.mono fun x ⟨hx, hx'⟩ => ⟨hx, le_of_lt hx'⟩

theorem unbounded_le_inter_le [LinearOrder α] (a : α) :
    Unbounded (· ≤ ·) (s ∩ { b | a ≤ b }) ↔ Unbounded (· ≤ ·) s := by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_le_inter_le a

/-! #### Less than -/


theorem bounded_lt_inter_not_lt [SemilatticeSup α] (a : α) :
    Bounded (· < ·) (s ∩ { b | ¬b < a }) ↔ Bounded (· < ·) s :=
  bounded_inter_not (fun x y => ⟨x ⊔ y, fun _ h => h.elim lt_sup_of_lt_left lt_sup_of_lt_right⟩) a

theorem unbounded_lt_inter_not_lt [SemilatticeSup α] (a : α) :
    Unbounded (· < ·) (s ∩ { b | ¬b < a }) ↔ Unbounded (· < ·) s := by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_lt_inter_not_lt a

theorem bounded_lt_inter_le [LinearOrder α] (a : α) :
    Bounded (· < ·) (s ∩ { b | a ≤ b }) ↔ Bounded (· < ·) s := by
  convert @bounded_lt_inter_not_lt _ s _ a
  exact not_lt.symm

theorem unbounded_lt_inter_le [LinearOrder α] (a : α) :
    Unbounded (· < ·) (s ∩ { b | a ≤ b }) ↔ Unbounded (· < ·) s := by
  convert @unbounded_lt_inter_not_lt _ s _ a
  exact not_lt.symm

theorem bounded_lt_inter_lt [LinearOrder α] [NoMaxOrder α] (a : α) :
    Bounded (· < ·) (s ∩ { b | a < b }) ↔ Bounded (· < ·) s := by
  rw [← bounded_le_iff_bounded_lt, ← bounded_le_iff_bounded_lt]
  exact bounded_le_inter_lt a

theorem unbounded_lt_inter_lt [LinearOrder α] [NoMaxOrder α] (a : α) :
    Unbounded (· < ·) (s ∩ { b | a < b }) ↔ Unbounded (· < ·) s := by
  rw [← not_bounded_iff, ← not_bounded_iff, not_iff_not]
  exact bounded_lt_inter_lt a

/-! #### Greater or equal -/


theorem bounded_ge_inter_not_ge [SemilatticeInf α] (a : α) :
    Bounded (· ≥ ·) (s ∩ { b | ¬a ≤ b }) ↔ Bounded (· ≥ ·) s :=
  @bounded_le_inter_not_le αᵒᵈ s _ a

theorem unbounded_ge_inter_not_ge [SemilatticeInf α] (a : α) :
    Unbounded (· ≥ ·) (s ∩ { b | ¬a ≤ b }) ↔ Unbounded (· ≥ ·) s :=
  @unbounded_le_inter_not_le αᵒᵈ s _ a

theorem bounded_ge_inter_gt [LinearOrder α] (a : α) :
    Bounded (· ≥ ·) (s ∩ { b | b < a }) ↔ Bounded (· ≥ ·) s :=
  @bounded_le_inter_lt αᵒᵈ s _ a

theorem unbounded_ge_inter_gt [LinearOrder α] (a : α) :
    Unbounded (· ≥ ·) (s ∩ { b | b < a }) ↔ Unbounded (· ≥ ·) s :=
  @unbounded_le_inter_lt αᵒᵈ s _ a

theorem bounded_ge_inter_ge [LinearOrder α] (a : α) :
    Bounded (· ≥ ·) (s ∩ { b | b ≤ a }) ↔ Bounded (· ≥ ·) s :=
  @bounded_le_inter_le αᵒᵈ s _ a

theorem unbounded_ge_iff_unbounded_inter_ge [LinearOrder α] (a : α) :
    Unbounded (· ≥ ·) (s ∩ { b | b ≤ a }) ↔ Unbounded (· ≥ ·) s :=
  @unbounded_le_inter_le αᵒᵈ s _ a

/-! #### Greater than -/


theorem bounded_gt_inter_not_gt [SemilatticeInf α] (a : α) :
    Bounded (· > ·) (s ∩ { b | ¬a < b }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_not_lt αᵒᵈ s _ a

theorem unbounded_gt_inter_not_gt [SemilatticeInf α] (a : α) :
    Unbounded (· > ·) (s ∩ { b | ¬a < b }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_not_lt αᵒᵈ s _ a

theorem bounded_gt_inter_ge [LinearOrder α] (a : α) :
    Bounded (· > ·) (s ∩ { b | b ≤ a }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_le αᵒᵈ s _ a

theorem unbounded_inter_ge [LinearOrder α] (a : α) :
    Unbounded (· > ·) (s ∩ { b | b ≤ a }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_le αᵒᵈ s _ a

theorem bounded_gt_inter_gt [LinearOrder α] [NoMinOrder α] (a : α) :
    Bounded (· > ·) (s ∩ { b | b < a }) ↔ Bounded (· > ·) s :=
  @bounded_lt_inter_lt αᵒᵈ s _ _ a

theorem unbounded_gt_inter_gt [LinearOrder α] [NoMinOrder α] (a : α) :
    Unbounded (· > ·) (s ∩ { b | b < a }) ↔ Unbounded (· > ·) s :=
  @unbounded_lt_inter_lt αᵒᵈ s _ _ a

end Set
