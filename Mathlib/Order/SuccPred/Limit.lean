/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Order.BoundedOrder.Lattice

/-!
# Successor and predecessor limits

We define the predicate `Order.IsSuccPrelimit` for "successor pre-limits", values that don't cover
any others. They are so named since they can't be the successors of anything smaller. We define
`Order.IsPredPrelimit` analogously, and prove basic results.

For some applications, it is desirable to exclude minimal elements from being successor limits, or
maximal elements from being predecessor limits. As such, we also provide `Order.IsSuccLimit` and
`Order.IsPredLimit`, which exclude these cases.
-/

@[expose] public section

variable {α : Type*} {a b : α}

namespace Order

open Function Set OrderDual

/-! ### Successor and predecessor limits -/

section LT

variable [LT α]

/-- A successor pre-limit is a value that doesn't cover any other.

It's so named because in a successor order, a successor pre-limit can't be the successor of anything
smaller.

Use `IsSuccLimit` if you want to exclude the case of a minimal element. -/
@[to_dual
/-- A predecessor pre-limit is a value that isn't covered by any other.

It's so named because in a predecessor order, a predecessor pre-limit can't be the predecessor of
anything smaller.

Use `IsPredLimit` to exclude the case of a maximal element. -/]
def IsSuccPrelimit (a : α) : Prop :=
  ∀ b, ¬b ⋖ a

@[to_dual]
theorem not_isSuccPrelimit_iff_exists_covBy (a : α) : ¬IsSuccPrelimit a ↔ ∃ b, b ⋖ a := by
  simp [IsSuccPrelimit]

@[to_dual (attr := simp)]
theorem IsSuccPrelimit.of_dense [DenselyOrdered α] (a : α) : IsSuccPrelimit a := fun _ => not_covBy

@[to_dual (attr := simp)]
theorem isSuccPrelimit_toDual_iff : IsSuccPrelimit (toDual a) ↔ IsPredPrelimit a := by
  simp [IsSuccPrelimit, IsPredPrelimit]

@[to_dual]
alias ⟨_, IsPredPrelimit.dual⟩ := isSuccPrelimit_toDual_iff

end LT

section Preorder

variable [Preorder α]

/-- A successor limit is a value that isn't minimal and doesn't cover any other.

It's so named because in a successor order, a successor limit can't be the successor of anything
smaller.

Use `IsSuccPrelimit` if you want to include the case of a minimal element. -/
@[to_dual
/-- A predecessor limit is a value that isn't maximal and doesn't cover any other.

It's so named because in a predecessor order, a predecessor limit can't be the predecessor of
anything larger.

Use `IsPredPrelimit` if you want to include the case of a maximal element. -/]
def IsSuccLimit (a : α) : Prop :=
  ¬ IsMin a ∧ IsSuccPrelimit a

@[to_dual (attr := simp)]
theorem isSuccLimit_toDual_iff : IsSuccLimit (toDual a) ↔ IsPredLimit a := by
  simp [IsSuccLimit, IsPredLimit]

@[to_dual] alias ⟨_, IsPredLimit.dual⟩ := isSuccLimit_toDual_iff

@[to_dual]
protected theorem IsSuccLimit.not_isMin (h : IsSuccLimit a) : ¬ IsMin a := h.1

@[to_dual (attr := simp)]
protected theorem IsSuccLimit.isSuccPrelimit (h : IsSuccLimit a) : IsSuccPrelimit a := h.2

@[deprecated IsPredLimit.isPredPrelimit (since := "2026-02-22")]
theorem not_isPredLimit_of_not_isPredPrelimit : ¬ IsPredPrelimit a → ¬ IsPredLimit a :=
  mt IsPredLimit.isPredPrelimit

@[to_dual]
theorem IsSuccPrelimit.isSuccLimit_of_not_isMin (h : IsSuccPrelimit a) (ha : ¬ IsMin a) :
    IsSuccLimit a :=
  ⟨ha, h⟩

@[to_dual]
theorem IsSuccPrelimit.isSuccLimit [NoMinOrder α] (h : IsSuccPrelimit a) : IsSuccLimit a :=
  h.isSuccLimit_of_not_isMin (not_isMin a)

@[to_dual]
theorem isSuccPrelimit_iff_isSuccLimit_of_not_isMin (h : ¬ IsMin a) :
    IsSuccPrelimit a ↔ IsSuccLimit a :=
  ⟨fun ha ↦ ha.isSuccLimit_of_not_isMin h, IsSuccLimit.isSuccPrelimit⟩

@[to_dual]
theorem isSuccPrelimit_iff_isSuccLimit [NoMinOrder α] : IsSuccPrelimit a ↔ IsSuccLimit a :=
  isSuccPrelimit_iff_isSuccLimit_of_not_isMin (not_isMin a)

@[to_dual]
protected theorem _root_.IsMin.not_isSuccLimit (h : IsMin a) : ¬ IsSuccLimit a :=
  fun ha ↦ ha.not_isMin h

@[to_dual]
protected theorem _root_.IsMin.isSuccPrelimit : IsMin a → IsSuccPrelimit a := fun h _ hab =>
  not_isMin_of_lt hab.lt h

@[to_dual]
theorem IsSuccLimit.nonempty_Iio (h : IsSuccLimit a) : (Set.Iio a).Nonempty :=
  not_isMin_iff.1 h.1

@[to_dual]
theorem IsSuccPrelimit.noMaxOrder_Iio (h : IsSuccPrelimit a) : NoMaxOrder (Set.Iio a) := by
  refine ⟨fun ⟨b, hb⟩ ↦ ?_⟩
  obtain ⟨c, hbc, hca⟩ := (not_covBy_iff hb).1 (h b)
  exact ⟨⟨c, hca⟩, hbc⟩

@[to_dual]
theorem isSuccPrelimit_bot [OrderBot α] : IsSuccPrelimit (⊥ : α) :=
  isMin_bot.isSuccPrelimit

@[to_dual]
theorem not_isSuccLimit_bot [OrderBot α] : ¬ IsSuccLimit (⊥ : α) :=
  isMin_bot.not_isSuccLimit

@[to_dual]
theorem IsSuccLimit.ne_bot [OrderBot α] (h : IsSuccLimit a) : a ≠ ⊥ := by
  rintro rfl
  exact not_isSuccLimit_bot h

@[to_dual]
theorem not_isSuccLimit_iff : ¬ IsSuccLimit a ↔ IsMin a ∨ ¬ IsSuccPrelimit a := by
  rw [IsSuccLimit, not_and_or, not_not]

@[to_dual]
theorem IsSuccPrelimit.subtypeVal {s : Set α} (hs : IsLowerSet s) {a : s}
    (ha : IsSuccPrelimit a) : IsSuccPrelimit a.1 := by
  intro b hb
  have := ha ⟨b, hs hb.le a.2⟩
  rw [not_covBy_iff] at this
  · obtain ⟨c, hc, hc'⟩ := this
    exact hb.2 hc hc'
  · exact hb.lt

@[to_dual]
theorem IsSuccLimit.subtypeVal {s : Set α} (hs : IsLowerSet s) {a : s}
    (ha : IsSuccLimit a) : IsSuccLimit a.1 := by
  refine ⟨?_, ha.isSuccPrelimit.subtypeVal hs⟩
  have := ha.1
  rw [not_isMin_iff] at ⊢ this
  obtain ⟨b, hb⟩ := this
  exact ⟨b, hb⟩

/-- Given `j < i` with `i` a successor pre-limit, `IsSuccPrelimit.mid` picks an arbitrary element
strictly between `j` and `i`. -/
@[to_dual
/-- Given `i < j` with `i` a predecessor pre-limit, `IsSuccPrelimit.mid` picks an arbitrary element
strictly between `i` and `j`. -/]
noncomputable def IsSuccPrelimit.mid {i j : α} (hi : IsSuccPrelimit i) (hj : j < i) : Ioo j i :=
  Classical.indefiniteDescription _ ((not_covBy_iff_nonempty_Ioo hj).mp <| hi j)

variable [SuccOrder α]

@[to_dual]
protected theorem IsSuccPrelimit.isMax (h : IsSuccPrelimit (succ a)) : IsMax a := by
  by_contra H
  exact h a (covBy_succ_of_not_isMax H)

@[to_dual]
protected theorem IsSuccLimit.isMax (h : IsSuccLimit (succ a)) : IsMax a :=
  h.isSuccPrelimit.isMax

set_option linter.existingAttributeWarning false in
@[to_dual, deprecated IsSuccPrelimit.isMax (since := "2026-03-31")]
theorem not_isSuccPrelimit_succ_of_not_isMax (ha : ¬ IsMax a) : ¬ IsSuccPrelimit (succ a) :=
  mt IsSuccPrelimit.isMax ha

attribute [deprecated IsPredPrelimit.isMin (since := "2026-03-31")]
not_isPredPrelimit_pred_of_not_isMin

set_option linter.existingAttributeWarning false in
@[to_dual, deprecated IsSuccLimit.isMax (since := "2026-03-31")]
theorem not_isSuccLimit_succ_of_not_isMax (ha : ¬ IsMax a) : ¬ IsSuccLimit (succ a) :=
  mt IsSuccLimit.isMax ha

attribute [deprecated IsPredLimit.isMin (since := "2026-03-31")]
not_isPredLimit_pred_of_not_isMin

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual]
theorem IsSuccPrelimit.succ_ne (h : IsSuccPrelimit a) (b : α) : succ b ≠ a := by
  rintro rfl
  exact not_isMax _ h.isMax

@[to_dual]
theorem IsSuccLimit.succ_ne (h : IsSuccLimit a) (b : α) : succ b ≠ a :=
  h.isSuccPrelimit.succ_ne b

@[to_dual (attr := simp)]
theorem not_isSuccPrelimit_succ (a : α) : ¬IsSuccPrelimit (succ a) := fun h => h.succ_ne _ rfl

@[to_dual (attr := simp)]
theorem not_isSuccLimit_succ (a : α) : ¬IsSuccLimit (succ a) := fun h => h.succ_ne _ rfl

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α] [NoMaxOrder α]

@[to_dual]
theorem IsSuccPrelimit.isMin_of_noMax (h : IsSuccPrelimit a) : IsMin a := by
  intro b hb
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_isSuccPrelimit_succ _ h).elim

@[to_dual (attr := simp)]
theorem isSuccPrelimit_iff_of_noMax : IsSuccPrelimit a ↔ IsMin a :=
  ⟨IsSuccPrelimit.isMin_of_noMax, IsMin.isSuccPrelimit⟩

@[to_dual (attr := simp)]
theorem not_isSuccLimit_of_noMax : ¬ IsSuccLimit a :=
  fun h ↦ h.not_isMin h.isSuccPrelimit.isMin_of_noMax

@[to_dual]
theorem not_isSuccPrelimit_of_noMax [NoMinOrder α] : ¬ IsSuccPrelimit a := by simp

end IsSuccArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_dual]
theorem isSuccLimit_iff_of_orderBot [OrderBot α] : IsSuccLimit a ↔ a ≠ ⊥ ∧ IsSuccPrelimit a := by
  rw [IsSuccLimit, isMin_iff_eq_bot]

@[deprecated (since := "2026-03-31")] alias isSuccLimit_iff := isSuccLimit_iff_of_orderBot
@[deprecated (since := "2026-03-31")] alias isPredLimit_iff := isPredLimit_iff_of_orderTop

@[to_dual lt_top]
theorem IsSuccLimit.bot_lt [OrderBot α] (h : IsSuccLimit a) : ⊥ < a :=
  h.ne_bot.bot_lt

variable [SuccOrder α]

@[to_dual]
theorem isSuccPrelimit_of_succ_ne (h : ∀ b, succ b ≠ a) : IsSuccPrelimit a := fun b hba =>
  h b (CovBy.succ_eq hba)

@[to_dual]
theorem not_isSuccPrelimit_iff : ¬ IsSuccPrelimit a ↔ ∃ b, ¬ IsMax b ∧ succ b = a := by
  rw [not_isSuccPrelimit_iff_exists_covBy]
  refine exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_isMax, (CovBy.succ_eq hba)⟩, ?_⟩
  rintro ⟨h, rfl⟩
  exact covBy_succ_of_not_isMax h

/-- See `not_isSuccPrelimit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
@[to_dual]
theorem mem_range_succ_of_not_isSuccPrelimit (h : ¬ IsSuccPrelimit a) :
    a ∈ range (succ : α → α) := by
  obtain ⟨b, hb⟩ := not_isSuccPrelimit_iff.1 h
  exact ⟨b, hb.2⟩

@[to_dual]
theorem mem_range_succ_or_isSuccPrelimit (a) : a ∈ range (succ : α → α) ∨ IsSuccPrelimit a :=
  or_iff_not_imp_right.2 <| mem_range_succ_of_not_isSuccPrelimit

@[to_dual]
theorem isMin_or_mem_range_succ_or_isSuccLimit (a) :
    IsMin a ∨ a ∈ range (succ : α → α) ∨ IsSuccLimit a := by
  rw [IsSuccLimit]
  have := mem_range_succ_or_isSuccPrelimit a
  tauto

@[to_dual isPredPrelimit_of_lt_pred]
theorem isSuccPrelimit_of_succ_lt (H : ∀ a < b, succ a < b) : IsSuccPrelimit b := fun a hab =>
  (H a hab.lt).ne (CovBy.succ_eq hab)

@[deprecated (since := "2025-12-20")]
alias isPredPrelimit_of_pred_lt := isPredPrelimit_of_lt_pred

@[to_dual lt_pred]
theorem IsSuccPrelimit.succ_lt (hb : IsSuccPrelimit b) (ha : a < b) : succ a < b := by
  by_cases h : IsMax a
  · rwa [h.succ_eq]
  · rw [lt_iff_le_and_ne, succ_le_iff_of_not_isMax h]
    refine ⟨ha, fun hab => ?_⟩
    subst hab
    exact (h hb.isMax).elim

@[to_dual lt_pred]
theorem IsSuccLimit.succ_lt (hb : IsSuccLimit b) (ha : a < b) : succ a < b :=
  hb.isSuccPrelimit.succ_lt ha

@[to_dual lt_pred_iff]
theorem IsSuccPrelimit.succ_lt_iff (hb : IsSuccPrelimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩

@[to_dual lt_pred_iff]
theorem IsSuccLimit.succ_lt_iff (hb : IsSuccLimit b) : succ a < b ↔ a < b :=
  hb.isSuccPrelimit.succ_lt_iff

@[to_dual isPredPrelimit_iff_lt_pred]
theorem isSuccPrelimit_iff_succ_lt : IsSuccPrelimit b ↔ ∀ a < b, succ a < b :=
  ⟨fun hb _ => hb.succ_lt, isSuccPrelimit_of_succ_lt⟩

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual]
theorem isSuccPrelimit_iff_succ_ne : IsSuccPrelimit a ↔ ∀ b, succ b ≠ a :=
  ⟨IsSuccPrelimit.succ_ne, isSuccPrelimit_of_succ_ne⟩

@[to_dual]
theorem not_isSuccPrelimit_iff' : ¬ IsSuccPrelimit a ↔ a ∈ range (succ : α → α) := by
  simp_rw [isSuccPrelimit_iff_succ_ne, not_forall, not_ne_iff, mem_range]

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

@[to_dual]
protected theorem IsSuccPrelimit.isMin (h : IsSuccPrelimit a) : IsMin a := fun b hb => by
  revert h
  refine Succ.rec (fun _ => le_rfl) (fun c _ H hc => ?_) hb
  have := hc.isMax.succ_eq
  rw [this] at hc ⊢
  exact H hc

@[to_dual (attr := simp)]
theorem isSuccPrelimit_iff_isMin : IsSuccPrelimit a ↔ IsMin a :=
  ⟨IsSuccPrelimit.isMin, IsMin.isSuccPrelimit⟩

@[deprecated (since := "2026-04-19")]
alias isSuccPrelimit_iff := isSuccPrelimit_iff_isMin
@[deprecated (since := "2026-04-19")]
alias isPredPrelimit_iff := isPredPrelimit_iff_isMax

@[to_dual (attr := simp)]
theorem not_isSuccLimit_of_isSuccArchimedean : ¬ IsSuccLimit a :=
  fun h ↦ h.not_isMin <| h.isSuccPrelimit.isMin

@[deprecated (since := "2026-04-19")]
alias not_isSuccLimit := not_isSuccLimit_of_isSuccArchimedean
@[deprecated (since := "2026-04-19")]
alias not_isPredLimit := not_isPredLimit_of_isPredArchimedean

@[to_dual]
theorem not_isSuccPrelimit_of_isSuccArchimedean [NoMinOrder α] : ¬ IsSuccPrelimit a := by simp

@[deprecated (since := "2026-04-19")]
alias not_isSuccPrelimit := not_isSuccPrelimit_of_isSuccArchimedean
@[deprecated (since := "2026-04-19")]
alias not_isPredPrelimit := not_isPredPrelimit_of_isPredArchimedean

end IsSuccArchimedean

end PartialOrder

section LinearOrder

variable [LinearOrder α]

@[to_dual]
theorem IsSuccPrelimit.le_iff_forall_le (h : IsSuccPrelimit a) : a ≤ b ↔ ∀ c < a, c ≤ b := by
  use fun ha c hc ↦ hc.le.trans ha
  intro H
  by_contra! ha
  exact h b ⟨ha, fun c hb hc ↦ (H c hc).not_gt hb⟩

@[to_dual]
theorem IsSuccLimit.le_iff_forall_le (h : IsSuccLimit a) : a ≤ b ↔ ∀ c < a, c ≤ b :=
  h.isSuccPrelimit.le_iff_forall_le

@[to_dual]
theorem IsSuccPrelimit.lt_iff_exists_lt (h : IsSuccPrelimit b) : a < b ↔ ∃ c < b, a < c := by
  rw [← not_iff_not]
  simp [h.le_iff_forall_le]

@[to_dual]
theorem IsSuccLimit.lt_iff_exists_lt (h : IsSuccLimit b) : a < b ↔ ∃ c < b, a < c :=
  h.isSuccPrelimit.lt_iff_exists_lt

@[to_dual]
lemma _root_.IsLUB.isSuccPrelimit_of_notMem {s : Set α} (hs : IsLUB s a) (ha : a ∉ s) :
    IsSuccPrelimit a := by
  intro b hb
  obtain ⟨c, hc, hbc, hca⟩ := hs.exists_between hb.lt
  obtain rfl := (hb.ge_of_gt hbc).antisymm hca
  contradiction

@[to_dual]
lemma _root_.IsLUB.mem_of_not_isSuccPrelimit {s : Set α} (hs : IsLUB s a) (ha : ¬IsSuccPrelimit a) :
    a ∈ s :=
  ha.imp_symm hs.isSuccPrelimit_of_notMem

@[to_dual]
lemma _root_.IsLUB.isSuccLimit_of_notMem {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty)
    (ha : a ∉ s) : IsSuccLimit a := by
  refine ⟨?_, hs.isSuccPrelimit_of_notMem ha⟩
  obtain ⟨b, hb⟩ := hs'
  obtain rfl | hb := (hs.1 hb).eq_or_lt
  · contradiction
  · exact hb.not_isMin

@[to_dual]
lemma _root_.IsLUB.mem_of_not_isSuccLimit {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty)
    (ha : ¬IsSuccLimit a) : a ∈ s :=
  ha.imp_symm <| hs.isSuccLimit_of_notMem hs'

@[to_dual]
theorem IsSuccPrelimit.isLUB_Iio (ha : IsSuccPrelimit a) : IsLUB (Iio a) a := by
  refine ⟨fun _ ↦ le_of_lt, fun b hb ↦ le_of_forall_lt fun c hc ↦ ?_⟩
  obtain ⟨d, hd, hd'⟩ := ha.lt_iff_exists_lt.1 hc
  exact hd'.trans_le (hb hd)

@[to_dual]
theorem IsSuccLimit.isLUB_Iio (ha : IsSuccLimit a) : IsLUB (Iio a) a :=
  ha.isSuccPrelimit.isLUB_Iio

@[to_dual]
theorem isLUB_Iio_iff_isSuccPrelimit : IsLUB (Iio a) a ↔ IsSuccPrelimit a := by
  refine ⟨fun ha b hb ↦ ?_, IsSuccPrelimit.isLUB_Iio⟩
  rw [hb.Iio_eq] at ha
  obtain rfl := isLUB_Iic.unique ha
  cases hb.lt.false

variable [SuccOrder α]

@[to_dual pred_le_iff]
theorem IsSuccPrelimit.le_succ_iff (hb : IsSuccPrelimit b) : b ≤ succ a ↔ b ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 hb.succ_lt_iff

@[to_dual pred_le_iff]
theorem IsSuccLimit.le_succ_iff (hb : IsSuccLimit b) : b ≤ succ a ↔ b ≤ a :=
  hb.isSuccPrelimit.le_succ_iff

end LinearOrder

end Order

/-! ### Induction principles -/

variable {motive : α → Sort*}

namespace Order

section isSuccPrelimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α]
  (succ : ∀ a, ¬IsMax a → motive (succ a)) (isSuccPrelimit : ∀ a, IsSuccPrelimit a → motive a)

variable (b) in
open Classical in
/-- A value can be built by building it on successors and successor pre-limits. -/
@[to_dual (attr := elab_as_elim)
/-- A value can be built by building it on predecessors and predecessor pre-limits. -/]
noncomputable def isSuccPrelimitRecOn : motive b :=
  if hb : IsSuccPrelimit b then isSuccPrelimit b hb else
    haveI H := Classical.choose_spec (not_isSuccPrelimit_iff.1 hb)
    cast (congr_arg motive H.2) (succ _ H.1)

@[to_dual]
theorem isSuccPrelimitRecOn_of_isSuccPrelimit (hb : IsSuccPrelimit b) :
    isSuccPrelimitRecOn b succ isSuccPrelimit = isSuccPrelimit b hb :=
  dif_pos hb

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α]
  (succ : ∀ a, ¬IsMax a → motive (succ a)) (isSuccPrelimit : ∀ a, IsSuccPrelimit a → motive a)

@[to_dual]
theorem isSuccPrelimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    isSuccPrelimitRecOn (Order.succ b) succ isSuccPrelimit = succ b hb := by
  have hb' := mt IsSuccPrelimit.isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff.1 hb')
  rw [isSuccPrelimitRecOn, dif_neg hb', cast_eq_iff_heq]
  congr!
  exact (succ_eq_succ_iff_of_not_isMax H.1 hb).1 H.2

@[to_dual (attr := simp)]
theorem isSuccPrelimitRecOn_succ [NoMaxOrder α] (b : α) :
    isSuccPrelimitRecOn (Order.succ b) succ isSuccPrelimit = succ b (not_isMax b) :=
  isSuccPrelimitRecOn_succ_of_not_isMax ..

end LinearOrder

end isSuccPrelimitRecOn

section isSuccLimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α]
  (isMin : ∀ a, IsMin a → motive a) (succ : ∀ a, ¬IsMax a → motive (succ a))
  (isSuccLimit : ∀ a, IsSuccLimit a → motive a)

variable (b) in
open Classical in
/-- A value can be built by building it on minimal elements, successors,
and successor limits. -/
@[to_dual (attr := elab_as_elim)
/-- A value can be built by building it on maximal elements, predecessors,
and predecessor limits. -/]
noncomputable def isSuccLimitRecOn : motive b :=
  isSuccPrelimitRecOn b succ fun a ha ↦
    if h : IsMin a then isMin a h else isSuccLimit a (ha.isSuccLimit_of_not_isMin h)

@[to_dual (attr := simp)]
theorem isSuccLimitRecOn_of_isSuccLimit (hb : IsSuccLimit b) :
    isSuccLimitRecOn b isMin succ isSuccLimit = isSuccLimit b hb := by
  rw [isSuccLimitRecOn, isSuccPrelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit,
    dif_neg hb.not_isMin]

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α]
  (isMin : ∀ a, IsMin a → motive a) (succ : ∀ a, ¬IsMax a → motive (succ a))
  (isSuccLimit : ∀ a, IsSuccLimit a → motive a)

@[to_dual]
theorem isSuccLimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    isSuccLimitRecOn (Order.succ b) isMin succ isSuccLimit = succ b hb := by
  rw [isSuccLimitRecOn, isSuccPrelimitRecOn_succ_of_not_isMax]

@[to_dual (attr := simp)]
theorem isSuccLimitRecOn_succ [NoMaxOrder α] (b : α) :
    isSuccLimitRecOn (Order.succ b) isMin succ isSuccLimit = succ b (not_isMax b) :=
  isSuccLimitRecOn_succ_of_not_isMax isMin succ isSuccLimit _

@[to_dual]
theorem isSuccLimitRecOn_of_isMin (hb : IsMin b) :
    isSuccLimitRecOn b isMin succ isSuccLimit = isMin b hb := by
  rw [isSuccLimitRecOn, isSuccPrelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit, dif_pos hb]

end LinearOrder

end isSuccLimitRecOn

end Order

open Order

namespace SuccOrder

section prelimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α] [WellFoundedLT α]
  (succ : ∀ a, ¬IsMax a → motive a → motive (Order.succ a))
  (isSuccPrelimit : ∀ a, IsSuccPrelimit a → (∀ b < a, motive b) → motive a)

variable (b) in
open Classical in
/-- Recursion principle on a well-founded partial `SuccOrder`. -/
@[to_dual (attr := elab_as_elim)
/-- Recursion principle on a well-founded partial `PredOrder`. -/]
noncomputable def prelimitRecOn : motive b :=
  wellFounded_lt.fix
    (fun a IH ↦ if h : IsSuccPrelimit a then isSuccPrelimit a h IH else
      haveI H := Classical.choose_spec (not_isSuccPrelimit_iff.1 h)
      cast (congr_arg motive H.2) (succ _ H.1 <| IH _ <| H.2.subst <| lt_succ_of_not_isMax H.1))
    b

@[to_dual (attr := simp)]
theorem prelimitRecOn_of_isSuccPrelimit (hb : IsSuccPrelimit b) :
    prelimitRecOn b succ isSuccPrelimit =
      isSuccPrelimit b hb fun x _ ↦ SuccOrder.prelimitRecOn x succ isSuccPrelimit := by
  rw [prelimitRecOn, WellFounded.fix_eq, dif_pos hb]; rfl

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] [WellFoundedLT α]
  (succ : ∀ a, ¬IsMax a → motive a → motive (Order.succ a))
  (isSuccPrelimit : ∀ a, IsSuccPrelimit a → (∀ b < a, motive b) → motive a)

@[to_dual]
theorem prelimitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    prelimitRecOn (Order.succ b) succ isSuccPrelimit =
      succ b hb (prelimitRecOn b succ isSuccPrelimit) := by
  have h := mt IsSuccPrelimit.isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff.1 h)
  rw [prelimitRecOn, WellFounded.fix_eq, dif_neg h]
  have {a c : α} {ha hc} {x : ∀ a, motive a} (h : a = c) :
    cast (congr_arg (motive ∘ Order.succ) h) (succ a ha (x a)) = succ c hc (x c) := by subst h; rfl
  exact this <| (succ_eq_succ_iff_of_not_isMax H.1 hb).1 H.2

@[to_dual (attr := simp)]
theorem prelimitRecOn_succ [NoMaxOrder α] (b : α) :
    prelimitRecOn (Order.succ b) succ isSuccPrelimit =
      succ b (not_isMax b) (prelimitRecOn b succ isSuccPrelimit) :=
  prelimitRecOn_succ_of_not_isMax _ _ _

end LinearOrder

end prelimitRecOn

section limitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α] [WellFoundedLT α] (isMin : ∀ a, IsMin a → motive a)
  (succ : ∀ a, ¬IsMax a → motive a → motive (Order.succ a))
  (isSuccLimit : ∀ a, IsSuccLimit a → (∀ b < a, motive b) → motive a)

variable (b) in
open Classical in
/-- Recursion principle on a well-founded partial `SuccOrder`, separating out the case of a
minimal element. -/
@[to_dual (attr := elab_as_elim)
/-- Recursion principle on a well-founded partial `PredOrder`, separating out the case of a
minimal element. -/]
noncomputable def limitRecOn : motive b :=
  prelimitRecOn b succ fun a ha IH ↦
    if h : IsMin a then isMin a h else isSuccLimit a (ha.isSuccLimit_of_not_isMin h) IH

@[to_dual (attr := simp)]
theorem limitRecOn_isMin (hb : IsMin b) : limitRecOn b isMin succ isSuccLimit = isMin b hb := by
  rw [limitRecOn, prelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit, dif_pos hb]

@[to_dual (attr := simp)]
theorem limitRecOn_of_isSuccLimit (hb : IsSuccLimit b) :
    limitRecOn b isMin succ isSuccLimit =
      isSuccLimit b hb fun x _ ↦ limitRecOn x isMin succ isSuccLimit := by
  rw [limitRecOn, prelimitRecOn_of_isSuccPrelimit _ _ hb.isSuccPrelimit, dif_neg hb.not_isMin]; rfl

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] [WellFoundedLT α] (isMin : ∀ a, IsMin a → motive a)
  (succ : ∀ a, ¬IsMax a → motive a → motive (Order.succ a))
  (isSuccLimit : ∀ a, IsSuccLimit a → (∀ b < a, motive b) → motive a)

@[to_dual]
theorem limitRecOn_succ_of_not_isMax (hb : ¬IsMax b) :
    limitRecOn (Order.succ b) isMin succ isSuccLimit =
      succ b hb (limitRecOn b isMin succ isSuccLimit) := by
  rw [limitRecOn, prelimitRecOn_succ_of_not_isMax]; rfl

@[to_dual (attr := simp)]
theorem limitRecOn_succ [NoMaxOrder α] (b : α) :
    limitRecOn (Order.succ b) isMin succ isSuccLimit =
      succ b (not_isMax b) (limitRecOn b isMin succ isSuccLimit) :=
  limitRecOn_succ_of_not_isMax isMin succ isSuccLimit _

end LinearOrder

end limitRecOn

end SuccOrder
