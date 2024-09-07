/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.BoundedOrder

/-!
# Successor and predecessor limits

We define the predicate `Order.IsSuccPrelimit` for "successor pre-limits", values that don't cover
any others. They are so named since they can't be the successors of anything smaller. We define
`Order.IsPredPrelimit` analogously, and prove basic results.

For some applications, it is desirable to exclude minimal elements from being successor limits, or
maximal elements from being predecessor limits. As such, we also provide `Order.IsSuccLimit` and
`Order.IsPredLimit`, which exclude these cases.

## TODO

For some applications, it's desirable to exclude the case where an element is minimal. A future PR
will introduce `IsSuccLimit` for this usage.

The plan is to eventually replace `Ordinal.IsLimit` and `Cardinal.IsLimit` with the common
predicate `Order.IsSuccLimit`.
-/


variable {α : Type*}

namespace Order

open Function Set OrderDual

/-! ### Successor limits -/


section LT

variable [LT α]

/-- A successor pre-limit is a value that doesn't cover any other.

It's so named because in a successor order, a successor pre-limit can't be the successor of anything
smaller.

For some applications, it's desirable to exclude the case where an element is minimal. A future PR
will introduce `IsSuccLimit` for this usage. -/
def IsSuccPrelimit (a : α) : Prop :=
  ∀ b, ¬b ⋖ a

theorem not_isSuccPrelimit_iff_exists_covBy (a : α) : ¬IsSuccPrelimit a ↔ ∃ b, b ⋖ a := by
  simp [IsSuccPrelimit]

@[deprecated not_isSuccPrelimit_iff_exists_covBy (since := "2024-09-05")]
alias not_isSuccLimit_iff_exists_covBy := not_isSuccPrelimit_iff_exists_covBy

@[simp]
theorem isSuccPrelimit_of_dense [DenselyOrdered α] (a : α) : IsSuccPrelimit a := fun _ => not_covBy

@[deprecated isSuccPrelimit_of_dense (since := "2024-09-05")]
alias isSuccLimit_of_dense := isSuccPrelimit_of_dense

end LT

section Preorder

variable [Preorder α] {a : α}

/-- A successor limit is a value that isn't minimal and doesn't cover any other.

It's so named because in a successor order, a successor limit can't be the successor of anything
smaller.

This previously allowed the element to be minimal. This usage is now covered by `IsSuccPrelimit`. -/
def IsSuccLimit (a : α) : Prop :=
  ¬ IsMin a ∧ IsSuccPrelimit a

protected theorem IsSuccLimit.not_isMin (h : IsSuccLimit a) : ¬ IsMin a := h.1
protected theorem IsSuccLimit.isSuccPrelimit (h : IsSuccLimit a) : IsSuccPrelimit a := h.2

theorem IsSuccLimit_iff' : IsSuccLimit a ↔ ¬ IsMin a ∧ IsSuccPrelimit a :=
  Iff.rfl

theorem IsSuccPrelimit.isSuccLimit_of_not_isMin (h : IsSuccPrelimit a) (ha : ¬ IsMin a) :
    IsSuccLimit a :=
  ⟨ha, h⟩

theorem IsSuccPrelimit.isSuccLimit [NoMinOrder α] (h : IsSuccPrelimit a) : IsSuccLimit a :=
  h.isSuccLimit_of_not_isMin (not_isMin a)

theorem isSuccPrelimit_iff_isSuccLimit_of_not_isMin (h : ¬ IsMin a) :
    IsSuccPrelimit a ↔ IsSuccLimit a :=
  ⟨fun ha ↦ ha.isSuccLimit_of_not_isMin h, IsSuccLimit.isSuccPrelimit⟩

theorem isSuccPrelimit_iff_isSuccLimit [NoMinOrder α] : IsSuccPrelimit a ↔ IsSuccLimit a :=
  isSuccPrelimit_iff_isSuccLimit_of_not_isMin (not_isMin a)

protected theorem _root_.IsMin.not_isSuccLimit (h : IsMin a) : ¬ IsSuccLimit a :=
  fun ha ↦ ha.not_isMin h

protected theorem _root_.IsMin.isSuccPrelimit : IsMin a → IsSuccPrelimit a := fun h _ hab =>
  not_isMin_of_lt hab.lt h

@[deprecated _root_.IsMin.isSuccPrelimit (since := "2024-09-05")]
alias _root_.IsMin.isSuccLimit := _root_.IsMin.isSuccPrelimit

theorem isSuccPrelimit_bot [OrderBot α] : IsSuccPrelimit (⊥ : α) :=
  isMin_bot.isSuccPrelimit

theorem not_isSuccLimit_bot [OrderBot α] : ¬ IsSuccLimit (⊥ : α) :=
  isMin_bot.not_isSuccLimit

theorem IsSuccLimit.ne_bot [OrderBot α] (h : IsSuccLimit a) : a ≠ ⊥ := by
  rintro rfl
  exact not_isSuccLimit_bot h

@[deprecated isSuccPrelimit_bot (since := "2024-09-05")]
alias isSuccLimit_bot := isSuccPrelimit_bot

theorem not_isSuccLimit_iff : ¬ IsSuccLimit a ↔ IsMin a ∨ ¬ IsSuccPrelimit a := by
  rw [IsSuccLimit, not_and_or, not_not]

variable [SuccOrder α]

protected theorem IsSuccPrelimit.isMax (h : IsSuccPrelimit (succ a)) : IsMax a := by
  by_contra H
  exact h a (covBy_succ_of_not_isMax H)

protected theorem IsSuccLimit.isMax (h : IsSuccLimit (succ a)) : IsMax a :=
  h.isSuccPrelimit.isMax

theorem not_isSuccPrelimit_succ_of_not_isMax (ha : ¬ IsMax a) : ¬ IsSuccPrelimit (succ a) :=
  mt IsSuccPrelimit.isMax ha

theorem not_isSuccLimit_succ_of_not_isMax (ha : ¬ IsMax a) : ¬ IsSuccLimit (succ a) :=
  mt IsSuccLimit.isMax ha

section NoMaxOrder

variable [NoMaxOrder α]

theorem IsSuccPrelimit.succ_ne (h : IsSuccPrelimit a) (b : α) : succ b ≠ a := by
  rintro rfl
  exact not_isMax _ h.isMax

theorem IsSuccLimit.succ_ne (h : IsSuccLimit a) (b : α) : succ b ≠ a :=
  h.isSuccPrelimit.succ_ne b

@[simp]
theorem not_isSuccPrelimit_succ (a : α) : ¬ IsSuccPrelimit (succ a) :=
  fun h => h.succ_ne _ rfl

@[simp]
theorem not_isSuccLimit_succ (a : α) : ¬ IsSuccLimit (succ a) :=
  fun h => h.succ_ne _ rfl

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α] [NoMaxOrder α]

theorem IsSuccPrelimit.isMin_of_noMax (h : IsSuccPrelimit a) : IsMin a := by
  intro b hb
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_isSuccPrelimit_succ _ h).elim

@[deprecated IsSuccPrelimit.isMin_of_noMax (since := "2024-09-05")]
alias IsSuccLimit.isMin_of_noMax := IsSuccPrelimit.isMin_of_noMax

@[simp]
theorem isSuccPrelimit_iff_of_noMax : IsSuccPrelimit a ↔ IsMin a :=
  ⟨IsSuccPrelimit.isMin_of_noMax, IsMin.isSuccPrelimit⟩

@[deprecated isSuccPrelimit_iff_of_noMax (since := "2024-09-05")]
alias isSuccLimit_iff_of_noMax := isSuccPrelimit_iff_of_noMax

@[simp]
theorem not_isSuccLimit_of_noMax : ¬ IsSuccLimit a :=
  fun h ↦ h.not_isMin h.isSuccPrelimit.isMin_of_noMax

theorem not_isSuccPrelimit_of_noMax [NoMinOrder α] : ¬ IsSuccPrelimit a := by simp

end IsSuccArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

theorem isSuccLimit_iff [OrderBot α] : IsSuccLimit a ↔ a ≠ ⊥ ∧ IsSuccPrelimit a := by
  rw [IsSuccLimit_iff', isMin_iff_eq_bot]

variable [SuccOrder α]

theorem isSuccPrelimit_of_succ_ne (h : ∀ b, succ b ≠ a) : IsSuccPrelimit a := fun b hba =>
  h b (CovBy.succ_eq hba)

@[deprecated isSuccPrelimit_of_succ_ne (since := "2024-09-05")]
alias isSuccLimit_of_succ_ne := isSuccPrelimit_of_succ_ne

theorem not_isSuccPrelimit_iff : ¬ IsSuccPrelimit a ↔ ∃ b, ¬ IsMax b ∧ succ b = a := by
  rw [not_isSuccPrelimit_iff_exists_covBy]
  refine exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_isMax, (CovBy.succ_eq hba)⟩, ?_⟩
  rintro ⟨h, rfl⟩
  exact covBy_succ_of_not_isMax h

/-- See `not_isSuccPrelimit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_succ_of_not_isSuccPrelimit (h : ¬ IsSuccPrelimit a) :
    a ∈ range (succ : α → α) := by
  obtain ⟨b, hb⟩ := not_isSuccPrelimit_iff.1 h
  exact ⟨b, hb.2⟩

@[deprecated mem_range_succ_of_not_isSuccPrelimit (since := "2024-09-05")]
alias mem_range_succ_of_not_isSuccLimit := mem_range_succ_of_not_isSuccPrelimit

theorem mem_range_succ_or_isSuccPrelimit (a) : a ∈ range (succ : α → α) ∨ IsSuccPrelimit a :=
  or_iff_not_imp_right.2 <| mem_range_succ_of_not_isSuccPrelimit

@[deprecated mem_range_succ_or_isSuccPrelimit (since := "2024-09-05")]
alias mem_range_succ_or_isSuccLimit := mem_range_succ_or_isSuccPrelimit

theorem isSuccPrelimit_of_succ_lt (H : ∀ a < b, succ a < b) : IsSuccPrelimit b := fun a hab =>
  (H a hab.lt).ne (CovBy.succ_eq hab)

@[deprecated isSuccPrelimit_of_succ_lt (since := "2024-09-05")]
alias isSuccLimit_of_succ_lt := isSuccPrelimit_of_succ_lt

theorem IsSuccPrelimit.succ_lt (hb : IsSuccPrelimit b) (ha : a < b) : succ a < b := by
  by_cases h : IsMax a
  · rwa [h.succ_eq]
  · rw [lt_iff_le_and_ne, succ_le_iff_of_not_isMax h]
    refine ⟨ha, fun hab => ?_⟩
    subst hab
    exact (h hb.isMax).elim

theorem IsSuccLimit.succ_lt (hb : IsSuccLimit b) (ha : a < b) : succ a < b :=
  hb.isSuccPrelimit.succ_lt ha

theorem IsSuccPrelimit.succ_lt_iff (hb : IsSuccPrelimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩

theorem IsSuccLimit.succ_lt_iff (hb : IsSuccLimit b) : succ a < b ↔ a < b :=
  hb.isSuccPrelimit.succ_lt_iff

theorem isSuccPrelimit_iff_succ_lt : IsSuccPrelimit b ↔ ∀ a < b, succ a < b :=
  ⟨fun hb _ => hb.succ_lt, isSuccPrelimit_of_succ_lt⟩

@[deprecated isSuccPrelimit_iff_succ_lt (since := "2024-09-05")]
alias isSuccLimit_iff_succ_lt := isSuccPrelimit_iff_succ_lt

section NoMaxOrder

variable [NoMaxOrder α]

theorem isSuccPrelimit_iff_succ_ne : IsSuccPrelimit a ↔ ∀ b, succ b ≠ a :=
  ⟨IsSuccPrelimit.succ_ne, isSuccPrelimit_of_succ_ne⟩

@[deprecated isSuccPrelimit_iff_succ_ne (since := "2024-09-05")]
alias isSuccLimit_iff_succ_ne := isSuccPrelimit_iff_succ_ne

theorem not_isSuccPrelimit_iff' : ¬ IsSuccPrelimit a ↔ a ∈ range (succ : α → α) := by
  simp_rw [isSuccPrelimit_iff_succ_ne, not_forall, not_ne_iff, mem_range]

@[deprecated not_isSuccPrelimit_iff' (since := "2024-09-05")]
alias not_isSuccLimit_iff' := not_isSuccPrelimit_iff'

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

protected theorem IsSuccPrelimit.isMin (h : IsSuccPrelimit a) : IsMin a := fun b hb => by
  revert h
  refine Succ.rec (fun _ => le_rfl) (fun c _ H hc => ?_) hb
  have := hc.isMax.succ_eq
  rw [this] at hc ⊢
  exact H hc

@[simp]
theorem isSuccPrelimit_iff : IsSuccPrelimit a ↔ IsMin a :=
  ⟨IsSuccPrelimit.isMin, IsMin.isSuccPrelimit⟩

@[simp]
theorem not_isSuccLimit : ¬ IsSuccLimit a :=
  fun h ↦ h.not_isMin <| h.isSuccPrelimit.isMin

theorem not_isSuccPrelimit [NoMinOrder α] : ¬ IsSuccPrelimit a := by simp

end IsSuccArchimedean

end PartialOrder

/-! ### Predecessor limits -/


section LT

variable [LT α] {a : α}

/-- A predecessor pre-limit is a value that isn't covered by any other.

It's so named because in a predecessor order, a predecessor pre-limit can't be the predecessor of
anything smaller.

For some applications, it's desirable to exclude maximal elements from this definition. For that,
see `IsPredLimit`. -/
def IsPredPrelimit (a : α) : Prop :=
  ∀ b, ¬ a ⋖ b

theorem not_isPredPrelimit_iff_exists_covBy (a : α) : ¬IsPredPrelimit a ↔ ∃ b, a ⋖ b := by
  simp [IsPredPrelimit]

@[deprecated not_isPredPrelimit_iff_exists_covBy (since := "2024-09-05")]
alias not_isPredLimit_iff_exists_covBy := not_isPredPrelimit_iff_exists_covBy

theorem isPredPrelimit_of_dense [DenselyOrdered α] (a : α) : IsPredPrelimit a := fun _ => not_covBy

@[deprecated isPredPrelimit_of_dense (since := "2024-09-05")]
alias isPredLimit_of_dense := isPredPrelimit_of_dense

@[simp]
theorem isSuccPrelimit_toDual_iff : IsSuccPrelimit (toDual a) ↔ IsPredPrelimit a := by
  simp [IsSuccPrelimit, IsPredPrelimit]

@[simp]
theorem isPredPrelimit_toDual_iff : IsPredPrelimit (toDual a) ↔ IsSuccPrelimit a := by
  simp [IsSuccPrelimit, IsPredPrelimit]

alias ⟨_, IsPredPrelimit.dual⟩ := isSuccPrelimit_toDual_iff
alias ⟨_, IsSuccPrelimit.dual⟩ := isPredPrelimit_toDual_iff
@[deprecated IsPredPrelimit.dual (since := "2024-09-05")]
alias isPredLimit.dual := IsPredPrelimit.dual
@[deprecated IsSuccPrelimit.dual (since := "2024-09-05")]
alias isSuccLimit.dual := IsSuccPrelimit.dual

end LT

section Preorder

variable [Preorder α] {a : α}

/-- A predecessor limit is a value that isn't maximal and doesn't cover any other.

It's so named because in a predecessor order, a predecessor limit can't be the predecessor of
anything larger.

This previously allowed the element to be maximal. This usage is now covered by `IsPredPreLimit`. -/
def IsPredLimit (a : α) : Prop :=
  ¬ IsMax a ∧ IsPredPrelimit a

protected theorem IsPredLimit.not_isMax (h : IsPredLimit a) : ¬ IsMax a := h.1
protected theorem IsPredLimit.isPredPrelimit (h : IsPredLimit a) : IsPredPrelimit a := h.2

theorem IsPredLimit_iff' : IsPredLimit a ↔ ¬ IsMax a ∧ IsPredPrelimit a :=
  Iff.rfl

@[simp]
theorem isSuccLimit_toDual_iff : IsSuccLimit (toDual a) ↔ IsPredLimit a := by
  simp [IsSuccLimit, IsPredLimit]

@[simp]
theorem isPredLimit_toDual_iff : IsPredLimit (toDual a) ↔ IsSuccLimit a := by
  simp [IsSuccLimit, IsPredLimit]

alias ⟨_, IsPredLimit.dual⟩ := isSuccLimit_toDual_iff
alias ⟨_, IsSuccLimit.dual⟩ := isPredLimit_toDual_iff

theorem IsPredPrelimit.isPredLimit_of_not_isMax (h : IsPredPrelimit a) (ha : ¬ IsMax a) :
    IsPredLimit a :=
  ⟨ha, h⟩

theorem IsPredPrelimit.isPredLimit [NoMaxOrder α] (h : IsPredPrelimit a) : IsPredLimit a :=
  h.isPredLimit_of_not_isMax (not_isMax a)

theorem isPredPrelimit_iff_isPredLimit_of_not_isMax (h : ¬ IsMax a) :
    IsPredPrelimit a ↔ IsPredLimit a :=
  ⟨fun ha ↦ ha.isPredLimit_of_not_isMax h, IsPredLimit.isPredPrelimit⟩

theorem isPredPrelimit_iff_isPredLimit [NoMaxOrder α] : IsPredPrelimit a ↔ IsPredLimit a :=
  isPredPrelimit_iff_isPredLimit_of_not_isMax (not_isMax a)

protected theorem _root_.IsMax.not_isPredLimit (h : IsMax a) : ¬ IsPredLimit a :=
  fun ha ↦ ha.not_isMax h

protected theorem _root_.IsMax.isPredPrelimit : IsMax a → IsPredPrelimit a := fun h _ hab =>
  not_isMax_of_lt hab.lt h

@[deprecated _root_.IsMax.isPredPrelimit (since := "2024-09-05")]
alias _root_.IsMax.isPredLimit := _root_.IsMax.isPredPrelimit

theorem isPredPrelimit_top [OrderTop α] : IsPredPrelimit (⊤ : α) :=
  isMax_top.isPredPrelimit

@[deprecated isPredPrelimit_top (since := "2024-09-05")]
alias isPredLimit_top := isPredPrelimit_top

theorem not_isPredLimit_top [OrderTop α] : ¬ IsPredLimit (⊤ : α) :=
  isMax_top.not_isPredLimit

theorem IsPredLimit.ne_top [OrderTop α] (h : IsPredLimit a) : a ≠ ⊤ :=
  h.dual.ne_bot

theorem not_isPredLimit_iff : ¬ IsPredLimit a ↔ IsMax a ∨ ¬ IsPredPrelimit a := by
  rw [IsPredLimit, not_and_or, not_not]

theorem not_isPredLimit_of_not_isPredPrelimit (h : ¬ IsPredPrelimit a) : ¬ IsPredLimit a :=
  not_isPredLimit_iff.2 (Or.inr h)

variable [PredOrder α]

protected theorem IsPredPrelimit.isMin (h : IsPredPrelimit (pred a)) : IsMin a :=
  h.dual.isMax

protected theorem IsPredLimit.isMin (h : IsPredLimit (pred a)) : IsMin a :=
  h.dual.isMax

theorem not_isPredPrelimit_pred_of_not_isMin (ha : ¬ IsMin a) : ¬ IsPredPrelimit (pred a) :=
  mt IsPredPrelimit.isMin ha

theorem not_isPredLimit_pred_of_not_isMin (ha : ¬ IsMin a) : ¬ IsPredLimit (pred a) :=
  mt IsPredLimit.isMin ha

section NoMinOrder

variable [NoMinOrder α]

theorem IsPredPrelimit.pred_ne (h : IsPredPrelimit a) (b : α) : pred b ≠ a :=
  h.dual.succ_ne b

theorem IsPredLimit.pred_ne (h : IsPredLimit a) (b : α) : pred b ≠ a :=
  h.isPredPrelimit.pred_ne b

@[simp]
theorem not_isPredPrelimit_pred (a : α) : ¬ IsPredPrelimit (pred a) :=
  fun h => h.pred_ne _ rfl

@[simp]
theorem not_isPredLimit_pred (a : α) : ¬ IsPredLimit (pred a) :=
  fun h => h.pred_ne _ rfl

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α] [NoMinOrder α]

theorem IsPredPrelimit.isMax_of_noMin (h : IsPredPrelimit a) : IsMax a :=
  h.dual.isMin_of_noMax

@[deprecated IsPredPrelimit.isMax_of_noMin (since := "2024-09-05")]
alias IsPredLimit.isMax_of_noMin := IsPredPrelimit.isMax_of_noMin

@[simp]
theorem isPredPrelimit_iff_of_noMin : IsPredPrelimit a ↔ IsMax a :=
  ⟨IsPredPrelimit.isMax_of_noMin, IsMax.isPredPrelimit⟩

@[deprecated isPredPrelimit_iff_of_noMin (since := "2024-09-05")]
alias isPredLimit_iff_of_noMin := isPredPrelimit_iff_of_noMin

theorem not_isPredPrelimit_of_noMin [NoMaxOrder α] : ¬ IsPredPrelimit a := by simp

@[simp]
theorem not_isPredLimit_of_noMin : ¬ IsPredLimit a :=
  fun h ↦ h.not_isMax h.isPredPrelimit.isMax_of_noMin

end IsPredArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

theorem isPredLimit_iff [OrderTop α] : IsPredLimit a ↔ a ≠ ⊤ ∧ IsPredPrelimit a := by
  rw [IsPredLimit_iff', isMax_iff_eq_top]

variable [PredOrder α]

theorem isPredPrelimit_of_pred_ne (h : ∀ b, pred b ≠ a) : IsPredPrelimit a := fun b hba =>
  h b (CovBy.pred_eq hba)

@[deprecated isPredPrelimit_of_pred_ne (since := "2024-09-05")]
alias isPredLimit_of_pred_ne := isPredPrelimit_of_pred_ne

theorem not_isPredPrelimit_iff : ¬ IsPredPrelimit a ↔ ∃ b, ¬ IsMin b ∧ pred b = a := by
  rw [← isSuccPrelimit_toDual_iff]
  exact not_isSuccPrelimit_iff

/-- See `not_isPredPrelimit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_pred_of_not_isPredPrelimit (h : ¬ IsPredPrelimit a) :
    a ∈ range (pred : α → α) := by
  obtain ⟨b, hb⟩ := not_isPredPrelimit_iff.1 h
  exact ⟨b, hb.2⟩

@[deprecated mem_range_pred_of_not_isPredPrelimit (since := "2024-09-05")]
alias mem_range_pred_of_not_isPredLimit := mem_range_pred_of_not_isPredPrelimit

theorem mem_range_pred_or_isPredPrelimit (a) : a ∈ range (pred : α → α) ∨ IsPredPrelimit a :=
  or_iff_not_imp_right.2 <| mem_range_pred_of_not_isPredPrelimit

@[deprecated mem_range_pred_or_isPredPrelimit (since := "2024-09-05")]
alias mem_range_pred_or_isPredLimit := mem_range_pred_or_isPredPrelimit

theorem isPredPrelimit_of_pred_lt (H : ∀ b > a, a < pred b) : IsPredPrelimit a := fun a hab =>
  (H a hab.lt).ne (CovBy.pred_eq hab).symm

@[deprecated isPredPrelimit_of_pred_lt (since := "2024-09-05")]
alias isPredLimit_of_pred_lt := isPredPrelimit_of_pred_lt

theorem IsPredPrelimit.lt_pred (ha : IsPredPrelimit a) (hb : a < b) : a < pred b :=
  ha.dual.succ_lt hb

theorem IsPredLimit.lt_pred (ha : IsPredLimit a) (hb : a < b) : a < pred b :=
  ha.isPredPrelimit.lt_pred hb

theorem IsPredPrelimit.lt_pred_iff (ha : IsPredPrelimit a) : a < pred b ↔ a < b :=
  ha.dual.succ_lt_iff

theorem IsPredLimit.lt_pred_iff (ha : IsPredLimit a) : a < pred b ↔ a < b :=
  ha.dual.succ_lt_iff

theorem isPredPrelimit_iff_lt_pred : IsPredPrelimit a ↔ ∀ b > a, a < pred b :=
  ⟨fun hb _ => hb.lt_pred, isPredPrelimit_of_pred_lt⟩

@[deprecated isPredPrelimit_iff_lt_pred (since := "2024-09-05")]
alias isPredLimit_iff_lt_pred := isPredPrelimit_iff_lt_pred

section NoMinOrder

variable [NoMinOrder α]

theorem isPredPrelimit_iff_pred_ne : IsPredPrelimit a ↔ ∀ b, pred b ≠ a :=
  ⟨IsPredPrelimit.pred_ne, isPredPrelimit_of_pred_ne⟩

theorem not_isPredPrelimit_iff' : ¬ IsPredPrelimit a ↔ a ∈ range (pred : α → α) := by
  simp_rw [isPredPrelimit_iff_pred_ne, not_forall, not_ne_iff, mem_range]

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem IsPredPrelimit.isMax (h : IsPredPrelimit a) : IsMax a :=
  h.dual.isMin

@[deprecated IsPredPrelimit.isMax (since := "2024-09-05")]
alias IsPredLimit.isMax := IsPredPrelimit.isMax

@[simp]
theorem isPredPrelimit_iff : IsPredPrelimit a ↔ IsMax a :=
  ⟨IsPredPrelimit.isMax, IsMax.isPredPrelimit⟩

@[simp]
theorem not_isPredLimit : ¬ IsPredLimit a :=
  fun h ↦ h.not_isMax <| h.isPredPrelimit.isMax

theorem not_isPredPrelimit [NoMaxOrder α] : ¬ IsPredPrelimit a := by simp

end IsPredArchimedean

end PartialOrder

/-! ### Induction principles -/


variable {C : α → Sort*} {b : α}

section isSuccPrelimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α]
  (hs : ∀ a, ¬ IsMax a → C (succ a)) (hl : ∀ a, IsSuccPrelimit a → C a)

open Classical in
/-- A value can be built by building it on successors and successor pre-limits. -/
@[elab_as_elim]
noncomputable def isSuccPrelimitRecOn (b : α) : C b :=
  if hb : IsSuccPrelimit b then hl b hb else
    have H := Classical.choose_spec (not_isSuccPrelimit_iff.1 hb)
    cast (congr_arg C H.2) (hs _ H.1)

@[simp]
theorem isSuccPrelimitRecOn_limit (hb : IsSuccPrelimit b) : isSuccPrelimitRecOn hs hl b = hl b hb :=
  dif_pos hb

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α]
  (hs : ∀ a, ¬ IsMax a → C (succ a)) (hl : ∀ a, IsSuccPrelimit a → C a)

theorem isSuccPrelimitRecOn_succ' (hb : ¬ IsMax b) :
    isSuccPrelimitRecOn hs hl (succ b) = hs b hb := by
  have hb' := not_isSuccPrelimit_succ_of_not_isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff.1 hb')
  rw [isSuccPrelimitRecOn, dif_neg hb', cast_eq_iff_heq]
  congr
  exacts [(succ_eq_succ_iff_of_not_isMax H.1 hb).1 H.2, proof_irrel_heq _ _]

@[simp]
theorem isSuccPrelimitRecOn_succ [NoMaxOrder α] (b : α) :
    isSuccPrelimitRecOn hs hl (succ b) = hs b (not_isMax b) :=
  isSuccPrelimitRecOn_succ' hs hl _

end LinearOrder

end isSuccPrelimitRecOn

section isSuccLimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α]
  (hm : ∀ a, IsMin a → C a) (hs : ∀ a, ¬ IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)

open Classical in
/-- A value can be built by building it on minimal elements, successors, and successor limits. -/
@[elab_as_elim]
noncomputable def isSuccLimitRecOn : ∀ b, C b :=
  isSuccPrelimitRecOn hs fun a ha ↦
    if h : IsMin a then hm a h else hl a (ha.isSuccLimit_of_not_isMin h)

@[simp]
theorem isSuccLimitRecOn_isMin (hb : IsMin b) : isSuccLimitRecOn hm hs hl b = hm b hb := by
  rw [isSuccLimitRecOn, isSuccPrelimitRecOn_limit _ _ hb.isSuccPrelimit, dif_pos hb]

@[simp]
theorem isSuccLimitRecOn_limit (hb : IsSuccLimit b) : isSuccLimitRecOn hm hs hl b = hl b hb := by
  rw [isSuccLimitRecOn, isSuccPrelimitRecOn_limit _ _ hb.isSuccPrelimit, dif_neg hb.not_isMin]

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α]
  (hm : ∀ a, IsMin a → C a) (hs : ∀ a, ¬ IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)

theorem isSuccLimitRecOn_succ' (hb : ¬ IsMax b) :
    isSuccLimitRecOn hm hs hl (succ b) = hs b hb := by
  rw [isSuccLimitRecOn, isSuccPrelimitRecOn_succ']

@[simp]
theorem isSuccLimitRecOn_succ [NoMaxOrder α] (b : α) :
    isSuccLimitRecOn hm hs hl (succ b) = hs b (not_isMax b) :=
  isSuccLimitRecOn_succ' hm hs hl _

end LinearOrder

end isSuccLimitRecOn

end Order

open Order

namespace SuccOrder

variable {C : α → Sort*} {b : α}

section prelimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α] [WellFoundedLT α]
  (hs : ∀ a, ¬ IsMax a → C a → C (Order.succ a)) (hl : ∀ a, IsSuccPrelimit a → (∀ b < a, C b) → C a)

open Classical in
/-- Recursion principle on a well-founded partial `SuccOrder`. -/
@[elab_as_elim] noncomputable def prelimitRecOn : ∀ b : α, C b :=
  wellFounded_lt.fix
    fun b IH ↦ if hb : IsSuccPrelimit b then hl b hb IH else
      have H := Classical.choose_spec (not_isSuccPrelimit_iff.1 hb)
      cast (congr_arg C H.2) (hs _ H.1 <| IH _ <| H.2.subst <| lt_succ_of_not_isMax H.1)

@[simp]
theorem prelimitRecOn_limit (hb : IsSuccPrelimit b) :
    prelimitRecOn hs hl b = hl b hb fun x _ ↦ SuccOrder.prelimitRecOn hs hl x := by
  rw [prelimitRecOn, WellFounded.fix_eq, dif_pos hb]

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] [WellFoundedLT α]
  (hs : ∀ a, ¬ IsMax a → C a → C (Order.succ a)) (hl : ∀ a, IsSuccPrelimit a → (∀ b < a, C b) → C a)

theorem prelimitRecOn_succ' (hb : ¬ IsMax b) :
    prelimitRecOn hs hl (Order.succ b) = hs b hb (prelimitRecOn hs hl b) := by
  have hb' := not_isSuccPrelimit_succ_of_not_isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff.1 hb')
  rw [prelimitRecOn, WellFounded.fix_eq, dif_neg hb']
  have {a c : α} {ha hc} {x : ∀ a, C a} (h : a = c) :
    cast (congr_arg (C ∘ succ) h) (hs a ha (x a)) = hs c hc (x c) := by subst h; rfl
  exact this <| (succ_eq_succ_iff_of_not_isMax H.1 hb).1 H.2

@[simp]
theorem prelimitRecOn_succ [NoMaxOrder α] (b : α) :
    prelimitRecOn hs hl (Order.succ b) = hs b (not_isMax b) (prelimitRecOn hs hl b) :=
  prelimitRecOn_succ' _ _ _

end LinearOrder

end prelimitRecOn

section limitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α] [WellFoundedLT α] (hm : ∀ a, IsMin a → C a)
  (hs : ∀ a, ¬ IsMax a → C a → C (Order.succ a)) (hl : ∀ a, IsSuccLimit a → (∀ b < a, C b) → C a)

open Classical in
/-- Recursion principle on a well-founded partial `SuccOrder`, separating out the case of a
minimal element. -/
@[elab_as_elim] noncomputable def limitRecOn : ∀ a, C a :=
  prelimitRecOn hs fun a ha IH ↦
    if h : IsMin a then hm a h else hl a (ha.isSuccLimit_of_not_isMin h) IH

@[simp]
theorem limitRecOn_isMin (hb : IsMin b) : limitRecOn hm hs hl b = hm b hb := by
  rw [limitRecOn, prelimitRecOn_limit _ _ hb.isSuccPrelimit, dif_pos hb]

@[simp]
theorem limitRecOn_limit (hb : IsSuccLimit b) :
    limitRecOn hm hs hl b = hl b hb fun x _ ↦ limitRecOn hm hs hl x := by
  rw [limitRecOn, prelimitRecOn_limit _ _ hb.isSuccPrelimit, dif_neg hb.not_isMin]; rfl

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] [WellFoundedLT α] (hm : ∀ a, IsMin a → C a)
  (hs : ∀ a, ¬ IsMax a → C a → C (Order.succ a)) (hl : ∀ a, IsSuccLimit a → (∀ b < a, C b) → C a)

theorem limitRecOn_succ' (hb : ¬ IsMax b) :
    limitRecOn hm hs hl (Order.succ b) = hs b hb (limitRecOn hm hs hl b) := by
  rw [limitRecOn, prelimitRecOn_succ']; rfl

@[simp]
theorem limitRecOn_succ [NoMaxOrder α] (b : α) :
    limitRecOn hm hs hl (Order.succ b) = hs b (not_isMax b) (limitRecOn hm hs hl b) :=
  limitRecOn_succ' hm hs hl _

end LinearOrder

end limitRecOn

end SuccOrder

namespace Order

variable {C : α → Sort*} {b : α}

section isPredPrelimitRecOn

section PartialOrder

variable [PartialOrder α] [PredOrder α]
  (hs : ∀ a, ¬ IsMin a → C (pred a)) (hl : ∀ a, IsPredPrelimit a → C a)

/-- A value can be built by building it on predecessors and predecessor pre-limits. -/
@[elab_as_elim]
noncomputable def isPredPrelimitRecOn (b : α) : C b :=
  isSuccPrelimitRecOn (α := αᵒᵈ) hs (fun a ha ↦ hl a ha.dual) b

@[simp]
theorem isPredPrelimitRecOn_limit (hb : IsPredPrelimit b) : isPredPrelimitRecOn hs hl b = hl b hb :=
  isSuccPrelimitRecOn_limit (α := αᵒᵈ) hs _ hb.dual

end PartialOrder

section LinearOrder

variable [LinearOrder α] [PredOrder α]
  (hs : ∀ a, ¬ IsMin a → C (pred a)) (hl : ∀ a, IsPredPrelimit a → C a)

theorem isPredPrelimitRecOn_pred' (hb : ¬ IsMin b) :
    isPredPrelimitRecOn hs hl (pred b) = hs b hb :=
  isSuccPrelimitRecOn_succ' (α := αᵒᵈ) hs _ hb

@[simp]
theorem isPredPrelimitRecOn_pred [NoMinOrder α] (b : α) :
    isPredPrelimitRecOn hs hl (pred b) = hs b (not_isMin b) :=
  isSuccPrelimitRecOn_succ (α := αᵒᵈ) hs _ b

end LinearOrder

end isPredPrelimitRecOn

section isPredLimitRecOn

section PartialOrder

variable [PartialOrder α] [PredOrder α]
  (hm : ∀ a, IsMax a → C a) (hs : ∀ a, ¬ IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)

/-- A value can be built by building it on maximal elements, predecessors,
and predecessor limits. -/
@[elab_as_elim]
noncomputable def isPredLimitRecOn (b : α) : C b :=
  isSuccLimitRecOn (α := αᵒᵈ) hm hs (fun a ha => hl a ha.dual) b

@[simp]
theorem isPredLimitRecOn_isMax (hb : IsMax b) : isPredLimitRecOn hm hs hl b = hm b hb :=
  isSuccLimitRecOn_isMin (α := αᵒᵈ) hm hs _ hb

@[simp]
theorem isPredLimitRecOn_limit (hb : IsPredLimit b) : isPredLimitRecOn hm hs hl b = hl b hb :=
  isSuccLimitRecOn_limit (α := αᵒᵈ) hm hs _ hb.dual

end PartialOrder

section LinearOrder

variable [LinearOrder α] [PredOrder α]
  (hm : ∀ a, IsMax a → C a) (hs : ∀ a, ¬ IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)

theorem isPredLimitRecOn_pred' (hb : ¬ IsMin b) : isPredLimitRecOn hm hs hl (pred b) = hs b hb :=
  isSuccLimitRecOn_succ' (α := αᵒᵈ) hm hs _ hb

@[simp]
theorem isPredLimitRecOn_pred [NoMinOrder α] :
    isPredLimitRecOn hm hs hl (pred b) = hs b (not_isMin b) :=
  isSuccLimitRecOn_succ (α := αᵒᵈ) hm hs _ b

end LinearOrder

end isPredLimitRecOn

end Order

open Order

namespace PredOrder

variable {C : α → Sort*} {b : α}

section prelimitRecOn

section PartialOrder

variable [PartialOrder α] [PredOrder α] [WellFoundedGT α]
  (hs : ∀ a, ¬ IsMin a → C a → C (Order.pred a)) (hl : ∀ a, IsPredPrelimit a → (∀ b > a, C b) → C a)

/-- Recursion principle on a well-founded partial `PredOrder`. -/
@[elab_as_elim] noncomputable def prelimitRecOn : ∀ b : α, C b :=
  SuccOrder.prelimitRecOn (α := αᵒᵈ) hs (fun a ha => hl a ha.dual)

@[simp]
theorem prelimitRecOn_limit (hb : IsPredPrelimit b) :
    prelimitRecOn hs hl b = hl b hb fun x _ ↦ prelimitRecOn hs hl x :=
  SuccOrder.prelimitRecOn_limit (α := αᵒᵈ) hs _ hb.dual

end PartialOrder

section LinearOrder

variable [LinearOrder α] [PredOrder α] [WellFoundedGT α]
  (hs : ∀ a, ¬ IsMin a → C a → C (Order.pred a)) (hl : ∀ a, IsPredPrelimit a → (∀ b > a, C b) → C a)

theorem prelimitRecOn_pred' (hb : ¬ IsMin b) :
    prelimitRecOn hs hl (Order.pred b) = hs b hb (prelimitRecOn hs hl b) :=
  SuccOrder.prelimitRecOn_succ' (α := αᵒᵈ) hs _ hb

@[simp]
theorem prelimitRecOn_pred [NoMinOrder α] (b : α) :
    prelimitRecOn hs hl (Order.pred b) = hs b (not_isMin b) (prelimitRecOn hs hl b) :=
  prelimitRecOn_pred' _ _ _

end LinearOrder

end prelimitRecOn

section limitRecOn

section PartialOrder

variable [PartialOrder α] [PredOrder α] [WellFoundedGT α] (hm : ∀ a, IsMax a → C a)
  (hs : ∀ a, ¬ IsMin a → C a → C (Order.pred a)) (hl : ∀ a, IsPredLimit a → (∀ b > a, C b) → C a)

open Classical in
/-- Recursion principle on a well-founded partial `PredOrder`, separating out the case of a
maximal element. -/
@[elab_as_elim] noncomputable def limitRecOn : ∀ a, C a :=
  SuccOrder.limitRecOn (α := αᵒᵈ) hm hs (fun a ha => hl a ha.dual)

@[simp]
theorem limitRecOn_isMax (hb : IsMax b) : limitRecOn hm hs hl b = hm b hb :=
  SuccOrder.limitRecOn_isMin (α := αᵒᵈ) hm hs _ hb

@[simp]
theorem limitRecOn_limit (hb : IsPredLimit b) :
    limitRecOn hm hs hl b = hl b hb fun x _ ↦ limitRecOn hm hs hl x :=
  SuccOrder.limitRecOn_limit (α := αᵒᵈ) hm hs _ hb.dual

end PartialOrder

section LinearOrder

variable [LinearOrder α] [PredOrder α] [WellFoundedGT α] (hm : ∀ a, IsMax a → C a)
  (hs : ∀ a, ¬ IsMin a → C a → C (Order.pred a)) (hl : ∀ a, IsPredLimit a → (∀ b > a, C b) → C a)

theorem limitRecOn_pred' (hb : ¬ IsMin b) :
    limitRecOn hm hs hl (Order.pred b) = hs b hb (limitRecOn hm hs hl b) :=
  SuccOrder.limitRecOn_succ' (α := αᵒᵈ) hm hs _ hb

@[simp]
theorem limitRecOn_pred [NoMinOrder α] (b : α) :
    limitRecOn hm hs hl (Order.pred b) = hs b (not_isMin b) (limitRecOn hm hs hl b) :=
  SuccOrder.limitRecOn_succ (α := αᵒᵈ) hm hs _ b

end LinearOrder

end limitRecOn

end PredOrder
