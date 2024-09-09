/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Order.BoundedOrder

/-!
# Successor and predecessor limits

We define the predicate `Order.IsSuccPrelimit` for "successor pre-limits", values that don't cover
any others. They are so named since they can't be the successors of anything smaller. We define
`Order.IsPredPrelimit` analogously, and prove basic results.

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

@[deprecated IsSuccPrelimit (since := "2024-09-05")]
alias IsSuccLimit := IsSuccPrelimit

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

protected theorem _root_.IsMin.isSuccPrelimit : IsMin a → IsSuccPrelimit a := fun h _ hab =>
  not_isMin_of_lt hab.lt h

@[deprecated _root_.IsMin.isSuccPrelimit (since := "2024-09-05")]
alias _root_.IsMin.isSuccLimit := _root_.IsMin.isSuccPrelimit

theorem isSuccPrelimit_bot [OrderBot α] : IsSuccPrelimit (⊥ : α) :=
  IsMin.isSuccPrelimit isMin_bot

@[deprecated isSuccPrelimit_bot (since := "2024-09-05")]
alias isSuccLimit_bot := isSuccPrelimit_bot

variable [SuccOrder α]

protected theorem IsSuccPrelimit.isMax (h : IsSuccPrelimit (succ a)) : IsMax a := by
  by_contra H
  exact h a (covBy_succ_of_not_isMax H)

@[deprecated IsSuccPrelimit.isMax (since := "2024-09-05")]
alias IsSuccLimit.isMax := IsSuccPrelimit.isMax

theorem not_isSuccPrelimit_succ_of_not_isMax (ha : ¬IsMax a) : ¬IsSuccPrelimit (succ a) := by
  contrapose! ha
  exact ha.isMax

@[deprecated not_isSuccPrelimit_succ_of_not_isMax (since := "2024-09-05")]
alias not_isSuccLimit_succ_of_not_isMax := not_isSuccPrelimit_succ_of_not_isMax

section NoMaxOrder

variable [NoMaxOrder α]

theorem IsSuccPrelimit.succ_ne (h : IsSuccPrelimit a) (b : α) : succ b ≠ a := by
  rintro rfl
  exact not_isMax _ h.isMax

@[deprecated IsSuccPrelimit.succ_ne (since := "2024-09-05")]
alias IsSuccLimit.succ_ne := IsSuccPrelimit.succ_ne

@[simp]
theorem not_isSuccPrelimit_succ (a : α) : ¬IsSuccPrelimit (succ a) := fun h => h.succ_ne _ rfl

@[deprecated not_isSuccPrelimit_succ (since := "2024-09-05")]
alias not_isSuccLimit_succ := not_isSuccPrelimit_succ

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

theorem IsSuccPrelimit.isMin_of_noMax [NoMaxOrder α] (h : IsSuccPrelimit a) : IsMin a := by
  intro b hb
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_isSuccPrelimit_succ _ h).elim

@[deprecated IsSuccPrelimit.isMin_of_noMax (since := "2024-09-05")]
alias IsSuccLimit.isMin_of_noMax := IsSuccPrelimit.isMin_of_noMax

@[simp]
theorem isSuccPrelimit_iff_of_noMax [NoMaxOrder α] : IsSuccPrelimit a ↔ IsMin a :=
  ⟨IsSuccPrelimit.isMin_of_noMax, IsMin.isSuccPrelimit⟩

@[deprecated isSuccPrelimit_iff_of_noMax (since := "2024-09-05")]
alias isSuccLimit_iff_of_noMax := isSuccPrelimit_iff_of_noMax

theorem not_isSuccPrelimit_of_noMax [NoMinOrder α] [NoMaxOrder α] : ¬IsSuccPrelimit a := by simp

@[deprecated not_isSuccPrelimit_of_noMax (since := "2024-09-05")]
alias not_isSuccLimit_of_noMax := not_isSuccPrelimit_of_noMax

end IsSuccArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α} {C : α → Sort*}

theorem isSuccPrelimit_of_succ_ne (h : ∀ b, succ b ≠ a) : IsSuccPrelimit a := fun b hba =>
  h b (CovBy.succ_eq hba)

@[deprecated isSuccPrelimit_of_succ_ne (since := "2024-09-05")]
alias isSuccLimit_of_succ_ne := isSuccPrelimit_of_succ_ne

theorem not_isSuccPrelimit_iff : ¬IsSuccPrelimit a ↔ ∃ b, ¬IsMax b ∧ succ b = a := by
  rw [not_isSuccPrelimit_iff_exists_covBy]
  refine exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_isMax, (CovBy.succ_eq hba)⟩, ?_⟩
  rintro ⟨h, rfl⟩
  exact covBy_succ_of_not_isMax h

@[deprecated not_isSuccPrelimit_iff (since := "2024-09-05")]
alias not_isSuccLimit_iff := not_isSuccPrelimit_iff

/-- See `not_isSuccPrelimit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_succ_of_not_isSuccPrelimit (h : ¬IsSuccPrelimit a) : a ∈ range (@succ α _ _) := by
  cases' not_isSuccPrelimit_iff.1 h with b hb
  exact ⟨b, hb.2⟩

@[deprecated mem_range_succ_of_not_isSuccPrelimit (since := "2024-09-05")]
alias mem_range_succ_of_not_isSuccLimit := mem_range_succ_of_not_isSuccPrelimit

theorem mem_range_succ_or_isSuccPrelimit (a) : a ∈ range (@succ α _ _) ∨ IsSuccPrelimit a :=
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

@[deprecated IsSuccPrelimit.succ_lt (since := "2024-09-05")]
alias IsSuccLimit.succ_lt := IsSuccPrelimit.succ_lt

theorem IsSuccPrelimit.succ_lt_iff (hb : IsSuccPrelimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩

@[deprecated IsSuccPrelimit.succ_lt_iff (since := "2024-09-05")]
alias IsSuccLimit.succ_lt_iff := IsSuccPrelimit.succ_lt_iff

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

theorem not_isSuccPrelimit_iff' : ¬IsSuccPrelimit a ↔ a ∈ range (@succ α _ _) := by
  simp_rw [isSuccPrelimit_iff_succ_ne, not_forall, not_ne_iff]
  rfl

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

@[deprecated IsSuccPrelimit.isMin (since := "2024-09-05")]
alias IsSuccLimit.isMin := IsSuccPrelimit.isMin

@[simp]
theorem isSuccPrelimit_iff : IsSuccPrelimit a ↔ IsMin a :=
  ⟨IsSuccPrelimit.isMin, IsMin.isSuccPrelimit⟩

@[deprecated isSuccPrelimit_iff (since := "2024-09-05")]
alias isSuccLimit_iff := isSuccPrelimit_iff

theorem not_isSuccPrelimit [NoMinOrder α] : ¬IsSuccPrelimit a := by simp

@[deprecated not_isSuccPrelimit (since := "2024-09-05")]
alias not_isSuccLimit := not_isSuccPrelimit

end IsSuccArchimedean

end PartialOrder

/-! ### Predecessor limits -/


section LT

variable [LT α] {a : α}

/-- A successor pre-limit is a value that isn't covered by any other.

It's so named because in a predecessor order, a predecessor limit can't be the predecessor of
anything greater.

For some applications, it's desirable to exclude the case where an element is maximal. A future PR
will introduce `IsPredLimit` for this usage. -/
def IsPredPrelimit (a : α) : Prop :=
  ∀ b, ¬a ⋖ b

@[deprecated IsPredPrelimit (since := "2024-09-05")]
alias IsPredLimit := IsPredPrelimit

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

@[deprecated isSuccPrelimit_toDual_iff (since := "2024-09-05")]
alias isSuccLimit_toDual_iff := isSuccPrelimit_toDual_iff

@[simp]
theorem isPredPrelimit_toDual_iff : IsPredPrelimit (toDual a) ↔ IsSuccPrelimit a := by
  simp [IsSuccPrelimit, IsPredPrelimit]

@[deprecated isPredPrelimit_toDual_iff (since := "2024-09-05")]
alias isPredLimit_toDual_iff := isPredPrelimit_toDual_iff

alias ⟨_, IsPredPrelimit.dual⟩ := isSuccPrelimit_toDual_iff
alias ⟨_, IsSuccPrelimit.dual⟩ := isPredPrelimit_toDual_iff
@[deprecated IsPredPrelimit.dual (since := "2024-09-05")]
alias isPredLimit.dual := IsPredPrelimit.dual
@[deprecated IsSuccPrelimit.dual (since := "2024-09-05")]
alias isSuccLimit.dual := IsSuccPrelimit.dual

end LT

section Preorder

variable [Preorder α] {a : α}

protected theorem _root_.IsMax.isPredPrelimit : IsMax a → IsPredPrelimit a := fun h _ hab =>
  not_isMax_of_lt hab.lt h

@[deprecated _root_.IsMax.isPredPrelimit (since := "2024-09-05")]
alias _root_.IsMax.isPredLimit := _root_.IsMax.isPredPrelimit

theorem isPredPrelimit_top [OrderTop α] : IsPredPrelimit (⊤ : α) :=
   IsMax.isPredPrelimit isMax_top

@[deprecated isPredPrelimit_top (since := "2024-09-05")]
alias isPredLimit_top := isPredPrelimit_top

variable [PredOrder α]

protected theorem IsPredPrelimit.isMin (h : IsPredPrelimit (pred a)) : IsMin a := by
  by_contra H
  exact h a (pred_covBy_of_not_isMin H)

@[deprecated IsPredPrelimit.isMin (since := "2024-09-05")]
alias IsPredLimit.isMin := IsPredPrelimit.isMin

theorem not_isPredPrelimit_pred_of_not_isMin (ha : ¬IsMin a) : ¬IsPredPrelimit (pred a) := by
  contrapose! ha
  exact ha.isMin

@[deprecated not_isPredPrelimit_pred_of_not_isMin (since := "2024-09-05")]
alias not_isPredLimit_pred_of_not_isMin := not_isPredPrelimit_pred_of_not_isMin

section NoMinOrder

variable [NoMinOrder α]

theorem IsPredPrelimit.pred_ne (h : IsPredPrelimit a) (b : α) : pred b ≠ a := by
  rintro rfl
  exact not_isMin _ h.isMin

@[deprecated IsPredPrelimit.pred_ne (since := "2024-09-05")]
alias IsPredLimit.pred_ne := IsPredPrelimit.pred_ne

@[simp]
theorem not_isPredPrelimit_pred (a : α) : ¬IsPredPrelimit (pred a) := fun h => h.pred_ne _ rfl

@[deprecated not_isPredPrelimit_pred (since := "2024-09-05")]
alias not_isPredLimit_pred := not_isPredPrelimit_pred

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem IsPredPrelimit.isMax_of_noMin [NoMinOrder α] (h : IsPredPrelimit a) : IsMax a :=
  h.dual.isMin_of_noMax

@[deprecated IsPredPrelimit.isMax_of_noMin (since := "2024-09-05")]
alias IsPredLimit.isMax_of_noMin := IsPredPrelimit.isMax_of_noMin

@[simp]
theorem isPredPrelimit_iff_of_noMin [NoMinOrder α] : IsPredPrelimit a ↔ IsMax a :=
  isSuccPrelimit_toDual_iff.symm.trans isSuccPrelimit_iff_of_noMax

@[deprecated isPredPrelimit_iff_of_noMin (since := "2024-09-05")]
alias isPredLimit_iff_of_noMin := isPredPrelimit_iff_of_noMin

theorem not_isPredPrelimit_of_noMin [NoMinOrder α] [NoMaxOrder α] : ¬IsPredPrelimit a := by simp

@[deprecated not_isPredPrelimit_of_noMin (since := "2024-09-05")]
alias not_isPredLimit_of_noMin := not_isPredPrelimit_of_noMin

end IsPredArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [PredOrder α] {a b : α} {C : α → Sort*}

theorem isPredPrelimit_of_pred_ne (h : ∀ b, pred b ≠ a) : IsPredPrelimit a := fun b hba =>
  h b (CovBy.pred_eq hba)

@[deprecated isPredPrelimit_of_pred_ne (since := "2024-09-05")]
alias isPredLimit_of_pred_ne := isPredPrelimit_of_pred_ne

theorem not_isPredPrelimit_iff : ¬IsPredPrelimit a ↔ ∃ b, ¬IsMin b ∧ pred b = a := by
  rw [← isSuccPrelimit_toDual_iff]
  exact not_isSuccPrelimit_iff

@[deprecated not_isPredPrelimit_iff (since := "2024-09-05")]
alias not_isPredLimit_iff := not_isPredPrelimit_iff

/-- See `not_isPredPrelimit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_pred_of_not_isPredPrelimit (h : ¬IsPredPrelimit a) : a ∈ range (@pred α _ _) := by
  cases' not_isPredPrelimit_iff.1 h with b hb
  exact ⟨b, hb.2⟩

@[deprecated mem_range_pred_of_not_isPredPrelimit (since := "2024-09-05")]
alias mem_range_pred_of_not_isPredLimit := mem_range_pred_of_not_isPredPrelimit

theorem mem_range_pred_or_isPredPrelimit (a) : a ∈ range (@pred α _ _) ∨ IsPredPrelimit a :=
  or_iff_not_imp_right.2 <| mem_range_pred_of_not_isPredPrelimit

@[deprecated mem_range_pred_or_isPredPrelimit (since := "2024-09-05")]
alias mem_range_pred_or_isPredLimit := mem_range_pred_or_isPredPrelimit

theorem isPredPrelimit_of_pred_lt (H : ∀ a > b, pred a < b) : IsPredPrelimit b := fun a hab =>
  (H a hab.lt).ne (CovBy.pred_eq hab)

@[deprecated isPredPrelimit_of_pred_lt (since := "2024-09-05")]
alias isPredLimit_of_pred_lt := isPredPrelimit_of_pred_lt

theorem IsPredPrelimit.lt_pred (h : IsPredPrelimit a) : a < b → a < pred b :=
  h.dual.succ_lt

@[deprecated IsPredPrelimit.lt_pred (since := "2024-09-05")]
alias IsPredLimit.lt_pred := IsPredPrelimit.lt_pred

theorem IsPredPrelimit.lt_pred_iff (h : IsPredPrelimit a) : a < pred b ↔ a < b :=
  h.dual.succ_lt_iff

@[deprecated IsPredPrelimit.lt_pred_iff (since := "2024-09-05")]
alias IsPredLimit.lt_pred_iff := IsPredPrelimit.lt_pred_iff

theorem isPredPrelimit_iff_lt_pred : IsPredPrelimit a ↔ ∀ ⦃b⦄, a < b → a < pred b :=
  isSuccPrelimit_toDual_iff.symm.trans isSuccPrelimit_iff_succ_lt

@[deprecated isPredPrelimit_iff_lt_pred (since := "2024-09-05")]
alias isPredLimit_iff_lt_pred := isPredPrelimit_iff_lt_pred

section NoMinOrder

variable [NoMinOrder α]

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem IsPredPrelimit.isMax (h : IsPredPrelimit a) : IsMax a :=
  h.dual.isMin

@[deprecated IsPredPrelimit.isMax (since := "2024-09-05")]
alias IsPredLimit.isMax := IsPredPrelimit.isMax

@[simp]
theorem isPredPrelimit_iff : IsPredPrelimit a ↔ IsMax a :=
  isSuccPrelimit_toDual_iff.symm.trans isSuccPrelimit_iff

@[deprecated isPredPrelimit_iff (since := "2024-09-05")]
alias isPredLimit_iff := isPredPrelimit_iff

theorem not_isPredPrelimit [NoMaxOrder α] : ¬IsPredPrelimit a := by simp

@[deprecated not_isPredPrelimit (since := "2024-09-05")]
alias not_isPredLimit := not_isPredPrelimit

end IsPredArchimedean

end PartialOrder

/-! ### Induction principles -/


variable {C : α → Sort*} {b : α}

section isSuccPrelimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α]

/-- A value can be built by building it on successors and successor limits. -/
@[elab_as_elim]
noncomputable def isSuccPrelimitRecOn (b : α) (hs : ∀ a, ¬ IsMax a → C (succ a))
    (hl : ∀ a, IsSuccPrelimit a → C a) : C b := by
  by_cases hb : IsSuccPrelimit b
  · exact hl b hb
  · have H := Classical.choose_spec (not_isSuccPrelimit_iff.1 hb)
    rw [← H.2]
    exact hs _ H.1

@[deprecated isSuccPrelimitRecOn (since := "2024-09-05")]
alias isSuccLimitRecOn := isSuccPrelimitRecOn

theorem isSuccPrelimitRecOn_limit (hs : ∀ a, ¬ IsMax a → C (succ a))
    (hl : ∀ a, IsSuccPrelimit a → C a) (hb : IsSuccPrelimit b) :
    isSuccPrelimitRecOn b hs hl = hl b hb :=
  dif_pos hb

@[deprecated isSuccPrelimitRecOn_limit (since := "2024-09-05")]
alias isSuccLimitRecOn_limit := isSuccPrelimitRecOn_limit

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α]

theorem isSuccPrelimitRecOn_succ' (hs : ∀ a, ¬ IsMax a → C (succ a))
    (hl : ∀ a, IsSuccPrelimit a → C a) (hb : ¬ IsMax b) :
    isSuccPrelimitRecOn (succ b) hs hl = hs b hb := by
  have hb' := not_isSuccPrelimit_succ_of_not_isMax hb
  have H := Classical.choose_spec (not_isSuccPrelimit_iff.1 hb')
  rw [isSuccPrelimitRecOn]
  simp only [cast_eq_iff_heq, hb', not_false_iff, eq_mpr_eq_cast, dif_neg]
  congr 1 <;> first |
    exact (succ_eq_succ_iff_of_not_isMax H.left hb).mp H.right |
    exact proof_irrel_heq H.left hb

@[deprecated isSuccPrelimitRecOn_succ' (since := "2024-09-05")]
alias isSuccLimitRecOn_succ' := isSuccPrelimitRecOn_succ'

@[simp]
theorem isSuccPrelimitRecOn_succ [NoMaxOrder α] (hs : ∀ a, ¬ IsMax a → C (succ a))
    (hl : ∀ a, IsSuccPrelimit a → C a) (b : α) :
    @isSuccPrelimitRecOn α C _ _ (succ b) hs hl = hs b (not_isMax b) :=
  isSuccPrelimitRecOn_succ' _ _ _

@[deprecated isSuccPrelimitRecOn_succ (since := "2024-09-05")]
alias isSuccLimitRecOn_succ := isSuccPrelimitRecOn_succ

end LinearOrder

end isSuccPrelimitRecOn

section isPredPrelimitRecOn

section PartialOrder

variable [PartialOrder α] [PredOrder α]

/-- A value can be built by building it on predecessors and predecessor limits. -/
@[elab_as_elim]
noncomputable def isPredPrelimitRecOn (b : α) (hs : ∀ a, ¬ IsMin a → C (pred a))
    (hl : ∀ a, IsPredPrelimit a → C a) : C b :=
  @isSuccPrelimitRecOn αᵒᵈ _ _ _ _ hs fun _ ha => hl _ ha.dual

@[deprecated isPredPrelimitRecOn (since := "2024-09-05")]
alias isPredLimitRecOn := isPredPrelimitRecOn

theorem isPredPrelimitRecOn_limit (hs : ∀ a, ¬ IsMin a → C (pred a))
    (hl : ∀ a, IsPredPrelimit a → C a) (hb : IsPredPrelimit b) :
    isPredPrelimitRecOn b hs hl = hl b hb :=
  isSuccPrelimitRecOn_limit _ _ hb.dual

@[deprecated isPredPrelimitRecOn_limit (since := "2024-09-05")]
alias isPredLimitRecOn_limit := isPredPrelimitRecOn_limit

end PartialOrder

section LinearOrder

variable [LinearOrder α] [PredOrder α]
  (hs : ∀ a, ¬ IsMin a → C (pred a)) (hl : ∀ a, IsPredPrelimit a → C a)

theorem isPredPrelimitRecOn_pred' {b : α} (hb : ¬ IsMin b) :
    @isPredPrelimitRecOn α C _ _ (pred b) hs hl = hs b hb :=
  isSuccPrelimitRecOn_succ' _ _ _

@[deprecated isPredPrelimitRecOn_pred' (since := "2024-09-05")]
alias isPredLimitRecOn_pred' := isPredPrelimitRecOn_pred'

@[simp]
theorem isPredPrelimitRecOn_pred [NoMinOrder α] (b : α) :
    @isPredPrelimitRecOn α C _ _ (pred b) hs hl = hs b (not_isMin b) :=
  isSuccPrelimitRecOn_succ _ _ _

@[deprecated isPredPrelimitRecOn_pred (since := "2024-09-05")]
alias isPredLimitRecOn_pred := isPredPrelimitRecOn_pred

end LinearOrder

end isPredPrelimitRecOn

end Order

open Order

variable {C : α → Sort*} {b : α}

namespace SuccOrder

section prelimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α] [WellFoundedLT α]

open scoped Classical in
/-- Recursion principle on a well-founded partial `SuccOrder`. -/
@[elab_as_elim] noncomputable def prelimitRecOn (b : α)
    (hs : ∀ a, ¬ IsMax a → C a → C (Order.succ a))
    (hl : ∀ a, IsSuccPrelimit a → (∀ b < a, C b) → C a) : C b :=
  wellFounded_lt.fix
    (fun a IH ↦ if h : IsSuccPrelimit a then hl a h IH else
      let x := Classical.indefiniteDescription _ (not_isSuccPrelimit_iff.mp h)
      x.2.2 ▸ hs x x.2.1 (IH x <| x.2.2.subst <| lt_succ_of_not_isMax x.2.1))
    b

@[deprecated prelimitRecOn (since := "2024-09-05")]
alias limitRecOn := prelimitRecOn

@[simp]
theorem prelimitRecOn_limit (hs : ∀ a, ¬ IsMax a → C a → C (Order.succ a))
    (hl : ∀ a, IsSuccPrelimit a → (∀ b < a, C b) → C a) (hb : IsSuccPrelimit b) :
    prelimitRecOn b hs hl = hl b hb fun x _ ↦ prelimitRecOn x hs hl := by
  rw [prelimitRecOn, WellFounded.fix_eq, dif_pos hb]; rfl

@[deprecated prelimitRecOn_limit (since := "2024-09-05")]
alias limitRecOn_limit := prelimitRecOn_limit

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] [WellFoundedLT α]
  (hs : ∀ a, ¬ IsMax a → C a → C (Order.succ a)) (hl : ∀ a, IsSuccPrelimit a → (∀ b < a, C b) → C a)

@[simp]
theorem prelimitRecOn_succ (hb : ¬ IsMax b) :
    prelimitRecOn (Order.succ b) hs hl = hs b hb (prelimitRecOn b hs hl) := by
  have h := not_isSuccPrelimit_succ_of_not_isMax hb
  rw [prelimitRecOn, WellFounded.fix_eq, dif_neg h]
  have {b c hb hc} {x : ∀ a, C a} (h : b = c) :
    congr_arg Order.succ h ▸ hs b hb (x b) = hs c hc (x c) := by subst h; rfl
  let x := Classical.indefiniteDescription _ (not_isSuccPrelimit_iff.mp h)
  exact this ((succ_eq_succ_iff_of_not_isMax x.2.1 hb).mp x.2.2)

@[deprecated prelimitRecOn_succ (since := "2024-09-05")]
alias limitRecOn_succ := prelimitRecOn_succ

end LinearOrder

end prelimitRecOn

end SuccOrder

namespace PredOrder

section prelimitRecOn

section PartialOrder

variable [PartialOrder α] [PredOrder α] [WellFoundedGT α]

/-- Recursion principle on a well-founded partial `PredOrder`. -/
@[elab_as_elim] noncomputable def prelimitRecOn (b : α)
    (hp : ∀ a, ¬ IsMin a → C a → C (Order.pred a))
    (hl : ∀ a, IsPredPrelimit a → (∀ b > a, C b) → C a) : C b :=
  SuccOrder.prelimitRecOn (α := αᵒᵈ) b hp fun a ha => hl a ha.dual

@[deprecated prelimitRecOn (since := "2024-09-05")]
alias limitRecOn := prelimitRecOn

@[simp]
theorem prelimitRecOn_limit (hp : ∀ a, ¬ IsMin a → C a → C (Order.pred a))
    (hl : ∀ a, IsPredPrelimit a → (∀ b > a, C b) → C a) (hb : IsPredPrelimit b) :
    prelimitRecOn b hp hl = hl b hb fun x _ ↦ prelimitRecOn x hp hl :=
  SuccOrder.prelimitRecOn_limit _ _ hb.dual

@[deprecated prelimitRecOn_limit (since := "2024-09-05")]
alias limitRecOn_limit := prelimitRecOn_limit

end PartialOrder

section LinearOrder

variable [LinearOrder α] [PredOrder α] [WellFoundedGT α]
  (hp : ∀ a, ¬ IsMin a → C a → C (Order.pred a)) (hl : ∀ a, IsPredPrelimit a → (∀ b > a, C b) → C a)

@[simp]
theorem prelimitRecOn_pred (hb : ¬ IsMin b) :
    prelimitRecOn (Order.pred b) hp hl = hp b hb (prelimitRecOn b hp hl) :=
  SuccOrder.prelimitRecOn_succ (α := αᵒᵈ) _ _ hb

@[deprecated prelimitRecOn_pred (since := "2024-09-05")]
alias limitRecOn_pred := prelimitRecOn_pred

end LinearOrder

end prelimitRecOn

end PredOrder
