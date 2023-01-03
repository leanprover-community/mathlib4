/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios

! This file was ported from Lean 3 source module order.succ_pred.limit
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.BoundedOrder

/-!
# Successor and predecessor limits

We define the predicate `Order.isSuccLimit` for "successor limits", values that don't cover any
others. They are so named since they can't be the successors of anything smaller. We define
`Order.isSuccLimit` analogously, and prove basic results.

## Todo

The plan is to eventually replace `Ordinal.IsLimit` and `Cardinal.IsLimit` with the common
predicate `Order.isSuccLimit`.
-/


variable {α : Type _}

namespace Order

open Function Set OrderDual

/-! ### Successor limits -/


section LT

variable [LT α]

/-- A successor limit is a value that doesn't cover any other.

It's so named because in a successor order, a successor limit can't be the successor of anything
smaller. -/
def IsSuccLimit (a : α) : Prop :=
  ∀ b, ¬b ⋖ a
#align order.is_succ_limit Order.isSuccLimit

theorem not_isSuccLimit_iff_exists_covby (a : α) : ¬isSuccLimit a ↔ ∃ b, b ⋖ a := by
  simp [isSuccLimit]
#align order.not_is_succ_limit_iff_exists_covby Order.not_isSuccLimit_iff_exists_covby

@[simp]
theorem isSuccLimit_of_dense [DenselyOrdered α] (a : α) : isSuccLimit a := fun _ => not_covby
#align order.is_succ_limit_of_dense Order.isSuccLimit_of_dense

end LT

section Preorder

variable [Preorder α] {a : α}

protected theorem IsMin.isSuccLimit : IsMin a → isSuccLimit a := fun h _ hab =>
  not_isMin_of_lt hab.lt h
#align is_min.is_succ_limit Order.IsMin.isSuccLimit

theorem isSuccLimit_bot [OrderBot α] : isSuccLimit (⊥ : α) :=
  IsMin.isSuccLimit isMin_bot
#align order.is_succ_limit_bot Order.isSuccLimit_bot

variable [SuccOrder α]

protected theorem isSuccLimit.isMax (h : isSuccLimit (succ a)) : IsMax a := by
  by_contra H
  exact h a (covby_succ_of_not_isMax H)
#align order.is_succ_limit.is_max Order.isSuccLimit.isMax

theorem not_isSuccLimit_succ_of_not_isMax (ha : ¬IsMax a) : ¬isSuccLimit (succ a) :=
  by
  contrapose! ha
  exact ha.isMax
#align order.not_is_succ_limit_succ_of_not_is_max Order.not_isSuccLimit_succ_of_not_isMax

section NoMaxOrder

variable [NoMaxOrder α]

theorem isSuccLimit.succ_ne (h : isSuccLimit a) (b : α) : succ b ≠ a :=
  by
  rintro rfl
  exact not_isMax _ h.isMax
#align order.is_succ_limit.succ_ne Order.isSuccLimit.succ_ne

@[simp]
theorem not_isSuccLimit_succ (a : α) : ¬isSuccLimit (succ a) := fun h => h.succ_ne _ rfl
#align order.not_is_succ_limit_succ Order.not_isSuccLimit_succ

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

theorem isSuccLimit.isMin_of_noMax [NoMaxOrder α] (h : isSuccLimit a) : IsMin a := fun b hb =>
  by
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_isSuccLimit_succ _ h).elim
#align order.is_succ_limit.is_min_of_no_max Order.isSuccLimit.isMin_of_noMax

@[simp]
theorem isSuccLimit_iff_of_noMax [NoMaxOrder α] : isSuccLimit a ↔ IsMin a :=
  ⟨isSuccLimit.isMin_of_noMax, IsMin.isSuccLimit⟩
#align order.is_succ_limit_iff_of_no_max Order.isSuccLimit_iff_of_noMax

theorem not_isSuccLimit_of_noMax [NoMinOrder α] [NoMaxOrder α] : ¬isSuccLimit a := by simp
#align order.not_is_succ_limit_of_no_max Order.not_isSuccLimit_of_noMax

end IsSuccArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α} {C : α → Sort _}

theorem isSuccLimit_of_succ_ne (h : ∀ b, succ b ≠ a) : isSuccLimit a := fun b hba =>
  h b (Order.Covby.succ_eq hba)
#align order.is_succ_limit_of_succ_ne Order.isSuccLimit_of_succ_ne

theorem not_isSuccLimit_iff : ¬isSuccLimit a ↔ ∃ b, ¬IsMax b ∧ succ b = a :=
  by
  rw [not_isSuccLimit_iff_exists_covby]
  refine' exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_is_max, (Covby.succ_eq hba)⟩, _⟩
  rintro ⟨h, rfl⟩
  exact covby_succ_of_not_isMax h
#align order.not_is_succ_limit_iff Order.not_isSuccLimit_iff

/-- See `not_isSuccLimit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_succ_of_not_isSuccLimit (h : ¬isSuccLimit a) : a ∈ range (@succ α _ _) :=
  by
  cases' not_isSuccLimit_iff.1 h with b hb
  exact ⟨b, hb.2⟩
#align order.mem_range_succ_of_not_is_succ_limit Order.mem_range_succ_of_not_isSuccLimit

theorem isSuccLimit_of_succ_lt (H : ∀ a < b, succ a < b) : isSuccLimit b := fun a hab =>
  (H a hab.lt).ne (Covby.succ_eq hab)
#align order.is_succ_limit_of_succ_lt Order.isSuccLimit_of_succ_lt

theorem isSuccLimit.succ_lt (hb : isSuccLimit b) (ha : a < b) : succ a < b :=
  by
  by_cases h : IsMax a
  · rwa [h.succ_eq]
  · rw [lt_iff_le_and_ne, succ_le_iff_of_not_isMax h]
    refine' ⟨ha, fun hab => _⟩
    subst hab
    exact (h hb.isMax).elim
#align order.is_succ_limit.succ_lt Order.isSuccLimit.succ_lt

theorem isSuccLimit.succ_lt_iff (hb : isSuccLimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩
#align order.is_succ_limit.succ_lt_iff Order.isSuccLimit.succ_lt_iff

theorem isSuccLimit_iff_succ_lt : isSuccLimit b ↔ ∀ a < b, succ a < b :=
  ⟨fun hb _ => hb.succ_lt, isSuccLimit_of_succ_lt⟩
#align order.is_succ_limit_iff_succ_lt Order.isSuccLimit_iff_succ_lt

/-- A value can be built by building it on successors and successor limits. -/
@[elab_as_elim]
noncomputable def isSuccLimitRecOn (b : α) (hs : ∀ a, ¬IsMax a → C (succ a))
    (hl : ∀ a, isSuccLimit a → C a) : C b :=
  by
  by_cases hb : isSuccLimit b
  · exact hl b hb
  · have H := Classical.choose_spec (not_isSuccLimit_iff.1 hb)
    rw [← H.2]
    exact hs _ H.1
#align order.is_succ_limit_rec_on Order.isSuccLimitRecOn

theorem isSuccLimitRecOn_limit (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, isSuccLimit a → C a)
    (hb : isSuccLimit b) : @isSuccLimitRecOn α _ _ C b hs hl = hl b hb := by
  classical exact dif_pos hb
#align order.is_succ_limit_rec_on_limit Order.isSuccLimit_rec_on_limit

theorem isSuccLimitRecOn_succ' (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, isSuccLimit a → C a)
    {b : α} (hb : ¬IsMax b) : @isSuccLimitRecOn α _ _ C (succ b) hs hl = hs b hb :=
  by
  have hb' := not_isSuccLimit_succ_of_not_isMax hb
  have H := Classical.choose_spec (not_isSuccLimit_iff.1 hb')
  rw [isSuccLimitRecOn]
  simp only [cast_eq_iff_heq, hb', not_false_iff, eq_mpr_eq_cast, dif_neg]
  congr 1 <;> first |
    exact (succ_eq_succ_iff_of_not_isMax H.left hb).mp H.right |
    exact proof_irrel_heq H.left hb
#align order.is_succ_limit_rec_on_succ' Order.isSuccLimit_rec_on_succ'

section NoMaxOrder

variable [NoMaxOrder α]

@[simp]
theorem isSuccLimit_rec_on_succ (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, isSuccLimit a → C a)
    (b : α) : @isSuccLimitRecOn α _ _ C (succ b) hs hl = hs b (not_isMax b) :=
  isSuccLimit_rec_on_succ' _ _ _
#align order.is_succ_limit_rec_on_succ Order.isSuccLimit_rec_on_succ

theorem isSuccLimit_iff_succ_ne : isSuccLimit a ↔ ∀ b, succ b ≠ a :=
  ⟨isSuccLimit.succ_ne, isSuccLimit_of_succ_ne⟩
#align order.is_succ_limit_iff_succ_ne Order.isSuccLimit_iff_succ_ne

theorem not_isSuccLimit_iff' : ¬isSuccLimit a ↔ a ∈ range (@succ α _ _) :=
  by
  simp_rw [isSuccLimit_iff_succ_ne, not_forall, not_ne_iff]
  rfl
#align order.not_is_succ_limit_iff' Order.not_isSuccLimit_iff'

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

protected theorem isSuccLimit.isMin (h : isSuccLimit a) : IsMin a := fun b hb =>
  by
  revert h
  refine' Succ.rec (fun _ => le_rfl) (fun c _ H hc => _) hb
  have := hc.isMax.succ_eq
  rw [this] at hc⊢
  exact H hc
#align order.is_succ_limit.is_min Order.isSuccLimit.isMin

@[simp]
theorem isSuccLimit_iff : isSuccLimit a ↔ IsMin a :=
  ⟨isSuccLimit.isMin, IsMin.isSuccLimit⟩
#align order.is_succ_limit_iff Order.isSuccLimit_iff

theorem not_isSuccLimit [NoMinOrder α] : ¬isSuccLimit a := by simp
#align order.not_is_succ_limit Order.not_isSuccLimit

end IsSuccArchimedean

end PartialOrder

/-! ### Predecessor limits -/


section LT

variable [LT α] {a : α}

/-- A predecessor limit is a value that isn't covered by any other.

It's so named because in a predecessor order, a predecessor limit can't be the predecessor of
anything greater. -/
def isPredLimit (a : α) : Prop :=
  ∀ b, ¬a ⋖ b
#align order.is_pred_limit Order.isPredLimit

theorem not_isPredLimit_iff_exists_covby (a : α) : ¬isPredLimit a ↔ ∃ b, a ⋖ b := by
  simp [isPredLimit]
#align order.not_is_pred_limit_iff_exists_covby Order.not_isPredLimit_iff_exists_covby

theorem isPredLimit_of_dense [DenselyOrdered α] (a : α) : isPredLimit a := fun _ => not_covby
#align order.is_pred_limit_of_dense Order.isPredLimit_of_dense

@[simp]
theorem isSuccLimit_to_dual_iff : isSuccLimit (toDual a) ↔ isPredLimit a := by
  simp [isSuccLimit, isPredLimit]
#align order.is_succ_limit_to_dual_iff Order.isSuccLimit_to_dual_iff

@[simp]
theorem isPredLimit_to_dual_iff : isPredLimit (toDual a) ↔ isSuccLimit a := by
  simp [isSuccLimit, isPredLimit]
#align order.is_pred_limit_to_dual_iff Order.isPredLimit_to_dual_iff

alias isSuccLimit_to_dual_iff ↔ _ isPredLimit.dual

alias isPredLimit_to_dual_iff ↔ _ isSuccLimit.dual

end LT

section Preorder

variable [Preorder α] {a : α}

protected theorem IsMax.isPredLimit : IsMax a → isPredLimit a := fun h _ hab =>
  not_isMax_of_lt hab.lt h
#align is_max.is_pred_limit Order.IsMax.isPredLimit

theorem isPredLimit_top [OrderTop α] : isPredLimit (⊤ : α) :=
   IsMax.isPredLimit isMax_top
#align order.is_pred_limit_top Order.isPredLimit_top

variable [PredOrder α]

protected theorem isPredLimit.isMin (h : isPredLimit (pred a)) : IsMin a :=
  by
  by_contra H
  exact h a (pred_covby_of_not_isMin H)
#align order.isPredLimit.is_min Order.isPredLimit.isMin

theorem not_isPredLimit_pred_of_not_isMin (ha : ¬IsMin a) : ¬isPredLimit (pred a) :=
  by
  contrapose! ha
  exact ha.isMin
#align order.not_is_pred_limit_pred_of_not_is_min Order.not_isPredLimit_pred_of_not_isMin

section NoMinOrder

variable [NoMinOrder α]

theorem isPredLimit.pred_ne (h : isPredLimit a) (b : α) : pred b ≠ a :=
  by
  rintro rfl
  exact not_isMin _ h.isMin
#align order.is_pred_limit.pred_ne Order.isPredLimit.pred_ne

@[simp]
theorem not_isPredLimit_pred (a : α) : ¬isPredLimit (pred a) := fun h => h.pred_ne _ rfl
#align order.not_is_pred_limit_pred Order.not_isPredLimit_pred

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem isPredLimit.isMax_of_noMin [NoMinOrder α] (h : isPredLimit a) : IsMax a :=
  (isPredLimit.dual h).isMin_of_noMax
#align order.is_pred_limit.is_max_of_no_min Order.isPredLimit.isMax_of_noMin

@[simp]
theorem isPredLimit_iff_of_noMin [NoMinOrder α] : isPredLimit a ↔ IsMax a :=
  isSuccLimit_to_dual_iff.symm.trans isSuccLimit_iff_of_noMax
#align order.is_pred_limit_iff_of_no_min Order.isPredLimit_iff_of_noMin

theorem not_isPredLimit_of_noMin [NoMinOrder α] [NoMaxOrder α] : ¬isPredLimit a := by simp
#align order.not_is_pred_limit_of_no_min Order.not_isPredLimit_of_noMin

end IsPredArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [PredOrder α] {a b : α} {C : α → Sort _}

theorem isPredLimit_of_pred_ne (h : ∀ b, pred b ≠ a) : isPredLimit a := fun b hba =>
  h b (Covby.pred_eq hba)
#align order.is_pred_limit_of_pred_ne Order.isPredLimit_of_pred_ne

theorem not_isPredLimit_iff : ¬isPredLimit a ↔ ∃ b, ¬IsMin b ∧ pred b = a :=
  by
  rw [← isSuccLimit_to_dual_iff]
  exact not_isSuccLimit_iff
#align order.not_is_pred_limit_iff Order.not_isPredLimit_iff

/-- See `not_isPredLimit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_pred_of_not_isPredLimit (h : ¬isPredLimit a) : a ∈ range (@pred α _ _) :=
  by
  cases' not_isPredLimit_iff.1 h with b hb
  exact ⟨b, hb.2⟩
#align order.mem_range_pred_of_not_is_pred_limit Order.mem_range_pred_of_not_isPredLimit

theorem isPredLimit_of_pred_lt (H : ∀ a > b, pred a < b) : isPredLimit b := fun a hab =>
  (H a hab.lt).ne (Covby.pred_eq hab)
#align order.is_pred_limit_of_pred_lt Order.isPredLimit_of_pred_lt

theorem isPredLimit.lt_pred (h : isPredLimit a) : a < b → a < pred b :=
  (isPredLimit.dual h).succ_lt
#align order.isPredLimit.lt_pred Order.isPredLimit.lt_pred

theorem isPredLimit.lt_pred_iff (h : isPredLimit a) : a < pred b ↔ a < b :=
  (isPredLimit.dual h).succ_lt_iff
#align order.is_pred_limit.lt_pred_iff Order.isPredLimit.lt_pred_iff

theorem isPredLimit_iff_lt_pred : isPredLimit a ↔ ∀ ⦃b⦄, a < b → a < pred b :=
  isSuccLimit_to_dual_iff.symm.trans isSuccLimit_iff_succ_lt
#align order.is_pred_limit_iff_lt_pred Order.isPredLimit_iff_lt_pred

/-- A value can be built by building it on predecessors and predecessor limits. -/
@[elab_as_elim]
noncomputable def isPredLimitRecOn (b : α) (hs : ∀ a, ¬IsMin a → C (pred a))
    (hl : ∀ a, isPredLimit a → C a) : C b :=
  @isSuccLimitRecOn αᵒᵈ _ _ _ _ hs fun _ ha => hl _ (isSuccLimit.dual ha)
#align order.is_pred_limit_rec_on Order.isPredLimitRecOn

theorem isPredLimit_rec_on_limit (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, isPredLimit a → C a)
    (hb : isPredLimit b) : @isPredLimitRecOn α _ _ C b hs hl = hl b hb :=
  isSuccLimit_rec_on_limit _ _ (isPredLimit.dual hb)
#align order.is_pred_limit_rec_on_limit Order.isPredLimit_rec_on_limit

theorem isPredLimit_rec_on_pred' (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, isPredLimit a → C a)
    {b : α} (hb : ¬IsMin b) : @isPredLimitRecOn α _ _ C (pred b) hs hl = hs b hb :=
  isSuccLimit_rec_on_succ' _ _ _
#align order.is_pred_limit_rec_on_pred' Order.isPredLimit_rec_on_pred'

section NoMinOrder

variable [NoMinOrder α]

@[simp]
theorem isPredLimit_rec_on_pred (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, isPredLimit a → C a)
    (b : α) : @isPredLimitRecOn α _ _ C (pred b) hs hl = hs b (not_isMin b) :=
  isSuccLimit_rec_on_succ _ _ _
#align order.is_pred_limit_rec_on_pred Order.isPredLimit_rec_on_pred

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem isPredLimit.isMax (h : isPredLimit a) : IsMax a :=
  (isPredLimit.dual h).isMin
#align order.isPredLimit.is_max Order.isPredLimit.isMax

@[simp]
theorem isPredLimit_iff : isPredLimit a ↔ IsMax a :=
  isSuccLimit_to_dual_iff.symm.trans isSuccLimit_iff
#align order.is_pred_limit_iff Order.isPredLimit_iff

theorem not_isPredLimit [NoMaxOrder α] : ¬isPredLimit a := by simp
#align order.not_is_pred_limit Order.not_isPredLimit

end IsPredArchimedean

end PartialOrder

end Order
