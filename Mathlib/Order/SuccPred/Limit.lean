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

We define the predicate `Order.IsSuccLimit` for "successor limits", values that don't cover any
others. They are so named since they can't be the successors of anything smaller. We define
`Order.IsSuccLimit` analogously, and prove basic results.

## Todo

The plan is to eventually replace `Ordinal.IsLimit` and `Cardinal.IsLimit` with the common
predicate `Order.IsSuccLimit`.
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
#align order.is_succ_limit Order.IsSuccLimit

theorem not_is_succ_limit_iff_exists_covby (a : α) : ¬IsSuccLimit a ↔ ∃ b, b ⋖ a := by
  simp [IsSuccLimit]
#align order.not_is_succ_limit_iff_exists_covby Order.not_is_succ_limit_iff_exists_covby

@[simp]
theorem is_succ_limit_of_dense [DenselyOrdered α] (a : α) : IsSuccLimit a := fun _ => not_covby
#align order.is_succ_limit_of_dense Order.is_succ_limit_of_dense

end LT

section Preorder

variable [Preorder α] {a : α}

protected theorem IsMin.is_succ_limit : IsMin a → IsSuccLimit a := fun h _ hab =>
  not_isMin_of_lt hab.lt h
#align is_min.is_succ_limit Order.IsMin.is_succ_limit

theorem is_succ_limit_bot [OrderBot α] : IsSuccLimit (⊥ : α) :=
  IsMin.is_succ_limit isMin_bot
#align order.is_succ_limit_bot Order.is_succ_limit_bot

variable [SuccOrder α]

protected theorem IsSuccLimit.isMax (h : IsSuccLimit (succ a)) : IsMax a :=
  by
  by_contra H
  exact h a (covby_succ_of_not_isMax H)
#align order.is_succ_limit.is_max Order.IsSuccLimit.isMax

theorem not_is_succ_limit_succ_of_not_isMax (ha : ¬IsMax a) : ¬IsSuccLimit (succ a) :=
  by
  contrapose! ha
  exact ha.isMax
#align order.not_is_succ_limit_succ_of_not_is_max Order.not_is_succ_limit_succ_of_not_isMax

section NoMaxOrder

variable [NoMaxOrder α]

theorem IsSuccLimit.succ_ne (h : IsSuccLimit a) (b : α) : succ b ≠ a :=
  by
  rintro rfl
  exact not_isMax _ h.isMax
#align order.is_succ_limit.succ_ne Order.IsSuccLimit.succ_ne

@[simp]
theorem not_is_succ_limit_succ (a : α) : ¬IsSuccLimit (succ a) := fun h => h.succ_ne _ rfl
#align order.not_is_succ_limit_succ Order.not_is_succ_limit_succ

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

theorem IsSuccLimit.isMin_of_noMax [NoMaxOrder α] (h : IsSuccLimit a) : IsMin a := fun b hb =>
  by
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_is_succ_limit_succ _ h).elim
#align order.is_succ_limit.is_min_of_no_max Order.IsSuccLimit.isMin_of_noMax

@[simp]
theorem is_succ_limit_iff_of_noMax [NoMaxOrder α] : IsSuccLimit a ↔ IsMin a :=
  ⟨IsSuccLimit.isMin_of_noMax, IsMin.is_succ_limit⟩
#align order.is_succ_limit_iff_of_no_max Order.is_succ_limit_iff_of_noMax

theorem not_is_succ_limit_of_noMax [NoMinOrder α] [NoMaxOrder α] : ¬IsSuccLimit a := by simp
#align order.not_is_succ_limit_of_no_max Order.not_is_succ_limit_of_noMax

end IsSuccArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α} {C : α → Sort _}

theorem is_succ_limit_of_succ_ne (h : ∀ b, succ b ≠ a) : IsSuccLimit a := fun b hba =>
  h b (Order.Covby.succ_eq hba)
#align order.is_succ_limit_of_succ_ne Order.is_succ_limit_of_succ_ne

theorem not_is_succ_limit_iff : ¬IsSuccLimit a ↔ ∃ b, ¬IsMax b ∧ succ b = a :=
  by
  rw [not_is_succ_limit_iff_exists_covby]
  refine' exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_is_max, (Covby.succ_eq hba)⟩, _⟩
  rintro ⟨h, rfl⟩
  exact covby_succ_of_not_isMax h
#align order.not_is_succ_limit_iff Order.not_is_succ_limit_iff

/-- See `not_is_succ_limit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_succ_of_not_is_succ_limit (h : ¬IsSuccLimit a) : a ∈ range (@succ α _ _) :=
  by
  cases' not_is_succ_limit_iff.1 h with b hb
  exact ⟨b, hb.2⟩
#align order.mem_range_succ_of_not_is_succ_limit Order.mem_range_succ_of_not_is_succ_limit

theorem is_succ_limit_of_succ_lt (H : ∀ a < b, succ a < b) : IsSuccLimit b := fun a hab =>
  (H a hab.lt).ne (Covby.succ_eq hab)
#align order.is_succ_limit_of_succ_lt Order.is_succ_limit_of_succ_lt

theorem IsSuccLimit.succ_lt (hb : IsSuccLimit b) (ha : a < b) : succ a < b :=
  by
  by_cases h : IsMax a
  · rwa [h.succ_eq]
  · rw [lt_iff_le_and_ne, succ_le_iff_of_not_isMax h]
    refine' ⟨ha, fun hab => _⟩
    subst hab
    exact (h hb.isMax).elim
#align order.is_succ_limit.succ_lt Order.IsSuccLimit.succ_lt

theorem IsSuccLimit.succ_lt_iff (hb : IsSuccLimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩
#align order.is_succ_limit.succ_lt_iff Order.IsSuccLimit.succ_lt_iff

theorem is_succ_limit_iff_succ_lt : IsSuccLimit b ↔ ∀ a < b, succ a < b :=
  ⟨fun hb _ => hb.succ_lt, is_succ_limit_of_succ_lt⟩
#align order.is_succ_limit_iff_succ_lt Order.is_succ_limit_iff_succ_lt

/-- A value can be built by building it on successors and successor limits. -/
@[elab_as_elim]
noncomputable def isSuccLimitRecOn (b : α) (hs : ∀ a, ¬IsMax a → C (succ a))
    (hl : ∀ a, IsSuccLimit a → C a) : C b :=
  by
  by_cases hb : IsSuccLimit b
  · exact hl b hb
  · have H := Classical.choose_spec (not_is_succ_limit_iff.1 hb)
    rw [← H.2]
    exact hs _ H.1
#align order.is_succ_limit_rec_on Order.isSuccLimitRecOn

theorem is_succ_limit_rec_on_limit (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    (hb : IsSuccLimit b) : @isSuccLimitRecOn α _ _ C b hs hl = hl b hb := by
  classical exact dif_pos hb
#align order.is_succ_limit_rec_on_limit Order.is_succ_limit_rec_on_limit

theorem is_succ_limit_rec_on_succ' (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    {b : α} (hb : ¬IsMax b) : @isSuccLimitRecOn α _ _ C (succ b) hs hl = hs b hb :=
  by
  have hb' := not_is_succ_limit_succ_of_not_isMax hb
  have H := Classical.choose_spec (not_is_succ_limit_iff.1 hb')
  rw [isSuccLimitRecOn]
  simp only [cast_eq_iff_heq, hb', not_false_iff, eq_mpr_eq_cast, dif_neg]
  congr 1 <;> first |
    exact (succ_eq_succ_iff_of_not_isMax H.left hb).mp H.right |
    exact proof_irrel_heq H.left hb

#align order.is_succ_limit_rec_on_succ' Order.is_succ_limit_rec_on_succ'

section NoMaxOrder

variable [NoMaxOrder α]

@[simp]
theorem is_succ_limit_rec_on_succ (hs : ∀ a, ¬IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    (b : α) : @isSuccLimitRecOn α _ _ C (succ b) hs hl = hs b (not_isMax b) :=
  is_succ_limit_rec_on_succ' _ _ _
#align order.is_succ_limit_rec_on_succ Order.is_succ_limit_rec_on_succ

theorem is_succ_limit_iff_succ_ne : IsSuccLimit a ↔ ∀ b, succ b ≠ a :=
  ⟨IsSuccLimit.succ_ne, is_succ_limit_of_succ_ne⟩
#align order.is_succ_limit_iff_succ_ne Order.is_succ_limit_iff_succ_ne

theorem not_is_succ_limit_iff' : ¬IsSuccLimit a ↔ a ∈ range (@succ α _ _) :=
  by
  simp_rw [is_succ_limit_iff_succ_ne, not_forall, not_ne_iff]
  rfl
#align order.not_is_succ_limit_iff' Order.not_is_succ_limit_iff'

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

protected theorem IsSuccLimit.isMin (h : IsSuccLimit a) : IsMin a := fun b hb =>
  by
  revert h
  refine' Succ.rec (fun _ => le_rfl) (fun c _ H hc => _) hb
  have := hc.isMax.succ_eq
  rw [this] at hc⊢
  exact H hc
#align order.is_succ_limit.is_min Order.IsSuccLimit.isMin

@[simp]
theorem is_succ_limit_iff : IsSuccLimit a ↔ IsMin a :=
  ⟨IsSuccLimit.isMin, IsMin.is_succ_limit⟩
#align order.is_succ_limit_iff Order.is_succ_limit_iff

theorem not_is_succ_limit [NoMinOrder α] : ¬IsSuccLimit a := by simp
#align order.not_is_succ_limit Order.not_is_succ_limit

end IsSuccArchimedean

end PartialOrder

/-! ### Predecessor limits -/


section LT

variable [LT α] {a : α}

/-- A predecessor limit is a value that isn't covered by any other.

It's so named because in a predecessor order, a predecessor limit can't be the predecessor of
anything greater. -/
def IsPredLimit (a : α) : Prop :=
  ∀ b, ¬a ⋖ b
#align order.is_pred_limit Order.IsPredLimit

theorem not_is_pred_limit_iff_exists_covby (a : α) : ¬IsPredLimit a ↔ ∃ b, a ⋖ b := by
  simp [IsPredLimit]
#align order.not_is_pred_limit_iff_exists_covby Order.not_is_pred_limit_iff_exists_covby

theorem is_pred_limit_of_dense [DenselyOrdered α] (a : α) : IsPredLimit a := fun _ => not_covby
#align order.is_pred_limit_of_dense Order.is_pred_limit_of_dense

@[simp]
theorem is_succ_limit_to_dual_iff : IsSuccLimit (toDual a) ↔ IsPredLimit a := by
  simp [IsSuccLimit, IsPredLimit]
#align order.is_succ_limit_to_dual_iff Order.is_succ_limit_to_dual_iff

@[simp]
theorem is_pred_limit_to_dual_iff : IsPredLimit (toDual a) ↔ IsSuccLimit a := by
  simp [IsSuccLimit, IsPredLimit]
#align order.is_pred_limit_to_dual_iff Order.is_pred_limit_to_dual_iff

alias is_succ_limit_to_dual_iff ↔ _ is_pred_limit.dual

alias is_pred_limit_to_dual_iff ↔ _ is_succ_limit.dual

end LT

section Preorder

variable [Preorder α] {a : α}

protected theorem IsMax.is_pred_limit : IsMax a → IsPredLimit a := fun h _ hab =>
  not_isMax_of_lt hab.lt h
#align is_max.is_pred_limit Order.IsMax.is_pred_limit

theorem is_pred_limit_top [OrderTop α] : IsPredLimit (⊤ : α) :=
   IsMax.is_pred_limit isMax_top
#align order.is_pred_limit_top Order.is_pred_limit_top

variable [PredOrder α]

protected theorem IsPredLimit.isMin (h : IsPredLimit (pred a)) : IsMin a :=
  by
  by_contra H
  exact h a (pred_covby_of_not_isMin H)
#align order.is_pred_limit.is_min Order.IsPredLimit.isMin

theorem not_is_pred_limit_pred_of_not_isMin (ha : ¬IsMin a) : ¬IsPredLimit (pred a) :=
  by
  contrapose! ha
  exact ha.isMin
#align order.not_is_pred_limit_pred_of_not_is_min Order.not_is_pred_limit_pred_of_not_isMin

section NoMinOrder

variable [NoMinOrder α]

theorem IsPredLimit.pred_ne (h : IsPredLimit a) (b : α) : pred b ≠ a :=
  by
  rintro rfl
  exact not_isMin _ h.isMin
#align order.is_pred_limit.pred_ne Order.IsPredLimit.pred_ne

@[simp]
theorem not_is_pred_limit_pred (a : α) : ¬IsPredLimit (pred a) := fun h => h.pred_ne _ rfl
#align order.not_is_pred_limit_pred Order.not_is_pred_limit_pred

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem IsPredLimit.isMax_of_noMin [NoMinOrder α] (h : IsPredLimit a) : IsMax a :=
  (is_pred_limit.dual h).isMin_of_noMax
#align order.is_pred_limit.is_max_of_no_min Order.IsPredLimit.isMax_of_noMin

@[simp]
theorem is_pred_limit_iff_of_noMin [NoMinOrder α] : IsPredLimit a ↔ IsMax a :=
  is_succ_limit_to_dual_iff.symm.trans is_succ_limit_iff_of_noMax
#align order.is_pred_limit_iff_of_no_min Order.is_pred_limit_iff_of_noMin

theorem not_is_pred_limit_of_noMin [NoMinOrder α] [NoMaxOrder α] : ¬IsPredLimit a := by simp
#align order.not_is_pred_limit_of_no_min Order.not_is_pred_limit_of_noMin

end IsPredArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [PredOrder α] {a b : α} {C : α → Sort _}

theorem is_pred_limit_of_pred_ne (h : ∀ b, pred b ≠ a) : IsPredLimit a := fun b hba =>
  h b (Covby.pred_eq hba)
#align order.is_pred_limit_of_pred_ne Order.is_pred_limit_of_pred_ne

theorem not_is_pred_limit_iff : ¬IsPredLimit a ↔ ∃ b, ¬IsMin b ∧ pred b = a :=
  by
  rw [← is_succ_limit_to_dual_iff]
  exact not_is_succ_limit_iff
#align order.not_is_pred_limit_iff Order.not_is_pred_limit_iff

/-- See `not_is_pred_limit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_pred_of_not_is_pred_limit (h : ¬IsPredLimit a) : a ∈ range (@pred α _ _) :=
  by
  cases' not_is_pred_limit_iff.1 h with b hb
  exact ⟨b, hb.2⟩
#align order.mem_range_pred_of_not_is_pred_limit Order.mem_range_pred_of_not_is_pred_limit

theorem is_pred_limit_of_pred_lt (H : ∀ a > b, pred a < b) : IsPredLimit b := fun a hab =>
  (H a hab.lt).ne (Covby.pred_eq hab)
#align order.is_pred_limit_of_pred_lt Order.is_pred_limit_of_pred_lt

theorem IsPredLimit.lt_pred (h : IsPredLimit a) : a < b → a < pred b :=
  (is_pred_limit.dual h).succ_lt
#align order.is_pred_limit.lt_pred Order.IsPredLimit.lt_pred

theorem IsPredLimit.lt_pred_iff (h : IsPredLimit a) : a < pred b ↔ a < b :=
  (is_pred_limit.dual h).succ_lt_iff
#align order.is_pred_limit.lt_pred_iff Order.IsPredLimit.lt_pred_iff

theorem is_pred_limit_iff_lt_pred : IsPredLimit a ↔ ∀ ⦃b⦄, a < b → a < pred b :=
  is_succ_limit_to_dual_iff.symm.trans is_succ_limit_iff_succ_lt
#align order.is_pred_limit_iff_lt_pred Order.is_pred_limit_iff_lt_pred

/-- A value can be built by building it on predecessors and predecessor limits. -/
@[elab_as_elim]
noncomputable def isPredLimitRecOn (b : α) (hs : ∀ a, ¬IsMin a → C (pred a))
    (hl : ∀ a, IsPredLimit a → C a) : C b :=
  @isSuccLimitRecOn αᵒᵈ _ _ _ _ hs fun _ ha => hl _ (is_succ_limit.dual ha)
#align order.is_pred_limit_rec_on Order.isPredLimitRecOn

theorem is_pred_limit_rec_on_limit (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)
    (hb : IsPredLimit b) : @isPredLimitRecOn α _ _ C b hs hl = hl b hb :=
  is_succ_limit_rec_on_limit _ _ (is_pred_limit.dual hb)
#align order.is_pred_limit_rec_on_limit Order.is_pred_limit_rec_on_limit

theorem is_pred_limit_rec_on_pred' (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)
    {b : α} (hb : ¬IsMin b) : @isPredLimitRecOn α _ _ C (pred b) hs hl = hs b hb :=
  is_succ_limit_rec_on_succ' _ _ _
#align order.is_pred_limit_rec_on_pred' Order.is_pred_limit_rec_on_pred'

section NoMinOrder

variable [NoMinOrder α]

@[simp]
theorem is_pred_limit_rec_on_pred (hs : ∀ a, ¬IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)
    (b : α) : @isPredLimitRecOn α _ _ C (pred b) hs hl = hs b (not_isMin b) :=
  is_succ_limit_rec_on_succ _ _ _
#align order.is_pred_limit_rec_on_pred Order.is_pred_limit_rec_on_pred

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem IsPredLimit.isMax (h : IsPredLimit a) : IsMax a :=
  (is_pred_limit.dual h).isMin
#align order.is_pred_limit.is_max Order.IsPredLimit.isMax

@[simp]
theorem is_pred_limit_iff : IsPredLimit a ↔ IsMax a :=
  is_succ_limit_to_dual_iff.symm.trans is_succ_limit_iff
#align order.is_pred_limit_iff Order.is_pred_limit_iff

theorem not_is_pred_limit [NoMaxOrder α] : ¬IsPredLimit a := by simp
#align order.not_is_pred_limit Order.not_is_pred_limit

end IsPredArchimedean

end PartialOrder

end Order
