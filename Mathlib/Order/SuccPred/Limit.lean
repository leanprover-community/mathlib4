/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.BoundedOrder

/-!
# Successor and predecessor limits

We define the predicate `Order.IsSuccLimit` for "successor limits", values that don't cover any
others. They are so named since they can't be the successors of anything smaller. We define
`Order.IsPredLimit` analogously, and prove basic results.

## TODO

The plan is to eventually replace `Ordinal.IsLimit` and `Cardinal.IsLimit` with the common
predicate `Order.IsSuccLimit`.
-/


variable {α : Type*}

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

theorem not_isSuccLimit_iff_exists_covBy (a : α) : ¬IsSuccLimit a ↔ ∃ b, b ⋖ a := by
  simp [IsSuccLimit]

@[simp]
theorem isSuccLimit_of_dense [DenselyOrdered α] (a : α) : IsSuccLimit a := fun _ => not_covBy

end LT

section Preorder

variable [Preorder α] {a : α}

protected theorem _root_.IsMin.isSuccLimit : IsMin a → IsSuccLimit a := fun h _ hab =>
  not_isMin_of_lt hab.lt h

theorem isSuccLimit_bot [OrderBot α] : IsSuccLimit (⊥ : α) :=
  IsMin.isSuccLimit isMin_bot

variable [SuccOrder α]

protected theorem IsSuccLimit.isMax (h : IsSuccLimit (succ a)) : IsMax a := by
  by_contra H
  exact h a (covBy_succ_of_not_isMax H)

theorem not_isSuccLimit_succ_of_not_isMax (ha : ¬IsMax a) : ¬IsSuccLimit (succ a) := by
  contrapose! ha
  exact ha.isMax

section NoMaxOrder

variable [NoMaxOrder α]

theorem IsSuccLimit.succ_ne (h : IsSuccLimit a) (b : α) : succ b ≠ a := by
  rintro rfl
  exact not_isMax _ h.isMax

@[simp]
theorem not_isSuccLimit_succ (a : α) : ¬IsSuccLimit (succ a) := fun h => h.succ_ne _ rfl

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

theorem IsSuccLimit.isMin_of_noMax [NoMaxOrder α] (h : IsSuccLimit a) : IsMin a := fun b hb => by
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩
  · exact le_rfl
  · rw [iterate_succ_apply'] at h
    exact (not_isSuccLimit_succ _ h).elim

@[simp]
theorem isSuccLimit_iff_of_noMax [NoMaxOrder α] : IsSuccLimit a ↔ IsMin a :=
  ⟨IsSuccLimit.isMin_of_noMax, IsMin.isSuccLimit⟩

theorem not_isSuccLimit_of_noMax [NoMinOrder α] [NoMaxOrder α] : ¬IsSuccLimit a := by simp

end IsSuccArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α} {C : α → Sort*}

theorem isSuccLimit_of_succ_ne (h : ∀ b, succ b ≠ a) : IsSuccLimit a := fun b hba =>
  h b (CovBy.succ_eq hba)

theorem not_isSuccLimit_iff : ¬IsSuccLimit a ↔ ∃ b, ¬IsMax b ∧ succ b = a := by
  rw [not_isSuccLimit_iff_exists_covBy]
  refine exists_congr fun b => ⟨fun hba => ⟨hba.lt.not_isMax, (CovBy.succ_eq hba)⟩, ?_⟩
  rintro ⟨h, rfl⟩
  exact covBy_succ_of_not_isMax h

/-- See `not_isSuccLimit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_succ_of_not_isSuccLimit (h : ¬IsSuccLimit a) : a ∈ range (@succ α _ _) := by
  cases' not_isSuccLimit_iff.1 h with b hb
  exact ⟨b, hb.2⟩

theorem mem_range_succ_or_isSuccLimit (a) : a ∈ range (@succ α _ _) ∨ IsSuccLimit a :=
  or_iff_not_imp_right.2 <| mem_range_succ_of_not_isSuccLimit

theorem isSuccLimit_of_succ_lt (H : ∀ a < b, succ a < b) : IsSuccLimit b := fun a hab =>
  (H a hab.lt).ne (CovBy.succ_eq hab)

theorem IsSuccLimit.succ_lt (hb : IsSuccLimit b) (ha : a < b) : succ a < b := by
  by_cases h : IsMax a
  · rwa [h.succ_eq]
  · rw [lt_iff_le_and_ne, succ_le_iff_of_not_isMax h]
    refine ⟨ha, fun hab => ?_⟩
    subst hab
    exact (h hb.isMax).elim

theorem IsSuccLimit.succ_lt_iff (hb : IsSuccLimit b) : succ a < b ↔ a < b :=
  ⟨fun h => (le_succ a).trans_lt h, hb.succ_lt⟩

theorem isSuccLimit_iff_succ_lt : IsSuccLimit b ↔ ∀ a < b, succ a < b :=
  ⟨fun hb _ => hb.succ_lt, isSuccLimit_of_succ_lt⟩

section NoMaxOrder

variable [NoMaxOrder α]

theorem isSuccLimit_iff_succ_ne : IsSuccLimit a ↔ ∀ b, succ b ≠ a :=
  ⟨IsSuccLimit.succ_ne, isSuccLimit_of_succ_ne⟩

theorem not_isSuccLimit_iff' : ¬IsSuccLimit a ↔ a ∈ range (@succ α _ _) := by
  simp_rw [isSuccLimit_iff_succ_ne, not_forall, not_ne_iff]
  rfl

end NoMaxOrder

section IsSuccArchimedean

variable [IsSuccArchimedean α]

protected theorem IsSuccLimit.isMin (h : IsSuccLimit a) : IsMin a := fun b hb => by
  revert h
  refine Succ.rec (fun _ => le_rfl) (fun c _ H hc => ?_) hb
  have := hc.isMax.succ_eq
  rw [this] at hc ⊢
  exact H hc

@[simp]
theorem isSuccLimit_iff : IsSuccLimit a ↔ IsMin a :=
  ⟨IsSuccLimit.isMin, IsMin.isSuccLimit⟩

theorem not_isSuccLimit [NoMinOrder α] : ¬IsSuccLimit a := by simp

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

theorem not_isPredLimit_iff_exists_covBy (a : α) : ¬IsPredLimit a ↔ ∃ b, a ⋖ b := by
  simp [IsPredLimit]

theorem isPredLimit_of_dense [DenselyOrdered α] (a : α) : IsPredLimit a := fun _ => not_covBy

@[simp]
theorem isSuccLimit_toDual_iff : IsSuccLimit (toDual a) ↔ IsPredLimit a := by
  simp [IsSuccLimit, IsPredLimit]

@[simp]
theorem isPredLimit_toDual_iff : IsPredLimit (toDual a) ↔ IsSuccLimit a := by
  simp [IsSuccLimit, IsPredLimit]

alias ⟨_, isPredLimit.dual⟩ := isSuccLimit_toDual_iff

alias ⟨_, isSuccLimit.dual⟩ := isPredLimit_toDual_iff

end LT

section Preorder

variable [Preorder α] {a : α}

protected theorem _root_.IsMax.isPredLimit : IsMax a → IsPredLimit a := fun h _ hab =>
  not_isMax_of_lt hab.lt h

theorem isPredLimit_top [OrderTop α] : IsPredLimit (⊤ : α) :=
   IsMax.isPredLimit isMax_top

variable [PredOrder α]

protected theorem IsPredLimit.isMin (h : IsPredLimit (pred a)) : IsMin a := by
  by_contra H
  exact h a (pred_covBy_of_not_isMin H)

theorem not_isPredLimit_pred_of_not_isMin (ha : ¬IsMin a) : ¬IsPredLimit (pred a) := by
  contrapose! ha
  exact ha.isMin

section NoMinOrder

variable [NoMinOrder α]

theorem IsPredLimit.pred_ne (h : IsPredLimit a) (b : α) : pred b ≠ a := by
  rintro rfl
  exact not_isMin _ h.isMin

@[simp]
theorem not_isPredLimit_pred (a : α) : ¬IsPredLimit (pred a) := fun h => h.pred_ne _ rfl

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem IsPredLimit.isMax_of_noMin [NoMinOrder α] (h : IsPredLimit a) : IsMax a :=
  (isPredLimit.dual h).isMin_of_noMax

@[simp]
theorem isPredLimit_iff_of_noMin [NoMinOrder α] : IsPredLimit a ↔ IsMax a :=
  isSuccLimit_toDual_iff.symm.trans isSuccLimit_iff_of_noMax

theorem not_isPredLimit_of_noMin [NoMinOrder α] [NoMaxOrder α] : ¬IsPredLimit a := by simp

end IsPredArchimedean

end Preorder

section PartialOrder

variable [PartialOrder α] [PredOrder α] {a b : α} {C : α → Sort*}

theorem isPredLimit_of_pred_ne (h : ∀ b, pred b ≠ a) : IsPredLimit a := fun b hba =>
  h b (CovBy.pred_eq hba)

theorem not_isPredLimit_iff : ¬IsPredLimit a ↔ ∃ b, ¬IsMin b ∧ pred b = a := by
  rw [← isSuccLimit_toDual_iff]
  exact not_isSuccLimit_iff

/-- See `not_isPredLimit_iff` for a version that states that `a` is a successor of a value other
than itself. -/
theorem mem_range_pred_of_not_isPredLimit (h : ¬IsPredLimit a) : a ∈ range (@pred α _ _) := by
  cases' not_isPredLimit_iff.1 h with b hb
  exact ⟨b, hb.2⟩

theorem mem_range_pred_or_isPredLimit (a) : a ∈ range (@pred α _ _) ∨ IsPredLimit a :=
  or_iff_not_imp_right.2 <| mem_range_pred_of_not_isPredLimit

theorem isPredLimit_of_pred_lt (H : ∀ a > b, pred a < b) : IsPredLimit b := fun a hab =>
  (H a hab.lt).ne (CovBy.pred_eq hab)

theorem IsPredLimit.lt_pred (h : IsPredLimit a) : a < b → a < pred b :=
  (isPredLimit.dual h).succ_lt

theorem IsPredLimit.lt_pred_iff (h : IsPredLimit a) : a < pred b ↔ a < b :=
  (isPredLimit.dual h).succ_lt_iff

theorem isPredLimit_iff_lt_pred : IsPredLimit a ↔ ∀ ⦃b⦄, a < b → a < pred b :=
  isSuccLimit_toDual_iff.symm.trans isSuccLimit_iff_succ_lt

section NoMinOrder

variable [NoMinOrder α]

end NoMinOrder

section IsPredArchimedean

variable [IsPredArchimedean α]

protected theorem IsPredLimit.isMax (h : IsPredLimit a) : IsMax a :=
  (isPredLimit.dual h).isMin

@[simp]
theorem isPredLimit_iff : IsPredLimit a ↔ IsMax a :=
  isSuccLimit_toDual_iff.symm.trans isSuccLimit_iff

theorem not_isPredLimit [NoMaxOrder α] : ¬IsPredLimit a := by simp

end IsPredArchimedean

end PartialOrder

/-! ### Induction principles -/


variable {C : α → Sort*} {b : α}

section isSuccLimitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α]

/-- A value can be built by building it on successors and successor limits. -/
@[elab_as_elim]
noncomputable def isSuccLimitRecOn (b : α) (hs : ∀ a, ¬ IsMax a → C (succ a))
    (hl : ∀ a, IsSuccLimit a → C a) : C b := by
  by_cases hb : IsSuccLimit b
  · exact hl b hb
  · have H := Classical.choose_spec (not_isSuccLimit_iff.1 hb)
    rw [← H.2]
    exact hs _ H.1

theorem isSuccLimitRecOn_limit (hs : ∀ a, ¬ IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    (hb : IsSuccLimit b) : @isSuccLimitRecOn α C _ _ b hs hl = hl b hb :=
  dif_pos hb

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α]

theorem isSuccLimitRecOn_succ' (hs : ∀ a, ¬ IsMax a → C (succ a)) (hl : ∀ a, IsSuccLimit a → C a)
    (hb : ¬ IsMax b) : @isSuccLimitRecOn α C _ _ (succ b) hs hl = hs b hb := by
  have hb' := not_isSuccLimit_succ_of_not_isMax hb
  have H := Classical.choose_spec (not_isSuccLimit_iff.1 hb')
  rw [isSuccLimitRecOn]
  simp only [cast_eq_iff_heq, hb', not_false_iff, eq_mpr_eq_cast, dif_neg]
  congr 1 <;> first |
    exact (succ_eq_succ_iff_of_not_isMax H.left hb).mp H.right |
    exact proof_irrel_heq H.left hb

@[simp]
theorem isSuccLimitRecOn_succ [NoMaxOrder α] (hs : ∀ a, ¬ IsMax a → C (succ a))
    (hl : ∀ a, IsSuccLimit a → C a) (b : α) :
    @isSuccLimitRecOn α C _ _ (succ b) hs hl = hs b (not_isMax b) :=
  isSuccLimitRecOn_succ' _ _ _

end LinearOrder

end isSuccLimitRecOn

section isPredLimitRecOn

section PartialOrder

variable [PartialOrder α] [PredOrder α]

/-- A value can be built by building it on predecessors and predecessor limits. -/
@[elab_as_elim]
noncomputable def isPredLimitRecOn (b : α) (hs : ∀ a, ¬ IsMin a → C (pred a))
    (hl : ∀ a, IsPredLimit a → C a) : C b :=
  @isSuccLimitRecOn αᵒᵈ _ _ _ _ hs fun _ ha => hl _ (isSuccLimit.dual ha)

theorem isPredLimitRecOn_limit (hs : ∀ a, ¬ IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)
    (hb : IsPredLimit b) : @isPredLimitRecOn α C _ _ b hs hl = hl b hb :=
  isSuccLimitRecOn_limit _ _ (isPredLimit.dual hb)

end PartialOrder

section LinearOrder

variable [LinearOrder α] [PredOrder α]
  (hs : ∀ a, ¬ IsMin a → C (pred a)) (hl : ∀ a, IsPredLimit a → C a)

theorem isPredLimitRecOn_pred' {b : α} (hb : ¬ IsMin b) :
    @isPredLimitRecOn α C _ _ (pred b) hs hl = hs b hb :=
  isSuccLimitRecOn_succ' _ _ _

@[simp]
theorem isPredLimitRecOn_pred [NoMinOrder α] (b : α) :
    @isPredLimitRecOn α C _ _ (pred b) hs hl = hs b (not_isMin b) :=
  isSuccLimitRecOn_succ _ _ _

end LinearOrder

end isPredLimitRecOn

end Order

open Order

variable {C : α → Sort*} {b : α}

namespace SuccOrder

section limitRecOn

section PartialOrder

variable [PartialOrder α] [SuccOrder α] [WellFoundedLT α]

open scoped Classical in
/-- Recursion principle on a well-founded partial `SuccOrder`. -/
@[elab_as_elim] noncomputable def limitRecOn (b : α)
    (hs : ∀ a, ¬ IsMax a → C a → C (Order.succ a))
    (hl : ∀ a, IsSuccLimit a → (∀ b < a, C b) → C a) : C b :=
  wellFounded_lt.fix
    (fun a IH ↦ if h : IsSuccLimit a then hl a h IH else
      let x := Classical.indefiniteDescription _ (not_isSuccLimit_iff.mp h)
      x.2.2 ▸ hs x x.2.1 (IH x <| x.2.2.subst <| lt_succ_of_not_isMax x.2.1))
    b

@[simp]
theorem limitRecOn_limit (hs : ∀ a, ¬ IsMax a → C a → C (Order.succ a))
    (hl : ∀ a, IsSuccLimit a → (∀ b < a, C b) → C a) (hb : IsSuccLimit b) :
    limitRecOn b hs hl = hl b hb fun x _ ↦ SuccOrder.limitRecOn x hs hl := by
  rw [SuccOrder.limitRecOn, WellFounded.fix_eq, dif_pos hb]; rfl

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] [WellFoundedLT α]
  (hs : ∀ a, ¬ IsMax a → C a → C (Order.succ a)) (hl : ∀ a, IsSuccLimit a → (∀ b < a, C b) → C a)

@[simp]
theorem limitRecOn_succ (hb : ¬ IsMax b) :
    limitRecOn (Order.succ b) hs hl = hs b hb (limitRecOn b hs hl) := by
  have h := not_isSuccLimit_succ_of_not_isMax hb
  rw [limitRecOn, WellFounded.fix_eq, dif_neg h]
  have {b c hb hc} {x : ∀ a, C a} (h : b = c) :
    congr_arg Order.succ h ▸ hs b hb (x b) = hs c hc (x c) := by subst h; rfl
  let x := Classical.indefiniteDescription _ (not_isSuccLimit_iff.mp h)
  exact this ((succ_eq_succ_iff_of_not_isMax x.2.1 hb).mp x.2.2)

end LinearOrder

end limitRecOn

end SuccOrder

namespace PredOrder

section limitRecOn

section PartialOrder

variable [PartialOrder α] [PredOrder α] [WellFoundedGT α]

/-- Recursion principle on a well-founded partial `PredOrder`. -/
@[elab_as_elim] noncomputable def limitRecOn (b : α)
    (hp : ∀ a, ¬ IsMin a → C a → C (Order.pred a))
    (hl : ∀ a, IsPredLimit a → (∀ b > a, C b) → C a) : C b :=
  SuccOrder.limitRecOn (α := αᵒᵈ) b hp fun a ha => hl a (isSuccLimit.dual ha)

@[simp]
theorem limitRecOn_limit (hp : ∀ a, ¬ IsMin a → C a → C (Order.pred a))
    (hl : ∀ a, IsPredLimit a → (∀ b > a, C b) → C a) (hb : IsPredLimit b) :
    limitRecOn b hp hl = hl b hb fun x _ ↦ limitRecOn x hp hl :=
  SuccOrder.limitRecOn_limit _ _ (isPredLimit.dual hb)

end PartialOrder

section LinearOrder

variable [LinearOrder α] [PredOrder α] [WellFoundedGT α]
  (hp : ∀ a, ¬ IsMin a → C a → C (Order.pred a)) (hl : ∀ a, IsPredLimit a → (∀ b > a, C b) → C a)

@[simp]
theorem limitRecOn_pred (hb : ¬ IsMin b) :
    limitRecOn (Order.pred b) hp hl = hp b hb (limitRecOn b hp hl) :=
  SuccOrder.limitRecOn_succ (α := αᵒᵈ) _ _ hb

end LinearOrder

end limitRecOn

end PredOrder
