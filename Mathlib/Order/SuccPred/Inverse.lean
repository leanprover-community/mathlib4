/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.SuccPred.Basic

/-!
# "Predecessor" from successor

For a `SuccOrder`, we define `pred' a` as some non-maximal element `b` with `succ b = a` if it
exists, and `pred' a = a` otherwise. In a successor-predecessor partial order, `pred'` and `pred`
coincide, but in general, `pred'` need not form a valid `PredOrder`.

`pred'` is most nicely behaved in a linear order with no maximum, where it forms a Galois
connection with `succ`.

We also dually define `succ'` for a `PredOrder`.
-/

namespace Order

open Set OrderDual

variable {α : Type*}

/-! ### Predecessor from successor -/


open Classical in
/-- A predecessor-like operation defined in a succesor order.

If `a` is the succesor of some non-maximal `b`, `pred' a` returns an arbitrary such `b`. Otherwise,
`pred' a = a`. -/
noncomputable def pred' [Preorder α] [SuccOrder α] (a : α) : α :=
  if h : ∃ b, ¬ IsMax b ∧ succ b = a then Classical.choose h else a

section Preorder

variable [Preorder α] [SuccOrder α] {a b : α}

theorem pred'_ne_self_iff' : pred' a ≠ a ↔ ∃ b, ¬ IsMax b ∧ succ b = a := by
  constructor <;>
  intro H
  · by_contra ha
    rw [pred', dif_neg ha] at H
    exact H.irrefl
  · rw [pred', dif_pos H]
    obtain ⟨hb, hb'⟩ := Classical.choose_spec H
    conv_rhs => rw [← hb']
    exact (lt_succ_of_not_isMax hb).ne

theorem pred'_eq_self_iff' : pred' a = a ↔ ∀ b, succ b = a → IsMax b := by
  simp_rw [← not_ne_iff, pred'_ne_self_iff', not_exists, not_and', not_not]

/-- See `pred'_eq_self_iff'` for the most general version. -/
theorem pred'_eq_self (ha : a ∉ range succ) : pred' a = a :=
  pred'_eq_self_iff'.2 fun b h => (ha ⟨b, h⟩).elim

theorem not_isMax_pred'_succ (ha : ¬ IsMax a) : ¬ IsMax (pred' (succ a)) := by
  have H : ∃ b, ¬ IsMax b ∧ succ b = succ a := ⟨_, ha, rfl⟩
  rw [pred', dif_pos H]
  exact (Classical.choose_spec H).1

@[simp]
theorem succ_pred'_succ_of_not_isMax (ha : ¬ IsMax a) : succ (pred' (succ a)) = succ a := by
  have H : ∃ b, ¬ IsMax b ∧ succ b = succ a := ⟨_, ha, rfl⟩
  rw [pred', dif_pos H]
  exact (Classical.choose_spec H).2

theorem pred'_le_self (a : α) : pred' a ≤ a := by
  by_cases H : ∃ b, ¬ IsMax b ∧ succ b = a
  · obtain ⟨b, hb, rfl⟩ := H
    apply (le_succ _).trans
    rw [succ_pred'_succ_of_not_isMax hb]
  · rw [pred', dif_neg H]

theorem succ_pred'_eq_self_iff_of_not_isMax (ha : ¬ IsMax a) :
    succ (pred' a) = a ↔ a ∈ range succ := by
  refine ⟨fun h ↦ ⟨_, h⟩, ?_⟩
  rintro ⟨b, rfl⟩
  rw [succ_pred'_succ_of_not_isMax]
  obtain ⟨c, hc⟩ := not_isMax_iff.1 ha
  exact ((le_succ b).trans_lt hc).not_isMax

theorem pred'_wcovBy (a : α) : pred' a ⩿ a := by
  by_cases H : ∃ b, ¬ IsMax b ∧ succ b = a
  · obtain ⟨b, hb, rfl⟩ := H
    conv_rhs => rw [← succ_pred'_succ_of_not_isMax hb]
    exact wcovBy_succ _
  · rw [pred', dif_neg H]

section NoMaxOrder

variable [NoMaxOrder α]

theorem pred'_ne_self_iff : pred' a ≠ a ↔ a ∈ range succ := by
  simp [pred'_ne_self_iff']

theorem pred'_eq_self_iff : pred' a = a ↔ a ∉ range succ := by
  rw [← not_iff_not, not_not_mem, ← pred'_ne_self_iff]

theorem succ_pred'_succ : succ (pred' (succ a)) = succ a :=
  succ_pred'_succ_of_not_isMax (not_isMax a)

theorem succ_pred'_eq_self_iff : succ (pred' a) = a ↔ a ∈ range succ :=
  succ_pred'_eq_self_iff_of_not_isMax (not_isMax a)

end NoMaxOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a : α}

theorem _root_.IsMin.pred'_eq (ha : IsMin a) : pred' a = a :=
  ha.eq_of_le (pred'_le_self a)

@[simp]
theorem pred'_bot [OrderBot α] : pred' (⊥ : α) = ⊥ :=
  isMin_bot.pred'_eq

section NoMaxOrder

variable [NoMaxOrder α]

theorem pred'_lt_self_iff : pred' a < a ↔ a ∈ range succ := by
  rw [(pred'_le_self a).lt_iff_ne, pred'_ne_self_iff]

end NoMaxOrder

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] {a b : α}

@[simp]
theorem pred'_succ_of_not_isMax (ha : ¬ IsMax a) : pred' (succ a) = a := by
  rw [← succ_eq_succ_iff_of_not_isMax (not_isMax_pred'_succ ha) ha, succ_pred'_succ_of_not_isMax ha]

@[simp]
theorem lt_pred'_iff_succ_lt_of_not_isMax (ha : ¬ IsMax a) (hb : ¬ IsMax b) :
    a < pred' b ↔ succ a < b := by
  by_cases H : ∃ c, ¬ IsMax c ∧ succ c = b
  · obtain ⟨c, hc, rfl⟩ := H
    rw [pred'_succ_of_not_isMax hc, succ_lt_succ_iff_of_not_isMax ha hc]
  · rw [pred', dif_neg H]
    constructor <;>
    intro h
    · rw [← succ_le_iff_of_not_isMax ha] at h
      exact h.lt_of_ne fun hb ↦ H ⟨a, ha, hb⟩
    · exact (le_succ a).trans_lt h

@[simp]
theorem pred'_le_iff_le_succ_of_not_isMax (ha : ¬ IsMax a) (hb : ¬ IsMax b) :
    pred' a ≤ b ↔ a ≤ succ b :=
  le_iff_le_iff_lt_iff_lt.2 (lt_pred'_iff_succ_lt_of_not_isMax hb ha)

theorem pred'_mono : Monotone (pred' : α → α) := by
  intro a b h
  by_cases ha : IsMax a
  · obtain rfl := ha.eq_of_le h
    rfl
  · by_cases H : ∃ c, ¬ IsMax c ∧ succ c = b
    · obtain ⟨c, hc, rfl⟩ := H
      rwa [pred'_succ_of_not_isMax hc, pred'_le_iff_le_succ_of_not_isMax ha hc]
    · conv_rhs => rw [pred', dif_neg H]
      exact (pred'_le_self a).trans h

section NoMaxOrder

variable [NoMaxOrder α]

theorem pred'_succ (a : α) : pred' (succ a) = a :=
  pred'_succ_of_not_isMax (not_isMax a)

theorem lt_pred'_iff_succ_lt : a < pred' b ↔ succ a < b :=
  lt_pred'_iff_succ_lt_of_not_isMax (not_isMax a) (not_isMax b)

theorem pred'_le_iff_le_succ : pred' a ≤ b ↔ a ≤ succ b :=
  pred'_le_iff_le_succ_of_not_isMax (not_isMax a) (not_isMax b)

theorem gc_pred'_succ : GaloisConnection (pred' : α → α) succ := fun _ _ ↦ pred'_le_iff_le_succ

end NoMaxOrder

end LinearOrder

/-! ### Successor from predecessor -/


open Classical in
/-- A successor-like operation defined in a predecessor order.

If `a` is the predecessor of some non-minimal `b`, `succ' a` returns an arbitrary such `b`.
Otherwise, `succ' a = a`. -/
noncomputable def succ' [Preorder α] [PredOrder α] (a : α) : α :=
  pred' (α := αᵒᵈ) (toDual a)

section Preorder

variable [Preorder α] [PredOrder α] {a b : α}

theorem succ'_ne_self_iff' : succ' a ≠ a ↔ ∃ b, ¬ IsMin b ∧ pred b = a :=
  pred'_ne_self_iff' (α := αᵒᵈ)

theorem succ'_eq_self_iff' : succ' a = a ↔ ∀ b, pred b = a → IsMin b :=
  pred'_eq_self_iff' (α := αᵒᵈ)

/-- See `succ'_eq_self_iff'` for the most general version. -/
theorem succ'_eq_self (ha : a ∉ range pred) : succ' a = a :=
  pred'_eq_self (α := αᵒᵈ) ha

theorem not_isMin_succ'_pred (ha : ¬ IsMin a) : ¬ IsMin (succ' (pred a)) :=
  not_isMax_pred'_succ (α := αᵒᵈ) ha

@[simp]
theorem pred_succ'_pred_of_not_isMin (ha : ¬ IsMin a) : pred (succ' (pred a)) = pred a :=
  succ_pred'_succ_of_not_isMax (α := αᵒᵈ) ha

theorem self_le_succ' (a : α) : a ≤ succ' a :=
  pred'_le_self (α := αᵒᵈ) _

theorem pred_succ'_eq_self_iff_of_not_isMin (ha : ¬ IsMin a) :
    pred (succ' a) = a ↔ a ∈ range pred :=
  succ_pred'_eq_self_iff_of_not_isMax (α := αᵒᵈ) ha

theorem wcovBy_succ' (a : α) : a ⩿ succ' a :=
  (pred'_wcovBy (toDual a)).ofDual

section NoMinOrder

variable [NoMinOrder α]

theorem succ'_ne_self_iff : succ' a ≠ a ↔ a ∈ range pred :=
  pred'_ne_self_iff (α := αᵒᵈ)

theorem succ'_eq_self_iff : succ' a = a ↔ a ∉ range pred :=
  pred'_eq_self_iff (α := αᵒᵈ)

theorem pred_succ'_pred : pred (succ' (pred a)) = pred a :=
  succ_pred'_succ (α := αᵒᵈ)

theorem pred_succ'_eq_self_iff : pred (succ' a) = a ↔ a ∈ range pred :=
  succ_pred'_eq_self_iff (α := αᵒᵈ)

end NoMinOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [PredOrder α] {a : α}

theorem _root_.IsMax.succ'_eq (ha : IsMax a) : succ' a = a :=
  ha.toDual.pred'_eq

@[simp]
theorem succ'_top [OrderTop α] : succ' (⊤ : α) = ⊤ :=
  isMax_top.succ'_eq

section NoMinOrder

variable [NoMinOrder α]

theorem self_lt_succ'_iff : a < succ' a ↔ a ∈ range pred :=
  pred'_lt_self_iff (α := αᵒᵈ)

end NoMinOrder

end PartialOrder

section LinearOrder

variable [LinearOrder α] [PredOrder α] {a b : α}

@[simp]
theorem succ'_pred_of_not_isMin (ha : ¬ IsMin a) : succ' (pred a) = a :=
  pred'_succ_of_not_isMax (α := αᵒᵈ) ha

@[simp]
theorem succ'_lt_iff_lt_pred_of_not_isMin (ha : ¬ IsMin a) (hb : ¬ IsMin b) :
    succ' a < b ↔ a < pred b :=
  lt_pred'_iff_succ_lt_of_not_isMax (α := αᵒᵈ) hb ha

@[simp]
theorem le_succ'_iff_pred_le_of_not_isMin (ha : ¬ IsMin a) (hb : ¬ IsMin b) :
    a ≤ succ' b ↔ pred a ≤ b :=
  pred'_le_iff_le_succ_of_not_isMax (α := αᵒᵈ) hb ha

theorem succ'_mono : Monotone (succ' : α → α) :=
  fun _ _ h ↦ pred'_mono (α := αᵒᵈ) h

section NoMinOrder

variable [NoMinOrder α]

theorem succ'_pred (a : α) : succ' (pred a) = a :=
  pred'_succ (α := αᵒᵈ) a

theorem succ'_lt_iff_lt_pred : succ' a < b ↔ a < pred b :=
  lt_pred'_iff_succ_lt (α := αᵒᵈ)

theorem le_succ'_iff_pred_le : a ≤ succ' b ↔ pred a ≤ b :=
  pred'_le_iff_le_succ (α := αᵒᵈ)

theorem gc_pred_succ' : GaloisConnection (pred : α → α) succ' := fun _ _ ↦ le_succ'_iff_pred_le.symm

end NoMinOrder

end LinearOrder

/-! ### Successor-predecessor orders -/


section SuccPredOrder

variable [PartialOrder α] [SuccOrder α] [PredOrder α]

@[simp]
theorem pred'_eq_pred : pred' = (pred : α → α) := by
  ext a
  obtain ha | ha := (pred'_wcovBy a).covBy_or_eq
  · rw [ha.pred_eq]
  · by_cases ha' : IsMin a
    · rw [ha'.pred_eq, ha'.pred'_eq]
    · rw [pred'_eq_self_iff'] at ha
      rwa [(ha (pred a) (succ_pred_of_not_isMin ha')).eq_of_le (pred_le a), pred'_eq_self_iff']

theorem pred'_eq_pred_apply (a : α) : pred' a = pred a := by
  rw [pred'_eq_pred]

@[simp]
theorem succ'_eq_succ : succ' = (succ : α → α) :=
  pred'_eq_pred (α := αᵒᵈ)

theorem succ'_eq_succ_apply (a : α) : succ' a = succ a := by
  rw [succ'_eq_succ]

end SuccPredOrder

end Order
