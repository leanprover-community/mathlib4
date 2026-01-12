/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Cover
public import Mathlib.Order.Iterate

/-!
# Successor and predecessor

This file defines successor and predecessor orders. `succ a`, the successor of an element `a : α` is
the least element greater than `a`. `pred a` is the greatest element less than `a`. Typical examples
include `ℕ`, `ℤ`, `ℕ+`, `Fin n`, but also `ENat`, the lexicographic order of a successor/predecessor
order...

## Typeclasses

* `SuccOrder`: Order equipped with a sensible successor function.
* `PredOrder`: Order equipped with a sensible predecessor function.

## Implementation notes

Maximal elements don't have a sensible successor. Thus the naïve typeclass
```lean
class NaiveSuccOrder (α : Type*) [Preorder α] where
  (succ : α → α)
  (succ_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
  (lt_succ_iff : ∀ {a b}, a < succ b ↔ a ≤ b)
```
can't apply to an `OrderTop` because plugging in `a = b = ⊤` into either of `succ_le_iff` and
`lt_succ_iff` yields `⊤ < ⊤` (or more generally `m < m` for a maximal element `m`).
The solution taken here is to remove the implications `≤ → <` and instead require that `a < succ a`
for all non-maximal elements (enforced by the combination of `le_succ` and the contrapositive of
`max_of_succ_le`).
The stricter condition of every element having a sensible successor can be obtained through the
combination of `SuccOrder α` and `NoMaxOrder α`.
-/

@[expose] public section

open Function OrderDual Set

variable {α β : Type*}

/-- Order equipped with a sensible successor function. -/
class SuccOrder (α : Type*) [Preorder α] where
  /-- Successor function -/
  succ : α → α
  /-- Proof of basic ordering with respect to `succ` -/
  le_succ : ∀ a, a ≤ succ a
  /-- Proof of interaction between `succ` and maximal element -/
  max_of_succ_le {a} : succ a ≤ a → IsMax a
  /-- Proof that `succ a` is the least element greater than `a` -/
  succ_le_of_lt {a b} : a < b → succ a ≤ b

/-- Order equipped with a sensible predecessor function. -/
@[to_dual (attr := ext)]
class PredOrder (α : Type*) [Preorder α] where
  /-- Predecessor function -/
  pred : α → α
  /-- Proof of basic ordering with respect to `pred` -/
  pred_le : ∀ a, pred a ≤ a
  /-- Proof of interaction between `pred` and minimal element -/
  min_of_le_pred {a} : a ≤ pred a → IsMin a
  /-- Proof that `pred b` is the greatest element less than `b` -/
  le_pred_of_lt {a b} : a < b → a ≤ pred b

attribute [to_dual existing] PredOrder.le_pred_of_lt

instance [Preorder α] [SuccOrder α] : PredOrder αᵒᵈ where
  pred := toDual ∘ SuccOrder.succ ∘ ofDual
  pred_le := by simp [SuccOrder.le_succ]
  min_of_le_pred h := by apply SuccOrder.max_of_succ_le h
  le_pred_of_lt {a b} h := SuccOrder.succ_le_of_lt h

@[to_dual existing]
instance [Preorder α] [PredOrder α] : SuccOrder αᵒᵈ where
  succ := toDual ∘ PredOrder.pred ∘ ofDual
  le_succ := by simp [PredOrder.pred_le]
  max_of_succ_le h := by apply PredOrder.min_of_le_pred h
  succ_le_of_lt {a b} h := PredOrder.le_pred_of_lt h

section Preorder

variable [Preorder α]

/-- A constructor for `SuccOrder α` usable when `α` has no maximal element. -/
def SuccOrder.ofSuccLeIff (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b) :
    SuccOrder α where
  succ := succ
  le_succ _ := (hsucc_le_iff.1 le_rfl).le
  max_of_succ_le ha := (lt_irrefl _ <| hsucc_le_iff.1 ha).elim
  succ_le_of_lt := hsucc_le_iff.2

/-- A constructor for `PredOrder α` usable when `α` has no minimal element. -/
def PredOrder.ofLePredIff (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b) :
    PredOrder α where
  pred := pred
  pred_le _ := (hle_pred_iff.1 le_rfl).le
  min_of_le_pred ha := (lt_irrefl _ <| hle_pred_iff.1 ha).elim
  le_pred_of_lt := hle_pred_iff.2

end Preorder

section LinearOrder

variable [LinearOrder α]

/-- A constructor for `SuccOrder α` for `α` a linear order. -/
@[simps]
def SuccOrder.ofCore (succ : α → α) (hn : ∀ {a}, ¬IsMax a → ∀ b, a < b ↔ succ a ≤ b)
    (hm : ∀ a, IsMax a → succ a = a) : SuccOrder α where
  succ := succ
  succ_le_of_lt {a b} := by_cases (fun h hab ↦ (hm a h).symm ▸ hab.le) fun h ↦ (hn h b).mp
  le_succ a := by_cases (fun h ↦ (hm a h).symm.le) fun h ↦ le_of_lt <| by simpa using (hn h a).not
  max_of_succ_le {a} := not_imp_not.mp fun h ↦ by simpa using (hn h a).not

/-- A constructor for `PredOrder α` for `α` a linear order. -/
@[simps]
def PredOrder.ofCore (pred : α → α)
    (hn : ∀ {a}, ¬IsMin a → ∀ b, b ≤ pred a ↔ b < a) (hm : ∀ a, IsMin a → pred a = a) :
    PredOrder α where
  pred := pred
  le_pred_of_lt {a b} := by_cases (fun h hab ↦ (hm b h).symm ▸ hab.le) fun h ↦ (hn h a).mpr
  pred_le a := by_cases (fun h ↦ (hm a h).le) fun h ↦ le_of_lt <| by simpa using (hn h a).not
  min_of_le_pred {a} := not_imp_not.mp fun h ↦ by simpa using (hn h a).not

variable (α)

open Classical in
/-- A well-order is a `SuccOrder`. -/
noncomputable def SuccOrder.ofLinearWellFoundedLT [WellFoundedLT α] : SuccOrder α :=
  ofCore (fun a ↦ if h : (Ioi a).Nonempty then wellFounded_lt.min _ h else a)
    (fun ha _ ↦ by
      rw [not_isMax_iff] at ha
      simp_rw [Set.Nonempty, mem_Ioi, dif_pos ha]
      exact ⟨(wellFounded_lt.min_le · ha), lt_of_lt_of_le (wellFounded_lt.min_mem _ ha)⟩)
    fun _ ha ↦ dif_neg (not_not_intro ha <| not_isMax_iff.mpr ·)

/-- A linear order with well-founded greater-than relation is a `PredOrder`. -/
@[to_dual existing]
noncomputable def PredOrder.ofLinearWellFoundedGT (α) [LinearOrder α] [WellFoundedGT α] :
    PredOrder α := letI := SuccOrder.ofLinearWellFoundedLT αᵒᵈ; inferInstanceAs (PredOrder αᵒᵈᵒᵈ)

end LinearOrder

/-! ### Successor order -/


namespace Order

section Preorder

variable [Preorder α] [SuccOrder α] {a b : α}

/-- The successor of an element. If `a` is not maximal, then `succ a` is the least element greater
than `a`. If `a` is maximal, then `succ a = a`. -/
@[to_dual /-- The predecessor of an element. If `a` is not minimal, then `pred a` is the greatest
element less than `a`. If `a` is minimal, then `pred a = a`. -/]
def succ : α → α :=
  SuccOrder.succ

@[to_dual pred_le]
theorem le_succ : ∀ a : α, a ≤ succ a :=
  SuccOrder.le_succ

@[to_dual min_of_le_pred]
theorem max_of_succ_le {a : α} : succ a ≤ a → IsMax a :=
  SuccOrder.max_of_succ_le

@[to_dual le_pred_of_lt]
theorem succ_le_of_lt {a b : α} : a < b → succ a ≤ b :=
  SuccOrder.succ_le_of_lt

@[to_dual le_pred]
alias _root_.LT.lt.succ_le := succ_le_of_lt

@[to_dual (attr := simp) le_pred_iff_isMin]
theorem succ_le_iff_isMax : succ a ≤ a ↔ IsMax a :=
  ⟨max_of_succ_le, fun h => h <| le_succ _⟩

alias ⟨_root_.IsMax.of_succ_le, _root_.IsMax.succ_le⟩ := succ_le_iff_isMax

attribute [to_dual of_le_pred] IsMax.of_succ_le
attribute [to_dual le_pred] IsMax.succ_le

@[to_dual (attr := simp) pred_lt_iff_not_isMin]
theorem lt_succ_iff_not_isMax : a < succ a ↔ ¬IsMax a :=
  ⟨not_isMax_of_lt, fun ha => (le_succ a).lt_of_not_ge fun h => ha <| max_of_succ_le h⟩

@[to_dual pred_lt_of_not_isMin]
alias ⟨_, lt_succ_of_not_isMax⟩ := lt_succ_iff_not_isMax

theorem wcovBy_succ (a : α) : a ⩿ succ a :=
  ⟨le_succ a, fun _ hb => (succ_le_of_lt hb).not_gt⟩

theorem covBy_succ_of_not_isMax (h : ¬IsMax a) : a ⋖ succ a :=
  (wcovBy_succ a).covBy_of_lt <| lt_succ_of_not_isMax h

@[to_dual pred_lt_of_le_of_not_isMin]
theorem lt_succ_of_le_of_not_isMax (hab : b ≤ a) (ha : ¬IsMax a) : b < succ a :=
  hab.trans_lt <| lt_succ_of_not_isMax ha

@[to_dual le_pred_iff_of_not_isMin]
theorem succ_le_iff_of_not_isMax (ha : ¬IsMax a) : succ a ≤ b ↔ a < b :=
  ⟨(lt_succ_of_not_isMax ha).trans_le, succ_le_of_lt⟩

@[to_dual]
lemma succ_lt_succ_of_not_isMax (h : a < b) (hb : ¬ IsMax b) : succ a < succ b :=
  lt_succ_of_le_of_not_isMax (succ_le_of_lt h) hb

@[to_dual (attr := simp, mono, gcongr)]
theorem succ_le_succ (h : a ≤ b) : succ a ≤ succ b := by
  by_cases hb : IsMax b
  · by_cases hba : b ≤ a
    · exact (hb <| hba.trans <| le_succ _).trans (le_succ _)
    · exact succ_le_of_lt ((h.lt_of_not_ge hba).trans_le <| le_succ b)
  · rw [succ_le_iff_of_not_isMax fun ha => hb <| ha.mono h]
    apply lt_succ_of_le_of_not_isMax h hb

theorem succ_mono : Monotone (succ : α → α) := fun _ _ => succ_le_succ

/-- See also `Order.succ_eq_of_covBy`. -/
lemma le_succ_of_wcovBy (h : a ⩿ b) : b ≤ succ a := by
  obtain hab | ⟨-, hba⟩ := h.covBy_or_le_and_le
  · by_contra hba
    exact h.2 (lt_succ_of_not_isMax hab.lt.not_isMax) <| hab.lt.succ_le.lt_of_not_ge hba
  · exact hba.trans (le_succ _)

alias _root_.WCovBy.le_succ := le_succ_of_wcovBy

@[to_dual pred_iterate_le]
theorem le_succ_iterate (k : ℕ) (x : α) : x ≤ succ^[k] x :=
  id_le_iterate_of_id_le le_succ _ _

theorem isMax_iterate_succ_of_eq_of_lt {n m : ℕ} (h_eq : succ^[n] a = succ^[m] a)
    (h_lt : n < m) : IsMax (succ^[n] a) := by
  refine max_of_succ_le (le_trans ?_ h_eq.symm.le)
  rw [← iterate_succ_apply' succ]
  have h_le : n + 1 ≤ m := Nat.succ_le_of_lt h_lt
  exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ a) h_le

theorem isMax_iterate_succ_of_eq_of_ne {n m : ℕ} (h_eq : succ^[n] a = succ^[m] a)
    (h_ne : n ≠ m) : IsMax (succ^[n] a) := by
  rcases le_total n m with h | h
  · exact isMax_iterate_succ_of_eq_of_lt h_eq (lt_of_le_of_ne h h_ne)
  · rw [h_eq]
    exact isMax_iterate_succ_of_eq_of_lt h_eq.symm (lt_of_le_of_ne h h_ne.symm)

theorem Iic_subset_Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iic a ⊆ Iio (succ a) :=
  fun _ => (lt_succ_of_le_of_not_isMax · ha)

theorem Ici_succ_of_not_isMax (ha : ¬IsMax a) : Ici (succ a) = Ioi a :=
  Set.ext fun _ => succ_le_iff_of_not_isMax ha

theorem Icc_subset_Ico_succ_right_of_not_isMax (hb : ¬IsMax b) : Icc a b ⊆ Ico a (succ b) := by
  rw [← Ici_inter_Iio, ← Ici_inter_Iic]
  gcongr
  intro _ h
  apply lt_succ_of_le_of_not_isMax h hb

theorem Ioc_subset_Ioo_succ_right_of_not_isMax (hb : ¬IsMax b) : Ioc a b ⊆ Ioo a (succ b) := by
  rw [← Ioi_inter_Iio, ← Ioi_inter_Iic]
  gcongr
  intro _ h
  apply Iic_subset_Iio_succ_of_not_isMax hb h

theorem Icc_succ_left_of_not_isMax (ha : ¬IsMax a) : Icc (succ a) b = Ioc a b := by
  rw [← Ici_inter_Iic, Ici_succ_of_not_isMax ha, Ioi_inter_Iic]

theorem Ico_succ_left_of_not_isMax (ha : ¬IsMax a) : Ico (succ a) b = Ioo a b := by
  rw [← Ici_inter_Iio, Ici_succ_of_not_isMax ha, Ioi_inter_Iio]

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual pred_lt]
theorem lt_succ (a : α) : a < succ a :=
  lt_succ_of_not_isMax <| not_isMax a

@[to_dual (attr := simp) pred_lt_of_le]
theorem lt_succ_of_le : a ≤ b → a < succ b :=
  (lt_succ_of_le_of_not_isMax · <| not_isMax b)

@[to_dual (attr := simp) le_pred_iff]
theorem succ_le_iff : succ a ≤ b ↔ a < b :=
  succ_le_iff_of_not_isMax <| not_isMax a

@[to_dual (attr := gcongr)]
theorem succ_lt_succ (hab : a < b) : succ a < succ b := by simp [hab]

theorem succ_strictMono : StrictMono (succ : α → α) := fun _ _ => succ_lt_succ

theorem covBy_succ (a : α) : a ⋖ succ a :=
  covBy_succ_of_not_isMax <| not_isMax a

theorem Iic_subset_Iio_succ (a : α) : Iic a ⊆ Iio (succ a) := by simp

@[simp]
theorem Ici_succ (a : α) : Ici (succ a) = Ioi a :=
  Ici_succ_of_not_isMax <| not_isMax _

@[simp]
theorem Icc_subset_Ico_succ_right (a b : α) : Icc a b ⊆ Ico a (succ b) :=
  Icc_subset_Ico_succ_right_of_not_isMax <| not_isMax _

@[simp]
theorem Ioc_subset_Ioo_succ_right (a b : α) : Ioc a b ⊆ Ioo a (succ b) :=
  Ioc_subset_Ioo_succ_right_of_not_isMax <| not_isMax _

@[simp]
theorem Icc_succ_left (a b : α) : Icc (succ a) b = Ioc a b :=
  Icc_succ_left_of_not_isMax <| not_isMax _

@[simp]
theorem Ico_succ_left (a b : α) : Ico (succ a) b = Ioo a b :=
  Ico_succ_left_of_not_isMax <| not_isMax _

end NoMaxOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α}

@[to_dual (attr := simp)]
theorem succ_eq_iff_isMax : succ a = a ↔ IsMax a :=
  ⟨fun h => max_of_succ_le h.le, fun h => h.eq_of_ge <| le_succ _⟩

@[to_dual]
alias ⟨_, _root_.IsMax.succ_eq⟩ := succ_eq_iff_isMax

@[to_dual le_iff_eq_or_le_pred']
lemma le_iff_eq_or_succ_le : a ≤ b ↔ a = b ∨ succ a ≤ b := by
  by_cases ha : IsMax a
  · simpa [ha.succ_eq] using le_of_eq
  · rw [succ_le_iff_of_not_isMax ha, le_iff_eq_or_lt]

@[to_dual le_iff_eq_or_le_pred]
lemma le_iff_eq_or_succ_le' : a ≤ b ↔ b = a ∨ succ a ≤ b := by
  rw [eq_comm]
  exact le_iff_eq_or_succ_le

@[to_dual le_and_pred_le_iff]
theorem le_and_le_succ_iff : a ≤ b ∧ b ≤ succ a ↔ b = a ∨ b = succ a := by
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hba : b ≠ a ↦
    h.2.antisymm (succ_le_of_lt <| h.1.lt_of_ne <| hba.symm), ?_⟩
  rintro (rfl | rfl)
  · exact ⟨le_rfl, le_succ b⟩
  · exact ⟨le_succ a, le_rfl⟩

@[to_dual pred_le_and_le_iff]
theorem le_succ_and_le_iff : b ≤ succ a ∧ a ≤ b ↔ b = a ∨ b = succ a := by
  rw [and_comm]
  exact le_and_le_succ_iff

@[deprecated (since := "2025-12-04")]
alias le_le_succ_iff := le_and_le_succ_iff

/-- See also `Order.le_succ_of_wcovBy`. -/
lemma succ_eq_of_covBy (h : a ⋖ b) : succ a = b := (succ_le_of_lt h.lt).antisymm h.wcovBy.le_succ

alias _root_.CovBy.succ_eq := succ_eq_of_covBy

theorem _root_.OrderIso.map_succ [PartialOrder β] [SuccOrder β] (f : α ≃o β) (a : α) :
    f (succ a) = succ (f a) := by
  by_cases h : IsMax a
  · rw [h.succ_eq, (f.isMax_apply.2 h).succ_eq]
  · exact ((apply_covBy_apply_iff f).2 <| covBy_succ_of_not_isMax h).succ_eq.symm

section NoMaxOrder

variable [NoMaxOrder α]

theorem succ_eq_iff_covBy : succ a = b ↔ a ⋖ b :=
  ⟨by rintro rfl; exact covBy_succ _, CovBy.succ_eq⟩

end NoMaxOrder

section OrderTop

variable [OrderTop α]

@[to_dual (attr := simp)]
theorem succ_top : succ (⊤ : α) = ⊤ := by
  rw [succ_eq_iff_isMax, isMax_iff_eq_top]

@[to_dual le_pred_iff_eq_bot]
theorem succ_le_iff_eq_top : succ a ≤ a ↔ a = ⊤ :=
  succ_le_iff_isMax.trans isMax_iff_eq_top

@[to_dual pred_lt_iff_ne_bot]
theorem lt_succ_iff_ne_top : a < succ a ↔ a ≠ ⊤ :=
  lt_succ_iff_not_isMax.trans not_isMax_iff_ne_top

end OrderTop

section OrderBot

variable [OrderBot α] [Nontrivial α]

@[to_dual pred_lt_top]
theorem bot_lt_succ (a : α) : ⊥ < succ a :=
  (lt_succ_of_not_isMax not_isMax_bot).trans_le <| succ_le_succ bot_le

@[to_dual]
theorem succ_ne_bot (a : α) : succ a ≠ ⊥ :=
  (bot_lt_succ a).ne'

end OrderBot

end PartialOrder

section LinearOrder

variable [LinearOrder α] [SuccOrder α] {a b : α}

@[to_dual le_of_pred_lt]
theorem le_of_lt_succ {a b : α} : a < succ b → a ≤ b := fun h ↦ by
  by_contra! nh
  exact (h.trans_le (succ_le_of_lt nh)).false

@[to_dual pred_lt_iff_of_not_isMin]
theorem lt_succ_iff_of_not_isMax (ha : ¬IsMax a) : b < succ a ↔ b ≤ a :=
  ⟨le_of_lt_succ, fun h => h.trans_lt <| lt_succ_of_not_isMax ha⟩

@[to_dual (reorder := ha hb)]
theorem succ_lt_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a < succ b ↔ a < b := by
  rw [lt_succ_iff_of_not_isMax hb, succ_le_iff_of_not_isMax ha]

@[to_dual (reorder := ha hb)]
theorem succ_le_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a ≤ succ b ↔ a ≤ b := by
  rw [succ_le_iff_of_not_isMax ha, lt_succ_iff_of_not_isMax hb]

theorem Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iio (succ a) = Iic a :=
  Set.ext fun _ => lt_succ_iff_of_not_isMax ha

theorem Ico_succ_right_of_not_isMax (hb : ¬IsMax b) : Ico a (succ b) = Icc a b := by
  rw [← Ici_inter_Iio, Iio_succ_of_not_isMax hb, Ici_inter_Iic]

theorem Ioo_succ_right_of_not_isMax (hb : ¬IsMax b) : Ioo a (succ b) = Ioc a b := by
  rw [← Ioi_inter_Iio, Iio_succ_of_not_isMax hb, Ioi_inter_Iic]

@[to_dual]
theorem succ_eq_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a = succ b ↔ a = b := by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, succ_le_succ_iff_of_not_isMax ha hb,
    succ_lt_succ_iff_of_not_isMax ha hb]

@[to_dual pred_le_iff_eq_or_le]
theorem le_succ_iff_eq_or_le : a ≤ succ b ↔ a = succ b ∨ a ≤ b := by
  by_cases hb : IsMax b
  · rw [hb.succ_eq, or_iff_right_of_imp le_of_eq]
  · rw [← lt_succ_iff_of_not_isMax hb, le_iff_eq_or_lt]

@[to_dual pred_lt_iff_eq_or_lt_of_not_isMin]
theorem lt_succ_iff_eq_or_lt_of_not_isMax (hb : ¬IsMax b) : a < succ b ↔ a = b ∨ a < b :=
  (lt_succ_iff_of_not_isMax hb).trans le_iff_eq_or_lt

theorem not_isMin_succ [Nontrivial α] (a : α) : ¬ IsMin (succ a) := by
  obtain ha | ha := (le_succ a).eq_or_lt
  · exact (ha ▸ succ_eq_iff_isMax.1 ha.symm).not_isMin
  · exact not_isMin_of_lt ha

theorem Iic_succ (a : α) : Iic (succ a) = insert (succ a) (Iic a) :=
  ext fun _ => le_succ_iff_eq_or_le

theorem Icc_succ_right (h : a ≤ succ b) : Icc a (succ b) = insert (succ b) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ici.2 h)]

theorem Ioc_succ_right (h : a < succ b) : Ioc a (succ b) = insert (succ b) (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ioi.2 h)]

theorem Iio_succ_eq_insert_of_not_isMax (h : ¬IsMax a) : Iio (succ a) = insert a (Iio a) :=
  ext fun _ => lt_succ_iff_eq_or_lt_of_not_isMax h

theorem Ico_succ_right_eq_insert_of_not_isMax (h₁ : a ≤ b) (h₂ : ¬IsMax b) :
    Ico a (succ b) = insert b (Ico a b) := by
  simp_rw [← Iio_inter_Ici, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ici.2 h₁)]

theorem Ioo_succ_right_eq_insert_of_not_isMax (h₁ : a < b) (h₂ : ¬IsMax b) :
    Ioo a (succ b) = insert b (Ioo a b) := by
  simp_rw [← Iio_inter_Ioi, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ioi.2 h₁)]

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual (attr := simp) pred_lt_iff]
theorem lt_succ_iff : a < succ b ↔ a ≤ b :=
  lt_succ_iff_of_not_isMax <| not_isMax b

@[to_dual] theorem succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b := by simp
@[to_dual] theorem succ_lt_succ_iff : succ a < succ b ↔ a < b := by simp

@[to_dual] alias ⟨le_of_succ_le_succ, _⟩ := succ_le_succ_iff
@[to_dual] alias ⟨lt_of_succ_lt_succ, _⟩ := succ_lt_succ_iff

-- TODO: prove for a succ-archimedean non-linear order with bottom
@[simp]
theorem Iio_succ (a : α) : Iio (succ a) = Iic a :=
  Iio_succ_of_not_isMax <| not_isMax _

@[simp]
theorem Ico_succ_right (a b : α) : Ico a (succ b) = Icc a b :=
  Ico_succ_right_of_not_isMax <| not_isMax _

-- TODO: prove for a succ-archimedean non-linear order
@[simp]
theorem Ioo_succ_right (a b : α) : Ioo a (succ b) = Ioc a b :=
  Ioo_succ_right_of_not_isMax <| not_isMax _

@[to_dual (attr := simp)]
theorem succ_eq_succ_iff : succ a = succ b ↔ a = b :=
  succ_eq_succ_iff_of_not_isMax (not_isMax a) (not_isMax b)

@[to_dual]
theorem succ_injective : Injective (succ : α → α) := fun _ _ => succ_eq_succ_iff.1

@[to_dual]
theorem succ_ne_succ_iff : succ a ≠ succ b ↔ a ≠ b :=
  succ_injective.ne_iff

@[to_dual]
alias ⟨_, succ_ne_succ⟩ := succ_ne_succ_iff

@[to_dual pred_lt_iff_eq_or_gt]
theorem lt_succ_iff_eq_or_lt : a < succ b ↔ a = b ∨ a < b :=
  lt_succ_iff.trans le_iff_eq_or_lt

@[to_dual pred_lt_iff_eq_or_lt]
theorem lt_succ_iff_eq_or_gt : a < succ b ↔ b = a ∨ a < b := by
  rw [eq_comm, lt_succ_iff_eq_or_lt]

theorem Iio_succ_eq_insert (a : α) : Iio (succ a) = insert a (Iio a) :=
  Iio_succ_eq_insert_of_not_isMax <| not_isMax a

theorem Ico_succ_right_eq_insert (h : a ≤ b) : Ico a (succ b) = insert b (Ico a b) :=
  Ico_succ_right_eq_insert_of_not_isMax h <| not_isMax b

theorem Ioo_succ_right_eq_insert (h : a < b) : Ioo a (succ b) = insert b (Ioo a b) :=
  Ioo_succ_right_eq_insert_of_not_isMax h <| not_isMax b

@[simp]
theorem Ioo_eq_empty_iff_le_succ : Ioo a b = ∅ ↔ b ≤ succ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    exact ⟨succ a, lt_succ_iff_not_isMax.mpr (not_isMax a), h⟩
  · ext x
    suffices a < x → b ≤ x by simpa
    exact fun hx ↦ le_of_lt_succ <| lt_of_le_of_lt h <| succ_strictMono hx

end NoMaxOrder

section OrderBot

variable [OrderBot α]

@[to_dual pred_top_lt_iff]
theorem lt_succ_bot_iff [NoMaxOrder α] : a < succ ⊥ ↔ a = ⊥ := by rw [lt_succ_iff, le_bot_iff]

@[to_dual pred_top_le_iff]
theorem le_succ_bot_iff : a ≤ succ ⊥ ↔ a = ⊥ ∨ a = succ ⊥ := by
  rw [le_succ_iff_eq_or_le, le_bot_iff, or_comm]

end OrderBot

end LinearOrder

/-- There is at most one way to define the successors in a `PartialOrder`. -/
instance [PartialOrder α] : Subsingleton (SuccOrder α) :=
  ⟨by
    intro h₀ h₁
    ext a
    by_cases ha : IsMax a
    · exact (@IsMax.succ_eq _ _ h₀ _ ha).trans ha.succ_eq.symm
    · exact @CovBy.succ_eq _ _ h₀ _ _ (covBy_succ_of_not_isMax ha)⟩

theorem succ_eq_sInf [CompleteLattice α] [SuccOrder α] (a : α) :
    succ a = sInf (Set.Ioi a) := by
  apply (le_sInf fun b => succ_le_of_lt).antisymm
  obtain rfl | ha := eq_or_ne a ⊤
  · rw [succ_top]
    exact le_top
  · exact sInf_le (lt_succ_iff_ne_top.2 ha)

theorem succ_eq_iInf [CompleteLattice α] [SuccOrder α] (a : α) : succ a = ⨅ b > a, b := by
  rw [succ_eq_sInf, iInf_subtype', iInf, Subtype.range_coe_subtype, Ioi]

theorem succ_eq_csInf [ConditionallyCompleteLattice α] [SuccOrder α] [NoMaxOrder α] (a : α) :
    succ a = sInf (Set.Ioi a) := by
  apply (le_csInf nonempty_Ioi fun b => succ_le_of_lt).antisymm
  exact csInf_le ⟨a, fun b => le_of_lt⟩ <| lt_succ a

/-! ### Predecessor order -/

section Preorder

variable [Preorder α] [PredOrder α] {a b : α}

-- TODO: auto-generate all of these through `to_dual`

@[to_dual existing wcovBy_succ]
theorem pred_wcovBy (a : α) : pred a ⩿ a :=
  ⟨pred_le a, fun _ hb nh => (le_pred_of_lt nh).not_gt hb⟩

@[to_dual existing covBy_succ_of_not_isMax]
theorem pred_covBy_of_not_isMin (h : ¬IsMin a) : pred a ⋖ a :=
  (pred_wcovBy a).covBy_of_lt <| pred_lt_of_not_isMin h

@[deprecated pred_lt_of_le_of_not_isMin (since := "2025-12-04")]
theorem pred_lt_of_not_isMin_of_le (ha : ¬IsMin a) : a ≤ b → pred a < b :=
  (pred_lt_of_not_isMin ha).trans_le

@[to_dual existing]
theorem pred_mono : Monotone (pred : α → α) := fun _ _ => pred_le_pred

@[deprecated (since := "2025-12-04")]
alias pred_le_pred_of_not_isMin_of_le := pred_mono

/-- See also `Order.pred_eq_of_covBy`. -/
@[to_dual existing le_succ_of_wcovBy]
lemma pred_le_of_wcovBy (h : a ⩿ b) : pred b ≤ a := by
  obtain hab | ⟨-, hba⟩ := h.covBy_or_le_and_le
  · by_contra hba
    exact h.2 (hab.lt.le_pred.lt_of_not_ge hba) (pred_lt_of_not_isMin hab.lt.not_isMin)
  · exact (pred_le _).trans hba

@[to_dual existing le_succ]
alias _root_.WCovBy.pred_le := pred_le_of_wcovBy

theorem isMin_iterate_pred_of_eq_of_lt {n m : ℕ} (h_eq : pred^[n] a = pred^[m] a)
    (h_lt : n < m) : IsMin (pred^[n] a) :=
  @isMax_iterate_succ_of_eq_of_lt αᵒᵈ _ _ _ _ _ h_eq h_lt

theorem isMin_iterate_pred_of_eq_of_ne {n m : ℕ} (h_eq : pred^[n] a = pred^[m] a)
    (h_ne : n ≠ m) : IsMin (pred^[n] a) :=
  @isMax_iterate_succ_of_eq_of_ne αᵒᵈ _ _ _ _ _ h_eq h_ne

theorem Ici_subset_Ioi_pred_of_not_isMin (ha : ¬IsMin a) : Ici a ⊆ Ioi (pred a) :=
  fun _ h ↦ pred_lt_of_le_of_not_isMin h ha

theorem Iic_pred_of_not_isMin (ha : ¬IsMin a) : Iic (pred a) = Iio a :=
  Set.ext fun _ => le_pred_iff_of_not_isMin ha

theorem Icc_subset_Ioc_pred_left_of_not_isMin (ha : ¬IsMin a) : Icc a b ⊆ Ioc (pred a) b := by
  rw [← Ioi_inter_Iic, ← Ici_inter_Iic]
  gcongr
  apply Ici_subset_Ioi_pred_of_not_isMin ha

theorem Ico_subset_Ioo_pred_left_of_not_isMin (ha : ¬IsMin a) : Ico a b ⊆ Ioo (pred a) b := by
  rw [← Ioi_inter_Iio, ← Ici_inter_Iio]
  gcongr
  apply Ici_subset_Ioi_pred_of_not_isMin ha

theorem Icc_pred_right_of_not_isMin (ha : ¬IsMin b) : Icc a (pred b) = Ico a b := by
  rw [← Ici_inter_Iic, Iic_pred_of_not_isMin ha, Ici_inter_Iio]

theorem Ioc_pred_right_of_not_isMin (ha : ¬IsMin b) : Ioc a (pred b) = Ioo a b := by
  rw [← Ioi_inter_Iic, Iic_pred_of_not_isMin ha, Ioi_inter_Iio]

section NoMinOrder

variable [NoMinOrder α]

@[deprecated (since := "2025-12-04")]
alias pred_le_pred_of_le := pred_mono

@[to_dual existing]
theorem pred_strictMono : StrictMono (pred : α → α) := fun _ _ => pred_lt_pred

@[to_dual existing covBy_succ]
theorem pred_covBy (a : α) : pred a ⋖ a :=
  pred_covBy_of_not_isMin <| not_isMin a

theorem Ici_subset_Ioi_pred (a : α) : Ici a ⊆ Ioi (pred a) := by simp

@[simp]
theorem Iic_pred (a : α) : Iic (pred a) = Iio a :=
  Iic_pred_of_not_isMin <| not_isMin a

@[simp]
theorem Icc_subset_Ioc_pred_left (a b : α) : Icc a b ⊆ Ioc (pred a) b :=
  Icc_subset_Ioc_pred_left_of_not_isMin <| not_isMin _

@[simp]
theorem Ico_subset_Ioo_pred_left (a b : α) : Ico a b ⊆ Ioo (pred a) b :=
  Ico_subset_Ioo_pred_left_of_not_isMin <| not_isMin _

@[simp]
theorem Icc_pred_right (a b : α) : Icc a (pred b) = Ico a b :=
  Icc_pred_right_of_not_isMin <| not_isMin _

@[simp]
theorem Ioc_pred_right (a b : α) : Ioc a (pred b) = Ioo a b :=
  Ioc_pred_right_of_not_isMin <| not_isMin _

end NoMinOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [PredOrder α] {a b : α}

@[deprecated le_and_pred_le_iff (since := "2025-12-04")]
alias pred_le_le_iff := pred_le_and_le_iff

/-- See also `Order.pred_le_of_wcovBy`. -/
@[to_dual existing]
lemma pred_eq_of_covBy (h : a ⋖ b) : pred b = a := h.wcovBy.pred_le.antisymm (le_pred_of_lt h.lt)

@[to_dual existing]
alias _root_.CovBy.pred_eq := pred_eq_of_covBy

@[to_dual existing]
theorem _root_.OrderIso.map_pred {β : Type*} [PartialOrder β] [PredOrder β] (f : α ≃o β) (a : α) :
    f (pred a) = pred (f a) :=
  f.dual.map_succ a

section NoMinOrder

variable [NoMinOrder α]

@[to_dual existing]
theorem pred_eq_iff_covBy : pred b = a ↔ a ⋖ b :=
  ⟨by
    rintro rfl
    exact pred_covBy _, CovBy.pred_eq⟩

end NoMinOrder

end PartialOrder

section LinearOrder

variable [LinearOrder α] [PredOrder α] {a b : α}

theorem Ioi_pred_of_not_isMin (ha : ¬IsMin a) : Ioi (pred a) = Ici a :=
  Set.ext fun _ => pred_lt_iff_of_not_isMin ha

theorem Ioc_pred_left_of_not_isMin (ha : ¬IsMin a) : Ioc (pred a) b = Icc a b := by
  rw [← Ioi_inter_Iic, Ioi_pred_of_not_isMin ha, Ici_inter_Iic]

theorem Ioo_pred_left_of_not_isMin (ha : ¬IsMin a) : Ioo (pred a) b = Ico a b := by
  rw [← Ioi_inter_Iio, Ioi_pred_of_not_isMin ha, Ici_inter_Iio]

theorem not_isMax_pred [Nontrivial α] (a : α) : ¬ IsMax (pred a) :=
  not_isMin_succ (α := αᵒᵈ) a

theorem Ici_pred (a : α) : Ici (pred a) = insert (pred a) (Ici a) :=
  ext fun _ => pred_le_iff_eq_or_le

theorem Ioi_pred_eq_insert_of_not_isMin (ha : ¬IsMin a) : Ioi (pred a) = insert a (Ioi a) := by
  simpa using Ioi_pred_of_not_isMin ha

theorem Icc_pred_left (h : pred a ≤ b) : Icc (pred a) b = insert (pred a) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Ici_pred, insert_inter_of_mem (mem_Iic.2 h)]

theorem Ico_pred_left (h : pred a < b) : Ico (pred a) b = insert (pred a) (Ico a b) := by
  simp_rw [← Ici_inter_Iio, Ici_pred, insert_inter_of_mem (mem_Iio.2 h)]

section NoMinOrder

variable [NoMinOrder α]

-- TODO: prove for a pred-archimedean non-linear order with top
@[simp]
theorem Ioi_pred (a : α) : Ioi (pred a) = Ici a :=
  Ioi_pred_of_not_isMin <| not_isMin a

@[simp]
theorem Ioc_pred_left (a b : α) : Ioc (pred a) b = Icc a b :=
  Ioc_pred_left_of_not_isMin <| not_isMin _

-- TODO: prove for a pred-archimedean non-linear order
@[simp]
theorem Ioo_pred_left (a b : α) : Ioo (pred a) b = Ico a b :=
  Ioo_pred_left_of_not_isMin <| not_isMin _

theorem Ioi_pred_eq_insert (a : α) : Ioi (pred a) = insert a (Ioi a) :=
  ext fun _ => pred_lt_iff_eq_or_gt

theorem Ico_pred_right_eq_insert (h : a ≤ b) : Ioc (pred a) b = insert a (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iic.2 h)]

theorem Ioo_pred_right_eq_insert (h : a < b) : Ioo (pred a) b = insert a (Ioo a b) := by
  simp_rw [← Ioi_inter_Iio, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iio.2 h)]

@[simp]
theorem Ioo_eq_empty_iff_pred_le : Ioo a b = ∅ ↔ pred b ≤ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    exact ⟨pred b, h, pred_lt_iff_not_isMin.mpr (not_isMin b)⟩
  · ext x
    suffices a < x → b ≤ x by simpa
    exact fun hx ↦ le_of_pred_lt <| lt_of_le_of_lt h hx

end NoMinOrder

end LinearOrder

/-- There is at most one way to define the predecessors in a `PartialOrder`. -/
@[to_dual existing]
instance [PartialOrder α] : Subsingleton (PredOrder α) :=
  ⟨by
    intro h₀ h₁
    ext a
    by_cases ha : IsMin a
    · exact (@IsMin.pred_eq _ _ h₀ _ ha).trans ha.pred_eq.symm
    · exact @CovBy.pred_eq _ _ h₀ _ _ (pred_covBy_of_not_isMin ha)⟩

theorem pred_eq_sSup [CompleteLattice α] [PredOrder α] :
    ∀ a : α, pred a = sSup (Set.Iio a) :=
  succ_eq_sInf (α := αᵒᵈ)

theorem pred_eq_iSup [CompleteLattice α] [PredOrder α] (a : α) : pred a = ⨆ b < a, b :=
  succ_eq_iInf (α := αᵒᵈ) a

theorem pred_eq_csSup [ConditionallyCompleteLattice α] [PredOrder α] [NoMinOrder α] (a : α) :
    pred a = sSup (Set.Iio a) :=
  succ_eq_csInf (α := αᵒᵈ) a

/-! ### Successor-predecessor orders -/

section SuccPredOrder
section Preorder
variable [Preorder α] [SuccOrder α] [PredOrder α] {a b : α}

@[to_dual pred_succ_le]
lemma le_succ_pred (a : α) : a ≤ succ (pred a) := (pred_wcovBy _).le_succ

@[to_dual le_succ_iff_pred_le]
lemma pred_le_iff_le_succ : pred a ≤ b ↔ a ≤ succ b where
  mp hab := (le_succ_pred _).trans (succ_le_succ hab)
  mpr hab := (pred_le_pred hab).trans (pred_succ_le _)

lemma gc_pred_succ : GaloisConnection (pred : α → α) succ := fun _ _ ↦ pred_le_iff_le_succ

end Preorder

variable [PartialOrder α] [SuccOrder α] [PredOrder α] {a : α}

@[simp]
theorem succ_pred_of_not_isMin (h : ¬IsMin a) : succ (pred a) = a :=
  CovBy.succ_eq (pred_covBy_of_not_isMin h)

@[simp]
theorem pred_succ_of_not_isMax (h : ¬IsMax a) : pred (succ a) = a :=
  CovBy.pred_eq (covBy_succ_of_not_isMax h)

theorem succ_pred [NoMinOrder α] (a : α) : succ (pred a) = a :=
  CovBy.succ_eq (pred_covBy _)

theorem pred_succ [NoMaxOrder α] (a : α) : pred (succ a) = a :=
  CovBy.pred_eq (covBy_succ _)

theorem pred_succ_iterate_of_not_isMax (i : α) (n : ℕ) (hin : ¬IsMax (succ^[n - 1] i)) :
    pred^[n] (succ^[n] i) = i := by
  induction n with
  | zero => simp only [Function.iterate_zero, id]
  | succ n hn =>
    rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at hin
    have h_not_max : ¬IsMax (succ^[n - 1] i) := by
      rcases n with - | n
      · simpa using hin
      rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at hn ⊢
      have h_sub_le : succ^[n] i ≤ succ^[n.succ] i := by
        rw [Function.iterate_succ']
        exact le_succ _
      refine fun h_max => hin fun j hj => ?_
      have hj_le : j ≤ succ^[n] i := h_max (h_sub_le.trans hj)
      exact hj_le.trans h_sub_le
    rw [Function.iterate_succ, Function.iterate_succ']
    simp only [Function.comp_apply]
    rw [pred_succ_of_not_isMax hin]
    exact hn h_not_max

theorem succ_pred_iterate_of_not_isMin (i : α) (n : ℕ) (hin : ¬IsMin (pred^[n - 1] i)) :
    succ^[n] (pred^[n] i) = i :=
  @pred_succ_iterate_of_not_isMax αᵒᵈ _ _ _ i n hin

end SuccPredOrder

end Order

open Order

/-! ### `WithBot`, `WithTop`
Adding a greatest/least element to a `SuccOrder` or to a `PredOrder`.

As far as successors and predecessors are concerned, there are four ways to add a bottom or top
element to an order:
* Adding a `⊤` to an `OrderTop`: Preserves `succ` and `pred`.
* Adding a `⊤` to a `NoMaxOrder`: Preserves `succ`. Never preserves `pred`.
* Adding a `⊥` to an `OrderBot`: Preserves `succ` and `pred`.
* Adding a `⊥` to a `NoMinOrder`: Preserves `pred`. Never preserves `succ`.
  where "preserves `(succ/pred)`" means
  `(Succ/Pred)Order α → (Succ/Pred)Order ((WithTop/WithBot) α)`.
-/

namespace WithTop

/-! #### Adding a `⊤` to an `OrderTop` -/

section Succ

variable [PartialOrder α] [SuccOrder α] [∀ a : α, Decidable (succ a = a)]

instance : SuccOrder (WithTop α) where
  succ a :=
    match a with
    | ⊤ => ⊤
    | Option.some a => ite (succ a = a) ⊤ (some (succ a))
  le_succ a := by
    obtain - | a := a
    · exact le_top
    change _ ≤ ite _ _ _
    split_ifs
    · exact le_top
    · exact coe_le_coe.2 (le_succ a)
  max_of_succ_le {a} ha := by
    cases a
    · exact isMax_top
    dsimp only at ha
    split_ifs at ha with ha'
    · exact (not_top_le_coe _ ha).elim
    · rw [coe_le_coe, succ_le_iff_isMax, ← succ_eq_iff_isMax] at ha
      exact (ha' ha).elim
  succ_le_of_lt {a b} h := by
    cases b
    · exact le_top
    cases a
    · exact (not_top_lt h).elim
    rw [coe_lt_coe] at h
    change ite _ _ _ ≤ _
    split_ifs with ha
    · rw [succ_eq_iff_isMax] at ha
      exact (ha.not_lt h).elim
    · exact coe_le_coe.2 (succ_le_of_lt h)

@[simp]
theorem succ_coe_of_isMax {a : α} (h : IsMax a) : succ ↑a = (⊤ : WithTop α) :=
  dif_pos (succ_eq_iff_isMax.2 h)

theorem succ_coe_of_not_isMax {a : α} (h : ¬ IsMax a) : succ (↑a : WithTop α) = ↑(succ a) :=
  dif_neg (succ_eq_iff_isMax.not.2 h)

@[simp]
theorem succ_coe [NoMaxOrder α] {a : α} : succ (↑a : WithTop α) = ↑(succ a) :=
  succ_coe_of_not_isMax <| not_isMax a

end Succ

section Pred

variable [Preorder α] [OrderTop α] [PredOrder α]

instance : PredOrder (WithTop α) where
  pred a :=
    match a with
    | ⊤ => some ⊤
    | Option.some a => some (pred a)
  pred_le a :=
    match a with
    | ⊤ => le_top
    | Option.some a => coe_le_coe.2 (pred_le a)
  min_of_le_pred {a} ha := by
    cases a
    · exact ((coe_lt_top (⊤ : α)).not_ge ha).elim
    · exact (min_of_le_pred <| coe_le_coe.1 ha).withTop
  le_pred_of_lt {a b} h := by
    cases a
    · exact (le_top.not_gt h).elim
    cases b
    · exact coe_le_coe.2 le_top
    exact coe_le_coe.2 (le_pred_of_lt <| coe_lt_coe.1 h)

/-- Not to be confused with `WithTop.pred_bot`, which is about `WithTop.pred`. -/
@[simp] lemma orderPred_top : pred (⊤ : WithTop α) = ↑(⊤ : α) := rfl

/-- Not to be confused with `WithTop.pred_coe`, which is about `WithTop.pred`. -/
@[simp] lemma orderPred_coe (a : α) : pred (↑a : WithTop α) = ↑(pred a) := rfl

@[simp]
theorem pred_untop :
    ∀ (a : WithTop α) (ha : a ≠ ⊤),
      pred (a.untop ha) = (pred a).untop (by induction a <;> simp)
  | ⊤, ha => (ha rfl).elim
  | (a : α), _ => rfl

end Pred

section Pred

variable [Preorder α] [NoMaxOrder α]

@[to_dual]
instance [hα : Nonempty α] : IsEmpty (PredOrder (WithTop α)) :=
  ⟨by
    intro
    cases h : pred (⊤ : WithTop α) with
    | top => exact hα.elim fun a => (min_of_le_pred h.ge).not_lt <| coe_lt_top a
    | coe a =>
      obtain ⟨c, hc⟩ := exists_gt a
      rw [← coe_lt_coe, ← h] at hc
      exact (le_pred_of_lt (coe_lt_top c)).not_gt hc⟩

end Pred

end WithTop

namespace WithBot

/-! #### Adding a `⊥` to an `OrderBot` -/

section Succ

variable [Preorder α] [OrderBot α] [SuccOrder α]

@[to_dual existing]
instance : SuccOrder (WithBot α) where
  succ a :=
    match a with
    | ⊥ => some ⊥
    | Option.some a => some (succ a)
  le_succ a :=
    match a with
    | ⊥ => bot_le
    | Option.some a => coe_le_coe.2 (le_succ a)
  max_of_succ_le {a} ha := by
    cases a
    · exact ((bot_lt_coe (⊥ : α)).not_ge ha).elim
    · exact (max_of_succ_le <| coe_le_coe.1 ha).withBot
  succ_le_of_lt {a b} h := by
    cases b
    · exact (not_lt_bot h).elim
    cases a
    · exact coe_le_coe.2 bot_le
    · exact coe_le_coe.2 (succ_le_of_lt <| coe_lt_coe.1 h)

/-- Not to be confused with `WithBot.succ_bot`, which is about `WithBot.succ`. -/
@[simp] lemma orderSucc_bot : succ (⊥ : WithBot α) = ↑(⊥ : α) := rfl

/-- Not to be confused with `WithBot.succ_coe`, which is about `WithBot.succ`. -/
@[simp] lemma orderSucc_coe (a : α) : succ (↑a : WithBot α) = ↑(succ a) := rfl

@[simp]
theorem succ_unbot :
    ∀ (a : WithBot α) (ha : a ≠ ⊥),
      succ (a.unbot ha) = (succ a).unbot (by induction a <;> simp)
  | ⊥, ha => (ha rfl).elim
  | (a : α), _ => rfl

end Succ

section Pred

variable [PartialOrder α] [PredOrder α] [∀ a : α, Decidable (pred a = a)]

@[to_dual existing]
instance : PredOrder (WithBot α) where
  pred a :=
    match a with
    | ⊥ => ⊥
    | Option.some a => ite (pred a = a) ⊥ (some (pred a))
  pred_le a := by
    obtain - | a := a
    · exact bot_le
    change ite _ _ _ ≤ _
    split_ifs
    · exact bot_le
    · exact coe_le_coe.2 (pred_le a)
  min_of_le_pred {a} ha := by
    cases a with
    | bot => exact isMin_bot
    | coe a =>
      dsimp only at ha
      split_ifs at ha with ha'
      · exact (not_coe_le_bot _ ha).elim
      · rw [coe_le_coe, le_pred_iff_isMin, ← pred_eq_iff_isMin] at ha
        exact (ha' ha).elim
  le_pred_of_lt {a b} h := by
    cases a
    · exact bot_le
    cases b
    · exact (not_lt_bot h).elim
    rw [coe_lt_coe] at h
    change _ ≤ ite _ _ _
    split_ifs with hb
    · rw [pred_eq_iff_isMin] at hb
      exact (hb.not_lt h).elim
    · exact coe_le_coe.2 (le_pred_of_lt h)

@[simp]
theorem pred_coe_of_isMin {a : α} (h : IsMin a) : pred ↑a = (⊥ : WithBot α) :=
  dif_pos (pred_eq_iff_isMin.2 h)

theorem pred_coe_of_not_isMin {a : α} (h : ¬ IsMin a) : pred (↑a : WithBot α) = ↑(pred a) :=
  dif_neg (pred_eq_iff_isMin.not.2 h)

theorem pred_coe [NoMinOrder α] {a : α} : pred (↑a : WithBot α) = ↑(pred a) :=
  pred_coe_of_not_isMin <| not_isMin a

end Pred

end WithBot

section OrderIso

variable {X Y : Type*} [Preorder X] [Preorder Y]

-- See note [reducible non-instances]
/-- `SuccOrder` transfers across equivalences between orders. -/
protected abbrev SuccOrder.ofOrderIso [SuccOrder X] (f : X ≃o Y) : SuccOrder Y where
  succ y := f (succ (f.symm y))
  le_succ y := by rw [← map_inv_le_iff f]; exact le_succ (f.symm y)
  max_of_succ_le h := by
    rw [← f.symm.isMax_apply]
    refine max_of_succ_le ?_
    simp [f.le_symm_apply, h]
  succ_le_of_lt h := by rw [← le_map_inv_iff]; exact succ_le_of_lt (by simp [h])

-- See note [reducible non-instances]
/-- `PredOrder` transfers across equivalences between orders. -/
protected abbrev PredOrder.ofOrderIso [PredOrder X] (f : X ≃o Y) :
    PredOrder Y where
  pred y := f (pred (f.symm y))
  pred_le y := by rw [← le_map_inv_iff f]; exact pred_le (f.symm y)
  min_of_le_pred h := by
    rw [← f.symm.isMin_apply]
    refine min_of_le_pred ?_
    simp [f.symm_apply_le, h]
  le_pred_of_lt h := by rw [← map_inv_le_iff]; exact le_pred_of_lt (by simp [h])

end OrderIso

section OrdConnected

variable {α : Type*} [PartialOrder α] {s : Set α} [s.OrdConnected]

open scoped Classical in
noncomputable instance Set.OrdConnected.predOrder [PredOrder α] :
    PredOrder s where
  pred x := if h : Order.pred x.1 ∈ s then ⟨Order.pred x.1, h⟩ else x
  pred_le := fun ⟨x, hx⟩ ↦ by dsimp; split <;> simp_all [Order.pred_le]
  min_of_le_pred := @fun ⟨x, hx⟩ h ↦ by
    dsimp at h
    split_ifs at h with h'
    · simp only [Subtype.mk_le_mk, Order.le_pred_iff_isMin] at h
      rintro ⟨y, _⟩ hy
      simp [h hy]
    · rintro ⟨y, hy⟩ h
      rcases h.lt_or_eq with h | h
      · simp only [Subtype.mk_lt_mk] at h
        have := h.le_pred
        absurd h'
        apply out' hy hx
        simp [this, Order.pred_le]
      · simp [h]
  le_pred_of_lt := @fun ⟨b, hb⟩ ⟨c, hc⟩ h ↦ by
    rw [Subtype.mk_lt_mk] at h
    dsimp only
    split
    · exact h.le_pred
    · exact h.le

@[simp, norm_cast]
lemma coe_pred_of_mem [PredOrder α] {a : s} (h : pred a.1 ∈ s) :
    (pred a).1 = pred ↑a := by classical
  change Subtype.val (dite ..) = _
  simp [h]

lemma isMin_of_pred_notMem [PredOrder α] {a : s} (h : pred ↑a ∉ s) : IsMin a := by classical
  rw [← pred_eq_iff_isMin]
  change dite .. = _
  simp [h]

lemma pred_notMem_iff_isMin [PredOrder α] [NoMinOrder α] {a : s} :
    pred ↑a ∉ s ↔ IsMin a where
  mp := isMin_of_pred_notMem
  mpr h nh := by
    replace h := congr($h.pred_eq.1)
    rw [coe_pred_of_mem nh] at h
    simp at h

noncomputable instance Set.OrdConnected.succOrder [SuccOrder α] :
    SuccOrder s :=
  letI : PredOrder sᵒᵈ := inferInstanceAs (PredOrder (OrderDual.ofDual ⁻¹' s))
  inferInstanceAs (SuccOrder sᵒᵈᵒᵈ)

@[simp, norm_cast]
lemma coe_succ_of_mem [SuccOrder α] {a : s} (h : succ ↑a ∈ s) :
    (succ a).1 = succ ↑a := by classical
  change Subtype.val (dite ..) = _
  split_ifs <;> trivial

lemma isMax_of_succ_notMem [SuccOrder α] {a : s} (h : succ ↑a ∉ s) : IsMax a := by
  classical
  rw [← succ_eq_iff_isMax]
  change dite .. = _
  split_ifs <;> trivial

lemma succ_notMem_iff_isMax [SuccOrder α] [NoMaxOrder α] {a : s} :
    succ ↑a ∉ s ↔ IsMax a where
  mp := isMax_of_succ_notMem
  mpr h nh := by
    replace h := congr($h.succ_eq.1)
    rw [coe_succ_of_mem nh] at h
    simp at h

end OrdConnected
