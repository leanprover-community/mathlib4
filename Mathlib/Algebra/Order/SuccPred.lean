/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Yaël Dillies
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Order.SuccPred.Limit
import Mathlib.Order.SuccPred.WithBot

/-!
# Interaction between successors and arithmetic

We define the `SuccAddOrder` and `PredSubOrder` typeclasses, for orders satisfying `succ x = x + 1`
and `pred x = x - 1` respectively. This allows us to transfer the API for successors and
predecessors into these common arithmetical forms.

## Todo

In the future, we will make `x + 1` and `x - 1` the `simp`-normal forms for `succ x` and `pred x`
respectively. This will require a refactor of `Ordinal` first, as the `simp`-normal form is
currently set the other way around.
-/

/-- A typeclass for `succ x = x + 1`. -/
class SuccAddOrder (α : Type*) [Preorder α] [Add α] [One α] extends SuccOrder α where
  succ_eq_add_one (x : α) : succ x = x + 1

/-- A typeclass for `pred x = x - 1`. -/
class PredSubOrder (α : Type*) [Preorder α] [Sub α] [One α] extends PredOrder α where
  pred_eq_sub_one (x : α) : pred x = x - 1

variable {α : Type*} {x y : α}

namespace Order

section Preorder

variable [Preorder α]

section Add

variable [Add α] [One α] [SuccAddOrder α]

theorem succ_eq_add_one (x : α) : succ x = x + 1 :=
  SuccAddOrder.succ_eq_add_one x

theorem add_one_le_of_lt (h : x < y) : x + 1 ≤ y := by
  rw [← succ_eq_add_one]
  exact succ_le_of_lt h

theorem add_one_le_iff_of_not_isMax (hx : ¬ IsMax x) : x + 1 ≤ y ↔ x < y := by
  rw [← succ_eq_add_one, succ_le_iff_of_not_isMax hx]

theorem add_one_le_iff [NoMaxOrder α] : x + 1 ≤ y ↔ x < y :=
  add_one_le_iff_of_not_isMax (not_isMax x)

@[simp]
theorem wcovBy_add_one (x : α) : x ⩿ x + 1 := by
  rw [← succ_eq_add_one]
  exact wcovBy_succ x

@[simp]
theorem covBy_add_one [NoMaxOrder α] (x : α) : x ⋖ x + 1 := by
  rw [← succ_eq_add_one]
  exact covBy_succ x

end Add

section Sub

variable [Sub α] [One α] [PredSubOrder α]

theorem pred_eq_sub_one (x : α) : pred x = x - 1 :=
  PredSubOrder.pred_eq_sub_one x

theorem le_sub_one_of_lt (h : x < y) : x ≤ y - 1 := by
  rw [← pred_eq_sub_one]
  exact le_pred_of_lt h

theorem le_sub_one_iff_of_not_isMin (hy : ¬ IsMin y) : x ≤ y - 1 ↔ x < y := by
  rw [← pred_eq_sub_one, le_pred_iff_of_not_isMin hy]

theorem le_sub_one_iff [NoMinOrder α] : x ≤ y - 1 ↔ x < y :=
  le_sub_one_iff_of_not_isMin (not_isMin y)

@[simp]
theorem sub_one_wcovBy (x : α) : x - 1 ⩿ x := by
  rw [← pred_eq_sub_one]
  exact pred_wcovBy x

@[simp]
theorem sub_one_covBy [NoMinOrder α] (x : α) : x - 1 ⋖ x := by
  rw [← pred_eq_sub_one]
  exact pred_covBy x

end Sub

@[simp]
theorem succ_iterate [AddMonoidWithOne α] [SuccAddOrder α] (x : α) (n : ℕ) :
    succ^[n] x = x + n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, add_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply', IH, Nat.cast_add, succ_eq_add_one, Nat.cast_one, add_assoc]

@[simp]
theorem pred_iterate [AddCommGroupWithOne α] [PredSubOrder α] (x : α) (n : ℕ) :
    pred^[n] x = x - n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, sub_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply', IH, Nat.cast_add, pred_eq_sub_one, Nat.cast_one, sub_sub]

end Preorder

section PartialOrder

variable [PartialOrder α]

theorem not_isMax_zero [Zero α] [One α] [ZeroLEOneClass α] [NeZero (1 : α)] : ¬ IsMax (0 : α) := by
  rw [not_isMax_iff]
  exact ⟨1, one_pos⟩

theorem one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] : 1 ≤ x ↔ 0 < x := by
  rw [← succ_le_iff_of_not_isMax not_isMax_zero, succ_eq_add_one, zero_add]

theorem covBy_iff_add_one_eq [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    x ⋖ y ↔ x + 1 = y := by
  rw [← succ_eq_add_one]
  exact succ_eq_iff_covBy.symm

theorem covBy_iff_sub_one_eq [Sub α] [One α] [PredSubOrder α] [NoMinOrder α] :
    x ⋖ y ↔ y - 1 = x := by
  rw [← pred_eq_sub_one]
  exact pred_eq_iff_covBy.symm

theorem IsSuccPrelimit.add_one_lt [Add α] [One α] [SuccAddOrder α]
    (hx : IsSuccPrelimit x) (hy : y < x) : y + 1 < x := by
  rw [← succ_eq_add_one]
  exact hx.succ_lt hy

theorem IsPredPrelimit.lt_sub_one [Sub α] [One α] [PredSubOrder α]
    (hx : IsPredPrelimit x) (hy : x < y) : x < y - 1 := by
  rw [← pred_eq_sub_one]
  exact hx.lt_pred hy

theorem IsSuccLimit.add_one_lt [Add α] [One α] [SuccAddOrder α]
    (hx : IsSuccLimit x) (hy : y < x) : y + 1 < x :=
  hx.isSuccPrelimit.add_one_lt hy

theorem IsPredLimit.lt_sub_one [Sub α] [One α] [PredSubOrder α]
    (hx : IsPredLimit x) (hy : x < y) : x < y - 1 :=
  hx.isPredPrelimit.lt_sub_one hy

theorem IsSuccPrelimit.add_natCast_lt [AddMonoidWithOne α] [SuccAddOrder α]
    (hx : IsSuccPrelimit x) (hy : y < x) : ∀ n : ℕ, y + n < x
  | 0 => by simpa
  | n + 1 => by
    rw [Nat.cast_add_one, ← add_assoc]
    exact hx.add_one_lt (hx.add_natCast_lt hy n)

theorem IsPredPrelimit.lt_sub_natCast [AddCommGroupWithOne α] [PredSubOrder α]
    (hx : IsPredPrelimit x) (hy : x < y) : ∀ n : ℕ, x < y - n
  | 0 => by simpa
  | n + 1 => by
    rw [Nat.cast_add_one, ← sub_sub]
    exact hx.lt_sub_one (hx.lt_sub_natCast hy n)

theorem IsSuccLimit.add_natCast_lt [AddMonoidWithOne α] [SuccAddOrder α]
    (hx : IsSuccLimit x) (hy : y < x) : ∀ n : ℕ, y + n < x :=
  hx.isSuccPrelimit.add_natCast_lt hy

theorem IsPredLimit.lt_sub_natCast [AddCommGroupWithOne α] [PredSubOrder α]
    (hx : IsPredLimit x) (hy : x < y) : ∀ n : ℕ, x < y - n :=
  hx.isPredPrelimit.lt_sub_natCast hy

theorem IsSuccLimit.natCast_lt [AddMonoidWithOne α] [SuccAddOrder α]
    [OrderBot α] [CanonicallyOrderedAdd α]
    (hx : IsSuccLimit x) : ∀ n : ℕ, n < x := by
  simpa [bot_eq_zero] using hx.add_natCast_lt hx.bot_lt

theorem not_isSuccLimit_natCast [AddMonoidWithOne α] [SuccAddOrder α]
    [OrderBot α] [CanonicallyOrderedAdd α]
    (n : ℕ) : ¬ IsSuccLimit (n : α) :=
  fun h ↦ (h.natCast_lt n).false

@[simp]
theorem succ_eq_zero [AddZeroClass α] [OrderBot α] [CanonicallyOrderedAdd α] [One α] [NoMaxOrder α]
    [SuccAddOrder α] {a : WithBot α} : WithBot.succ a = 0 ↔ a = ⊥ := by
  cases a
  · simp [bot_eq_zero]
  · rename_i a
    simp only [WithBot.succ_coe, WithBot.coe_ne_bot, iff_false]
    by_contra h
    simpa [h] using max_of_succ_le (a := a)

end PartialOrder

section LinearOrder

variable [LinearOrder α]

section Add

variable [Add α] [One α] [SuccAddOrder α]

theorem le_of_lt_add_one (h : x < y + 1) : x ≤ y := by
  rw [← succ_eq_add_one] at h
  exact le_of_lt_succ h

theorem lt_add_one_iff_of_not_isMax (hy : ¬ IsMax y) : x < y + 1 ↔ x ≤ y := by
  rw [← succ_eq_add_one, lt_succ_iff_of_not_isMax hy]

theorem lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x ≤ y :=
  lt_add_one_iff_of_not_isMax (not_isMax y)

end Add

section Sub

variable [Sub α] [One α] [PredSubOrder α]

theorem le_of_sub_one_lt (h : x - 1 < y) : x ≤ y := by
  rw [← pred_eq_sub_one] at h
  exact le_of_pred_lt h

theorem sub_one_lt_iff_of_not_isMin (hx : ¬ IsMin x) : x - 1 < y ↔ x ≤ y := by
  rw [← pred_eq_sub_one, pred_lt_iff_of_not_isMin hx]

theorem sub_one_lt_iff [NoMinOrder α] : x - 1 < y ↔ x ≤ y :=
  sub_one_lt_iff_of_not_isMin (not_isMin x)

end Sub

theorem lt_one_iff_nonpos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] : x < 1 ↔ x ≤ 0 := by
  rw [← lt_succ_iff_of_not_isMax not_isMax_zero, succ_eq_add_one, zero_add]

end LinearOrder

end Order

section Monotone
variable {α β : Type*} [PartialOrder α] [Preorder β]

section SuccAddOrder
variable [Add α] [One α] [SuccAddOrder α] [IsSuccArchimedean α] {s : Set α} {f : α → β}

lemma monotoneOn_of_le_add_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMax a → a ∈ s → a + 1 ∈ s → f a ≤ f (a + 1)) → MonotoneOn f s := by
  simpa [Order.succ_eq_add_one] using monotoneOn_of_le_succ hs (f := f)

lemma antitoneOn_of_add_one_le (hs : s.OrdConnected) :
    (∀ a, ¬ IsMax a → a ∈ s → a + 1 ∈ s → f (a + 1) ≤ f a) → AntitoneOn f s := by
  simpa [Order.succ_eq_add_one] using antitoneOn_of_succ_le hs (f := f)

lemma strictMonoOn_of_lt_add_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMax a → a ∈ s → a + 1 ∈ s → f a < f (a + 1)) → StrictMonoOn f s := by
  simpa [Order.succ_eq_add_one] using strictMonoOn_of_lt_succ hs (f := f)

lemma strictAntiOn_of_add_one_lt (hs : s.OrdConnected) :
    (∀ a, ¬ IsMax a → a ∈ s → a + 1 ∈ s → f (a + 1) < f a) → StrictAntiOn f s := by
  simpa [Order.succ_eq_add_one] using strictAntiOn_of_succ_lt hs (f := f)

lemma monotone_of_le_add_one : (∀ a, ¬ IsMax a → f a ≤ f (a + 1)) → Monotone f := by
  simpa [Order.succ_eq_add_one] using monotone_of_le_succ (f := f)

lemma antitone_of_add_one_le : (∀ a, ¬ IsMax a → f (a + 1) ≤ f a) → Antitone f := by
  simpa [Order.succ_eq_add_one] using antitone_of_succ_le (f := f)

lemma strictMono_of_lt_add_one : (∀ a, ¬ IsMax a → f a < f (a + 1)) → StrictMono f := by
  simpa [Order.succ_eq_add_one] using strictMono_of_lt_succ (f := f)

lemma strictAnti_of_add_one_lt : (∀ a, ¬ IsMax a → f (a + 1) < f a) → StrictAnti f := by
  simpa [Order.succ_eq_add_one] using strictAnti_of_succ_lt (f := f)

end SuccAddOrder

section PredSubOrder
variable [Sub α] [One α] [PredSubOrder α] [IsPredArchimedean α] {s : Set α} {f : α → β}

lemma monotoneOn_of_sub_one_le (hs : s.OrdConnected) :
    (∀ a, ¬ IsMin a → a ∈ s → a - 1 ∈ s → f (a - 1) ≤ f a) → MonotoneOn f s := by
  simpa [Order.pred_eq_sub_one] using monotoneOn_of_pred_le hs (f := f)

lemma antitoneOn_of_le_sub_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMin a → a ∈ s → a - 1 ∈ s → f a ≤ f (a - 1)) → AntitoneOn f s := by
  simpa [Order.pred_eq_sub_one] using antitoneOn_of_le_pred hs (f := f)

lemma strictMonoOn_of_sub_one_lt (hs : s.OrdConnected) :
    (∀ a, ¬ IsMin a → a ∈ s → a - 1 ∈ s → f (a - 1) < f a) → StrictMonoOn f s := by
  simpa [Order.pred_eq_sub_one] using strictMonoOn_of_pred_lt hs (f := f)

lemma strictAntiOn_of_lt_sub_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMin a → a ∈ s → a - 1 ∈ s → f a < f (a - 1)) → StrictAntiOn f s := by
  simpa [Order.pred_eq_sub_one] using strictAntiOn_of_lt_pred hs (f := f)

lemma monotone_of_sub_one_le : (∀ a, ¬ IsMin a → f (a - 1) ≤ f a) → Monotone f := by
  simpa [Order.pred_eq_sub_one] using monotone_of_pred_le (f := f)

lemma antitone_of_le_sub_one : (∀ a, ¬ IsMin a → f a ≤ f (a - 1)) → Antitone f := by
  simpa [Order.pred_eq_sub_one] using antitone_of_le_pred (f := f)

lemma strictMono_of_sub_one_lt : (∀ a, ¬ IsMin a → f (a - 1) < f a) → StrictMono f := by
  simpa [Order.pred_eq_sub_one] using strictMono_of_pred_lt (f := f)

lemma strictAnti_of_lt_sub_one : (∀ a, ¬ IsMin a → f a < f (a - 1)) → StrictAnti f := by
  simpa [Order.pred_eq_sub_one] using strictAnti_of_lt_pred (f := f)

end PredSubOrder
end Monotone
