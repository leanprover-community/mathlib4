/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Cover
import Mathlib.Order.Iterate

#align_import order.succ_pred.basic from "leanprover-community/mathlib"@"0111834459f5d7400215223ea95ae38a1265a907"

/-!
# Successor and predecessor

This file defines successor and predecessor orders. `succ a`, the successor of an element `a : α` is
the least element greater than `a`. `pred a` is the greatest element less than `a`. Typical examples
include `ℕ`, `ℤ`, `ℕ+`, `Fin n`, but also `ENat`, the lexicographic order of a successor/predecessor
order...

## Typeclasses

* `SuccOrder`: Order equipped with a sensible successor function.
* `PredOrder`: Order equipped with a sensible predecessor function.
* `IsSuccArchimedean`: `SuccOrder` where `succ` iterated to an element gives all the greater
  ones.
* `IsPredArchimedean`: `PredOrder` where `pred` iterated to an element gives all the smaller
  ones.

## Implementation notes

Maximal elements don't have a sensible successor. Thus the naïve typeclass
```lean
class NaiveSuccOrder (α : Type*) [Preorder α] :=
  (succ : α → α)
  (succ_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
  (lt_succ_iff : ∀ {a b}, a < succ b ↔ a ≤ b)
```
can't apply to an `OrderTop` because plugging in `a = b = ⊤` into either of `succ_le_iff` and
`lt_succ_iff` yields `⊤ < ⊤` (or more generally `m < m` for a maximal element `m`).
The solution taken here is to remove the implications `≤ → <` and instead require that `a < succ a`
for all non maximal elements (enforced by the combination of `le_succ` and the contrapositive of
`max_of_succ_le`).
The stricter condition of every element having a sensible successor can be obtained through the
combination of `SuccOrder α` and `NoMaxOrder α`.

## TODO

Is `GaloisConnection pred succ` always true? If not, we should introduce
```lean
class SuccPredOrder (α : Type*) [Preorder α] extends SuccOrder α, PredOrder α :=
  (pred_succ_gc : GaloisConnection (pred : α → α) succ)
```
`Covby` should help here.
-/


open Function OrderDual Set

variable {α : Type*}

/-- Order equipped with a sensible successor function. -/
@[ext]
class SuccOrder (α : Type*) [Preorder α] where
  /--Successor function-/
  succ : α → α
  /--Proof of basic ordering with respect to `succ`-/
  le_succ : ∀ a, a ≤ succ a
  /--Proof of interaction between `succ` and maximal element-/
  max_of_succ_le {a} : succ a ≤ a → IsMax a
  /--Proof that `succ` satisfies ordering invariants between `LT` and `LE`-/
  succ_le_of_lt {a b} : a < b → succ a ≤ b
  /--Proof that `succ` satisfies ordering invariants between `LE` and `LT`-/
  le_of_lt_succ {a b} : a < succ b → a ≤ b
#align succ_order SuccOrder
#align succ_order.ext_iff SuccOrder.ext_iff
#align succ_order.ext SuccOrder.ext

/-- Order equipped with a sensible predecessor function. -/
@[ext]
class PredOrder (α : Type*) [Preorder α] where
  /--Predecessor function-/
  pred : α → α
  /--Proof of basic ordering with respect to `pred`-/
  pred_le : ∀ a, pred a ≤ a
  /--Proof of interaction between `pred` and minimal element-/
  min_of_le_pred {a} : a ≤ pred a → IsMin a
  /--Proof that `pred` satisfies ordering invariants between `LT` and `LE`-/
  le_pred_of_lt {a b} : a < b → a ≤ pred b
  /--Proof that `pred` satisfies ordering invariants between `LE` and `LT`-/
  le_of_pred_lt {a b} : pred a < b → a ≤ b
#align pred_order PredOrder
#align pred_order.ext PredOrder.ext
#align pred_order.ext_iff PredOrder.ext_iff

instance [Preorder α] [SuccOrder α] :
    PredOrder αᵒᵈ where
  pred := toDual ∘ SuccOrder.succ ∘ ofDual
  pred_le := by
    simp only [comp, OrderDual.forall, ofDual_toDual, toDual_le_toDual,
     SuccOrder.le_succ, implies_true]
  min_of_le_pred h := by apply SuccOrder.max_of_succ_le h
                         -- 🎉 no goals
  le_pred_of_lt := by intro a b h; exact SuccOrder.succ_le_of_lt h
                      -- ⊢ a ≤ (↑toDual ∘ SuccOrder.succ ∘ ↑ofDual) b
                                   -- 🎉 no goals
  le_of_pred_lt := SuccOrder.le_of_lt_succ

instance [Preorder α] [PredOrder α] :
    SuccOrder αᵒᵈ where
  succ := toDual ∘ PredOrder.pred ∘ ofDual
  le_succ := by
    simp only [comp, OrderDual.forall, ofDual_toDual, toDual_le_toDual,
     PredOrder.pred_le, implies_true]
  max_of_succ_le h := by apply PredOrder.min_of_le_pred h
                         -- 🎉 no goals
  succ_le_of_lt := by intro a b h; exact PredOrder.le_pred_of_lt h
                      -- ⊢ (↑toDual ∘ PredOrder.pred ∘ ↑ofDual) a ≤ b
                                   -- 🎉 no goals
  le_of_lt_succ := PredOrder.le_of_pred_lt

section Preorder

variable [Preorder α]

/-- A constructor for `SuccOrder α` usable when `α` has no maximal element. -/
def SuccOrder.ofSuccLeIffOfLeLtSucc (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
    (hle_of_lt_succ : ∀ {a b}, a < succ b → a ≤ b) : SuccOrder α :=
  { succ
    le_succ := fun _ => (hsucc_le_iff.1 le_rfl).le
    max_of_succ_le := fun ha => (lt_irrefl _ <| hsucc_le_iff.1 ha).elim
    succ_le_of_lt := fun h => hsucc_le_iff.2 h
    le_of_lt_succ := fun h => hle_of_lt_succ h}
#align succ_order.of_succ_le_iff_of_le_lt_succ SuccOrder.ofSuccLeIffOfLeLtSucc

/-- A constructor for `PredOrder α` usable when `α` has no minimal element. -/
def PredOrder.ofLePredIffOfPredLePred (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b)
    (hle_of_pred_lt : ∀ {a b}, pred a < b → a ≤ b) : PredOrder α :=
  { pred
    pred_le := fun _ => (hle_pred_iff.1 le_rfl).le
    min_of_le_pred := fun ha => (lt_irrefl _ <| hle_pred_iff.1 ha).elim
    le_pred_of_lt := fun h => hle_pred_iff.2 h
    le_of_pred_lt := fun h => hle_of_pred_lt h }
#align pred_order.of_le_pred_iff_of_pred_le_pred PredOrder.ofLePredIffOfPredLePred

end Preorder

section LinearOrder

variable [LinearOrder α]

/-- A constructor for `SuccOrder α` for `α` a linear order. -/
@[simps]
def SuccOrder.ofCore (succ : α → α) (hn : ∀ {a}, ¬IsMax a → ∀ b, a < b ↔ succ a ≤ b)
    (hm : ∀ a, IsMax a → succ a = a) : SuccOrder α :=
  { succ
    succ_le_of_lt := fun {a b} =>
      by_cases (fun h hab => (hm a h).symm ▸ hab.le) fun h => (hn h b).mp
    le_succ := fun a =>
      by_cases (fun h => (hm a h).symm.le) fun h => le_of_lt <| by simpa using (hn h a).not
                                                                   -- 🎉 no goals
    le_of_lt_succ := fun {a b} hab =>
      by_cases (fun h => hm b h ▸ hab.le) fun h => by simpa [hab] using (hn h a).not
                                                      -- 🎉 no goals
                                                            -- 🎉 no goals
    max_of_succ_le := fun {a} => not_imp_not.mp fun h => by simpa using (hn h a).not }
#align succ_order.of_core SuccOrder.ofCore
#align succ_order.of_core_succ SuccOrder.ofCore_succ

/-- A constructor for `PredOrder α` for `α` a linear order. -/
@[simps]
def PredOrder.ofCore {α} [LinearOrder α] (pred : α → α)
    (hn : ∀ {a}, ¬IsMin a → ∀ b, b ≤ pred a ↔ b < a) (hm : ∀ a, IsMin a → pred a = a) :
    PredOrder α :=
  { pred
    le_pred_of_lt := fun {a b} =>
      by_cases (fun h hab => (hm b h).symm ▸ hab.le) fun h => (hn h a).mpr
    pred_le := fun a =>
      by_cases (fun h => (hm a h).le) fun h => le_of_lt <| by simpa using (hn h a).not
                                                              -- 🎉 no goals
    le_of_pred_lt := fun {a b} hab =>
      by_cases (fun h => hm a h ▸ hab.le) fun h => by simpa [hab] using (hn h b).not
                                                      -- 🎉 no goals
                                                            -- 🎉 no goals
    min_of_le_pred := fun {a} => not_imp_not.mp fun h => by simpa using (hn h a).not }
#align pred_order.of_core PredOrder.ofCore
#align pred_order.of_core_pred PredOrder.ofCore_pred

/-- A constructor for `SuccOrder α` usable when `α` is a linear order with no maximal element. -/
def SuccOrder.ofSuccLeIff (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b) :
    SuccOrder α :=
  { succ
    le_succ := fun _ => (hsucc_le_iff.1 le_rfl).le
    max_of_succ_le := fun ha => (lt_irrefl _ <| hsucc_le_iff.1 ha).elim
    succ_le_of_lt := fun h => hsucc_le_iff.2 h
    le_of_lt_succ := fun {_ _} h => le_of_not_lt ((not_congr hsucc_le_iff).1 h.not_le) }
#align succ_order.of_succ_le_iff SuccOrder.ofSuccLeIff

/-- A constructor for `PredOrder α` usable when `α` is a linear order with no minimal element. -/
def PredOrder.ofLePredIff (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b) :
    PredOrder α :=
  { pred
    pred_le := fun _ => (hle_pred_iff.1 le_rfl).le
    min_of_le_pred := fun ha => (lt_irrefl _ <| hle_pred_iff.1 ha).elim
    le_pred_of_lt := fun h => hle_pred_iff.2 h
    le_of_pred_lt := fun {_ _} h => le_of_not_lt ((not_congr hle_pred_iff).1 h.not_le) }
#align pred_order.of_le_pred_iff PredOrder.ofLePredIff

end LinearOrder

/-! ### Successor order -/


namespace Order

section Preorder

variable [Preorder α] [SuccOrder α] {a b : α}

/-- The successor of an element. If `a` is not maximal, then `succ a` is the least element greater
than `a`. If `a` is maximal, then `succ a = a`. -/
def succ : α → α :=
  SuccOrder.succ
#align order.succ Order.succ

theorem le_succ : ∀ a : α, a ≤ succ a :=
  SuccOrder.le_succ
#align order.le_succ Order.le_succ

theorem max_of_succ_le {a : α} : succ a ≤ a → IsMax a :=
  SuccOrder.max_of_succ_le
#align order.max_of_succ_le Order.max_of_succ_le

theorem succ_le_of_lt {a b : α} : a < b → succ a ≤ b :=
  SuccOrder.succ_le_of_lt
#align order.succ_le_of_lt Order.succ_le_of_lt

theorem le_of_lt_succ {a b : α} : a < succ b → a ≤ b :=
  SuccOrder.le_of_lt_succ
#align order.le_of_lt_succ Order.le_of_lt_succ

@[simp]
theorem succ_le_iff_isMax : succ a ≤ a ↔ IsMax a :=
  ⟨max_of_succ_le, fun h => h <| le_succ _⟩
#align order.succ_le_iff_is_max Order.succ_le_iff_isMax

@[simp]
theorem lt_succ_iff_not_isMax : a < succ a ↔ ¬IsMax a :=
  ⟨not_isMax_of_lt, fun ha => (le_succ a).lt_of_not_le fun h => ha <| max_of_succ_le h⟩
#align order.lt_succ_iff_not_is_max Order.lt_succ_iff_not_isMax

alias ⟨_, lt_succ_of_not_isMax⟩ := lt_succ_iff_not_isMax
#align order.lt_succ_of_not_is_max Order.lt_succ_of_not_isMax

theorem wcovby_succ (a : α) : a ⩿ succ a :=
  ⟨le_succ a, fun _ hb => (succ_le_of_lt hb).not_lt⟩
#align order.wcovby_succ Order.wcovby_succ

theorem covby_succ_of_not_isMax (h : ¬IsMax a) : a ⋖ succ a :=
  (wcovby_succ a).covby_of_lt <| lt_succ_of_not_isMax h
#align order.covby_succ_of_not_is_max Order.covby_succ_of_not_isMax

theorem lt_succ_iff_of_not_isMax (ha : ¬IsMax a) : b < succ a ↔ b ≤ a :=
  ⟨le_of_lt_succ, fun h => h.trans_lt <| lt_succ_of_not_isMax ha⟩
#align order.lt_succ_iff_of_not_is_max Order.lt_succ_iff_of_not_isMax

theorem succ_le_iff_of_not_isMax (ha : ¬IsMax a) : succ a ≤ b ↔ a < b :=
  ⟨(lt_succ_of_not_isMax ha).trans_le, succ_le_of_lt⟩
#align order.succ_le_iff_of_not_is_max Order.succ_le_iff_of_not_isMax

theorem succ_lt_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) : succ a < succ b ↔ a < b :=
  by rw [lt_succ_iff_of_not_isMax hb, succ_le_iff_of_not_isMax ha]
     -- 🎉 no goals
#align order.succ_lt_succ_iff_of_not_is_max Order.succ_lt_succ_iff_of_not_isMax

theorem succ_le_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) : succ a ≤ succ b ↔ a ≤ b :=
  by rw [succ_le_iff_of_not_isMax ha, lt_succ_iff_of_not_isMax hb]
     -- 🎉 no goals
#align order.succ_le_succ_iff_of_not_is_max Order.succ_le_succ_iff_of_not_isMax

@[simp, mono]
theorem succ_le_succ (h : a ≤ b) : succ a ≤ succ b := by
  by_cases hb : IsMax b
  -- ⊢ succ a ≤ succ b
  · by_cases hba : b ≤ a
    -- ⊢ succ a ≤ succ b
    · exact (hb <| hba.trans <| le_succ _).trans (le_succ _)
      -- 🎉 no goals
    · exact succ_le_of_lt ((h.lt_of_not_le hba).trans_le <| le_succ b)
      -- 🎉 no goals
  · rwa [succ_le_iff_of_not_isMax fun ha => hb <| ha.mono h, lt_succ_iff_of_not_isMax hb]
    -- 🎉 no goals
#align order.succ_le_succ Order.succ_le_succ

theorem succ_mono : Monotone (succ : α → α) := fun _ _ => succ_le_succ
#align order.succ_mono Order.succ_mono

theorem le_succ_iterate (k : ℕ) (x : α) : x ≤ succ^[k] x := by
  conv_lhs => rw [(by simp only [Function.iterate_id, id.def] : x = id^[k] x)]
  -- ⊢ id^[k] x ≤ succ^[k] x
  exact Monotone.le_iterate_of_le succ_mono le_succ k x
  -- 🎉 no goals
#align order.le_succ_iterate Order.le_succ_iterate

theorem isMax_iterate_succ_of_eq_of_lt {n m : ℕ} (h_eq : succ^[n] a = succ^[m] a)
    (h_lt : n < m) : IsMax (succ^[n] a) := by
  refine' max_of_succ_le (le_trans _ h_eq.symm.le)
  -- ⊢ succ (succ^[n] a) ≤ succ^[m] a
  have : succ (succ^[n] a) = succ^[n + 1] a := by rw [Function.iterate_succ', comp]
  -- ⊢ succ (succ^[n] a) ≤ succ^[m] a
  rw [this]
  -- ⊢ succ^[n + 1] a ≤ succ^[m] a
  have h_le : n + 1 ≤ m := Nat.succ_le_of_lt h_lt
  -- ⊢ succ^[n + 1] a ≤ succ^[m] a
  exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ a) h_le
  -- 🎉 no goals
#align order.is_max_iterate_succ_of_eq_of_lt Order.isMax_iterate_succ_of_eq_of_lt

theorem isMax_iterate_succ_of_eq_of_ne {n m : ℕ} (h_eq : succ^[n] a = succ^[m] a)
    (h_ne : n ≠ m) : IsMax (succ^[n] a) := by
  cases' le_total n m with h h
  -- ⊢ IsMax (succ^[n] a)
  · exact isMax_iterate_succ_of_eq_of_lt h_eq (lt_of_le_of_ne h h_ne)
    -- 🎉 no goals
  · rw [h_eq]
    -- ⊢ IsMax (succ^[m] a)
    exact isMax_iterate_succ_of_eq_of_lt h_eq.symm (lt_of_le_of_ne h h_ne.symm)
    -- 🎉 no goals
#align order.is_max_iterate_succ_of_eq_of_ne Order.isMax_iterate_succ_of_eq_of_ne

theorem Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iio (succ a) = Iic a :=
  Set.ext fun _ => lt_succ_iff_of_not_isMax ha
#align order.Iio_succ_of_not_is_max Order.Iio_succ_of_not_isMax

theorem Ici_succ_of_not_isMax (ha : ¬IsMax a) : Ici (succ a) = Ioi a :=
  Set.ext fun _ => succ_le_iff_of_not_isMax ha
#align order.Ici_succ_of_not_is_max Order.Ici_succ_of_not_isMax

theorem Ico_succ_right_of_not_isMax (hb : ¬IsMax b) : Ico a (succ b) = Icc a b := by
  rw [← Ici_inter_Iio, Iio_succ_of_not_isMax hb, Ici_inter_Iic]
  -- 🎉 no goals
#align order.Ico_succ_right_of_not_is_max Order.Ico_succ_right_of_not_isMax

theorem Ioo_succ_right_of_not_isMax (hb : ¬IsMax b) : Ioo a (succ b) = Ioc a b := by
  rw [← Ioi_inter_Iio, Iio_succ_of_not_isMax hb, Ioi_inter_Iic]
  -- 🎉 no goals
#align order.Ioo_succ_right_of_not_is_max Order.Ioo_succ_right_of_not_isMax

theorem Icc_succ_left_of_not_isMax (ha : ¬IsMax a) : Icc (succ a) b = Ioc a b := by
  rw [← Ici_inter_Iic, Ici_succ_of_not_isMax ha, Ioi_inter_Iic]
  -- 🎉 no goals
#align order.Icc_succ_left_of_not_is_max Order.Icc_succ_left_of_not_isMax

theorem Ico_succ_left_of_not_isMax (ha : ¬IsMax a) : Ico (succ a) b = Ioo a b := by
  rw [← Ici_inter_Iio, Ici_succ_of_not_isMax ha, Ioi_inter_Iio]
  -- 🎉 no goals
#align order.Ico_succ_left_of_not_is_max Order.Ico_succ_left_of_not_isMax

section NoMaxOrder

variable [NoMaxOrder α]

theorem lt_succ (a : α) : a < succ a :=
  lt_succ_of_not_isMax <| not_isMax a
#align order.lt_succ Order.lt_succ

@[simp]
theorem lt_succ_iff : a < succ b ↔ a ≤ b :=
  lt_succ_iff_of_not_isMax <| not_isMax b
#align order.lt_succ_iff Order.lt_succ_iff

@[simp]
theorem succ_le_iff : succ a ≤ b ↔ a < b :=
  succ_le_iff_of_not_isMax <| not_isMax a
#align order.succ_le_iff Order.succ_le_iff

theorem succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b := by simp
                                                         -- 🎉 no goals
#align order.succ_le_succ_iff Order.succ_le_succ_iff

theorem succ_lt_succ_iff : succ a < succ b ↔ a < b := by simp
                                                         -- 🎉 no goals
#align order.succ_lt_succ_iff Order.succ_lt_succ_iff

alias ⟨le_of_succ_le_succ, _⟩ := succ_le_succ_iff
#align order.le_of_succ_le_succ Order.le_of_succ_le_succ

alias ⟨lt_of_succ_lt_succ, succ_lt_succ⟩ := succ_lt_succ_iff
#align order.lt_of_succ_lt_succ Order.lt_of_succ_lt_succ
#align order.succ_lt_succ Order.succ_lt_succ

theorem succ_strictMono : StrictMono (succ : α → α) := fun _ _ => succ_lt_succ
#align order.succ_strict_mono Order.succ_strictMono

theorem covby_succ (a : α) : a ⋖ succ a :=
  covby_succ_of_not_isMax <| not_isMax a
#align order.covby_succ Order.covby_succ

@[simp]
theorem Iio_succ (a : α) : Iio (succ a) = Iic a :=
  Iio_succ_of_not_isMax <| not_isMax _
#align order.Iio_succ Order.Iio_succ

@[simp]
theorem Ici_succ (a : α) : Ici (succ a) = Ioi a :=
  Ici_succ_of_not_isMax <| not_isMax _
#align order.Ici_succ Order.Ici_succ

@[simp]
theorem Ico_succ_right (a b : α) : Ico a (succ b) = Icc a b :=
  Ico_succ_right_of_not_isMax <| not_isMax _
#align order.Ico_succ_right Order.Ico_succ_right

@[simp]
theorem Ioo_succ_right (a b : α) : Ioo a (succ b) = Ioc a b :=
  Ioo_succ_right_of_not_isMax <| not_isMax _
#align order.Ioo_succ_right Order.Ioo_succ_right

@[simp]
theorem Icc_succ_left (a b : α) : Icc (succ a) b = Ioc a b :=
  Icc_succ_left_of_not_isMax <| not_isMax _
#align order.Icc_succ_left Order.Icc_succ_left

@[simp]
theorem Ico_succ_left (a b : α) : Ico (succ a) b = Ioo a b :=
  Ico_succ_left_of_not_isMax <| not_isMax _
#align order.Ico_succ_left Order.Ico_succ_left

end NoMaxOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α}

@[simp]
theorem succ_eq_iff_isMax : succ a = a ↔ IsMax a :=
  ⟨fun h => max_of_succ_le h.le, fun h => h.eq_of_ge <| le_succ _⟩
#align order.succ_eq_iff_is_max Order.succ_eq_iff_isMax

alias ⟨_, _root_.IsMax.succ_eq⟩ := succ_eq_iff_isMax
#align is_max.succ_eq IsMax.succ_eq

theorem succ_eq_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) :
    succ a = succ b ↔ a = b := by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, succ_le_succ_iff_of_not_isMax ha hb,
    succ_lt_succ_iff_of_not_isMax ha hb]
#align order.succ_eq_succ_iff_of_not_is_max Order.succ_eq_succ_iff_of_not_isMax

theorem le_le_succ_iff : a ≤ b ∧ b ≤ succ a ↔ b = a ∨ b = succ a := by
  refine'
    ⟨fun h =>
      or_iff_not_imp_left.2 fun hba : b ≠ a =>
        h.2.antisymm (succ_le_of_lt <| h.1.lt_of_ne <| hba.symm),
      _⟩
  rintro (rfl | rfl)
  -- ⊢ b ≤ b ∧ b ≤ succ b
  · exact ⟨le_rfl, le_succ b⟩
    -- 🎉 no goals
  · exact ⟨le_succ a, le_rfl⟩
    -- 🎉 no goals
#align order.le_le_succ_iff Order.le_le_succ_iff

theorem _root_.Covby.succ_eq (h : a ⋖ b) : succ a = b :=
  (succ_le_of_lt h.lt).eq_of_not_lt fun h' => h.2 (lt_succ_of_not_isMax h.lt.not_isMax) h'
#align covby.succ_eq Covby.succ_eq

theorem _root_.Wcovby.le_succ (h : a ⩿ b) : b ≤ succ a := by
  obtain h | rfl := h.covby_or_eq
  -- ⊢ b ≤ succ a
  · exact (Covby.succ_eq h).ge
    -- 🎉 no goals
  · exact le_succ _
    -- 🎉 no goals
#align wcovby.le_succ Wcovby.le_succ

theorem le_succ_iff_eq_or_le : a ≤ succ b ↔ a = succ b ∨ a ≤ b := by
  by_cases hb : IsMax b
  -- ⊢ a ≤ succ b ↔ a = succ b ∨ a ≤ b
  · rw [hb.succ_eq, or_iff_right_of_imp le_of_eq]
    -- 🎉 no goals
  · rw [← lt_succ_iff_of_not_isMax hb, le_iff_eq_or_lt]
    -- 🎉 no goals
#align order.le_succ_iff_eq_or_le Order.le_succ_iff_eq_or_le

theorem lt_succ_iff_eq_or_lt_of_not_isMax (hb : ¬IsMax b) : a < succ b ↔ a = b ∨ a < b :=
  (lt_succ_iff_of_not_isMax hb).trans le_iff_eq_or_lt
#align order.lt_succ_iff_eq_or_lt_of_not_is_max Order.lt_succ_iff_eq_or_lt_of_not_isMax

theorem Iic_succ (a : α) : Iic (succ a) = insert (succ a) (Iic a) :=
  ext fun _ => le_succ_iff_eq_or_le
#align order.Iic_succ Order.Iic_succ

theorem Icc_succ_right (h : a ≤ succ b) : Icc a (succ b) = insert (succ b) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ici.2 h)]
  -- 🎉 no goals
#align order.Icc_succ_right Order.Icc_succ_right

theorem Ioc_succ_right (h : a < succ b) : Ioc a (succ b) = insert (succ b) (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ioi.2 h)]
  -- 🎉 no goals
#align order.Ioc_succ_right Order.Ioc_succ_right

theorem Iio_succ_eq_insert_of_not_isMax (h : ¬IsMax a) : Iio (succ a) = insert a (Iio a) :=
  ext fun _ => lt_succ_iff_eq_or_lt_of_not_isMax h
#align order.Iio_succ_eq_insert_of_not_is_max Order.Iio_succ_eq_insert_of_not_isMax

theorem Ico_succ_right_eq_insert_of_not_isMax (h₁ : a ≤ b) (h₂ : ¬IsMax b) :
    Ico a (succ b) = insert b (Ico a b) := by
  simp_rw [← Iio_inter_Ici, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ici.2 h₁)]
  -- 🎉 no goals
#align order.Ico_succ_right_eq_insert_of_not_is_max Order.Ico_succ_right_eq_insert_of_not_isMax

theorem Ioo_succ_right_eq_insert_of_not_isMax (h₁ : a < b) (h₂ : ¬IsMax b) :
    Ioo a (succ b) = insert b (Ioo a b) := by
  simp_rw [← Iio_inter_Ioi, Iio_succ_eq_insert_of_not_isMax h₂, insert_inter_of_mem (mem_Ioi.2 h₁)]
  -- 🎉 no goals
#align order.Ioo_succ_right_eq_insert_of_not_is_max Order.Ioo_succ_right_eq_insert_of_not_isMax

section NoMaxOrder

variable [NoMaxOrder α]

@[simp]
theorem succ_eq_succ_iff : succ a = succ b ↔ a = b :=
  succ_eq_succ_iff_of_not_isMax (not_isMax a) (not_isMax b)
#align order.succ_eq_succ_iff Order.succ_eq_succ_iff

theorem succ_injective : Injective (succ : α → α) := fun _ _ => succ_eq_succ_iff.1
#align order.succ_injective Order.succ_injective

theorem succ_ne_succ_iff : succ a ≠ succ b ↔ a ≠ b :=
  succ_injective.ne_iff
#align order.succ_ne_succ_iff Order.succ_ne_succ_iff

alias ⟨_, succ_ne_succ⟩ := succ_ne_succ_iff
#align order.succ_ne_succ Order.succ_ne_succ

theorem lt_succ_iff_eq_or_lt : a < succ b ↔ a = b ∨ a < b :=
  lt_succ_iff.trans le_iff_eq_or_lt
#align order.lt_succ_iff_eq_or_lt Order.lt_succ_iff_eq_or_lt

theorem succ_eq_iff_covby : succ a = b ↔ a ⋖ b :=
  ⟨by
    rintro rfl
    -- ⊢ a ⋖ succ a
    exact covby_succ _, Covby.succ_eq⟩
    -- 🎉 no goals
#align order.succ_eq_iff_covby Order.succ_eq_iff_covby

theorem Iio_succ_eq_insert (a : α) : Iio (succ a) = insert a (Iio a) :=
  Iio_succ_eq_insert_of_not_isMax <| not_isMax a
#align order.Iio_succ_eq_insert Order.Iio_succ_eq_insert

theorem Ico_succ_right_eq_insert (h : a ≤ b) : Ico a (succ b) = insert b (Ico a b) :=
  Ico_succ_right_eq_insert_of_not_isMax h <| not_isMax b
#align order.Ico_succ_right_eq_insert Order.Ico_succ_right_eq_insert

theorem Ioo_succ_right_eq_insert (h : a < b) : Ioo a (succ b) = insert b (Ioo a b) :=
  Ioo_succ_right_eq_insert_of_not_isMax h <| not_isMax b
#align order.Ioo_succ_right_eq_insert Order.Ioo_succ_right_eq_insert

end NoMaxOrder

section OrderTop

variable [OrderTop α]

@[simp]
theorem succ_top : succ (⊤ : α) = ⊤ := by
  rw [succ_eq_iff_isMax, isMax_iff_eq_top]
  -- 🎉 no goals
#align order.succ_top Order.succ_top

--Porting note: removing @[simp],`simp` can prove it
theorem succ_le_iff_eq_top : succ a ≤ a ↔ a = ⊤ :=
  succ_le_iff_isMax.trans isMax_iff_eq_top
#align order.succ_le_iff_eq_top Order.succ_le_iff_eq_top

--Porting note: removing @[simp],`simp` can prove it
theorem lt_succ_iff_ne_top : a < succ a ↔ a ≠ ⊤ :=
  lt_succ_iff_not_isMax.trans not_isMax_iff_ne_top
#align order.lt_succ_iff_ne_top Order.lt_succ_iff_ne_top

end OrderTop

section OrderBot

variable [OrderBot α]

--Porting note: removing @[simp],`simp` can prove it
theorem lt_succ_bot_iff [NoMaxOrder α] : a < succ ⊥ ↔ a = ⊥ := by rw [lt_succ_iff, le_bot_iff]
                                                                  -- 🎉 no goals
#align order.lt_succ_bot_iff Order.lt_succ_bot_iff

theorem le_succ_bot_iff : a ≤ succ ⊥ ↔ a = ⊥ ∨ a = succ ⊥ := by
  rw [le_succ_iff_eq_or_le, le_bot_iff, or_comm]
  -- 🎉 no goals
#align order.le_succ_bot_iff Order.le_succ_bot_iff

variable [Nontrivial α]

theorem bot_lt_succ (a : α) : ⊥ < succ a :=
  (lt_succ_of_not_isMax not_isMax_bot).trans_le <| succ_mono bot_le
#align order.bot_lt_succ Order.bot_lt_succ

theorem succ_ne_bot (a : α) : succ a ≠ ⊥ :=
  (bot_lt_succ a).ne'
#align order.succ_ne_bot Order.succ_ne_bot

end OrderBot

end PartialOrder

/-- There is at most one way to define the successors in a `PartialOrder`. -/
instance [PartialOrder α] : Subsingleton (SuccOrder α) :=
  ⟨by
    intro h₀ h₁
    -- ⊢ h₀ = h₁
    ext a
    -- ⊢ SuccOrder.succ a = SuccOrder.succ a
    by_cases ha : IsMax a
    -- ⊢ SuccOrder.succ a = SuccOrder.succ a
    · exact (@IsMax.succ_eq _ _ h₀ _ ha).trans ha.succ_eq.symm
      -- 🎉 no goals
    · exact @Covby.succ_eq _ _ h₀ _ _ (covby_succ_of_not_isMax ha)⟩
      -- 🎉 no goals

section CompleteLattice

variable [CompleteLattice α] [SuccOrder α]

theorem succ_eq_iInf (a : α) : succ a = ⨅ (b) (_ : a < b), b := by
  refine' le_antisymm (le_iInf fun b => le_iInf succ_le_of_lt) _
  -- ⊢ ⨅ (b : α) (_ : a < b), b ≤ succ a
  obtain rfl | ha := eq_or_ne a ⊤
  -- ⊢ ⨅ (b : α) (_ : ⊤ < b), b ≤ succ ⊤
  · rw [succ_top]
    -- ⊢ ⨅ (b : α) (_ : ⊤ < b), b ≤ ⊤
    exact le_top
    -- 🎉 no goals
  exact iInf₂_le _ (lt_succ_iff_ne_top.2 ha)
  -- 🎉 no goals
#align order.succ_eq_infi Order.succ_eq_iInf

end CompleteLattice

/-! ### Predecessor order -/

section Preorder

variable [Preorder α] [PredOrder α] {a b : α}

/-- The predecessor of an element. If `a` is not minimal, then `pred a` is the greatest element less
than `a`. If `a` is minimal, then `pred a = a`. -/
def pred : α → α :=
  PredOrder.pred
#align order.pred Order.pred

theorem pred_le : ∀ a : α, pred a ≤ a :=
  PredOrder.pred_le
#align order.pred_le Order.pred_le

theorem min_of_le_pred {a : α} : a ≤ pred a → IsMin a :=
  PredOrder.min_of_le_pred
#align order.min_of_le_pred Order.min_of_le_pred

theorem le_pred_of_lt {a b : α} : a < b → a ≤ pred b :=
  PredOrder.le_pred_of_lt
#align order.le_pred_of_lt Order.le_pred_of_lt

theorem le_of_pred_lt {a b : α} : pred a < b → a ≤ b :=
  PredOrder.le_of_pred_lt
#align order.le_of_pred_lt Order.le_of_pred_lt

@[simp]
theorem le_pred_iff_isMin : a ≤ pred a ↔ IsMin a :=
  ⟨min_of_le_pred, fun h => h <| pred_le _⟩
#align order.le_pred_iff_is_min Order.le_pred_iff_isMin

@[simp]
theorem pred_lt_iff_not_isMin : pred a < a ↔ ¬IsMin a :=
  ⟨not_isMin_of_lt, fun ha => (pred_le a).lt_of_not_le fun h => ha <| min_of_le_pred h⟩
#align order.pred_lt_iff_not_is_min Order.pred_lt_iff_not_isMin

alias ⟨_, pred_lt_of_not_isMin⟩ := pred_lt_iff_not_isMin
#align order.pred_lt_of_not_is_min Order.pred_lt_of_not_isMin

theorem pred_wcovby (a : α) : pred a ⩿ a :=
  ⟨pred_le a, fun _ hb => (le_of_pred_lt hb).not_lt⟩
#align order.pred_wcovby Order.pred_wcovby

theorem pred_covby_of_not_isMin (h : ¬IsMin a) : pred a ⋖ a :=
  (pred_wcovby a).covby_of_lt <| pred_lt_of_not_isMin h
#align order.pred_covby_of_not_is_min Order.pred_covby_of_not_isMin

theorem pred_lt_iff_of_not_isMin (ha : ¬IsMin a) : pred a < b ↔ a ≤ b :=
  ⟨le_of_pred_lt, (pred_lt_of_not_isMin ha).trans_le⟩
#align order.pred_lt_iff_of_not_is_min Order.pred_lt_iff_of_not_isMin

theorem le_pred_iff_of_not_isMin (ha : ¬IsMin a) : b ≤ pred a ↔ b < a :=
  ⟨fun h => h.trans_lt <| pred_lt_of_not_isMin ha, le_pred_of_lt⟩
#align order.le_pred_iff_of_not_is_min Order.le_pred_iff_of_not_isMin

@[simp, mono]
theorem pred_le_pred {a b : α} (h : a ≤ b) : pred a ≤ pred b :=
  succ_le_succ h.dual
#align order.pred_le_pred Order.pred_le_pred

theorem pred_mono : Monotone (pred : α → α) := fun _ _ => pred_le_pred
#align order.pred_mono Order.pred_mono

theorem pred_iterate_le (k : ℕ) (x : α) : pred^[k] x ≤ x := by
  conv_rhs => rw [(by simp only [Function.iterate_id, id.def] : x = id^[k] x)]
  -- ⊢ pred^[k] x ≤ id^[k] x
  exact Monotone.iterate_le_of_le pred_mono pred_le k x
  -- 🎉 no goals
#align order.pred_iterate_le Order.pred_iterate_le

theorem isMin_iterate_pred_of_eq_of_lt {n m : ℕ} (h_eq : pred^[n] a = pred^[m] a)
    (h_lt : n < m) : IsMin (pred^[n] a) :=
  @isMax_iterate_succ_of_eq_of_lt αᵒᵈ _ _ _ _ _ h_eq h_lt
#align order.is_min_iterate_pred_of_eq_of_lt Order.isMin_iterate_pred_of_eq_of_lt

theorem isMin_iterate_pred_of_eq_of_ne {n m : ℕ} (h_eq : pred^[n] a = pred^[m] a)
    (h_ne : n ≠ m) : IsMin (pred^[n] a) :=
  @isMax_iterate_succ_of_eq_of_ne αᵒᵈ _ _ _ _ _ h_eq h_ne
#align order.is_min_iterate_pred_of_eq_of_ne Order.isMin_iterate_pred_of_eq_of_ne

theorem Ioi_pred_of_not_isMin (ha : ¬IsMin a) : Ioi (pred a) = Ici a :=
  Set.ext fun _ => pred_lt_iff_of_not_isMin ha
#align order.Ioi_pred_of_not_is_min Order.Ioi_pred_of_not_isMin

theorem Iic_pred_of_not_isMin (ha : ¬IsMin a) : Iic (pred a) = Iio a :=
  Set.ext fun _ => le_pred_iff_of_not_isMin ha
#align order.Iic_pred_of_not_is_min Order.Iic_pred_of_not_isMin

theorem Ioc_pred_left_of_not_isMin (ha : ¬IsMin a) : Ioc (pred a) b = Icc a b := by
  rw [← Ioi_inter_Iic, Ioi_pred_of_not_isMin ha, Ici_inter_Iic]
  -- 🎉 no goals
#align order.Ioc_pred_left_of_not_is_min Order.Ioc_pred_left_of_not_isMin

theorem Ioo_pred_left_of_not_isMin (ha : ¬IsMin a) : Ioo (pred a) b = Ico a b := by
  rw [← Ioi_inter_Iio, Ioi_pred_of_not_isMin ha, Ici_inter_Iio]
  -- 🎉 no goals
#align order.Ioo_pred_left_of_not_is_min Order.Ioo_pred_left_of_not_isMin

theorem Icc_pred_right_of_not_isMin (ha : ¬IsMin b) : Icc a (pred b) = Ico a b := by
  rw [← Ici_inter_Iic, Iic_pred_of_not_isMin ha, Ici_inter_Iio]
  -- 🎉 no goals
#align order.Icc_pred_right_of_not_is_min Order.Icc_pred_right_of_not_isMin

theorem Ioc_pred_right_of_not_isMin (ha : ¬IsMin b) : Ioc a (pred b) = Ioo a b := by
  rw [← Ioi_inter_Iic, Iic_pred_of_not_isMin ha, Ioi_inter_Iio]
  -- 🎉 no goals
#align order.Ioc_pred_right_of_not_is_min Order.Ioc_pred_right_of_not_isMin

section NoMinOrder

variable [NoMinOrder α]

theorem pred_lt (a : α) : pred a < a :=
  pred_lt_of_not_isMin <| not_isMin a
#align order.pred_lt Order.pred_lt

@[simp]
theorem pred_lt_iff : pred a < b ↔ a ≤ b :=
  pred_lt_iff_of_not_isMin <| not_isMin a
#align order.pred_lt_iff Order.pred_lt_iff

@[simp]
theorem le_pred_iff : a ≤ pred b ↔ a < b :=
  le_pred_iff_of_not_isMin <| not_isMin b
#align order.le_pred_iff Order.le_pred_iff

theorem pred_le_pred_iff : pred a ≤ pred b ↔ a ≤ b := by simp
                                                         -- 🎉 no goals
#align order.pred_le_pred_iff Order.pred_le_pred_iff

theorem pred_lt_pred_iff : pred a < pred b ↔ a < b := by simp
                                                         -- 🎉 no goals
#align order.pred_lt_pred_iff Order.pred_lt_pred_iff

alias ⟨le_of_pred_le_pred, _⟩ := pred_le_pred_iff
#align order.le_of_pred_le_pred Order.le_of_pred_le_pred

alias ⟨lt_of_pred_lt_pred, pred_lt_pred⟩ := pred_lt_pred_iff
#align order.lt_of_pred_lt_pred Order.lt_of_pred_lt_pred
#align order.pred_lt_pred Order.pred_lt_pred

theorem pred_strictMono : StrictMono (pred : α → α) := fun _ _ => pred_lt_pred
#align order.pred_strict_mono Order.pred_strictMono

theorem pred_covby (a : α) : pred a ⋖ a :=
  pred_covby_of_not_isMin <| not_isMin a
#align order.pred_covby Order.pred_covby

@[simp]
theorem Ioi_pred (a : α) : Ioi (pred a) = Ici a :=
  Ioi_pred_of_not_isMin <| not_isMin a
#align order.Ioi_pred Order.Ioi_pred

@[simp]
theorem Iic_pred (a : α) : Iic (pred a) = Iio a :=
  Iic_pred_of_not_isMin <| not_isMin a
#align order.Iic_pred Order.Iic_pred

@[simp]
theorem Ioc_pred_left (a b : α) : Ioc (pred a) b = Icc a b :=
  Ioc_pred_left_of_not_isMin <| not_isMin _
#align order.Ioc_pred_left Order.Ioc_pred_left

@[simp]
theorem Ioo_pred_left (a b : α) : Ioo (pred a) b = Ico a b :=
  Ioo_pred_left_of_not_isMin <| not_isMin _
#align order.Ioo_pred_left Order.Ioo_pred_left

@[simp]
theorem Icc_pred_right (a b : α) : Icc a (pred b) = Ico a b :=
  Icc_pred_right_of_not_isMin <| not_isMin _
#align order.Icc_pred_right Order.Icc_pred_right

@[simp]
theorem Ioc_pred_right (a b : α) : Ioc a (pred b) = Ioo a b :=
  Ioc_pred_right_of_not_isMin <| not_isMin _
#align order.Ioc_pred_right Order.Ioc_pred_right

end NoMinOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [PredOrder α] {a b : α}

@[simp]
theorem pred_eq_iff_isMin : pred a = a ↔ IsMin a :=
  ⟨fun h => min_of_le_pred h.ge, fun h => h.eq_of_le <| pred_le _⟩
#align order.pred_eq_iff_is_min Order.pred_eq_iff_isMin

alias ⟨_, _root_.IsMin.pred_eq⟩ := pred_eq_iff_isMin
#align is_min.pred_eq IsMin.pred_eq

theorem pred_le_le_iff {a b : α} : pred a ≤ b ∧ b ≤ a ↔ b = a ∨ b = pred a := by
  refine'
    ⟨fun h =>
      or_iff_not_imp_left.2 fun hba : b ≠ a => (le_pred_of_lt <| h.2.lt_of_ne hba).antisymm h.1, _⟩
  rintro (rfl | rfl)
  -- ⊢ pred b ≤ b ∧ b ≤ b
  · exact ⟨pred_le b, le_rfl⟩
    -- 🎉 no goals
  · exact ⟨le_rfl, pred_le a⟩
    -- 🎉 no goals
#align order.pred_le_le_iff Order.pred_le_le_iff

theorem _root_.Covby.pred_eq {a b : α} (h : a ⋖ b) : pred b = a :=
  (le_pred_of_lt h.lt).eq_of_not_gt fun h' => h.2 h' <| pred_lt_of_not_isMin h.lt.not_isMin
#align covby.pred_eq Covby.pred_eq

theorem _root_.Wcovby.pred_le (h : a ⩿ b) : pred b ≤ a := by
  obtain h | rfl := h.covby_or_eq
  -- ⊢ pred b ≤ a
  · exact (Covby.pred_eq h).le
    -- 🎉 no goals
  · exact pred_le _
    -- 🎉 no goals
#align wcovby.pred_le Wcovby.pred_le

theorem pred_le_iff_eq_or_le : pred a ≤ b ↔ b = pred a ∨ a ≤ b := by
  by_cases ha : IsMin a
  -- ⊢ pred a ≤ b ↔ b = pred a ∨ a ≤ b
  · rw [ha.pred_eq, or_iff_right_of_imp ge_of_eq]
    -- 🎉 no goals
  · rw [← pred_lt_iff_of_not_isMin ha, le_iff_eq_or_lt, eq_comm]
    -- 🎉 no goals
#align order.pred_le_iff_eq_or_le Order.pred_le_iff_eq_or_le

theorem pred_lt_iff_eq_or_lt_of_not_isMin (ha : ¬IsMin a) : pred a < b ↔ a = b ∨ a < b :=
  (pred_lt_iff_of_not_isMin ha).trans le_iff_eq_or_lt
#align order.pred_lt_iff_eq_or_lt_of_not_is_min Order.pred_lt_iff_eq_or_lt_of_not_isMin

theorem Ici_pred (a : α) : Ici (pred a) = insert (pred a) (Ici a) :=
  ext fun _ => pred_le_iff_eq_or_le
#align order.Ici_pred Order.Ici_pred

theorem Ioi_pred_eq_insert_of_not_isMin (ha : ¬IsMin a) : Ioi (pred a) = insert a (Ioi a) := by
  ext x; simp only [insert, mem_setOf, @eq_comm _ x a, mem_Ioi, Set.insert]
  -- ⊢ x ∈ Ioi (pred a) ↔ x ∈ insert a (Ioi a)
         -- ⊢ pred a < x ↔ a = x ∨ a < x
  exact pred_lt_iff_eq_or_lt_of_not_isMin ha
  -- 🎉 no goals
#align order.Ioi_pred_eq_insert_of_not_is_min Order.Ioi_pred_eq_insert_of_not_isMin

theorem Icc_pred_left (h : pred a ≤ b) : Icc (pred a) b = insert (pred a) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Ici_pred, insert_inter_of_mem (mem_Iic.2 h)]
  -- 🎉 no goals
#align order.Icc_pred_left Order.Icc_pred_left

theorem Ico_pred_left (h : pred a < b) : Ico (pred a) b = insert (pred a) (Ico a b) := by
  simp_rw [← Ici_inter_Iio, Ici_pred, insert_inter_of_mem (mem_Iio.2 h)]
  -- 🎉 no goals
#align order.Ico_pred_left Order.Ico_pred_left

section NoMinOrder

variable [NoMinOrder α]

@[simp]
theorem pred_eq_pred_iff : pred a = pred b ↔ a = b := by
  simp_rw [eq_iff_le_not_lt, pred_le_pred_iff, pred_lt_pred_iff]
  -- 🎉 no goals
#align order.pred_eq_pred_iff Order.pred_eq_pred_iff

theorem pred_injective : Injective (pred : α → α) := fun _ _ => pred_eq_pred_iff.1
#align order.pred_injective Order.pred_injective

theorem pred_ne_pred_iff : pred a ≠ pred b ↔ a ≠ b :=
  pred_injective.ne_iff
#align order.pred_ne_pred_iff Order.pred_ne_pred_iff

alias ⟨_, pred_ne_pred⟩ := pred_ne_pred_iff
#align order.pred_ne_pred Order.pred_ne_pred

theorem pred_lt_iff_eq_or_lt : pred a < b ↔ a = b ∨ a < b :=
  pred_lt_iff.trans le_iff_eq_or_lt
#align order.pred_lt_iff_eq_or_lt Order.pred_lt_iff_eq_or_lt

theorem pred_eq_iff_covby : pred b = a ↔ a ⋖ b :=
  ⟨by
    rintro rfl
    -- ⊢ pred b ⋖ b
    exact pred_covby _, Covby.pred_eq⟩
    -- 🎉 no goals
#align order.pred_eq_iff_covby Order.pred_eq_iff_covby

theorem Ioi_pred_eq_insert (a : α) : Ioi (pred a) = insert a (Ioi a) :=
  ext fun _ => pred_lt_iff_eq_or_lt.trans <| or_congr_left eq_comm
#align order.Ioi_pred_eq_insert Order.Ioi_pred_eq_insert

theorem Ico_pred_right_eq_insert (h : a ≤ b) : Ioc (pred a) b = insert a (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iic.2 h)]
  -- 🎉 no goals
#align order.Ico_pred_right_eq_insert Order.Ico_pred_right_eq_insert

theorem Ioo_pred_right_eq_insert (h : a < b) : Ioo (pred a) b = insert a (Ioo a b) := by
  simp_rw [← Ioi_inter_Iio, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iio.2 h)]
  -- 🎉 no goals
#align order.Ioo_pred_right_eq_insert Order.Ioo_pred_right_eq_insert

end NoMinOrder

section OrderBot

variable [OrderBot α]

@[simp]
theorem pred_bot : pred (⊥ : α) = ⊥ :=
  isMin_bot.pred_eq
#align order.pred_bot Order.pred_bot

--Porting note: removing @[simp],`simp` can prove it
theorem le_pred_iff_eq_bot : a ≤ pred a ↔ a = ⊥ :=
  @succ_le_iff_eq_top αᵒᵈ _ _ _ _
#align order.le_pred_iff_eq_bot Order.le_pred_iff_eq_bot

--Porting note: removing @[simp],`simp` can prove it
theorem pred_lt_iff_ne_bot : pred a < a ↔ a ≠ ⊥ :=
  @lt_succ_iff_ne_top αᵒᵈ _ _ _ _
#align order.pred_lt_iff_ne_bot Order.pred_lt_iff_ne_bot

end OrderBot

section OrderTop

variable [OrderTop α]

--Porting note: removing @[simp],`simp` can prove it
theorem pred_top_lt_iff [NoMinOrder α] : pred ⊤ < a ↔ a = ⊤ :=
  @lt_succ_bot_iff αᵒᵈ _ _ _ _ _
#align order.pred_top_lt_iff Order.pred_top_lt_iff

theorem pred_top_le_iff : pred ⊤ ≤ a ↔ a = ⊤ ∨ a = pred ⊤ :=
  @le_succ_bot_iff αᵒᵈ _ _ _ _
#align order.pred_top_le_iff Order.pred_top_le_iff

variable [Nontrivial α]

theorem pred_lt_top (a : α) : pred a < ⊤ :=
  (pred_mono le_top).trans_lt <| pred_lt_of_not_isMin not_isMin_top
#align order.pred_lt_top Order.pred_lt_top

theorem pred_ne_top (a : α) : pred a ≠ ⊤ :=
  (pred_lt_top a).ne
#align order.pred_ne_top Order.pred_ne_top

end OrderTop

end PartialOrder

/-- There is at most one way to define the predecessors in a `PartialOrder`. -/
instance [PartialOrder α] : Subsingleton (PredOrder α) :=
  ⟨by
    intro h₀ h₁
    -- ⊢ h₀ = h₁
    ext a
    -- ⊢ PredOrder.pred a = PredOrder.pred a
    by_cases ha : IsMin a
    -- ⊢ PredOrder.pred a = PredOrder.pred a
    · exact (@IsMin.pred_eq _ _ h₀ _ ha).trans ha.pred_eq.symm
      -- 🎉 no goals
    · exact @Covby.pred_eq _ _ h₀ _ _ (pred_covby_of_not_isMin ha)⟩
      -- 🎉 no goals

section CompleteLattice

variable [CompleteLattice α] [PredOrder α]

theorem pred_eq_iSup (a : α) : pred a = ⨆ (b) (_ : b < a), b := by
  refine' le_antisymm _ (iSup_le fun b => iSup_le le_pred_of_lt)
  -- ⊢ pred a ≤ ⨆ (b : α) (_ : b < a), b
  obtain rfl | ha := eq_or_ne a ⊥
  -- ⊢ pred ⊥ ≤ ⨆ (b : α) (_ : b < ⊥), b
  · rw [pred_bot]
    -- ⊢ ⊥ ≤ ⨆ (b : α) (_ : b < ⊥), b
    exact bot_le
    -- 🎉 no goals
  · exact @le_iSup₂ _ _ (fun b => b < a) _ (fun a _ => a) (pred a) (pred_lt_iff_ne_bot.2 ha)
    -- 🎉 no goals
#align order.pred_eq_supr Order.pred_eq_iSup

end CompleteLattice

/-! ### Successor-predecessor orders -/

section SuccPredOrder

variable [PartialOrder α] [SuccOrder α] [PredOrder α] {a b : α}

@[simp]
theorem succ_pred_of_not_isMin (h : ¬IsMin a) : succ (pred a) = a :=
  Covby.succ_eq (pred_covby_of_not_isMin h)
#align order.succ_pred_of_not_is_min Order.succ_pred_of_not_isMin

@[simp]
theorem pred_succ_of_not_isMax (h : ¬IsMax a) : pred (succ a) = a :=
  Covby.pred_eq (covby_succ_of_not_isMax h)
#align order.pred_succ_of_not_is_max Order.pred_succ_of_not_isMax

--Porting note: removing @[simp],`simp` can prove it
theorem succ_pred [NoMinOrder α] (a : α) : succ (pred a) = a :=
  Covby.succ_eq (pred_covby _)
#align order.succ_pred Order.succ_pred

--Porting note: removing @[simp],`simp` can prove it
theorem pred_succ [NoMaxOrder α] (a : α) : pred (succ a) = a :=
  Covby.pred_eq (covby_succ _)
#align order.pred_succ Order.pred_succ

theorem pred_succ_iterate_of_not_isMax (i : α) (n : ℕ) (hin : ¬IsMax (succ^[n - 1] i)) :
    pred^[n] (succ^[n] i) = i := by
  induction' n with n hn
  -- ⊢ pred^[Nat.zero] (succ^[Nat.zero] i) = i
  · simp only [Nat.zero_eq, Function.iterate_zero, id.def]
    -- 🎉 no goals
  rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at hin
  -- ⊢ pred^[Nat.succ n] (succ^[Nat.succ n] i) = i
  have h_not_max : ¬IsMax (succ^[n - 1] i) := by
    cases' n with n
    · simpa using hin
    rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at hn ⊢
    have h_sub_le : succ^[n] i ≤ succ^[n.succ] i := by
      rw [Function.iterate_succ']
      exact le_succ _
    refine' fun h_max => hin fun j hj => _
    have hj_le : j ≤ succ^[n] i := h_max (h_sub_le.trans hj)
    exact hj_le.trans h_sub_le
  rw [Function.iterate_succ, Function.iterate_succ']
  -- ⊢ (pred^[n] ∘ pred) ((succ ∘ succ^[n]) i) = i
  simp only [Function.comp_apply]
  -- ⊢ pred^[n] (pred (succ (succ^[n] i))) = i
  rw [pred_succ_of_not_isMax hin]
  -- ⊢ pred^[n] (succ^[n] i) = i
  exact hn h_not_max
  -- 🎉 no goals
#align order.pred_succ_iterate_of_not_is_max Order.pred_succ_iterate_of_not_isMax

theorem succ_pred_iterate_of_not_isMin (i : α) (n : ℕ) (hin : ¬IsMin (pred^[n - 1] i)) :
    succ^[n] (pred^[n] i) = i :=
  @pred_succ_iterate_of_not_isMax αᵒᵈ _ _ _ i n hin
#align order.succ_pred_iterate_of_not_is_min Order.succ_pred_iterate_of_not_isMin

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

variable [DecidableEq α] [PartialOrder α] [OrderTop α] [SuccOrder α]

instance : SuccOrder (WithTop α) where
  succ a :=
    match a with
    | ⊤ => ⊤
    | Option.some a => ite (a = ⊤) ⊤ (some (succ a))
  le_succ a := by
    cases' a with a a
    · exact le_top
      -- 🎉 no goals
    change _ ≤ ite _ _ _
    -- ⊢ Option.some a ≤ if a = ⊤ then ⊤ else ↑(succ a)
    split_ifs
    -- ⊢ Option.some a ≤ ⊤
    · exact le_top
      -- 🎉 no goals
    · exact some_le_some.2 (le_succ a)
      -- 🎉 no goals
  max_of_succ_le {a} ha := by
    cases a
    · exact isMax_top
      -- 🎉 no goals
    dsimp only at ha
    -- ⊢ IsMax (Option.some val✝)
    split_ifs at ha with ha'
    -- ⊢ IsMax (Option.some val✝)
    · exact (not_top_le_coe _ ha).elim
      -- 🎉 no goals
    · rw [some_eq_coe, coe_le_coe, succ_le_iff_eq_top] at ha
      -- ⊢ IsMax (Option.some val✝)
      exact (ha' ha).elim
      -- 🎉 no goals
  succ_le_of_lt {a b} h := by
    cases b
    · exact le_top
      -- 🎉 no goals
    cases a
    · exact (not_top_lt h).elim
      -- 🎉 no goals
    rw [some_lt_some] at h
    -- ⊢ (fun a =>
    change ite _ _ _ ≤ _
    -- ⊢ (if val✝ = ⊤ then ⊤ else ↑(succ val✝)) ≤ Option.some val✝¹
    split_ifs with ha
    -- ⊢ ⊤ ≤ Option.some val✝¹
    · rw [ha] at h
      -- ⊢ ⊤ ≤ Option.some val✝¹
      exact (not_top_lt h).elim
      -- 🎉 no goals
    · exact some_le_some.2 (succ_le_of_lt h)
      -- 🎉 no goals
  le_of_lt_succ {a b} h := by
    cases a
    · exact (not_top_lt h).elim
      -- 🎉 no goals
    cases b
    · exact le_top
      -- 🎉 no goals
    dsimp only at h
    -- ⊢ Option.some val✝¹ ≤ Option.some val✝
    rw [some_le_some]
    -- ⊢ val✝¹ ≤ val✝
    split_ifs at h with hb
    -- ⊢ val✝¹ ≤ val✝
    · rw [hb]
      -- ⊢ val✝¹ ≤ ⊤
      exact le_top
      -- 🎉 no goals
    · exact le_of_lt_succ (some_lt_some.1 h)
      -- 🎉 no goals

@[simp]
theorem succ_coe_top : succ ↑(⊤ : α) = (⊤ : WithTop α) :=
  dif_pos rfl
#align with_top.succ_coe_top WithTop.succ_coe_top

theorem succ_coe_of_ne_top {a : α} (h : a ≠ ⊤) : succ (↑a : WithTop α) = ↑(succ a) :=
  dif_neg h
#align with_top.succ_coe_of_ne_top WithTop.succ_coe_of_ne_top

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
    | Option.some a => some_le_some.2 (pred_le a)
  min_of_le_pred {a} ha := by
    cases a
    · exact ((coe_lt_top (⊤ : α)).not_le ha).elim
      -- 🎉 no goals
    · exact (min_of_le_pred <| some_le_some.1 ha).withTop
      -- 🎉 no goals
  le_pred_of_lt {a b} h := by
    cases a
    · exact (le_top.not_lt h).elim
      -- 🎉 no goals
    cases b
    · exact some_le_some.2 le_top
      -- 🎉 no goals
    exact some_le_some.2 (le_pred_of_lt <| some_lt_some.1 h)
    -- 🎉 no goals
  le_of_pred_lt {a b} h := by
    cases b
    · exact le_top
      -- 🎉 no goals
    cases a
    · exact (not_top_lt <| some_lt_some.1 h).elim
      -- 🎉 no goals
    · exact some_le_some.2 (le_of_pred_lt <| some_lt_some.1 h)
      -- 🎉 no goals

@[simp]
theorem pred_top : pred (⊤ : WithTop α) = ↑(⊤ : α) :=
  rfl
#align with_top.pred_top WithTop.pred_top

@[simp]
theorem pred_coe (a : α) : pred (↑a : WithTop α) = ↑(pred a) :=
  rfl
#align with_top.pred_coe WithTop.pred_coe

@[simp]
theorem pred_untop :
    ∀ (a : WithTop α) (ha : a ≠ ⊤),
      pred (a.untop ha) = (pred a).untop (by induction a using WithTop.recTopCoe <;> simp)
                                             -- ⊢ pred ⊤ ≠ ⊤
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
  | ⊤, ha => (ha rfl).elim
  | (a : α), _ => rfl
#align with_top.pred_untop WithTop.pred_untop

end Pred

/-! #### Adding a `⊤` to a `NoMaxOrder` -/

section Succ

variable [Preorder α] [NoMaxOrder α] [SuccOrder α]

instance succOrderOfNoMaxOrder : SuccOrder (WithTop α) where
  succ a :=
    match a with
    | ⊤ => ⊤
    | Option.some a => some (succ a)
  le_succ a := by
    cases' a with a a
    · exact le_top
      -- 🎉 no goals
    · exact some_le_some.2 (le_succ a)
      -- 🎉 no goals
  max_of_succ_le {a} ha := by
    cases a
    · exact isMax_top
      -- 🎉 no goals
    · exact (not_isMax _ <| max_of_succ_le <| some_le_some.1 ha).elim
      -- 🎉 no goals
  succ_le_of_lt {a b} h := by
    cases a
    · exact (not_top_lt h).elim
      -- 🎉 no goals
    cases b
    · exact le_top
      -- 🎉 no goals
    · exact some_le_some.2 (succ_le_of_lt <| some_lt_some.1 h)
      -- 🎉 no goals
  le_of_lt_succ {a b} h := by
    cases a
    · exact (not_top_lt h).elim
      -- 🎉 no goals
    cases b
    · exact le_top
      -- 🎉 no goals
    · exact some_le_some.2 (le_of_lt_succ <| some_lt_some.1 h)
      -- 🎉 no goals
#align with_top.succ_order_of_no_max_order WithTop.succOrderOfNoMaxOrder

@[simp]
theorem succ_coe (a : α) : succ (↑a : WithTop α) = ↑(succ a) :=
  rfl
#align with_top.succ_coe WithTop.succ_coe

end Succ

section Pred

variable [Preorder α] [NoMaxOrder α]

instance [hα : Nonempty α] : IsEmpty (PredOrder (WithTop α)) :=
  ⟨by
    intro
    -- ⊢ False
    cases' h : pred (⊤ : WithTop α) with a ha
    -- ⊢ False
    · exact hα.elim fun a => (min_of_le_pred h.ge).not_lt <| coe_lt_top a
      -- 🎉 no goals
    · obtain ⟨c, hc⟩ := exists_gt a
      -- ⊢ False
      rw [← some_lt_some, ← h] at hc
      -- ⊢ False
      exact (le_of_pred_lt hc).not_lt (some_lt_none _)⟩
      -- 🎉 no goals

end Pred

end WithTop

namespace WithBot

/-! #### Adding a `⊥` to an `OrderBot` -/

section Succ

variable [Preorder α] [OrderBot α] [SuccOrder α]

instance : SuccOrder (WithBot α) where
  succ a :=
    match a with
    | ⊥ => some ⊥
    | Option.some a => some (succ a)
  le_succ a :=
    match a with
    | ⊥ => bot_le
    | Option.some a => some_le_some.2 (le_succ a)
  max_of_succ_le {a} ha := by
    cases a
    · exact ((none_lt_some (⊥ : α)).not_le ha).elim
      -- 🎉 no goals
    · exact (max_of_succ_le <| some_le_some.1 ha).withBot
      -- 🎉 no goals
  succ_le_of_lt {a b} h := by
    cases b
    · exact (not_lt_bot h).elim
      -- 🎉 no goals
    cases a
    · exact some_le_some.2 bot_le
      -- 🎉 no goals
    · exact some_le_some.2 (succ_le_of_lt <| some_lt_some.1 h)
      -- 🎉 no goals
  le_of_lt_succ {a b} h := by
    cases a
    · exact bot_le
      -- 🎉 no goals
    cases b
    · exact (not_lt_bot <| some_lt_some.1 h).elim
      -- 🎉 no goals
    · exact some_le_some.2 (le_of_lt_succ <| some_lt_some.1 h)
      -- 🎉 no goals

@[simp]
theorem succ_bot : succ (⊥ : WithBot α) = ↑(⊥ : α) :=
  rfl
#align with_bot.succ_bot WithBot.succ_bot

@[simp]
theorem succ_coe (a : α) : succ (↑a : WithBot α) = ↑(succ a) :=
  rfl
#align with_bot.succ_coe WithBot.succ_coe

@[simp]
theorem succ_unbot :
    ∀ (a : WithBot α) (ha : a ≠ ⊥),
      succ (a.unbot ha) = (succ a).unbot (by induction a using WithBot.recBotCoe <;> simp)
                                             -- ⊢ succ ⊥ ≠ ⊥
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
  | ⊥, ha => (ha rfl).elim
  | (a : α), _ => rfl
#align with_bot.succ_unbot WithBot.succ_unbot

end Succ

section Pred

variable [DecidableEq α] [PartialOrder α] [OrderBot α] [PredOrder α]

instance : PredOrder (WithBot α) where
  pred a :=
    match a with
    | ⊥ => ⊥
    | Option.some a => ite (a = ⊥) ⊥ (some (pred a))
  pred_le a := by
    cases' a with a a
    · exact bot_le
      -- 🎉 no goals
    change ite _ _ _ ≤ _
    -- ⊢ (if a = ⊥ then ⊥ else ↑(pred a)) ≤ Option.some a
    split_ifs
    -- ⊢ ⊥ ≤ Option.some a
    · exact bot_le
      -- 🎉 no goals
    · exact some_le_some.2 (pred_le a)
      -- 🎉 no goals
  min_of_le_pred {a} ha := by
    cases' a with a a
    · exact isMin_bot
      -- 🎉 no goals
    dsimp only at ha
    -- ⊢ IsMin (Option.some a)
    split_ifs at ha with ha'
    -- ⊢ IsMin (Option.some a)
    · exact (not_coe_le_bot _ ha).elim
      -- 🎉 no goals
    · rw [some_eq_coe, coe_le_coe, le_pred_iff_eq_bot] at ha
      -- ⊢ IsMin (Option.some a)
      exact (ha' ha).elim
      -- 🎉 no goals
  le_pred_of_lt {a b} h := by
    cases a
    · exact bot_le
      -- 🎉 no goals
    cases b
    · exact (not_lt_bot h).elim
      -- 🎉 no goals
    rw [some_lt_some] at h
    -- ⊢ Option.some val✝¹ ≤
    change _ ≤ ite _ _ _
    -- ⊢ Option.some val✝¹ ≤ if val✝ = ⊥ then ⊥ else ↑(pred val✝)
    split_ifs with hb
    -- ⊢ Option.some val✝¹ ≤ ⊥
    · rw [hb] at h
      -- ⊢ Option.some val✝¹ ≤ ⊥
      exact (not_lt_bot h).elim
      -- 🎉 no goals
    · exact some_le_some.2 (le_pred_of_lt h)
      -- 🎉 no goals
  le_of_pred_lt {a b} h := by
    cases b
    · exact (not_lt_bot h).elim
      -- 🎉 no goals
    cases a
    · exact bot_le
      -- 🎉 no goals
    dsimp only at h
    -- ⊢ Option.some val✝ ≤ Option.some val✝¹
    rw [some_le_some]
    -- ⊢ val✝ ≤ val✝¹
    split_ifs at h with ha
    -- ⊢ val✝ ≤ val✝¹
    · rw [ha]
      -- ⊢ ⊥ ≤ val✝¹
      exact bot_le
      -- 🎉 no goals
    · exact le_of_pred_lt (some_lt_some.1 h)
      -- 🎉 no goals

@[simp]
theorem pred_coe_bot : pred ↑(⊥ : α) = (⊥ : WithBot α) :=
  dif_pos rfl
#align with_bot.pred_coe_bot WithBot.pred_coe_bot

theorem pred_coe_of_ne_bot {a : α} (h : a ≠ ⊥) : pred (↑a : WithBot α) = ↑(pred a) :=
  dif_neg h
#align with_bot.pred_coe_of_ne_bot WithBot.pred_coe_of_ne_bot

end Pred

/-! #### Adding a `⊥` to a `NoMinOrder` -/

section Succ

variable [Preorder α] [NoMinOrder α]

instance [hα : Nonempty α] : IsEmpty (SuccOrder (WithBot α)) :=
  ⟨by
    intro
    -- ⊢ False
    cases' h : succ (⊥ : WithBot α) with a ha
    -- ⊢ False
    · exact hα.elim fun a => (max_of_succ_le h.le).not_lt <| bot_lt_coe a
      -- 🎉 no goals
    · obtain ⟨c, hc⟩ := exists_lt a
      -- ⊢ False
      rw [← some_lt_some, ← h] at hc
      -- ⊢ False
      exact (le_of_lt_succ hc).not_lt (none_lt_some _)⟩
      -- 🎉 no goals

end Succ

section Pred

variable [Preorder α] [NoMinOrder α] [PredOrder α]

instance predOrderOfNoMinOrder : PredOrder (WithBot α) where
  pred a :=
    match a with
    | ⊥ => ⊥
    | Option.some a => some (pred a)
  pred_le a := by
    cases' a with a a
    · exact bot_le
      -- 🎉 no goals
    · exact some_le_some.2 (pred_le a)
      -- 🎉 no goals
  min_of_le_pred {a} ha := by
    cases a
    · exact isMin_bot
      -- 🎉 no goals
    · exact (not_isMin _ <| min_of_le_pred <| some_le_some.1 ha).elim
      -- 🎉 no goals
  le_pred_of_lt {a b} h := by
    cases b
    · exact (not_lt_bot h).elim
      -- 🎉 no goals
    cases a
    · exact bot_le
      -- 🎉 no goals
    · exact some_le_some.2 (le_pred_of_lt <| some_lt_some.1 h)
      -- 🎉 no goals
  le_of_pred_lt {a b} h := by
    cases b
    · exact (not_lt_bot h).elim
      -- 🎉 no goals
    cases a
    · exact bot_le
      -- 🎉 no goals
    · exact some_le_some.2 (le_of_pred_lt <| some_lt_some.1 h)
      -- 🎉 no goals
#align with_bot.pred_order_of_no_min_order WithBot.predOrderOfNoMinOrder

@[simp]
theorem pred_coe (a : α) : pred (↑a : WithBot α) = ↑(pred a) :=
  rfl
#align with_bot.pred_coe WithBot.pred_coe

end Pred

end WithBot

/-! ### Archimedeanness -/

/-- A `SuccOrder` is succ-archimedean if one can go from any two comparable elements by iterating
`succ` -/
class IsSuccArchimedean (α : Type*) [Preorder α] [SuccOrder α] : Prop where
  /-- If `a ≤ b` then one can get to `a` from `b` by iterating `succ` -/
  exists_succ_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, succ^[n] a = b
#align is_succ_archimedean IsSuccArchimedean

/-- A `PredOrder` is pred-archimedean if one can go from any two comparable elements by iterating
`pred` -/
class IsPredArchimedean (α : Type*) [Preorder α] [PredOrder α] : Prop where
  /-- If `a ≤ b` then one can get to `b` from `a` by iterating `pred` -/
  exists_pred_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, pred^[n] b = a
#align is_pred_archimedean IsPredArchimedean

export IsSuccArchimedean (exists_succ_iterate_of_le)

export IsPredArchimedean (exists_pred_iterate_of_le)

section Preorder

variable [Preorder α]

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

instance : IsPredArchimedean αᵒᵈ :=
  ⟨fun {a b} h => by convert exists_succ_iterate_of_le h.ofDual⟩
                     -- 🎉 no goals

theorem LE.le.exists_succ_iterate (h : a ≤ b) : ∃ n, succ^[n] a = b :=
  exists_succ_iterate_of_le h
#align has_le.le.exists_succ_iterate LE.le.exists_succ_iterate

theorem exists_succ_iterate_iff_le : (∃ n, succ^[n] a = b) ↔ a ≤ b := by
  refine' ⟨_, exists_succ_iterate_of_le⟩
  -- ⊢ (∃ n, succ^[n] a = b) → a ≤ b
  rintro ⟨n, rfl⟩
  -- ⊢ a ≤ succ^[n] a
  exact id_le_iterate_of_id_le le_succ n a
  -- 🎉 no goals
#align exists_succ_iterate_iff_le exists_succ_iterate_iff_le

/-- Induction principle on a type with a `SuccOrder` for all elements above a given element `m`. -/
@[elab_as_elim]
theorem Succ.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (succ n)) ⦃n : α⦄
    (hmn : m ≤ n) : P n := by
  obtain ⟨n, rfl⟩ := hmn.exists_succ_iterate; clear hmn
  -- ⊢ P (succ^[n] m)
                                              -- ⊢ P (succ^[n] m)
  induction' n with n ih
  -- ⊢ P (succ^[Nat.zero] m)
  · exact h0
    -- 🎉 no goals
  · rw [Function.iterate_succ_apply']
    -- ⊢ P (succ (succ^[n] m))
    exact h1 _ (id_le_iterate_of_id_le le_succ n m) ih
    -- 🎉 no goals
#align succ.rec Succ.rec

theorem Succ.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) {a b : α} (h : a ≤ b) :
    p a ↔ p b := by
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate
  -- ⊢ p a ↔ p (succ^[n] a)
  exact Iterate.rec (fun b => p a ↔ p b) (fun c hc => hc.trans (hsucc _)) Iff.rfl n
  -- 🎉 no goals
#align succ.rec_iff Succ.rec_iff

end SuccOrder

section PredOrder

variable [PredOrder α] [IsPredArchimedean α] {a b : α}

instance : IsSuccArchimedean αᵒᵈ :=
  ⟨fun {a b} h => by convert exists_pred_iterate_of_le h.ofDual⟩
                     -- 🎉 no goals

theorem LE.le.exists_pred_iterate (h : a ≤ b) : ∃ n, pred^[n] b = a :=
  exists_pred_iterate_of_le h
#align has_le.le.exists_pred_iterate LE.le.exists_pred_iterate

theorem exists_pred_iterate_iff_le : (∃ n, pred^[n] b = a) ↔ a ≤ b :=
  @exists_succ_iterate_iff_le αᵒᵈ _ _ _ _ _
#align exists_pred_iterate_iff_le exists_pred_iterate_iff_le

/-- Induction principle on a type with a `PredOrder` for all elements below a given element `m`. -/
@[elab_as_elim]
theorem Pred.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, n ≤ m → P n → P (pred n)) ⦃n : α⦄
    (hmn : n ≤ m) : P n :=
  @Succ.rec αᵒᵈ _ _ _ _ _ h0 h1 _ hmn
#align pred.rec Pred.rec

theorem Pred.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) {a b : α} (h : a ≤ b) :
    p a ↔ p b :=
  (@Succ.rec_iff αᵒᵈ _ _ _ _ hsucc _ _ h).symm
#align pred.rec_iff Pred.rec_iff

end PredOrder

end Preorder

section LinearOrder

variable [LinearOrder α]

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

theorem exists_succ_iterate_or : (∃ n, succ^[n] a = b) ∨ ∃ n, succ^[n] b = a :=
  (le_total a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le
#align exists_succ_iterate_or exists_succ_iterate_or

theorem Succ.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) (a b : α) : p a ↔ p b :=
  (le_total a b).elim (Succ.rec_iff hsucc) fun h => (Succ.rec_iff hsucc h).symm
#align succ.rec_linear Succ.rec_linear

end SuccOrder

section PredOrder

variable [PredOrder α] [IsPredArchimedean α] {a b : α}

theorem exists_pred_iterate_or : (∃ n, pred^[n] b = a) ∨ ∃ n, pred^[n] a = b :=
  (le_total a b).imp exists_pred_iterate_of_le exists_pred_iterate_of_le
#align exists_pred_iterate_or exists_pred_iterate_or

theorem Pred.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) (a b : α) : p a ↔ p b :=
  (le_total a b).elim (Pred.rec_iff hsucc) fun h => (Pred.rec_iff hsucc h).symm
#align pred.rec_linear Pred.rec_linear

end PredOrder

end LinearOrder

section IsWellOrder

variable [LinearOrder α]

instance (priority := 100) IsWellOrder.toIsPredArchimedean [h : IsWellOrder α (· < ·)]
    [PredOrder α] : IsPredArchimedean α :=
  ⟨fun {a b} => by
    refine' WellFounded.fix (C := fun b => a ≤ b → ∃ n, Nat.iterate pred n b = a)
      h.wf _ b
    intros b ih hab
    -- ⊢ ∃ n, pred^[n] b = a
    replace hab := eq_or_lt_of_le hab
    -- ⊢ ∃ n, pred^[n] b = a
    rcases hab with (rfl | hab)
    -- ⊢ ∃ n, pred^[n] a = a
    · exact ⟨0, rfl⟩
      -- 🎉 no goals
    cases' le_or_lt b (pred b) with hb hb
    -- ⊢ ∃ n, pred^[n] b = a
    · cases (min_of_le_pred hb).not_lt hab
      -- 🎉 no goals
    dsimp at ih
    -- ⊢ ∃ n, pred^[n] b = a
    obtain ⟨k, hk⟩ := ih (pred b) hb (le_pred_of_lt hab)
    -- ⊢ ∃ n, pred^[n] b = a
    refine' ⟨k + 1, _⟩
    -- ⊢ pred^[k + 1] b = a
    rw [iterate_add_apply, iterate_one, hk]⟩
    -- 🎉 no goals
#align is_well_order.to_is_pred_archimedean IsWellOrder.toIsPredArchimedean

instance (priority := 100) IsWellOrder.toIsSuccArchimedean [h : IsWellOrder α (· > ·)]
    [SuccOrder α] : IsSuccArchimedean α :=
  let h : IsPredArchimedean αᵒᵈ := by infer_instance
                                      -- 🎉 no goals
  ⟨h.1⟩
#align is_well_order.to_is_succ_archimedean IsWellOrder.toIsSuccArchimedean

end IsWellOrder

section OrderBot

variable [Preorder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]

theorem Succ.rec_bot (p : α → Prop) (hbot : p ⊥) (hsucc : ∀ a, p a → p (succ a)) (a : α) : p a :=
  Succ.rec hbot (fun x _ h => hsucc x h) (bot_le : ⊥ ≤ a)
#align succ.rec_bot Succ.rec_bot

end OrderBot

section OrderTop

variable [Preorder α] [OrderTop α] [PredOrder α] [IsPredArchimedean α]

theorem Pred.rec_top (p : α → Prop) (htop : p ⊤) (hpred : ∀ a, p a → p (pred a)) (a : α) : p a :=
  Pred.rec htop (fun x _ h => hpred x h) (le_top : a ≤ ⊤)
#align pred.rec_top Pred.rec_top

end OrderTop

lemma SuccOrder.forall_ne_bot_iff
    [Nontrivial α] [PartialOrder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]
    (P : α → Prop) :
    (∀ i, i ≠ ⊥ → P i) ↔ (∀ i, P (SuccOrder.succ i)) := by
  refine' ⟨fun h i ↦ h _ (Order.succ_ne_bot i), fun h i hi ↦ _⟩
  -- ⊢ P i
  obtain ⟨j, rfl⟩ := exists_succ_iterate_of_le (bot_le : ⊥ ≤ i)
  -- ⊢ P (Order.succ^[j] ⊥)
  have hj : 0 < j := by apply Nat.pos_of_ne_zero; contrapose! hi; simp [hi]
  -- ⊢ P (Order.succ^[j] ⊥)
  rw [← Nat.succ_pred_eq_of_pos hj]
  -- ⊢ P (Order.succ^[Nat.succ (Nat.pred j)] ⊥)
  simp only [Function.iterate_succ', Function.comp_apply]
  -- ⊢ P (Order.succ (Order.succ^[Nat.pred j] ⊥))
  apply h
  -- 🎉 no goals
