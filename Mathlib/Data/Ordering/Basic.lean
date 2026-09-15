/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Yuyang Zhao
-/
module

public import Mathlib.Init

/-!
# Helper definitions and instances for `Ordering`
-/

@[expose] public section

universe u

variable {α : Type*}

namespace Ordering

/-- `Compares o a b` means that `a` and `b` have the ordering relation `o` between them, assuming
that the relation `a < b` is defined. -/
def Compares [LT α] : Ordering → α → α → Prop
  | lt, a, b => a < b
  | eq, a, b => a = b
  | gt, a, b => a > b

@[simp] lemma compares_lt [LT α] (a b : α) : Compares lt a b = (a < b) := rfl

@[simp] lemma compares_eq [LT α] (a b : α) : Compares eq a b = (a = b) := rfl

@[simp] lemma compares_gt [LT α] (a b : α) : Compares gt a b = (a > b) := rfl

/-- `o₁.dthen fun h => o₂(h)` is like `o₁.then o₂` but `o₂` is allowed to depend on
`h : o₁ = .eq`. -/
@[macro_inline] def dthen :
    (o : Ordering) → (o = .eq → Ordering) → Ordering
  | .eq, f => f rfl
  | o, _ => o

end Ordering

/--
Lift a decidable relation to an `Ordering`,
assuming that incomparable terms are `Ordering.eq`.
-/
def cmpUsing (lt : α → α → Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq

/--
Construct an `Ordering` from a type with a decidable `LT` instance,
assuming that incomparable terms are `Ordering.eq`.
-/
def cmp [LT α] [DecidableLT α] (a b : α) : Ordering :=
  cmpUsing (· < ·) a b

variable [LE α] [DecidableLE α]

/-- Like `cmp`, but uses a `≤` on the type instead of `<`. Given two elements `x` and `y`, returns a
three-way comparison result `Ordering`. -/
def cmpLE (x y : α) : Ordering :=
  if x ≤ y then if y ≤ x then Ordering.eq else Ordering.lt else Ordering.gt

theorem cmpLE_swap [Std.Total (α := α) (· ≤ ·)] (x y : α) :
    (cmpLE x y).swap = cmpLE y x := by
  by_cases xy : x ≤ y <;> by_cases yx : y ≤ x <;> simp [cmpLE, *, Ordering.swap]
  cases not_or_intro xy yx (Std.Total.total _ _)

theorem isLE_cmpLE {x y : α} :
    (cmpLE x y).isLE ↔ x ≤ y := by
  rw [cmpLE]
  (repeat' split) <;> simpa

theorem isGE_cmpLE [Std.Total (α := α) (· ≤ ·)] {x y : α} :
    (cmpLE x y).isGE ↔ y ≤ x := by
  rw [← Ordering.isLE_swap, cmpLE_swap, isLE_cmpLE]

@[simp]
theorem cmpLE_eq_lt [LT α] [Std.LawfulOrderLT α] {x y : α} :
    cmpLE x y = .lt ↔ x < y := by
  rw [Std.LawfulOrderLT.lt_iff, cmpLE]
  (repeat' split) <;> simp [*]

@[simp]
theorem cmpLE_eq_gt [LT α] [Std.LawfulOrderLT α] [Std.Total (α := α) (· ≤ ·)] {x y : α} :
    cmpLE x y = .gt ↔ y < x := by
  rw [Std.LawfulOrderLT.lt_iff, ← isGE_cmpLE, ← isLE_cmpLE]
  cases cmpLE x y <;> decide

@[simp]
theorem cmpLE_eq_eq [Std.Refl (α := α) (· ≤ ·)] [Std.Antisymm (α := α) (· ≤ ·)] {x y : α} :
    cmpLE x y = .eq ↔ x = y := by
  refine Iff.trans ?_ Std.le_antisymm_iff
  rw [cmpLE]
  (repeat' split) <;> simp [*]

theorem compareOfLessAndEq_eq_cmpLE [LT α] [DecidableLT α] [DecidableEq α] [Std.LawfulOrderLT α]
    [Std.Total (α := α) (· ≤ ·)] [Std.Antisymm (α := α) (· ≤ ·)] (x y : α) :
    compareOfLessAndEq x y = cmpLE x y := by
  rw [eq_comm, compareOfLessAndEq]
  simp only [← cmpLE_eq_lt, ← cmpLE_eq_eq (α := α)]
  cases cmpLE x y <;> decide
