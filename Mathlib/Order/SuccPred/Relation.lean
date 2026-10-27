/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Order.SuccPred.Archimedean

/-!
# Relations on types with a `SuccOrder`

This file contains properties about relations on types with a `SuccOrder`
and their closure operations (like the transitive closure).
-/

public section

open Function Order Relation Set

section PartialOrder

variable {α : Type*} [PartialOrder α] [SuccOrder α] [IsSuccArchimedean α]

/-- For `n ≤ m`, `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ succ i`
for all `i` between `n` and `m`. -/
@[to_dual reflTransGen_of_pred_of_ge
/-- For `m ≤ n`, `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ pred i`
for all `i` between `m` and `n`. -/]
theorem reflTransGen_of_succ_of_le (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ico n m, r i (succ i))
    (hnm : n ≤ m) : ReflTransGen r n m := by
  revert h; refine Succ.rec ?_ ?_ hnm
  · intro _
    exact ReflTransGen.refl
  · intro m hnm ih h
    have : ReflTransGen r n m := ih fun i hi => h i ⟨hi.1, hi.2.trans_le <| le_succ m⟩
    rcases (le_succ m).eq_or_lt with hm | hm
    · rwa [← hm]
    exact this.tail (h m ⟨hnm, hm⟩)

/-- For `m ≤ n`, `(n, m)` is in the reflexive-transitive closure of `~` if `succ i ~ i`
for all `i` between `m` and `n`. -/
@[to_dual reflTransGen_of_pred_of_le
/-- For `n ≤ m`, `(n, m)` is in the reflexive-transitive closure of `~` if `pred i ~ i`
for all `i` between `n` and `m`. -/]
theorem reflTransGen_of_succ_of_ge (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ico m n, r (succ i) i)
    (hmn : m ≤ n) : ReflTransGen r n m := by
  rw [← reflTransGen_swap]
  exact reflTransGen_of_succ_of_le (swap r) h hmn

/-- For `n < m`, `(n, m)` is in the transitive closure of a relation `~` if `i ~ succ i`
for all `i` between `n` and `m`. -/
@[to_dual transGen_of_pred_of_gt
/-- For `m < n`, `(n, m)` is in the transitive closure of a relation `~` if `i ~ pred i`
for all `i` between `m` and `n`. -/]
theorem transGen_of_succ_of_lt (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ico n m, r i (succ i))
    (hnm : n < m) : TransGen r n m :=
  (reflTransGen_iff_eq_or_transGen.mp <| reflTransGen_of_succ_of_le r h hnm.le).resolve_left
    hnm.ne'

/-- For `m < n`, `(n, m)` is in the transitive closure of a relation `~` if `succ i ~ i`
for all `i` between `m` and `n`. -/
@[to_dual transGen_of_pred_of_lt
/-- For `n < m`, `(n, m)` is in the transitive closure of a relation `~` if `pred i ~ i`
for all `i` between `n` and `m`. -/]
theorem transGen_of_succ_of_gt (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ico m n, r (succ i) i)
    (hmn : m < n) : TransGen r n m :=
  (reflTransGen_iff_eq_or_transGen.mp <| reflTransGen_of_succ_of_ge r h hmn.le).resolve_left
    hmn.ne

end PartialOrder

section LinearOrder

variable {α : Type*} [LinearOrder α] [SuccOrder α] [IsSuccArchimedean α]

/-- `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ succ i` and `succ i ~ i`
for all `i` between `n` and `m`. -/
@[to_dual
/-- `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ pred i` and `pred i ~ i`
for all `i` between `m` and `n`. -/]
theorem reflTransGen_of_succ (r : α → α → Prop) {n m : α} (h1 : ∀ i ∈ Ico n m, r i (succ i))
    (h2 : ∀ i ∈ Ico m n, r (succ i) i) : ReflTransGen r n m :=
  (le_total n m).elim (reflTransGen_of_succ_of_le r h1) <| reflTransGen_of_succ_of_ge r h2

/-- For `n ≠ m`, `(n, m)` is in the transitive closure of a relation `~` if `i ~ succ i` and
`succ i ~ i` for all `i` between `n` and `m`. -/
@[to_dual
/-- For `n ≠ m`, `(n, m)` is in the transitive closure of a relation `~` if `i ~ pred i` and
`pred i ~ i` for all `i` between `m` and `n`. -/]
theorem transGen_of_succ_of_ne (r : α → α → Prop) {n m : α} (h1 : ∀ i ∈ Ico n m, r i (succ i))
    (h2 : ∀ i ∈ Ico m n, r (succ i) i) (hnm : n ≠ m) : TransGen r n m :=
  (reflTransGen_iff_eq_or_transGen.mp (reflTransGen_of_succ r h1 h2)).resolve_left hnm.symm

/-- `(n, m)` is in the transitive closure of a reflexive relation `~` if `i ~ succ i` and
`succ i ~ i` for all `i` between `n` and `m`. -/
@[to_dual
/-- `(n, m)` is in the transitive closure of a reflexive relation `~` if `i ~ pred i` and
`pred i ~ i` for all `i` between `m` and `n`. -/]
theorem transGen_of_succ_of_refl (r : α → α → Prop) {n m : α} [Std.Refl r]
    (h1 : ∀ i ∈ Ico n m, r i (succ i)) (h2 : ∀ i ∈ Ico m n, r (succ i) i) : TransGen r n m := by
  rcases eq_or_ne m n with (rfl | hmn); · exact TransGen.single (refl m)
  exact transGen_of_succ_of_ne r h1 h2 hmn.symm

end LinearOrder
