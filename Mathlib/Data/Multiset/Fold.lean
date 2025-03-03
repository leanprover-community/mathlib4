/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Dedup

/-!
# The fold operation for a commutative associative operation over a multiset.
-/

namespace Multiset

variable {α β : Type*}

/-! ### fold -/


section Fold

variable (op : α → α → α) [hc : Std.Commutative op] [ha : Std.Associative op]

local notation a " * " b => op a b

/-- `fold op b s` folds a commutative associative operation `op` over
  the multiset `s`. -/
def fold : α → Multiset α → α :=
  foldr op

theorem fold_eq_foldr (b : α) (s : Multiset α) :
    fold op b s = foldr op b s :=
  rfl

@[simp]
theorem coe_fold_r (b : α) (l : List α) : fold op b l = l.foldr op b :=
  rfl

theorem coe_fold_l (b : α) (l : List α) : fold op b l = l.foldl op b :=
  (coe_foldr_swap op b l).trans <| by simp [hc.comm]

theorem fold_eq_foldl (b : α) (s : Multiset α) :
    fold op b s = foldl op b s :=
  Quot.inductionOn s fun _ => coe_fold_l _ _ _

@[simp]
theorem fold_zero (b : α) : (0 : Multiset α).fold op b = b :=
  rfl

@[simp]
theorem fold_cons_left : ∀ (b a : α) (s : Multiset α), (a ::ₘ s).fold op b = a * s.fold op b :=
  foldr_cons _

theorem fold_cons_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op b * a := by
  simp [hc.comm]

theorem fold_cons'_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (b * a) := by
  rw [fold_eq_foldl, foldl_cons, ← fold_eq_foldl]

theorem fold_cons'_left (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (a * b) := by
  rw [fold_cons'_right, hc.comm]

theorem fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) :
    (s₁ + s₂).fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂ :=
  Multiset.induction_on s₂
    (by rw [Multiset.add_zero, fold_zero, ← fold_cons'_right, ← fold_cons_right op])
    (fun a b h => by rw [fold_cons_left, add_cons, fold_cons_left, h, ← ha.assoc, hc.comm a,
      ha.assoc])

theorem fold_singleton (b a : α) : ({a} : Multiset α).fold op b = a * b :=
  foldr_singleton _ _ _

theorem fold_distrib {f g : β → α} (u₁ u₂ : α) (s : Multiset β) :
    (s.map fun x => f x * g x).fold op (u₁ * u₂) = (s.map f).fold op u₁ * (s.map g).fold op u₂ :=
  Multiset.induction_on s (by simp) (fun a b h => by
    rw [map_cons, fold_cons_left, h, map_cons, fold_cons_left, map_cons,
      fold_cons_right, ha.assoc, ← ha.assoc (g a), hc.comm (g a),
      ha.assoc, hc.comm (g a), ha.assoc])

theorem fold_hom {op' : β → β → β} [Std.Commutative op'] [Std.Associative op'] {m : α → β}
    (hm : ∀ x y, m (op x y) = op' (m x) (m y)) (b : α) (s : Multiset α) :
    (s.map m).fold op' (m b) = m (s.fold op b) :=
  Multiset.induction_on s (by simp) (by simp +contextual [hm])

theorem fold_union_inter [DecidableEq α] (s₁ s₂ : Multiset α) (b₁ b₂ : α) :
    ((s₁ ∪ s₂).fold op b₁ * (s₁ ∩ s₂).fold op b₂) = s₁.fold op b₁ * s₂.fold op b₂ := by
  rw [← fold_add op, union_add_inter, fold_add op]

@[simp]
theorem fold_dedup_idem [DecidableEq α] [hi : Std.IdempotentOp op] (s : Multiset α) (b : α) :
    (dedup s).fold op b = s.fold op b :=
  Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a ∈ s <;> simp [IH, h]
    show fold op b s = op a (fold op b s)
    rw [← cons_erase h, fold_cons_left, ← ha.assoc, hi.idempotent]

end Fold

end Multiset
