/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.FinsetOps
public import Mathlib.Data.Multiset.Fold

/-!
# Lattice operations on multisets

This file defines `Multiset.sup` and derives the dual `Multiset.inf` and their basic lemmas
via `to_dual`.
-/

@[expose] public section


namespace Multiset

variable {α : Type*}

-- `sup` can be defined with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
-- `inf` can be defined with just `[Top α]` where some lemmas hold without requiring `[OrderTop α]`
variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a multiset: `sup {a, b, c} = a ⊔ b ⊔ c` -/
@[to_dual /-- Infimum of a multiset: `inf {a, b, c} = a ⊓ b ⊓ c` -/]
def sup (s : Multiset α) : α :=
  s.fold (· ⊔ ·) ⊥

@[to_dual (attr := simp)]
theorem sup_coe (l : List α) : sup (l : Multiset α) = l.foldr (· ⊔ ·) ⊥ :=
  rfl

@[to_dual (attr := simp)]
theorem sup_zero : (0 : Multiset α).sup = ⊥ :=
  fold_zero _ _

@[to_dual (attr := simp)]
theorem sup_cons (a : α) (s : Multiset α) : (a ::ₘ s).sup = a ⊔ s.sup :=
  fold_cons_left _ _ _ _

@[to_dual (attr := simp)]
theorem sup_singleton {a : α} : ({a} : Multiset α).sup = a := sup_bot_eq _

@[to_dual (attr := simp)]
theorem sup_add (s₁ s₂ : Multiset α) : (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup :=
  Eq.trans (by simp [sup]) (fold_add _ _ _ _ _)

@[to_dual (attr := simp) le_inf]
theorem sup_le {s : Multiset α} {a : α} : s.sup ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and])

@[to_dual inf_le]
theorem le_sup {s : Multiset α} {a : α} (h : a ∈ s) : a ≤ s.sup :=
  sup_le.1 le_rfl _ h

@[to_dual (attr := gcongr)]
theorem sup_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.sup ≤ s₂.sup :=
  sup_le.2 fun _ hb => le_sup (h hb)

variable [DecidableEq α]

@[to_dual (attr := simp)]
theorem sup_dedup (s : Multiset α) : (dedup s).sup = s.sup :=
  fold_dedup_idem _ _ _

@[to_dual (attr := simp)]
theorem sup_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add]; simp

@[to_dual (attr := simp)]
theorem sup_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).sup = s₁.sup ⊔ s₂.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add]; simp

@[to_dual (attr := simp)]
theorem sup_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).sup = a ⊔ s.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_cons]; simp

theorem nodup_sup_iff {α : Type*} [DecidableEq α] {m : Multiset (Multiset α)} :
    m.sup.Nodup ↔ ∀ a : Multiset α, a ∈ m → a.Nodup := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons _ _ h => simp [h]

end Multiset
