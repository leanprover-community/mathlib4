/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Data.Multiset.Fold

#align_import data.multiset.lattice from "leanprover-community/mathlib"@"65a1391a0106c9204fe45bc73a039f056558cb83"

/-!
# Lattice operations on multisets
-/


namespace Multiset

variable {α : Type*}

/-! ### sup -/


section Sup

-- can be defined with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a multiset: `sup {a, b, c} = a ⊔ b ⊔ c` -/
def sup (s : Multiset α) : α :=
  s.fold (· ⊔ ·) ⊥
#align multiset.sup Multiset.sup

@[simp]
lemma sup_coe (l : List α) : sup (l : Multiset α) = l.foldr (· ⊔ ·) ⊥ :=
  rfl
#align multiset.sup_coe Multiset.sup_coe

@[simp]
lemma sup_zero : (0 : Multiset α).sup = ⊥ :=
  fold_zero _ _
#align multiset.sup_zero Multiset.sup_zero

@[simp]
lemma sup_cons (a : α) (s : Multiset α) : (a ::ₘ s).sup = a ⊔ s.sup :=
  fold_cons_left _ _ _ _
#align multiset.sup_cons Multiset.sup_cons

@[simp]
lemma sup_singleton {a : α} : ({a} : Multiset α).sup = a := sup_bot_eq _
#align multiset.sup_singleton Multiset.sup_singleton

@[simp]
lemma sup_add (s₁ s₂ : Multiset α) : (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup :=
  Eq.trans (by simp [sup]) (fold_add _ _ _ _ _)
#align multiset.sup_add Multiset.sup_add

@[simp]
lemma sup_le {s : Multiset α} {a : α} : s.sup ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  Multiset.induction_on s (by simp)
    (by simp (config := { contextual := true }) [or_imp, forall_and])
#align multiset.sup_le Multiset.sup_le

lemma le_sup {s : Multiset α} {a : α} (h : a ∈ s) : a ≤ s.sup :=
  sup_le.1 le_rfl _ h
#align multiset.le_sup Multiset.le_sup

lemma sup_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.sup ≤ s₂.sup :=
  sup_le.2 fun _ hb => le_sup (h hb)
#align multiset.sup_mono Multiset.sup_mono

variable [DecidableEq α]

@[simp]
lemma sup_dedup (s : Multiset α) : (dedup s).sup = s.sup :=
  fold_dedup_idem _ _ _
#align multiset.sup_dedup Multiset.sup_dedup

@[simp]
lemma sup_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add]; simp
#align multiset.sup_ndunion Multiset.sup_ndunion

@[simp]
lemma sup_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).sup = s₁.sup ⊔ s₂.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add]; simp
#align multiset.sup_union Multiset.sup_union

@[simp]
lemma sup_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).sup = a ⊔ s.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_cons]; simp
#align multiset.sup_ndinsert Multiset.sup_ndinsert

lemma nodup_sup_iff {α : Type*} [DecidableEq α] {m : Multiset (Multiset α)} :
    m.sup.Nodup ↔ ∀ a : Multiset α, a ∈ m → a.Nodup := by
  -- Porting note: this was originally `apply m.induction_on`, which failed due to
  -- `failed to elaborate eliminator, expected type is not available`
  induction' m using Multiset.induction_on with _ _ h
  · simp
  · simp [h]
#align multiset.nodup_sup_iff Multiset.nodup_sup_iff

end Sup

/-! ### inf -/


section Inf

-- can be defined with just `[Top α]` where some lemmas hold without requiring `[OrderTop α]`
variable [SemilatticeInf α] [OrderTop α]

/-- Infimum of a multiset: `inf {a, b, c} = a ⊓ b ⊓ c` -/
def inf (s : Multiset α) : α :=
  s.fold (· ⊓ ·) ⊤
#align multiset.inf Multiset.inf

@[simp]
lemma inf_coe (l : List α) : inf (l : Multiset α) = l.foldr (· ⊓ ·) ⊤ :=
  rfl
#align multiset.inf_coe Multiset.inf_coe

@[simp]
lemma inf_zero : (0 : Multiset α).inf = ⊤ :=
  fold_zero _ _
#align multiset.inf_zero Multiset.inf_zero

@[simp]
lemma inf_cons (a : α) (s : Multiset α) : (a ::ₘ s).inf = a ⊓ s.inf :=
  fold_cons_left _ _ _ _
#align multiset.inf_cons Multiset.inf_cons

@[simp]
lemma inf_singleton {a : α} : ({a} : Multiset α).inf = a := inf_top_eq _
#align multiset.inf_singleton Multiset.inf_singleton

@[simp]
lemma inf_add (s₁ s₂ : Multiset α) : (s₁ + s₂).inf = s₁.inf ⊓ s₂.inf :=
  Eq.trans (by simp [inf]) (fold_add _ _ _ _ _)
#align multiset.inf_add Multiset.inf_add

@[simp]
lemma le_inf {s : Multiset α} {a : α} : a ≤ s.inf ↔ ∀ b ∈ s, a ≤ b :=
  Multiset.induction_on s (by simp)
    (by simp (config := { contextual := true }) [or_imp, forall_and])
#align multiset.le_inf Multiset.le_inf

lemma inf_le {s : Multiset α} {a : α} (h : a ∈ s) : s.inf ≤ a :=
  le_inf.1 le_rfl _ h
#align multiset.inf_le Multiset.inf_le

lemma inf_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₂.inf ≤ s₁.inf :=
  le_inf.2 fun _ hb => inf_le (h hb)
#align multiset.inf_mono Multiset.inf_mono

variable [DecidableEq α]

@[simp]
lemma inf_dedup (s : Multiset α) : (dedup s).inf = s.inf :=
  fold_dedup_idem _ _ _
#align multiset.inf_dedup Multiset.inf_dedup

@[simp]
lemma inf_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).inf = s₁.inf ⊓ s₂.inf := by
  rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_add]; simp
#align multiset.inf_ndunion Multiset.inf_ndunion

@[simp]
lemma inf_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).inf = s₁.inf ⊓ s₂.inf := by
  rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_add]; simp
#align multiset.inf_union Multiset.inf_union

@[simp]
lemma inf_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).inf = a ⊓ s.inf := by
  rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_cons]; simp
#align multiset.inf_ndinsert Multiset.inf_ndinsert

end Inf

end Multiset
