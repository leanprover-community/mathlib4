/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Bind

#align_import data.multiset.fold from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

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
  foldr op (left_comm _ hc.comm ha.assoc)
#align multiset.fold Multiset.fold

theorem fold_eq_foldr (b : α) (s : Multiset α) :
    fold op b s = foldr op (left_comm _ hc.comm ha.assoc) b s :=
  rfl
#align multiset.fold_eq_foldr Multiset.fold_eq_foldr

@[simp]
theorem coe_fold_r (b : α) (l : List α) : fold op b l = l.foldr op b :=
  rfl
#align multiset.coe_fold_r Multiset.coe_fold_r

theorem coe_fold_l (b : α) (l : List α) : fold op b l = l.foldl op b :=
  (coe_foldr_swap op _ b l).trans <| by simp [hc.comm]
#align multiset.coe_fold_l Multiset.coe_fold_l

theorem fold_eq_foldl (b : α) (s : Multiset α) :
    fold op b s = foldl op (right_comm _ hc.comm ha.assoc) b s :=
  Quot.inductionOn s fun _ => coe_fold_l _ _ _
#align multiset.fold_eq_foldl Multiset.fold_eq_foldl

@[simp]
theorem fold_zero (b : α) : (0 : Multiset α).fold op b = b :=
  rfl
#align multiset.fold_zero Multiset.fold_zero

@[simp]
theorem fold_cons_left : ∀ (b a : α) (s : Multiset α), (a ::ₘ s).fold op b = a * s.fold op b :=
  foldr_cons _ _
#align multiset.fold_cons_left Multiset.fold_cons_left

theorem fold_cons_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op b * a := by
  simp [hc.comm]
#align multiset.fold_cons_right Multiset.fold_cons_right

theorem fold_cons'_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (b * a) := by
  rw [fold_eq_foldl, foldl_cons, ← fold_eq_foldl]
#align multiset.fold_cons'_right Multiset.fold_cons'_right

theorem fold_cons'_left (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (a * b) := by
  rw [fold_cons'_right, hc.comm]
#align multiset.fold_cons'_left Multiset.fold_cons'_left

theorem fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) :
    (s₁ + s₂).fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂ :=
  Multiset.induction_on s₂ (by rw [add_zero, fold_zero, ← fold_cons'_right, ← fold_cons_right op])
    (fun a b h => by rw [fold_cons_left, add_cons, fold_cons_left, h, ← ha.assoc, hc.comm a,
      ha.assoc])
#align multiset.fold_add Multiset.fold_add

theorem fold_bind {ι : Type*} (s : Multiset ι) (t : ι → Multiset α) (b : ι → α) (b₀ : α) :
    (s.bind t).fold op ((s.map b).fold op b₀) =
    (s.map fun i => (t i).fold op (b i)).fold op b₀ := by
  induction' s using Multiset.induction_on with a ha ih
  · rw [zero_bind, map_zero, map_zero, fold_zero]
  · rw [cons_bind, map_cons, map_cons, fold_cons_left, fold_cons_left, fold_add, ih]
#align multiset.fold_bind Multiset.fold_bind

theorem fold_singleton (b a : α) : ({a} : Multiset α).fold op b = a * b :=
  foldr_singleton _ _ _ _
#align multiset.fold_singleton Multiset.fold_singleton

theorem fold_distrib {f g : β → α} (u₁ u₂ : α) (s : Multiset β) :
    (s.map fun x => f x * g x).fold op (u₁ * u₂) = (s.map f).fold op u₁ * (s.map g).fold op u₂ :=
  Multiset.induction_on s (by simp) (fun a b h => by
    rw [map_cons, fold_cons_left, h, map_cons, fold_cons_left, map_cons,
      fold_cons_right, ha.assoc, ← ha.assoc (g a), hc.comm (g a),
      ha.assoc, hc.comm (g a), ha.assoc])
#align multiset.fold_distrib Multiset.fold_distrib

theorem fold_hom {op' : β → β → β} [Std.Commutative op'] [Std.Associative op'] {m : α → β}
    (hm : ∀ x y, m (op x y) = op' (m x) (m y)) (b : α) (s : Multiset α) :
    (s.map m).fold op' (m b) = m (s.fold op b) :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }) [hm])
#align multiset.fold_hom Multiset.fold_hom

theorem fold_union_inter [DecidableEq α] (s₁ s₂ : Multiset α) (b₁ b₂ : α) :
    ((s₁ ∪ s₂).fold op b₁ * (s₁ ∩ s₂).fold op b₂) = s₁.fold op b₁ * s₂.fold op b₂ := by
  rw [← fold_add op, union_add_inter, fold_add op]
#align multiset.fold_union_inter Multiset.fold_union_inter

@[simp]
theorem fold_dedup_idem [DecidableEq α] [hi : Std.IdempotentOp op] (s : Multiset α) (b : α) :
    (dedup s).fold op b = s.fold op b :=
  Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a ∈ s <;> simp [IH, h]
    show fold op b s = op a (fold op b s)
    rw [← cons_erase h, fold_cons_left, ← ha.assoc, hi.idempotent]
#align multiset.fold_dedup_idem Multiset.fold_dedup_idem

end Fold

open Nat

theorem le_smul_dedup [DecidableEq α] (s : Multiset α) : ∃ n : ℕ, s ≤ n • dedup s :=
  ⟨(s.map fun a => count a s).fold max 0,
    le_iff_count.2 fun a => by
      rw [count_nsmul]; by_cases h : a ∈ s
      · refine le_trans ?_ (Nat.mul_le_mul_left _ <| count_pos.2 <| mem_dedup.2 h)
        have : count a s ≤ fold max 0 (map (fun a => count a s) (a ::ₘ erase s a)) := by
          simp [le_max_left]
        rw [cons_erase h] at this
        simpa [mul_succ] using this
      · simp [count_eq_zero.2 h, Nat.zero_le]⟩
#align multiset.le_smul_dedup Multiset.le_smul_dedup

end Multiset
