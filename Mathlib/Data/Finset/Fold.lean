/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Multiset.Fold

/-!
# The fold operation for a commutative associative operation over a finset.
-/

assert_not_exists Monoid

namespace Finset

open Multiset

variable {α β γ : Type*}

/-! ### fold -/


section Fold

variable (op : β → β → β) [hc : Std.Commutative op] [ha : Std.Associative op]

local notation a " * " b => op a b

/-- `fold op b f s` folds the commutative associative operation `op` over the
  `f`-image of `s`, i.e. `fold (+) b f {1,2,3} = f 1 + f 2 + f 3 + b`. -/
def fold (b : β) (f : α → β) (s : Finset α) : β :=
  (s.1.map f).fold op b

variable {op} {f : α → β} {b : β} {s : Finset α} {a : α}

@[simp]
theorem fold_empty : (∅ : Finset α).fold op b f = b :=
  rfl

@[simp]
theorem fold_cons (h : a ∉ s) : (cons a s h).fold op b f = f a * s.fold op b f := by
  dsimp only [fold]
  rw [cons_val, Multiset.map_cons, fold_cons_left]

@[simp]
theorem fold_insert [DecidableEq α] (h : a ∉ s) :
    (insert a s).fold op b f = f a * s.fold op b f := by
  unfold fold
  rw [insert_val, ndinsert_of_notMem h, Multiset.map_cons, fold_cons_left]

@[simp]
theorem fold_singleton : ({a} : Finset α).fold op b f = f a * b :=
  rfl

@[simp]
theorem fold_map {g : γ ↪ α} {s : Finset γ} : (s.map g).fold op b f = s.fold op b (f ∘ g) := by
  simp only [fold, map, Multiset.map_map]

@[simp]
theorem fold_image [DecidableEq α] {g : γ → α} {s : Finset γ}
    (H : Set.InjOn g s) : (s.image g).fold op b f = s.fold op b (f ∘ g) := by
  simp only [fold, image_val_of_injOn H, Multiset.map_map]

@[congr]
theorem fold_congr {g : α → β} (H : ∀ x ∈ s, f x = g x) : s.fold op b f = s.fold op b g := by
  rw [fold, fold, map_congr rfl H]

theorem fold_op_distrib {f g : α → β} {b₁ b₂ : β} :
    (s.fold op (b₁ * b₂) fun x => f x * g x) = s.fold op b₁ f * s.fold op b₂ g := by
  simp only [fold, fold_distrib]

theorem fold_const [hd : Decidable (s = ∅)] (c : β) (h : op c (op b c) = op b c) :
    Finset.fold op b (fun _ => c) s = if s = ∅ then b else op b c := by
  classical
    induction' s using Finset.induction_on with x s hx IH generalizing hd
    · simp
    · simp only [Finset.fold_insert hx, IH, if_false, Finset.insert_ne_empty]
      split_ifs
      · rw [hc.comm]
      · exact h

theorem fold_hom {op' : γ → γ → γ} [Std.Commutative op'] [Std.Associative op'] {m : β → γ}
    (hm : ∀ x y, m (op x y) = op' (m x) (m y)) :
    (s.fold op' (m b) fun x => m (f x)) = m (s.fold op b f) := by
  rw [fold, fold, ← Multiset.fold_hom op hm, Multiset.map_map]
  simp only [Function.comp_apply]

theorem fold_disjUnion {s₁ s₂ : Finset α} {b₁ b₂ : β} (h) :
    (s₁.disjUnion s₂ h).fold op (b₁ * b₂) f = s₁.fold op b₁ f * s₂.fold op b₂ f :=
  (congr_arg _ <| Multiset.map_add _ _ _).trans (Multiset.fold_add _ _ _ _ _)

theorem fold_union_inter [DecidableEq α] {s₁ s₂ : Finset α} {b₁ b₂ : β} :
    ((s₁ ∪ s₂).fold op b₁ f * (s₁ ∩ s₂).fold op b₂ f) = s₁.fold op b₂ f * s₂.fold op b₁ f := by
  unfold fold
  rw [← fold_add op, ← Multiset.map_add, union_val, inter_val, union_add_inter, Multiset.map_add,
    hc.comm, fold_add]

@[simp]
theorem fold_insert_idem [DecidableEq α] [hi : Std.IdempotentOp op] :
    (insert a s).fold op b f = f a * s.fold op b f := by
  by_cases h : a ∈ s
  · rw [← insert_erase h]
    simp [← ha.assoc, hi.idempotent]
  · apply fold_insert h

theorem fold_image_idem [DecidableEq α] {g : γ → α} {s : Finset γ} [hi : Std.IdempotentOp op] :
    (image g s).fold op b f = s.fold op b (f ∘ g) := by
  induction' s using Finset.cons_induction with x xs hx ih
  · rw [fold_empty, image_empty, fold_empty]
  · haveI := Classical.decEq γ
    rw [fold_cons, cons_eq_insert, image_insert, fold_insert_idem, ih]
    simp only [Function.comp_apply]

/-- A stronger version of `Finset.fold_ite`, but relies on
an explicit proof of idempotency on the seed element, rather
than relying on typeclass idempotency over the whole type. -/
theorem fold_ite' {g : α → β} (hb : op b b = b) (p : α → Prop) [DecidablePred p] :
    Finset.fold op b (fun i => ite (p i) (f i) (g i)) s =
      op (Finset.fold op b f (s.filter p)) (Finset.fold op b g (s.filter fun i => ¬p i)) := by
  classical
    induction' s using Finset.induction_on with x s hx IH
    · simp [hb]
    · simp only [Finset.fold_insert hx]
      split_ifs with h
      · have : x ∉ Finset.filter p s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, ha.assoc, IH]
      · have : x ∉ Finset.filter (fun i => ¬ p i) s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, IH, ← ha.assoc, hc.comm]

/-- A weaker version of `Finset.fold_ite'`,
relying on typeclass idempotency over the whole type,
instead of solely on the seed element.
However, this is easier to use because it does not generate side goals. -/
theorem fold_ite [Std.IdempotentOp op] {g : α → β} (p : α → Prop) [DecidablePred p] :
    Finset.fold op b (fun i => ite (p i) (f i) (g i)) s =
      op (Finset.fold op b f (s.filter p)) (Finset.fold op b g (s.filter fun i => ¬p i)) :=
  fold_ite' (Std.IdempotentOp.idempotent _) _

theorem fold_op_rel_iff_and {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ r x y ∧ r x z)
    {c : β} : r c (s.fold op b f) ↔ r c b ∧ ∀ x ∈ s, r c (f x) := by
  classical
    induction' s using Finset.induction_on with a s ha IH
    · simp
    rw [Finset.fold_insert ha, hr, IH, ← and_assoc, @and_comm (r c (f a)), and_assoc]
    simp

theorem fold_op_rel_iff_or {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ r x y ∨ r x z)
    {c : β} : r c (s.fold op b f) ↔ r c b ∨ ∃ x ∈ s, r c (f x) := by
  classical
    induction' s using Finset.induction_on with a s ha IH
    · simp
    rw [Finset.fold_insert ha, hr, IH, ← or_assoc, @or_comm (r c (f a)), or_assoc]
    simp

@[simp]
theorem fold_union_empty_singleton [DecidableEq α] (s : Finset α) :
    Finset.fold (· ∪ ·) ∅ singleton s = s := by
  induction' s using Finset.induction_on with a s has ih
  · simp only [fold_empty]
  · rw [fold_insert has, ih, insert_eq]

theorem fold_sup_bot_singleton [DecidableEq α] (s : Finset α) :
    Finset.fold (· ⊔ ·) ⊥ singleton s = s :=
  fold_union_empty_singleton s

section Order

variable [LinearOrder β] (c : β)

theorem le_fold_min : c ≤ s.fold min b f ↔ c ≤ b ∧ ∀ x ∈ s, c ≤ f x :=
  fold_op_rel_iff_and le_min_iff

theorem fold_min_le : s.fold min b f ≤ c ↔ b ≤ c ∨ ∃ x ∈ s, f x ≤ c := by
  change _ ≥ _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  change _ ≤ _ ↔ _
  exact min_le_iff

theorem lt_fold_min : c < s.fold min b f ↔ c < b ∧ ∀ x ∈ s, c < f x :=
  fold_op_rel_iff_and lt_min_iff

theorem fold_min_lt : s.fold min b f < c ↔ b < c ∨ ∃ x ∈ s, f x < c := by
  change _ > _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  change _ < _ ↔ _
  exact min_lt_iff

theorem fold_max_le : s.fold max b f ≤ c ↔ b ≤ c ∧ ∀ x ∈ s, f x ≤ c := by
  change _ ≥ _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  change _ ≤ _ ↔ _
  exact max_le_iff

theorem le_fold_max : c ≤ s.fold max b f ↔ c ≤ b ∨ ∃ x ∈ s, c ≤ f x :=
  fold_op_rel_iff_or le_max_iff

theorem fold_max_lt : s.fold max b f < c ↔ b < c ∧ ∀ x ∈ s, f x < c := by
  change _ > _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  change _ < _ ↔ _
  exact max_lt_iff

theorem lt_fold_max : c < s.fold max b f ↔ c < b ∨ ∃ x ∈ s, c < f x :=
  fold_op_rel_iff_or lt_max_iff

end Order

end Fold

end Finset
