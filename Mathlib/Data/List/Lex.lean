/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Order.RelClasses
import Mathlib.Data.List.Basic

/-!
# Lexicographic ordering of lists.

The lexicographic order on `List α` is defined by `L < M` iff
* `[] < (a :: L)` for any `a` and `L`,
* `(a :: L) < (b :: M)` where `a < b`, or
* `(a :: L) < (a :: M)` where `L < M`.

## See also

Related files are:
* `Mathlib/Data/Finset/Colex.lean`: Colexicographic order on finite sets.
* `Mathlib/Data/PSigma/Order.lean`: Lexicographic order on `Σ' i, α i`.
* `Mathlib/Data/Pi/Lex.lean`: Lexicographic order on `Πₗ i, α i`.
* `Mathlib/Data/Sigma/Order.lean`: Lexicographic order on `Σ i, α i`.
* `Mathlib/Data/Prod/Lex.lean`: Lexicographic order on `α × β`.
-/


namespace List

open Nat

universe u

variable {α : Type u}

/-! ### lexicographic ordering -/

theorem lex_cons_iff {r : α → α → Prop} [IsIrrefl α r] {a l₁ l₂} :
    Lex r (a :: l₁) (a :: l₂) ↔ Lex r l₁ l₂ :=
  ⟨fun h => by obtain - | h | h := h; exacts [(irrefl_of r a h).elim, h], Lex.cons⟩

theorem lex_nil_or_eq_nil {r : α → α → Prop} (l : List α) : List.Lex r [] l ∨ l = [] :=
  match l with
  | [] => Or.inr rfl
  | _ :: _ => .inl .nil

@[deprecated (since := "2025-03-14")] alias Lex.nil_left_or_eq_nil := lex_nil_or_eq_nil

@[simp]
theorem lex_singleton_iff {r : α → α → Prop} (a b : α) : List.Lex r [a] [b] ↔ r a b :=
  ⟨fun | .rel h => h, .rel⟩

@[deprecated (since := "2025-03-14")] alias Lex.singleton_iff := lex_singleton_iff

namespace Lex

instance isOrderConnected (r : α → α → Prop) [IsOrderConnected α r] [IsTrichotomous α r] :
    IsOrderConnected (List α) (Lex r) where
  conn := aux where
    aux
    | _, [], _ :: _, nil => Or.inr nil
    | _, [], _ :: _, rel _ => Or.inr nil
    | _, [], _ :: _, cons _ => Or.inr nil
    | _, _ :: _, _ :: _, nil => Or.inl nil
    | _ :: _, b :: _, _ :: _, rel h => (IsOrderConnected.conn _ b _ h).imp rel rel
    | a :: l₁, b :: l₂, _ :: l₃, cons h => by
      rcases trichotomous_of r a b with (ab | rfl | ab)
      · exact Or.inl (rel ab)
      · exact (aux _ l₂ _ h).imp cons cons
      · exact Or.inr (rel ab)

instance isTrichotomous (r : α → α → Prop) [IsTrichotomous α r] :
    IsTrichotomous (List α) (Lex r) where
  trichotomous := aux where
    aux
    | [], [] => Or.inr (Or.inl rfl)
    | [], _ :: _ => Or.inl nil
    | _ :: _, [] => Or.inr (Or.inr nil)
    | a :: l₁, b :: l₂ => by
      rcases trichotomous_of r a b with (ab | rfl | ab)
      · exact Or.inl (rel ab)
      · exact (aux l₁ l₂).imp cons (Or.imp (congr_arg _) cons)
      · exact Or.inr (Or.inr (rel ab))

instance isAsymm (r : α → α → Prop) [IsAsymm α r] : IsAsymm (List α) (Lex r) where
  asymm := aux where
    aux
    | _, _, Lex.rel h₁, Lex.rel h₂ => asymm h₁ h₂
    | _, _, Lex.rel h₁, Lex.cons _ => asymm h₁ h₁
    | _, _, Lex.cons _, Lex.rel h₂ => asymm h₂ h₂
    | _, _, Lex.cons h₁, Lex.cons h₂ => aux _ _ h₁ h₂

instance decidableRel [DecidableEq α] (r : α → α → Prop) [DecidableRel r] : DecidableRel (Lex r)
  | l₁, [] => isFalse fun h => by cases h
  | [], _ :: _ => isTrue Lex.nil
  | a :: l₁, b :: l₂ => by
    haveI := decidableRel r l₁ l₂
    refine decidable_of_iff (r a b ∨ a = b ∧ Lex r l₁ l₂) ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with (h | ⟨rfl, h⟩)
      · exact Lex.rel h
      · exact Lex.cons h
    · rcases h with (_ | h | h)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩

theorem append_right (r : α → α → Prop) : ∀ {s₁ s₂} (t), Lex r s₁ s₂ → Lex r s₁ (s₂ ++ t)
  | _, _, _, nil => nil
  | _, _, _, cons h => cons (append_right r _ h)
  | _, _, _, rel r => rel r

theorem append_left (R : α → α → Prop) {t₁ t₂} (h : Lex R t₁ t₂) : ∀ s, Lex R (s ++ t₁) (s ++ t₂)
  | [] => h
  | _ :: l => cons (append_left R h l)

theorem imp {r s : α → α → Prop} (H : ∀ a b, r a b → s a b) : ∀ l₁ l₂, Lex r l₁ l₂ → Lex s l₁ l₂
  | _, _, nil => nil
  | _, _, cons h => cons (imp H _ _ h)
  | _, _, rel r => rel (H _ _ r)

theorem to_ne : ∀ {l₁ l₂ : List α}, Lex (· ≠ ·) l₁ l₂ → l₁ ≠ l₂
  | _, _, cons h, e => to_ne h (List.cons.inj e).2
  | _, _, rel r, e => r (List.cons.inj e).1

theorem _root_.Decidable.List.Lex.ne_iff [DecidableEq α] {l₁ l₂ : List α}
    (H : length l₁ ≤ length l₂) : Lex (· ≠ ·) l₁ l₂ ↔ l₁ ≠ l₂ :=
  ⟨to_ne, fun h => by
    induction' l₁ with a l₁ IH generalizing l₂ <;> rcases l₂ with - | ⟨b, l₂⟩
    · contradiction
    · apply nil
    · exact (not_lt_of_ge H).elim (succ_pos _)
    · by_cases ab : a = b
      · subst b
        exact .cons <| IH (le_of_succ_le_succ H) (mt (congr_arg _) h)
      · exact .rel ab ⟩

theorem ne_iff {l₁ l₂ : List α} (H : length l₁ ≤ length l₂) : Lex (· ≠ ·) l₁ l₂ ↔ l₁ ≠ l₂ := by
  classical
  exact Decidable.List.Lex.ne_iff H

end Lex

instance [LinearOrder α] : LinearOrder (List α) :=
  have : ∀ {r} [IsStrictTotalOrder α r], IsStrictTotalOrder (List α) (Lex r) :=
    { isStrictWeakOrder_of_isOrderConnected with }
  linearOrderOfSTO (Lex (· < ·))

--Note: this overrides an instance in core lean
instance LE' [LinearOrder α] : LE (List α) :=
  Preorder.toLE

theorem lt_iff_lex_lt [LT α] (l l' : List α) : List.lt l l' ↔ Lex (· < ·) l l' := by
  rw [List.lt]

theorem head_le_of_lt [Preorder α] {a a' : α} {l l' : List α} (h : (a' :: l') < (a :: l)) :
    a' ≤ a :=
  match h with
  | .cons _ => le_rfl
  | .rel h => h.le

theorem head!_le_of_lt [Preorder α] [Inhabited α] (l l' : List α) (h : l' < l) (hl' : l' ≠ []) :
    l'.head! ≤ l.head! := by
  replace h : List.Lex (· < ·) l' l := h
  by_cases hl : l = []
  · simp [hl] at h
  · rw [← List.cons_head!_tail hl', ← List.cons_head!_tail hl] at h
    exact head_le_of_lt h

theorem cons_le_cons [LinearOrder α] (a : α) {l l' : List α} (h : l' ≤ l) :
    a :: l' ≤ a :: l := by
  rw [le_iff_lt_or_eq] at h ⊢
  exact h.imp .cons (congr_arg _)

end List
