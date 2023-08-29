/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Order.RelClasses

#align_import data.list.lex from "leanprover-community/mathlib"@"d6aae1bcbd04b8de2022b9b83a5b5b10e10c777d"

/-!
# Lexicographic ordering of lists.

The lexicographic order on `List α` is defined by `L < M` iff
* `[] < (a :: L)` for any `a` and `L`,
* `(a :: L) < (b :: M)` where `a < b`, or
* `(a :: L) < (a :: M)` where `L < M`.

## See also

Related files are:
* `Mathlib.Data.Finset.Colex`: Colexicographic order on finite sets.
* `Mathlib.Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Mathlib.Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Mathlib.Data.Sigma.Order`: Lexicographic order on `Σ i, α i`.
* `Mathlib.Data.Prod.Lex`: Lexicographic order on `α × β`.
-/


namespace List

open Nat

universe u

variable {α : Type u}

/-! ### lexicographic ordering -/


/-- Given a strict order `<` on `α`, the lexicographic strict order on `List α`, for which
`[a0, ..., an] < [b0, ..., b_k]` if `a0 < b0` or `a0 = b0` and `[a1, ..., an] < [b1, ..., bk]`.
The definition is given for any relation `r`, not only strict orders. -/
inductive Lex (r : α → α → Prop) : List α → List α → Prop
  | nil {a l} : Lex r [] (a :: l)
  | cons {a l₁ l₂} (h : Lex r l₁ l₂) : Lex r (a :: l₁) (a :: l₂)
  | rel {a₁ l₁ a₂ l₂} (h : r a₁ a₂) : Lex r (a₁ :: l₁) (a₂ :: l₂)
#align list.lex List.Lex
#align list.lex.nil List.Lex.nil
#align list.lex.cons List.Lex.cons
#align list.lex.rel List.Lex.rel

namespace Lex

theorem cons_iff {r : α → α → Prop} [IsIrrefl α r] {a l₁ l₂} :
    Lex r (a :: l₁) (a :: l₂) ↔ Lex r l₁ l₂ :=
  ⟨fun h => by cases' h with _ _ _ _ _ h _ _ _ _ h; exacts [h, (irrefl_of r a h).elim], Lex.cons⟩
               -- ⊢ Lex r l₁ l₂
                                                    -- 🎉 no goals
#align list.lex.cons_iff List.Lex.cons_iff

@[simp]
theorem not_nil_right (r : α → α → Prop) (l : List α) : ¬Lex r l [] :=
  fun.
#align list.lex.not_nil_right List.Lex.not_nil_right

theorem nil_left_or_eq_nil {r : α → α → Prop} (l : List α) : List.Lex r [] l ∨ l = [] :=
  match l with
  | [] => Or.inr rfl
  | (_ :: _) => Or.inl nil

@[simp]
theorem singleton_iff {r : α → α → Prop} (a b : α) : List.Lex r [a] [b] ↔ r a b :=
  ⟨fun | rel h => h, List.Lex.rel⟩

instance isOrderConnected (r : α → α → Prop) [IsOrderConnected α r] [IsTrichotomous α r] :
    IsOrderConnected (List α) (Lex r) where
  conn := aux where
    aux
    | _, [], c :: l₃, nil => Or.inr nil
    | _, [], c :: l₃, rel _ => Or.inr nil
    | _, [], c :: l₃, cons _ => Or.inr nil
    | _, b :: l₂, c :: l₃, nil => Or.inl nil
    | a :: l₁, b :: l₂, c :: l₃, rel h => (IsOrderConnected.conn _ b _ h).imp rel rel
    | a :: l₁, b :: l₂, _ :: l₃, cons h => by
      rcases trichotomous_of r a b with (ab | rfl | ab)
      · exact Or.inl (rel ab)
        -- 🎉 no goals
      · exact (aux _ l₂ _ h).imp cons cons
        -- 🎉 no goals
      · exact Or.inr (rel ab)
        -- 🎉 no goals
#align list.lex.is_order_connected List.Lex.isOrderConnected

-- This can be removed after https://github.com/leanprover/lean4/pull/1866
attribute [nolint defLemma] isOrderConnected.aux

instance isTrichotomous (r : α → α → Prop) [IsTrichotomous α r] :
    IsTrichotomous (List α) (Lex r) where
  trichotomous := aux where
    aux
    | [], [] => Or.inr (Or.inl rfl)
    | [], b :: l₂ => Or.inl nil
    | a :: l₁, [] => Or.inr (Or.inr nil)
    | a :: l₁, b :: l₂ => by
      rcases trichotomous_of r a b with (ab | rfl | ab)
      · exact Or.inl (rel ab)
        -- 🎉 no goals
      · exact (aux l₁ l₂).imp cons (Or.imp (congr_arg _) cons)
        -- 🎉 no goals
      · exact Or.inr (Or.inr (rel ab))
        -- 🎉 no goals
#align list.lex.is_trichotomous List.Lex.isTrichotomous

-- This can be removed after https://github.com/leanprover/lean4/pull/1866
attribute [nolint defLemma] isTrichotomous.aux

instance isAsymm (r : α → α → Prop) [IsAsymm α r] : IsAsymm (List α) (Lex r) where
  asymm := aux where
    aux
    | _, _, Lex.rel h₁, Lex.rel h₂ => asymm h₁ h₂
    | _, _, Lex.rel h₁, Lex.cons _ => asymm h₁ h₁
    | _, _, Lex.cons _, Lex.rel h₂ => asymm h₂ h₂
    | _, _, Lex.cons h₁, Lex.cons h₂ => aux _ _ h₁ h₂
#align list.lex.is_asymm List.Lex.isAsymm

-- This can be removed after https://github.com/leanprover/lean4/pull/1866
attribute [nolint defLemma] isAsymm.aux

instance isStrictTotalOrder (r : α → α → Prop) [IsStrictTotalOrder α r] :
    IsStrictTotalOrder (List α) (Lex r) :=
  { isStrictWeakOrder_of_isOrderConnected with }
#align list.lex.is_strict_total_order List.Lex.isStrictTotalOrder

instance decidableRel [DecidableEq α] (r : α → α → Prop) [DecidableRel r] : DecidableRel (Lex r)
  | l₁, [] => isFalse fun h => by cases h
                                  -- 🎉 no goals
  | [], b :: l₂ => isTrue Lex.nil
  | a :: l₁, b :: l₂ => by
    haveI := decidableRel r l₁ l₂
    -- ⊢ Decidable (Lex r (a :: l₁) (b :: l₂))
    refine' decidable_of_iff (r a b ∨ a = b ∧ Lex r l₁ l₂) ⟨fun h => _, fun h => _⟩
    -- ⊢ Lex r (a :: l₁) (b :: l₂)
    · rcases h with (h | ⟨rfl, h⟩)
      -- ⊢ Lex r (a :: l₁) (b :: l₂)
      · exact Lex.rel h
        -- 🎉 no goals
      · exact Lex.cons h
        -- 🎉 no goals
    · rcases h with (_ | h | h)
      -- ⊢ r a a ∨ a = a ∧ Lex r l₁ l₂
      · exact Or.inr ⟨rfl, h⟩
        -- 🎉 no goals
      · exact Or.inl h
        -- 🎉 no goals
#align list.lex.decidable_rel List.Lex.decidableRel

theorem append_right (r : α → α → Prop) : ∀ {s₁ s₂} (t), Lex r s₁ s₂ → Lex r s₁ (s₂ ++ t)
  | _, _, _, nil => nil
  | _, _, _, cons h => cons (append_right r _ h)
  | _, _, _, rel r => rel r
#align list.lex.append_right List.Lex.append_right

theorem append_left (R : α → α → Prop) {t₁ t₂} (h : Lex R t₁ t₂) : ∀ s, Lex R (s ++ t₁) (s ++ t₂)
  | [] => h
  | _ :: l => cons (append_left R h l)
#align list.lex.append_left List.Lex.append_left

theorem imp {r s : α → α → Prop} (H : ∀ a b, r a b → s a b) : ∀ l₁ l₂, Lex r l₁ l₂ → Lex s l₁ l₂
  | _, _, nil => nil
  | _, _, cons h => cons (imp H _ _ h)
  | _, _, rel r => rel (H _ _ r)
#align list.lex.imp List.Lex.imp

theorem to_ne : ∀ {l₁ l₂ : List α}, Lex (· ≠ ·) l₁ l₂ → l₁ ≠ l₂
  | _, _, cons h, e => to_ne h (List.cons.inj e).2
  | _, _, rel r, e => r (List.cons.inj e).1
#align list.lex.to_ne List.Lex.to_ne

theorem _root_.Decidable.List.Lex.ne_iff [DecidableEq α] {l₁ l₂ : List α}
    (H : length l₁ ≤ length l₂) : Lex (· ≠ ·) l₁ l₂ ↔ l₁ ≠ l₂ :=
  ⟨to_ne, fun h => by
    induction' l₁ with a l₁ IH generalizing l₂ <;> cases' l₂ with b l₂
    -- ⊢ Lex (fun x x_1 => x ≠ x_1) [] l₂
                                                   -- ⊢ Lex (fun x x_1 => x ≠ x_1) [] []
                                                   -- ⊢ Lex (fun x x_1 => x ≠ x_1) (a :: l₁) []
    · contradiction
      -- 🎉 no goals
    · apply nil
      -- 🎉 no goals
    · exact (not_lt_of_ge H).elim (succ_pos _)
      -- 🎉 no goals
    · by_cases ab : a = b
      -- ⊢ Lex (fun x x_1 => x ≠ x_1) (a :: l₁) (b :: l₂)
      · subst b
        -- ⊢ Lex (fun x x_1 => x ≠ x_1) (a :: l₁) (a :: l₂)
        apply cons
        -- ⊢ Lex (fun x x_1 => x ≠ x_1) l₁ l₂
        exact IH (le_of_succ_le_succ H) (mt (congr_arg _) h)
        -- 🎉 no goals
      · exact rel ab ⟩
        -- 🎉 no goals
#align decidable.list.lex.ne_iff Decidable.List.Lex.ne_iff

theorem ne_iff {l₁ l₂ : List α} (H : length l₁ ≤ length l₂) : Lex (· ≠ ·) l₁ l₂ ↔ l₁ ≠ l₂ := by
  classical
  exact Decidable.List.Lex.ne_iff H
#align list.lex.ne_iff List.Lex.ne_iff

end Lex

--Note: this overrides an instance in core lean
instance LT' [LT α] : LT (List α) :=
  ⟨Lex (· < ·)⟩
#align list.has_lt' List.LT'

theorem nil_lt_cons [LT α] (a : α) (l : List α) : [] < a :: l :=
  Lex.nil
#align list.nil_lt_cons List.nil_lt_cons

instance [LinearOrder α] : LinearOrder (List α) :=
  linearOrderOfSTO (Lex (· < ·))

--Note: this overrides an instance in core lean
instance LE' [LinearOrder α] : LE (List α) :=
  Preorder.toLE
#align list.has_le' List.LE'

theorem lt_iff_lex_lt [LinearOrder α] (l l' : List α) : lt l l' ↔ Lex (· < ·) l l' := by
  constructor <;>
  -- ⊢ lt l l' → Lex (fun x x_1 => x < x_1) l l'
  intro h
  -- ⊢ Lex (fun x x_1 => x < x_1) l l'
  -- ⊢ lt l l'
  · induction h with
    | nil b bs => exact Lex.nil
    | @head a as b bs hab => apply Lex.rel; assumption
    | @tail a as b bs hab hba _ ih =>
      have heq : a = b := _root_.le_antisymm (le_of_not_lt hba) (le_of_not_lt hab)
      subst b; apply Lex.cons; assumption
  · induction h with
    | @nil a as => apply lt.nil
    | @cons a as bs _ ih => apply lt.tail <;> simp [ih]
    | @rel a as b bs h => apply lt.head; assumption

end List
