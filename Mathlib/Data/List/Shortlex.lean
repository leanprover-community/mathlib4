/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/

import Mathlib.Data.List.Lex
import Mathlib.Tactic.Linarith
import Mathlib.Order.RelClasses

/-!
# Shortlex ordering of lists.

Given a relation `r` on `α`, the shortlex order on `List α` is defined by `L < M` iff
* `L.length < M.length`
* `L.length = M.length` and `L < M` under the lexicographic ordering over `r` on lists

## Main results

We show that if `r` is well-founded, so too is the shortlex order over `r`

## See also

Related files are:
* `Mathlib/Data/List/Lex.lean`: Lexicographic order on `List α`.
* `Mathlib/Data/DFinsupp/WellFounded.lean`: Well-foundedness of lexicographic orders on `DFinsupp`
  and `Pi`.
-/

/-! ### shortlex ordering -/

namespace List

/-- Given a relation `r` on `α`, the shortlex order on `List α`, for which
`[a0, ..., an] < [b0, ..., b_k]` if `n < k` or `n = k` and `[a0, ..., an] < [b0, ..., bk]`
under the lexicographic order induced by `r`. -/
def Shortlex {α : Type*} (r : α → α → Prop) : List α → List α → Prop :=
  InvImage (Prod.Lex (· < ·) (List.Lex r)) fun a ↦ (a.length, a)

variable {α : Type*} {r : α → α → Prop}

/-- If a list `s` is shorter than a list `t`, then `s` is smaller than `t` under any shortlex
order. -/
theorem Shortlex.of_length_lt {s t : List α} (h : s.length < t.length) : Shortlex r s t :=
  Prod.Lex.left _ _ h

/-- If two lists `s` and `t` have the same length, `s` is smaller than `t` under the shortlex order
over a relation `r`  when `s` is smaller than `t` under the lexicographic order over `r` -/
theorem Shortlex.of_lex {s t : List α} (len_eq : s.length = t.length) (h_lex : List.Lex r s t) :
    Shortlex r s t := by
  apply Prod.lex_def.mpr
  right
  exact ⟨len_eq, h_lex⟩

theorem shortlex_def {s t : List α} :
    Shortlex r s t ↔ s.length < t.length ∨ s.length = t.length ∧ Lex r s t := Prod.lex_def

/-- If two lists `s` and `t` have the same length, `s` is smaller than `t` under the shortlex order
over a relation `r` exactly when `s` is smaller than `t` under the lexicographic order over `r`. -/
theorem shortlex_iff_lex {s t : List α} (h : s.length = t.length) :
    Shortlex r s t ↔ List.Lex r s t := by
  simp [shortlex_def, h]

theorem shortlex_cons_iff [IsIrrefl α r] {a : α} {s t : List α} :
    Shortlex r (a :: s) (a :: t) ↔ Shortlex r s t := by
  simp only [shortlex_def, length_cons, add_lt_add_iff_right, add_left_inj, List.lex_cons_iff]

alias ⟨Shortlex.of_cons, Shortlex.cons⟩ := shortlex_cons_iff

@[simp]
theorem not_shortlex_nil_right {s : List α} : ¬ Shortlex r s [] := by
  rw [shortlex_def]
  rintro (h1 | h2)
  · simp only [List.length_nil, not_lt_zero'] at h1
  · exact List.not_lex_nil h2.2

theorem shortlex_nil_or_eq_nil : ∀ s : List α, Shortlex r [] s ∨ s = []
  | [] => .inr rfl
  | _ :: tail => .inl <| .of_length_lt tail.length.succ_pos

@[simp]
theorem shortlex_singleton_iff (a b : α) : Shortlex r [a] [b] ↔ r a b := by
  simp only [shortlex_def, length_singleton, lt_self_iff_false, lex_singleton_iff, true_and,
    false_or]

namespace Shortlex

instance isTrichotomous [IsTrichotomous α r] : IsTrichotomous (List α) (Shortlex r) :=
  ⟨(InvImage.isTrichotomous (by simp [Function.Injective])).trichotomous⟩

instance isAsymm [IsAsymm α r] : IsAsymm (List α) (Shortlex r) :=
  inferInstanceAs <| IsAsymm (List α) (InvImage _ _)

theorem append_right {s₁ s₂ : List α} (t : List α) (h : Shortlex r s₁ s₂) :
    Shortlex r s₁ (s₂ ++ t) := by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append]
    cutsat
  cases t with
  | nil =>
    rw [List.append_nil]
    exact h
  | cons head tail =>
    apply of_length_lt
    rw [List.length_append, List.length_cons]
    cutsat

theorem append_left {t₁ t₂ : List α} (h : Shortlex r t₁ t₂) (s : List α) :
    Shortlex r (s ++ t₁) (s ++ t₂) := by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append, List.length_append]
    cutsat
  cases s with
  | nil =>
    rw [List.nil_append, List.nil_append]
    exact h
  | cons head tail =>
    apply of_lex
    · simp only [List.cons_append, List.length_cons, List.length_append,
      add_left_inj, add_right_inj]
      exact h2.1
    exact List.Lex.append_left r h2.2 (head :: tail)

section WellFounded

variable {h : WellFounded r}

private theorem _root_.Acc.shortlex {a : α} {b : List α} (aca : Acc r a)
    (acb : Acc (Shortlex r) b)
    (ih : ∀ s : List α, s.length < (a :: b).length → Acc (Shortlex r) s) :
    Acc (Shortlex r) (a :: b) := by
  induction aca generalizing b with
  | intro xa _ iha =>
    induction acb with
    | intro xb _ ihb =>
      refine Acc.intro (xa :: xb) fun p lt => ?_
      rcases shortlex_def.mp lt with h1 | ⟨h2len, h2lex⟩
      · exact ih _ h1
      · cases h2lex with
        | nil => simp at h2len
        | @cons x xs _ h =>
          simp only [length_cons, add_left_inj] at h2len
          refine ihb _ (of_lex h2len h) fun l hl => ?_
          apply ih
          rw [List.length_cons, ← h2len]
          exact hl
        | @rel x xs _ _ h =>
          simp only [List.length_cons, add_left_inj] at h2len
          refine iha _ h (ih xs (by rw [h2len]; simp)) fun l hl => ?_
          apply ih
          rw [List.length_cons, ← h2len]
          exact hl

theorem wf (h : WellFounded r) : WellFounded (Shortlex r) := .intro fun a => by
  induction len_a : a.length using Nat.caseStrongRecOn generalizing a with
  | zero =>
    rw [List.length_eq_zero_iff] at len_a
    rw [len_a]
    exact Acc.intro _ <| fun _ ylt => (not_shortlex_nil_right ylt).elim
  | ind n ih =>
    obtain ⟨head, tail, rfl⟩ := List.exists_of_length_succ a len_a
    rw [List.length_cons, add_left_inj] at len_a
    apply Acc.shortlex (WellFounded.apply h head) (ih n le_rfl tail len_a)
    intro l ll
    apply ih l.length _ _ rfl
    rw [← len_a]
    exact Nat.le_of_lt_succ ll

end WellFounded

end Shortlex

end List
