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
* `Mathlib/Data/List/Lex`: Lexicographic order on `List α`.
* `Mathlib/Data/DFinsupp/WellFounded`: Well-foundedness of lexicographic orders on `DFinsupp` and
  `Pi`.
-/

/-! ### shortlex ordering -/

namespace List

/-- Given a relation `r` on `α`, the shortlex order on `List α`, for which
`[a0, ..., an] < [b0, ..., b_k]` if `n < k` or `n = k` and `[a0, ..., an] < [b0, ..., bk]`
under the lexicographic order induced by `r`. -/
def Shortlex {α : Type*} (r : α → α → Prop) : List α → List α → Prop :=
  InvImage (Prod.Lex (· < ·) (List.Lex r)) fun a ↦ (a.length, a)

namespace Shortlex

variable {α : Type*} {r : α → α → Prop}

/-- If a list `s` is shorter than a list `t`, then `s` is smaller than `t` under any shortlex
order. -/
theorem of_length_lt {s t : List α} (h : s.length < t.length) : Shortlex r s t :=
  Prod.Lex.left _ _ h

/-- If two lists `s` and `t` have the same length, `s` is smaller than `t` under the shortlex order
over a relation `r`  when `s` is smaller than `t` under the lexicographic order over `r` -/
theorem of_lex {s t : List α} (len_eq : s.length = t.length) (h_lex : List.Lex r s t) :
    Shortlex r s t := by
  apply Prod.lex_def.mpr
  right
  exact ⟨len_eq, h_lex⟩

theorem _root_.List.shortlex_def {s t : List α} : Shortlex r s t ↔
    s.length < t.length ∨ s.length = t.length ∧ List.Lex r s t := Prod.lex_def

/-- If two lists `s` and `t` have the same length, `s` is smaller than `t` under the shortlex order
over a relation `r` exactly when `s` is smaller than `t` under the lexicographic order over `r`.-/
theorem _root_.List.shortlex_iff_lex {s t : List α} (h : s.length = t.length) :
    Shortlex r s t ↔ List.Lex r s t := by
  simp [shortlex_def, h]

theorem cons_iff [IsIrrefl α r] {a : α} {s t : List α} : Shortlex r (a :: s) (a :: t) ↔
    Shortlex r s t := by
  simp only [shortlex_def, length_cons, add_lt_add_iff_right, add_left_inj, List.Lex.cons_iff]

@[simp]
theorem not_nil_right {s : List α} : ¬ Shortlex r s [] := by
  rw [shortlex_def]
  rintro (h1 | h2)
  · simp only [List.length_nil, not_lt_zero'] at h1
  · exact List.not_lex_nil h2.2

theorem nil_left_or_eq_nil (s : List α) : Shortlex r [] s ∨ s = [] := by
  cases s with
  | nil => right; rfl
  | cons head tail => exact Or.inl (of_length_lt (Nat.succ_pos tail.length))

@[simp]
theorem singleton_iff (a b : α) : Shortlex r [a] [b] ↔ r a b := by
  simp only [shortlex_def, length_singleton, lt_self_iff_false, Lex.singleton_iff, true_and,
    false_or]

instance isTrichotomous [IsTrichotomous α r] : IsTrichotomous (List α) (Shortlex r) :=
  InvImage.trichotomous (by simp [Function.Injective])


instance isAsymm [IsAsymm α r] : IsAsymm (List α) (Shortlex r) where
  asymm := fun a b ab ba => (@InvImage.isAsymm _ _ (Prod.Lex (fun x1 x2 ↦ x1 < x2) (Lex r))
      Prod.IsAsymm (fun a : List α ↦ (a.length, a))).asymm a b ab ba

theorem append_right {s₁ s₂ : List α} (t : List α) : Shortlex r s₁ s₂ →
    Shortlex r s₁ (s₂ ++ t) := by
  intro h
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append]
    omega
  cases t with
  | nil =>
    rw [List.append_nil]
    exact h
  | cons head tail =>
    apply of_length_lt
    rw [List.length_append, List.length_cons]
    omega

theorem append_left {t₁ t₂ : List α} (h : Shortlex r t₁ t₂) (s : List α) :
    Shortlex r (s ++ t₁) (s ++ t₂) := by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append, List.length_append]
    omega
  cases s with
  | nil =>
    rw [List.nil_append, List.nil_append]
    exact h
  | cons head tail =>
    apply of_lex
    · simp only [List.cons_append, List.length_cons, List.length_append, Nat.succ_eq_add_one,
      add_left_inj, add_right_inj]
      exact h2.1
    exact List.Lex.append_left r h2.2 (head :: tail)

section WellFounded

variable {h : WellFounded r}

theorem _root_.Acc.shortlex {a : α} (n : ℕ) (aca : Acc r a)
    (acb : (b : List α) → b.length < n → Acc (Shortlex r) b) (b : List α) (hb : b.length < n)
    (ih : ∀ s : List α, s.length < (a::b).length → Acc (Shortlex r) s) :
    Acc (Shortlex r) ([a] ++ b) := by
  induction aca generalizing b with
  | intro xa _ iha =>
    induction (acb b hb) with
    | intro xb _ ihb =>
      apply Acc.intro ([xa] ++ xb)
      intro p lt
      rcases shortlex_def.mp lt with h1 | h2
      · exact ih _ h1
      · cases p with
        | nil => simp only [List.length_nil, List.singleton_append, List.length_cons,
          Nat.succ_eq_add_one, self_eq_add_left, add_eq_zero, List.length_eq_zero, one_ne_zero,
          and_false, false_and] at h2
        | cons headp tailp =>
          cases h2.2 with
          | cons h =>
            rw [List.append_eq, List.nil_append] at h
            simp only [List.length_cons, Nat.succ_eq_add_one, List.singleton_append,
              add_left_inj] at h2
            rw [← h2.1] at hb
            apply ihb _ (of_lex (h2.1) h) hb
            intro l hl
            apply ih
            rw [List.length_cons, ← h2.1]
            exact hl
          | rel h =>
            simp only [List.length_cons, Nat.succ_eq_add_one, List.singleton_append,
              add_left_inj] at h2
            rw [← h2.1] at hb
            apply iha headp h _ hb
            intro l hl
            apply ih
            rw [List.length_cons, ← h2.1]
            exact hl

theorem wf (h : WellFounded r) : WellFounded (Shortlex r) := by
  suffices h : ∀ n, ∀ (a : List α), a.length = n → Acc (Shortlex r) a from
    WellFounded.intro (fun a => h a.length a rfl)
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      intro a len_a
      rw [List.length_eq_zero] at len_a
      rw [len_a]
      exact Acc.intro _ <| fun _ ylt => (Shortlex.not_nil_right ylt).elim
    | succ n =>
      intro a len_a
      rcases List.exists_of_length_succ a len_a with ⟨head, tail, a_is⟩
      rw [a_is]
      rw [a_is, List.length_cons, add_left_inj] at len_a
      apply Acc.shortlex (n+1) (WellFounded.apply h head) (fun b bl => ih b.length bl _ rfl)
      · rw [len_a]
        exact lt_add_one n
      intro l ll
      apply ih l.length _ _ rfl
      rw [← len_a]
      exact ll

end WellFounded

end Shortlex

end List
