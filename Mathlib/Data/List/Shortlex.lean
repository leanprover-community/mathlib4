/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/

import Mathlib.Data.List.Lex
import Mathlib.Tactic.Linarith

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
  fun a b => Prod.Lex (fun n1 n2 => n1 < n2) (fun a b => List.Lex r a b) (a.length, a) (b.length, b)

namespace Shortlex

variable {α : Type*} {r : α → α → Prop}

/-- If a list `s` is shorter than a list `t`, then `s` is smaller than `t` under any shortlex
order -/
theorem of_length_lt {s t : List α} (h : s.length < t.length) : Shortlex r s t :=
  Prod.Lex.left _ _ h

/-- If two lists `s` and `t` have the same length, `s` is smaller than `t` under the shortlex order
over a relation `r`  when `s` is smaller than `t` under the lexicographic order over `r` -/
theorem of_lex {s t : List α} (h : s.length = t.length) (h2 : List.Lex r s t) :
    Shortlex r s t := by
  rw [Shortlex, h]
  exact Prod.Lex.right _ h2

/-- If two lists `s` and `t` have the same length, `s` is smaller than `t` under the shortlex order
over a relation `r` exactly when `s` is smaller than `t` under the lexicographic order over `r`-/
theorem _root_.List.shortlex_iff_lex {s t : List α} (h : s.length = t.length) :
    Shortlex r s t ↔ List.Lex r s t := by
  constructor
  · intro h2
    unfold Shortlex at h2
    rw [h, Prod.lex_def, lt_self_iff_false, false_or] at h2
    simp only [true_and] at h2
    exact h2
  exact fun h1 => of_lex h h1

theorem _root_.List.shortlex_def {s t : List α} : Shortlex r s t ↔
    s.length < t.length ∨ s.length = t.length ∧ List.Lex r s t := by
  constructor
  · intro hs
    unfold Shortlex at hs
    generalize hp : (s.length, s) = p at hs
    cases hs with
    | left b₁ b₂ h =>
      left
      rw [Prod.mk.injEq] at hp
      rw [← hp.1] at h
      exact h
    | right a h =>
      right
      rw [Prod.mk.injEq] at hp
      rw [← hp.2] at h
      exact ⟨hp.1, h⟩
  intro hpq
  rcases hpq with h1 | h2
  · exact of_length_lt h1
  exact of_lex h2.1 h2.2

theorem cons_iff [IsIrrefl α r] {a : α} {s t : List α} : Shortlex r (a :: s) (a :: t) ↔
    Shortlex r s t := by
  simp only [shortlex_def, length_cons, add_lt_add_iff_right, add_left_inj, List.Lex.cons_iff]

@[simp]
theorem not_nil_right {s : List α} : ¬ Shortlex r s [] := by
  rw [shortlex_def]
  rintro (h1 | h2)
  · simp only [List.length_nil, not_lt_zero'] at h1
  · exact List.Lex.not_nil_right _ _ h2.2

theorem nil_left_or_eq_nil (s : List α) : Shortlex r [] s ∨ s = [] := by
  cases s with
  | nil => right; rfl
  | cons head tail =>
    left
    apply of_length_lt
    simp only [List.length_nil, List.length_cons, Nat.succ_eq_add_one, lt_add_iff_pos_left,
      add_pos_iff, zero_lt_one, or_true]

@[simp]
theorem singleton_iff (a b : α) : Shortlex r [a] [b] ↔ r a b := by
  simp only [shortlex_def, length_singleton, lt_self_iff_false, Lex.singleton_iff, true_and,
    false_or]

instance isOrderConnected [IsOrderConnected α r] [IsTrichotomous α r] :
    IsOrderConnected (List α) (Shortlex r) where
  conn := by
    intro a b c ac
    rcases shortlex_def.mp ac with h1 | h2
    · rcases Nat.lt_or_ge a.length b.length with h3 | h4
      · left; exact of_length_lt h3
      rcases Nat.lt_or_ge b.length c.length with h3 | h4
      · right; exact of_length_lt h3
      omega
    rcases Nat.lt_or_ge a.length b.length with h3 | h4
    · left; exact of_length_lt h3
    rcases Nat.lt_or_ge b.length c.length with h3 | h4
    · right; exact of_length_lt h3
    have hab : a.length = b.length := by omega
    have hbc : b.length = c.length := by omega
    rcases List.Lex.isOrderConnected.aux r a b c h2.2 with h5 | h6
    · left
      exact of_lex hab h5
    right
    exact of_lex hbc h6

instance isTrichotomous [IsTrichotomous α r] : IsTrichotomous (List α) (Shortlex r) where
  trichotomous := by
    intro a b
    have : a.length < b.length ∨ a.length = b.length ∨ a.length > b.length :=
      trichotomous a.length b.length
    rcases this with h1 | h2 | h3
    · left; exact of_length_lt h1
    · induction a with
      | nil =>
        cases b with
        | nil => right; left; rfl
        | cons head tail => simp only [List.length_nil, List.length_cons, Nat.succ_eq_add_one,
          self_eq_add_left, add_eq_zero, List.length_eq_zero, one_ne_zero, and_false] at h2
      | cons head tail ih =>
        cases b with
        | nil => simp at h2
        | cons head1 tail1 =>
          simp only [length_cons, add_left_inj] at h2
          rcases @trichotomous _ (List.Lex r) _ (head :: tail) (head1 :: tail1) with h4 | h5 | h6
          · left
            apply of_lex
            · simp only [List.length_cons, Nat.succ_eq_add_one, add_left_inj]
              exact h2
            exact h4
          · right; left; exact h5
          right; right
          apply of_lex
          · simp only [List.length_cons, Nat.succ_eq_add_one, add_left_inj]
            exact h2.symm
          exact h6
    right; right
    exact of_length_lt h3

instance isAsymm [IsAsymm α r] : IsAsymm (List α) (Shortlex r) where
  asymm := by
    intro a b ab ba
    rcases shortlex_def.mp ab with h1 | h2
    · rcases shortlex_def.mp ba with h3 | h4
      · omega
      omega
    rcases shortlex_def.mp ba with h3 | h4
    · omega
    exact List.Lex.isAsymm.aux r a b h2.2 h4.2

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

theorem shortlexAccessible {a : α} (n : ℕ) (aca : Acc r a)
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
  have : ∀ n, ∀ (a : List α), a.length = n → Acc (Shortlex r) a := by
    intro n
    induction n using Nat.strongRecOn
    rename_i n ih
    cases n with
    | zero =>
      intro a len_a
      simp only [List.length_eq_zero] at len_a
      rw [len_a]
      exact Acc.intro _ <| fun _ ylt => (Shortlex.not_nil_right ylt).elim
    | succ n =>
      intro a len_a
      rcases List.exists_of_length_succ a len_a with ⟨head, tail, a_is⟩
      rw [a_is]
      rw [a_is, List.length_cons, add_left_inj] at len_a
      apply shortlexAccessible (n+1) (WellFounded.apply h head) (fun b bl => ih b.length bl _ rfl)
      · rw [len_a]
        exact lt_add_one n
      intro l ll
      apply ih l.length _ _ rfl
      rw [← len_a]
      exact ll
  exact WellFounded.intro fun a => this a.length _ rfl

end WellFounded

end Shortlex

end List
