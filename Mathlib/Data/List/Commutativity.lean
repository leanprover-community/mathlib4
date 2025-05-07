/-
Copyright (c) 2025 Shimanonogov Igor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shimanonogov Igor
-/
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Lemmas

/-!
# commutativity

In that In this file we prove the Lyndon-Schutzenberger theorem,
that states that lists commute if and only if they are the powers of the same list.
As a by-product, we prove various results about commutativity of append.

## Main results

- `comm_iff_common_root`: Lyndon-Schutzenberger theorem,
  lists commute if and only if they are repetitions of the same word.
-/

namespace List

variable {α : Type*} (n m : ℕ) {u v : List α}

theorem prefix_of_append_comm : (u ++ v = v ++ u) → (v <+: u ∨ u <+: v) := by
  intro h
  rw [List.append_eq_append_iff] at h
  cases h with
  | inl r =>
    right
    obtain ⟨as, h₁, h₂⟩ := r
    rw [h₁]
    exact List.prefix_append u as
  | inr l =>
    left
    obtain ⟨as, h₁, h₂⟩ := l
    rw [h₁]
    exact List.prefix_append v as


/-- Lyndon-Schutzenberger theorem: two lists commute with respect to append if and only if
    there are exists list `k`, that both of them are `k` repeated several times. -/
theorem comm_iff_repeatList_of_same {q p : List α} :
  (q ++ p = p ++ q) ↔ (∃ w k l, q = List.repeatList k w ∧ p = List.repeatList l w) := by
  constructor
  -- Forward direction (u++v=v++u → ∃w k l...)
  · intro h
    have pr := prefix_of_append_comm h
    match p, q with
      | [], smth =>
        exists smth, 1, 0
        constructor
        · simp
        · simp
      | smth, [] =>
        exists smth, 0, 1
      | hp :: tp, hq :: tq =>
        cases pr with
        | inr qp =>
          cases qp with
          | intro t ht =>
            rw [← ht]
            rw [← ht, List.append_assoc, List.append_cancel_left_eq] at h
            have bb := comm_iff_repeatList_of_same.mp h
            cases bb with | intro wc wct =>
            cases wct with | intro kc kct =>
            cases kct with | intro lc lct =>
            cases lct with
            | intro left right =>
              exists wc, kc, (kc+lc)
              constructor
              · assumption
              · rw [left, right, repeatList_append_repeatList]
        | inl pq =>
          cases pq with
            | intro t ht =>
              rw [← ht]
              rw [← ht, List.append_assoc, List.append_cancel_left_eq] at h
              have bb := comm_iff_repeatList_of_same.mp h.symm
              cases bb with | intro wc wct =>
              cases wct with | intro kc kct =>
              cases kct with | intro lc lct =>
              cases lct with
              | intro left right =>
                exists wc, (kc+lc), kc
                constructor
                · rw [left, right, repeatList_append_repeatList]
                · assumption

  -- Reverse direction (∃w k l... → u++v=v++u)
  · rintro ⟨w, k, l, rfl, rfl⟩
    rw [repeatList_append_repeatList, repeatList_append_repeatList, Nat.add_comm]

termination_by (p ++ q).length
decreasing_by

  · have n : (hp :: tp).length + t.length = (hq :: tq).length := by
        rw [← List.length_append]
        exact congrArg List.length ht
    rw [List.length_append, Nat.add_comm, n, List.length_append, List.length_cons]
    simp

  · have n : (hq :: tq).length + t.length = (hp :: tp).length := by
      rw [← List.length_append]
      exact congrArg List.length ht
    rw [List.length_append, Nat.add_comm, n, List.length_append, List.length_cons]
    simp

end List
