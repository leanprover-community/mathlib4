/-
Copyright (c) 2022 Russell Emerine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Russell Emerine
-/
import Mathlib.Computability.RegularExpressionToNFA.Defs
import Mathlib.Data.List.Indexes

#align_import computability.regular_expression_to_NFA.star

/-!
# Proof That Converting `r*` to NFA is Correct

Proves that given that `r` converts to an NFA correctly, then `r*` converts to an NFA correctly.
This is done by induction using the stronger condition that the number of "resets" in the machine
matches the exponent in `r ^ n`.

TODO: possibly merge the files in regular_expression_to_NFA together?
-/


universe u

variable {α : Type u}

namespace RegularExpression

section Star

variable (r : RegularExpression α)

/-- `r.trace q n` encompasses all the words (`List.reverse`d due to the implementation of
`NFA.eval`) that have a partitioning of length `n + 1`, where the
first `n` substrings are each in the language of `r.toNFA` and the remaining suffix makes it to
state `q` in the NFA. `q` can also be seen to represent the state `some q` in `r.star.to_NFA`,
making `n` represent the number of resets, analogous to the exponent of `r`.
-/
inductive trace : r.State → ℕ → Language α
  | nil : ∀ {q}, q ∈ r.toNFA.start → trace q 0 []
  | step : ∀ p {a q x n}, q ∈ r.toNFA.step p a → x ∈ trace p n → trace q n (a :: x)
  | reset : ∀ p {q x n}, p ∈ r.toNFA.accept → q ∈ r.toNFA.start → x ∈ trace p n → trace q n.succ x

theorem star_eval (x : List α) (q : r.State) :
    some q ∈ r.star.toNFA.eval x ↔ ∃ n, x.reverse ∈ r.trace q n := by
  constructor
  · induction x using List.list_reverse_induction generalizing q
    case base => exact (⟨0, trace.nil ·⟩)
    case ind as a ih =>
      simp only [NFA.eval_append_singleton, NFA.mem_stepSet, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.singleton_append]
      rintro ⟨⟨⟩ | p, mem, step | ⟨r, accept, step, start⟩⟩ <;>
        rcases ih p mem with ⟨n, t⟩
      · exact ⟨n, trace.step p step t⟩
      · exact ⟨n + 1, trace.reset r accept start <| trace.step p step t⟩
  · rintro ⟨n, t⟩
    rw [← x.reverse_reverse]
    generalize xreq : x.reverse = xr at t
    induction t generalizing x
    case nil _ start => exact start
    case step p a q as _ step _ ih =>
      simp only [List.reverse_eq_iff] at ih
      rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet]
      exact ⟨some p, ih as.reverse rfl, Or.inl step⟩
    case reset p q xr n accept start t ih =>
      simp only [List.reverse_eq_iff] at ih
      rcases xr with ⟨⟩ | ⟨a, as⟩
      · exact start
      specialize ih _ rfl
      simp only [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet] at *
      rcases ih with ⟨⟨⟩ | q, mem, step | ⟨p, accept, step, _⟩⟩ <;>
        exact ⟨some q, mem, Or.inr ⟨p, accept, step, start⟩⟩

theorem pow_eval (x : List α) (n : ℕ) (hr : r.matches' = r.toNFA.accepts) :
    x ∈ (r ^ n.succ).matches' ↔ ∃ q, q ∈ r.toNFA.accept ∧ x.reverse ∈ r.trace q n := by
  induction n generalizing x
  case zero =>
    constructor
    · rintro ⟨y, ⟨⟩, z, z_matches, rfl⟩
      rw [hr] at z_matches
      rcases z_matches with ⟨q, accept, eval⟩
      refine' ⟨q, accept, _⟩; clear accept
      induction z using List.list_reverse_induction generalizing q
      case base => exact trace.nil eval
      case ind as a ih =>
        rw [NFA.eval_append_singleton, NFA.mem_stepSet] at eval
        simp only [← List.concat_eq_append, List.nil_append, List.reverse_concat]
        rcases eval with ⟨p, mem, step⟩
        exact trace.step p step (ih p mem)
    · rintro ⟨q, accept, t⟩
      refine' ⟨[], rfl, x, hr ▸ ⟨q, accept, _⟩, by simp⟩
      clear accept
      induction x using List.list_reverse_induction generalizing q
      case base =>
        rcases t with ⟨start⟩ | ⟨⟩ | ⟨⟩
        exact start
      case ind as a ih =>
        rw [NFA.eval_append_singleton, NFA.mem_stepSet]
        rw [← List.concat_eq_append, List.reverse_concat] at t
        rcases t with ⟨⟩ | ⟨p, step, t⟩ | ⟨⟩
        exact ⟨p, ih p t, step⟩
  case succ n ih =>
    constructor
    · rw [matches'_pow, Nat.succ_eq_add_one, pow_add, ← matches'_pow, pow_one]
      rintro ⟨y, hy, z, hz, rfl⟩
      rw [hr] at hz
      rw [ih y] at hy
      rcases hz with ⟨q, accept, eval⟩
      refine' ⟨q, accept, _⟩; clear accept
      induction z using List.list_reverse_induction generalizing q
      case base =>
        rcases hy with ⟨p, accept, t⟩
        simp only [List.append_nil]
        exact trace.reset p accept eval t
      case ind as a ih =>
        rw [NFA.eval_append_singleton, NFA.mem_stepSet] at eval
        rcases eval with ⟨p, mem, step⟩
        simp only [← List.append_assoc]
        rw [← List.concat_eq_append, List.reverse_concat]
        exact trace.step p step (ih p mem)
    · rintro ⟨q, accept, t⟩
      rw [matches'_pow, Nat.succ_eq_add_one, pow_add, ← matches'_pow, pow_one]
      suffices ∃ y z, y ∈ (r ^ n.succ).matches' ∧ q ∈ r.toNFA.eval z ∧ y ++ z = x by
        rcases this with ⟨y, z, y_matches, eval, eq⟩
        refine' ⟨y, y_matches, z, _, eq⟩
        exact hr ▸ ⟨q, accept, eval⟩
      clear accept
      induction x using List.list_reverse_induction generalizing q
      case base =>
        rcases t with ⟨⟩ | ⟨⟩ | ⟨p, p_accept, start, t⟩
        exact ⟨[], [], ih [] |>.mpr ⟨p, p_accept, t⟩, start, by simp⟩
      case ind as a x_ih =>
        rw [← List.concat_eq_append, List.reverse_concat] at t
        rcases t with ⟨⟩ | ⟨p, step, t⟩ | ⟨p, accept, start, t⟩
        · rcases x_ih p t with ⟨y, z, y_matches, eval, rfl⟩
          refine' ⟨y, z ++ [a], y_matches, _, by simp⟩
          rw [NFA.eval_append_singleton, NFA.mem_stepSet]
          exact ⟨p, eval, step⟩
        · rw [← List.reverse_concat] at t
          exact ⟨as.concat a, [], ih (as.concat a) |>.mpr ⟨p, accept, t⟩, start, by simp⟩

end Star

end RegularExpression

