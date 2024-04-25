/-
Copyright (c) 2022 Russell Emerine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Russell Emerine
-/
import Computability.RegularExpressionToNFA.Defs

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

theorem star_iff_pow {r : RegularExpression α} {x} :
    x ∈ r.unit.matches' ↔ ∃ n : ℕ, x ∈ (r ^ n).matches' :=
  by
  constructor
  · intro h
    rcases h with ⟨xs, join, all_match⟩
    rw [join]; clear join
    revert all_match
    induction xs
    case nil =>
      intro h
      exact ⟨0, rfl⟩
    case cons x xs ih =>
      intro h
      simp only [List.mem_cons, forall_eq_or_imp] at h
      cases' h with x_match all_match
      specialize ih all_match
      rcases ih with ⟨n, ih⟩
      exact ⟨n.succ, x, xs.join, x_match, ih, rfl⟩
  · intro h
    rcases h with ⟨n, x_matches⟩
    revert x x_matches
    induction n
    case zero =>
      intro x h
      cases h
      refine' ⟨[], by simp, _⟩
      intro y h
      cases h
    case succ n ih =>
      intro x h
      rcases h with ⟨y, z, y_matches, z_matches, append⟩
      specialize ih z_matches
      rcases ih with ⟨zs, join, all_match⟩
      rw [← append]; clear append x
      refine' ⟨y :: zs, by simp [join], _⟩
      intro w h
      cases h
      case inl => rw [h]; exact y_matches
      case inr => exact all_match w h

section Star

variable (r : RegularExpression α)

/-- `r.trace x q n` represents a way to get to state q using transitions that recognise x. `q` looks
like a state in `r.to_NFA`, but it really represents the state `some q` in `r.star.to_NFA`. `n`
represents the number of resets, which corresponds to the exponent of `r`.
-/
inductive Trace : List α → r.StateM → ℕ → Prop
  | nil : ∀ {q}, q ∈ r.toNFA.start → trace List.nil q 0
  | step : ∀ {p a q x n}, q ∈ r.toNFA.step p a → trace x p n → trace (a :: x) q n
  | reset : ∀ {p q x n}, p ∈ r.toNFA.accept → q ∈ r.toNFA.start → trace x p n → trace x q n.succ

theorem star_eval (x : List α) (q : r.StateM) :
    some q ∈ r.unit.toNFA.eval x ↔ ∃ n, r.trace x.reverse q n :=
  by
  constructor
  · rw [← x.reverse_reverse]
    rw [x.reverse.reverse_reverse]
    induction x.reverse generalizing q
    case nil =>
      intro h
      exact ⟨0, trace.nil h⟩
    case cons a as ih =>
      intro h
      rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet] at h
      rcases h with ⟨p, mem, step⟩
      cases p; cases step
      rcases ih p mem with ⟨n, t⟩
      cases step
      case inl => exact ⟨n, trace.step step t⟩
      case inr =>
        rcases step with ⟨r, accept, step, start⟩
        refine' ⟨n + 1, trace.reset accept start _⟩
        exact trace.step step t
  · intro h
    rcases h with ⟨n, t⟩
    rw [← x.reverse_reverse]
    induction t
    case nil q start => exact start
    case step p a q as n step t
      ih =>
      rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet]
      exact ⟨some p, ih, Or.inl step⟩
    case reset p q x n accept start t ih =>
      cases x
      case nil => exact start
      case cons a
        as =>
        rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet] at *
        rcases ih with ⟨r, mem, step⟩
        cases' r with r; cases step
        refine' ⟨some r, mem, Or.inr _⟩
        cases step
        case inl => exact ⟨p, accept, step, start⟩
        case inr =>
          rcases step with ⟨s, accept, step, _⟩
          exact ⟨s, accept, step, start⟩

theorem pow_eval (x : List α) (n : ℕ) (hr : r.matches' = r.toNFA.accepts) :
    x ∈ (r ^ n.succ).matches' ↔ ∃ q, q ∈ r.toNFA.accept ∧ r.trace x.reverse q n :=
  by
  induction n generalizing x
  case zero =>
    constructor
    · intro h
      rcases h with ⟨y, z, h, z_matches, eq⟩
      cases z_matches
      rw [List.append_nil] at eq; rw [Eq] at *; clear z_matches eq y
      rw [hr] at h; clear hr
      rcases h with ⟨q, accept, eval⟩
      refine' ⟨q, accept, _⟩; clear accept
      rw [← x.reverse_reverse] at eval
      revert eval
      induction x.reverse generalizing q
      case nil =>
        intro h
        exact trace.nil h
      case cons a as =>
        intro h
        rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet] at h
        rcases h with ⟨p, mem, step⟩
        exact trace.step step (ih p mem)
    · intro h
      refine' ⟨x, [], _, rfl, by simp⟩
      rcases h with ⟨q, accept, t⟩
      rw [hr]; clear hr
      refine' ⟨q, accept, _⟩; clear accept
      rw [← x.reverse_reverse]
      revert t
      induction x.reverse generalizing q
      case nil =>
        intro t
        cases' t with _ start
        exact start
      case cons a as =>
        intro t
        rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet]
        cases' t with _ _ p _ _ _ _ step t
        exact ⟨p, ih p t, step⟩
  case succ n ih =>
    constructor
    · intro h
      rw [matches_pow, Nat.succ_eq_add_one, pow_add, ← matches_pow, pow_one] at h
      rcases h with ⟨y, z, hy, hz, eq⟩
      rw [← Eq] at *; clear eq x
      rw [hr] at hz; clear hr
      rw [ih y] at hy; clear ih
      rcases hz with ⟨q, accept, eval⟩
      refine' ⟨q, accept, _⟩; clear accept
      rw [← z.reverse_reverse] at eval
      rw [List.reverse_append]
      revert eval
      induction z.reverse generalizing q
      case nil =>
        intro eval
        rcases hy with ⟨p, accept, t⟩
        exact trace.reset accept eval t
      case cons a as =>
        intro eval
        rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet] at eval
        rcases eval with ⟨p, mem, step⟩
        exact trace.step step (ih p mem)
    · rintro ⟨q, accept, t⟩
      rw [matches_pow, Nat.succ_eq_add_one, pow_add, ← matches_pow, pow_one]
      suffices ∃ y z, y ∈ (r ^ n.succ).matches' ∧ q ∈ r.to_NFA.eval z ∧ y ++ z = x
        by
        rcases this with ⟨y, z, y_matches, eval, eq⟩
        refine' ⟨y, z, y_matches, _, Eq⟩
        rw [hr]
        exact ⟨q, accept, eval⟩
      clear accept
      rw [← x.reverse_reverse]
      revert t
      induction x.reverse generalizing q
      case nil =>
        intro t
        cases' t with _ _ _ _ _ _ _ _ _ p _ _ _ p_accept start t
        refine' ⟨[], [], _, start, by simp⟩
        rw [ih []]
        exact ⟨p, p_accept, t⟩
      case cons a as x_ih =>
        intro t
        cases t
        case step p _ _ _ step
          t =>
          rcases x_ih p t with ⟨y, z, y_matches, eval, eq⟩
          refine' ⟨y, z ++ [a], y_matches, _, by simp [← Eq]⟩
          rw [NFA.eval_append_singleton, NFA.mem_stepSet]
          exact ⟨p, eval, step⟩
        case reset p _ _ accept start
          t =>
          refine' ⟨(a :: as).reverse, [], _, start, by simp⟩
          rw [ih (a :: as).reverse]
          rw [(a :: as).reverse_reverse]
          exact ⟨p, accept, t⟩

end Star

end RegularExpression

