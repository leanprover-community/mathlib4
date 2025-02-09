/-
Copyright (c) 2024 Google. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
import Mathlib.Computability.DFA
import Mathlib.Data.Set.Finite.Basic

/-!
# Myhill–Nerode theorem

This file proves the Myhill–Nerode theorem using left quotients.

Given a language `L` and a word `x`, the *left quotient* of `L` by `x` is the set of suffixes `y`
such that `x ++ y` is in `L`. The *Myhill–Nerode theorem* shows that each left quotient, in fact,
corresponds to the state of an automaton that matches `L`, and that `L` is regular if and only if
there are finitely many such states.

## References

* <https://en.wikipedia.org/wiki/Syntactic_monoid#Myhill%E2%80%93Nerode_theorem>
-/

universe u v
variable {α : Type u} {σ : Type v} {L : Language α}

namespace Language

variable (L) in
/-- The *left quotient* of `x` is the set of suffixes `y` such that `x ++ y` is in `L`. -/
def leftQuotient (x : List α) : Language α := { y | x ++ y ∈ L }

variable (L) in
@[simp]
theorem leftQuotient_nil : L.leftQuotient [] = L := rfl

variable (L) in
theorem leftQuotient_append (x y : List α) :
    L.leftQuotient (x ++ y) = (L.leftQuotient x).leftQuotient y := by
  simp [leftQuotient, Language]

@[simp]
theorem mem_leftQuotient (x y : List α) : y ∈ L.leftQuotient x ↔ x ++ y ∈ L := Iff.rfl

theorem leftQuotient_accepts_apply (M : DFA α σ) (x : List α) :
    leftQuotient M.accepts x = M.acceptsFrom (M.eval x) := by
  ext y
  simp [DFA.mem_accepts, DFA.mem_acceptsFrom, DFA.eval, DFA.evalFrom_of_append]

theorem leftQuotient_accepts (M : DFA α σ) : leftQuotient M.accepts = M.acceptsFrom ∘ M.eval :=
  funext <| leftQuotient_accepts_apply M

theorem IsRegular.finite_range_leftQuotient (h : L.IsRegular) :
    (Set.range L.leftQuotient).Finite := by
  have ⟨σ, x, M, hM⟩ := h
  rw [← hM, leftQuotient_accepts]
  exact Set.finite_of_finite_preimage (Set.toFinite _)
    (Set.range_comp_subset_range M.eval M.acceptsFrom)

variable (L) in
/-- The left quotients of a language are the states of an automaton that accepts the language. -/
def toDFA : DFA α (Set.range L.leftQuotient) where
  step s a := by
    refine ⟨s.val.leftQuotient [a], ?_⟩
    obtain ⟨y, hy⟩ := s.prop
    exists y ++ [a]
    rw [← hy, leftQuotient_append]
  start := ⟨L, by exists []⟩
  accept := { s | [] ∈ s.val }

@[simp]
theorem mem_accept_toDFA (s : Set.range L.leftQuotient) : s ∈ L.toDFA.accept ↔ [] ∈ s.val := Iff.rfl

@[simp]
theorem step_toDFA (s : Set.range L.leftQuotient) (a : α) :
    (L.toDFA.step s a).val = s.val.leftQuotient [a] := rfl

variable (L) in
@[simp]
theorem start_toDFA : L.toDFA.start.val = L := rfl

variable (L) in
@[simp]
theorem accepts_toDFA : L.toDFA.accepts = L := by
  ext x
  rw [DFA.mem_accepts]
  suffices L.toDFA.eval x = L.leftQuotient x by simp [this]
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih, leftQuotient_append]

theorem IsRegular.of_finite_range_leftQuotient (h : Set.Finite (Set.range L.leftQuotient)) :
    L.IsRegular :=
  Language.isRegular_iff.mpr ⟨_, h.fintype, L.toDFA, by simp⟩

/--
**Myhill–Nerode theorem**. A language is regular if and only if the set of left quotients is finite.
-/
theorem isRegular_iff_finite_range_leftQuotient :
    L.IsRegular ↔ (Set.range L.leftQuotient).Finite :=
  ⟨IsRegular.finite_range_leftQuotient, .of_finite_range_leftQuotient⟩

end Language
