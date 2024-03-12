/-
Copyright (c) 2024 Google. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
import Mathlib.Computability.DFA
import Mathlib.Data.Set.Finite

/-!
# Myhill–Nerode theorem

This file proves the Myhill–Nerode theorem via left quotients.

Given a language `L` and a word `x`, the *left quotient* is the set of suffixes `y` such that
`x ++ y` is in `L`. The *Myhill–Nerode theorem* shows that each left quotient, in fact, corresponds
to the state of an automaton that matches `L`, and that `L` is regular if and only if there are
finitely many such states.

## Implementation notes

Since mathlib doesn't have an `IsRegular` definition yet, we define regularity directly as the
existence of a DFA.

## References

* <https://en.wikipedia.org/wiki/Syntactic_monoid#Myhill%E2%80%93Nerode_theorem>
-/

universe u v
variable {α : Type u} {σ : Type v} (L : Language α)

namespace Language

/-- The *left quotient* of `x` is the set of suffixes `y` such that `x ++ y` is in `L`. -/
def leftQuotient (x : List α) : Language α := { y | x ++ y ∈ L }

@[simp]
theorem leftQuotient_nil : L.leftQuotient [] = L := rfl

@[simp]
theorem leftQuotient_append (x y : List α) :
    L.leftQuotient (x ++ y) = (L.leftQuotient x).leftQuotient y := by
  dsimp [leftQuotient, Language]
  simp_rw [List.append_assoc]

@[simp]
theorem leftQuotient_mem (x y : List α) : y ∈ L.leftQuotient x ↔ x ++ y ∈ L := Iff.rfl

theorem leftQuotient_accepts (M : DFA α σ) (x : List α) :
    leftQuotient M.accepts x = M.acceptsFrom (M.eval x) := by
  ext y
  rw [DFA.mem_acceptsFrom, DFA.eval, ← DFA.evalFrom_of_append, ← DFA.mem_accepts, leftQuotient_mem]

theorem leftQuotient_accepts' (M : DFA α σ) : leftQuotient M.accepts = M.acceptsFrom ∘ M.eval :=
  funext <| leftQuotient_accepts M

theorem finite_leftQuotient_of_dfa [Finite σ] (M : DFA α σ) :
    Set.Finite (Set.range M.accepts.leftQuotient) :=
  leftQuotient_accepts' M ▸
    Set.finite_of_finite_preimage (Set.toFinite _)
      (Set.range_comp_subset_range M.eval M.acceptsFrom)

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
theorem mem_toDFA_accept (s : Set.range L.leftQuotient) : s ∈ L.toDFA.accept ↔ [] ∈ s.val := Iff.rfl

@[simp]
theorem toDFA_step (s : Set.range L.leftQuotient) (a : α) :
    (L.toDFA.step s a).val = s.val.leftQuotient [a] := rfl

@[simp]
theorem toDFA_start : L.toDFA.start.val = L := rfl

@[simp]
theorem toDFA_accepts : L.toDFA.accepts = L := by
  ext x
  rw [DFA.mem_accepts, ← DFA.eval]
  suffices L.toDFA.eval x = L.leftQuotient x by simp [this]
  induction x using List.list_reverse_induction with
  | base => simp
  | ind x a ih => simp [ih]

theorem exists_dfa_of_finite_leftQuotient (h : Set.Finite (Set.range L.leftQuotient)) :
    ∃ n, ∃ M : DFA α (Fin n), M.accepts = L :=
  have ⟨n, ⟨f⟩⟩ := h.exists_equiv_fin
  ⟨n, DFA.equivOfStates f L.toDFA, by simp⟩

/--
**Myhill–Nerode theorem**. There exists a DFA for a language if and only if the set of left
quotients is finite.
-/
theorem exists_dfa_iff_finite_leftQuotient :
    (∃ n, ∃ M : DFA α (Fin n), M.accepts = L) ↔ Set.Finite (Set.range L.leftQuotient) :=
  ⟨fun ⟨_, M, hM⟩ => hM ▸ finite_leftQuotient_of_dfa M, exists_dfa_of_finite_leftQuotient L⟩

end Language
