/-
Copyright (c) 2024 Google. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
module

public import Mathlib.Computability.DFA

import Mathlib.Data.Set.Finite.Basic

/-!
# Myhill–Nerode theorem

This file proves the Myhill–Nerode theorem using left quotients.

Given a language `L` and a word `x`, the *left quotient* of `L` by `x` is the set of suffixes `y`
such that `x * y` is in `L`. The *Myhill–Nerode theorem* shows that each left quotient, in fact,
corresponds to the state of an automaton that matches `L`, and that `L` is regular if and only if
there are finitely many such states.

## References

* <https://en.wikipedia.org/wiki/Syntactic_monoid#Myhill%E2%80%93Nerode_theorem>
-/

@[expose] public section

universe u v
variable {α : Type u} {σ : Type v} {L : Language α}

namespace Language

variable (L) in
/-- The *left quotient* of `x` is the set of suffixes `y` such that `x ++ y` is in `L`. -/
def leftQuotient (x : FreeMonoid α) : Language α := .ofSet {y | x * y ∈ L.toSet}

variable (L) in
@[simp]
theorem leftQuotient_one : L.leftQuotient 1 = L := rfl

variable (L) in
theorem leftQuotient_mul (x y : FreeMonoid α) :
    L.leftQuotient (x * y) = (L.leftQuotient x).leftQuotient y := by
  simp [leftQuotient, mul_assoc]

@[deprecated (since := "2026-10-31")] alias leftQuotient_nil := leftQuotient_one
@[deprecated (since := "2026-10-31")] alias leftQuotient_append := leftQuotient_mul

@[simp]
theorem mem_leftQuotient (x y : FreeMonoid α) : y ∈ (L.leftQuotient x).toSet ↔ x * y ∈ L.toSet :=
  Iff.rfl

theorem leftQuotient_accepts_apply (M : DFA α σ) (x : FreeMonoid α) :
    M.accepts.leftQuotient x = M.acceptsFrom (M.eval x) := by
  ext y
  simp [DFA.mem_accepts, DFA.mem_acceptsFrom, DFA.eval, DFA.evalFrom_mul]

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
    refine ⟨s.val.leftQuotient (.of a), ?_⟩
    obtain ⟨y, hy⟩ := s.prop
    exists y * .of a
    rw [← hy, leftQuotient_mul]
  start := ⟨L, by exists 1⟩
  accept := {s | 1 ∈ s.val.toSet}

@[simp]
theorem mem_accept_toDFA (s : Set.range L.leftQuotient) : s ∈ L.toDFA.accept ↔ 1 ∈ s.val.toSet :=
  Iff.rfl

@[simp]
theorem step_toDFA (s : Set.range L.leftQuotient) (a : α) :
    (L.toDFA.step s a).val = s.val.leftQuotient (.of a) := rfl

variable (L) in
@[simp]
theorem start_toDFA : L.toDFA.start.val = L := rfl

variable (L) in
@[simp]
theorem accepts_toDFA : L.toDFA.accepts = L := by
  ext x
  rw [DFA.mem_accepts]
  suffices L.toDFA.eval x = L.leftQuotient x by simp [this]
  induction x using FreeMonoid.reverseMulRecOn with
  | one => simp
  | mul_of x a ih => simp [ih, leftQuotient_mul]

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
