/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Yaël Dillies
-/
import Mathlib.Computability.NFA

/-!
# Epsilon Nondeterministic Finite Automata

This file contains the definition of an epsilon Nondeterministic Finite Automaton (`εNFA`), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitions,
which can be followed without reading a character.
Since this definition allows for automata with infinite states, a `Fintype` instance must be
supplied for true `εNFA`'s.
-/


open Set

open Computability

-- "ε_NFA"

universe u v

/-- An `εNFA` is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `Set` of states and can make ε-transitions by
  inputting `none`.
  Since this definition allows for Automata with infinite states, a `Fintype` instance must be
  supplied for true `εNFA`'s. -/
structure εNFA (α : Type u) (σ : Type v) where
  /-- Transition function. The automaton is rendered non-deterministic by this transition function
  returning `Set σ` (rather than `σ`), and ε-transitions are made possible by taking `Option α`
  (rather than `α`). -/
  step : σ → Option α → Set σ
  /-- Starting states. -/
  start : Set σ
  /-- Set of acceptance states. -/
  accept : Set σ

variable {α : Type u} {σ : Type v} (M : εNFA α σ) {S : Set σ} {s : σ} {a : α}

namespace εNFA

/-- The `εClosure` of a set is the set of states which can be reached by taking a finite string of
ε-transitions from an element of the set. -/
inductive εClosure (S : Set σ) : Set σ
  | base : ∀ s ∈ S, εClosure S s
  | step : ∀ (s), ∀ t ∈ M.step s none, εClosure S s → εClosure S t

@[simp]
theorem subset_εClosure (S : Set σ) : S ⊆ M.εClosure S :=
  εClosure.base

@[simp]
theorem εClosure_empty : M.εClosure ∅ = ∅ :=
  eq_empty_of_forall_not_mem fun s hs ↦ by induction hs <;> assumption

@[simp]
theorem εClosure_univ : M.εClosure univ = univ :=
  eq_univ_of_univ_subset <| subset_εClosure _ _

/-- `M.stepSet S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`. -/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.εClosure (M.step s a)

variable {M}

@[simp]
theorem mem_stepSet_iff : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.εClosure (M.step t a) := by
  simp_rw [stepSet, mem_iUnion₂, exists_prop]

@[simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by
  simp_rw [stepSet, mem_empty_iff_false, iUnion_false, iUnion_empty]

variable (M)

/-- `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element
of `S`. -/
def evalFrom (start : Set σ) : List α → Set σ :=
  List.foldl M.stepSet (M.εClosure start)

@[simp]
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = M.εClosure S :=
  rfl

@[simp]
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet (M.εClosure S) a :=
  rfl

@[simp]
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  rw [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp]
theorem evalFrom_empty (x : List α) : M.evalFrom ∅ x = ∅ := by
  induction' x using List.reverseRecOn with x a ih
  · rw [evalFrom_nil, εClosure_empty]
  · rw [evalFrom_append_singleton, ih, stepSet_empty]

/-- `M.eval x` computes all possible paths through `M` with input `x` starting at an element of
`M.start`. -/
def eval :=
  M.evalFrom M.start

@[simp]
theorem eval_nil : M.eval [] = M.εClosure M.start :=
  rfl

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet (M.εClosure M.start) a :=
  rfl

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α :=
  { x | ∃ S ∈ M.accept, S ∈ M.eval x }

/-! ### Conversions between `εNFA` and `NFA` -/


/-- `M.toNFA` is an `NFA` constructed from an `εNFA` `M`. -/
def toNFA : NFA α σ where
  step S a := M.εClosure (M.step S a)
  start := M.εClosure M.start
  accept := M.accept

@[simp]
theorem toNFA_evalFrom_match (start : Set σ) :
    M.toNFA.evalFrom (M.εClosure start) = M.evalFrom start :=
  rfl

@[simp]
theorem toNFA_correct : M.toNFA.accepts = M.accepts :=
  rfl

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c, x = a ++ b ++ c ∧
      a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts :=
  M.toNFA.pumping_lemma hx hlen

end εNFA

namespace NFA

/-- `M.toεNFA` is an `εNFA` constructed from an `NFA` `M` by using the same start and accept
  states and transition functions. -/
def toεNFA (M : NFA α σ) : εNFA α σ where
  step s a := a.casesOn' ∅ fun a ↦ M.step s a
  start := M.start
  accept := M.accept

@[simp]
theorem toεNFA_εClosure (M : NFA α σ) (S : Set σ) : M.toεNFA.εClosure S = S := by
  ext a
  refine ⟨?_, εNFA.εClosure.base _⟩
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩)
  · exact h
  · cases h

@[simp]
theorem toεNFA_evalFrom_match (M : NFA α σ) (start : Set σ) :
    M.toεNFA.evalFrom start = M.evalFrom start := by
  rw [evalFrom, εNFA.evalFrom, toεNFA_εClosure]
  suffices εNFA.stepSet (toεNFA M) = stepSet M by rw [this]
  ext S s
  simp only [stepSet, εNFA.stepSet, exists_prop, Set.mem_iUnion]
  apply exists_congr
  simp only [and_congr_right_iff]
  intro _ _
  rw [M.toεNFA_εClosure]
  rfl

@[simp]
theorem toεNFA_correct (M : NFA α σ) : M.toεNFA.accepts = M.accepts := by
  rw [εNFA.accepts, εNFA.eval, toεNFA_evalFrom_match]
  rfl

end NFA

/-! ### Regex-like operations -/


namespace εNFA

instance : Zero (εNFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, ∅, ∅⟩⟩

instance : One (εNFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, univ, univ⟩⟩

instance : Inhabited (εNFA α σ) :=
  ⟨0⟩

@[simp]
theorem step_zero (s a) : (0 : εNFA α σ).step s a = ∅ :=
  rfl

@[simp]
theorem step_one (s a) : (1 : εNFA α σ).step s a = ∅ :=
  rfl

@[simp]
theorem start_zero : (0 : εNFA α σ).start = ∅ :=
  rfl

@[simp]
theorem start_one : (1 : εNFA α σ).start = univ :=
  rfl

@[simp]
theorem accept_zero : (0 : εNFA α σ).accept = ∅ :=
  rfl

@[simp]
theorem accept_one : (1 : εNFA α σ).accept = univ :=
  rfl

end εNFA
