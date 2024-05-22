/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Powerset

#align_import computability.NFA from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

/-!
# Nondeterministic Finite Automata
This file contains the definition of a Nondeterministic Finite Automaton (NFA), a state machine
which determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular
set by evaluating the string over every possible path.
We show that DFA's are equivalent to NFA's however the construction from NFA to DFA uses an
exponential number of states.
Note that this definition allows for Automaton with infinite states; a `Fintype` instance must be
supplied for true NFA's.
-/

open Set

open Computability

universe u v

-- Porting note: Required as `NFA` is used in mathlib3
set_option linter.uppercaseLean3 false

/-- An NFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a set of starting states (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `Set` of states. These are the states that it
  may be sent to. -/
structure NFA (α : Type u) (σ : Type v) where
  step : σ → α → Set σ
  start : Set σ
  accept : Set σ
#align NFA NFA

variable {α : Type u} {σ σ' : Type v} (M : NFA α σ)

namespace NFA

instance : Inhabited (NFA α σ) :=
  ⟨NFA.mk (fun _ _ => ∅) ∅ ∅⟩

/-- `M.stepSet S a` is the union of `M.step s a` for all `s ∈ S`. -/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.step s a
#align NFA.step_set NFA.stepSet

theorem mem_stepSet (s : σ) (S : Set σ) (a : α) : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.step t a := by
  simp [stepSet]
#align NFA.mem_step_set NFA.mem_stepSet

@[simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by simp [stepSet]
#align NFA.step_set_empty NFA.stepSet_empty

/-- `M.evalFrom S x` computes all possible paths though `M` with input `x` starting at an element
  of `S`. -/
def evalFrom (start : Set σ) : List α → Set σ :=
  List.foldl M.stepSet start
#align NFA.eval_from NFA.evalFrom

@[simp]
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = S :=
  rfl
#align NFA.eval_from_nil NFA.evalFrom_nil

@[simp]
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet S a :=
  rfl
#align NFA.eval_from_singleton NFA.evalFrom_singleton

@[simp]
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]
#align NFA.eval_from_append_singleton NFA.evalFrom_append_singleton

/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start`. -/
def eval : List α → Set σ :=
  M.evalFrom M.start
#align NFA.eval NFA.eval

@[simp]
theorem eval_nil : M.eval [] = M.start :=
  rfl
#align NFA.eval_nil NFA.eval_nil

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet M.start a :=
  rfl
#align NFA.eval_singleton NFA.eval_singleton

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _
#align NFA.eval_append_singleton NFA.eval_append_singleton

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α := {x | ∃ S ∈ M.accept, S ∈ M.eval x}
#align NFA.accepts NFA.accepts

theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ ∃ S ∈ M.accept, S ∈ M.evalFrom M.start x := by
  rfl

/-- `M.toDFA` is a `DFA` constructed from an `NFA` `M` using the subset construction. The
  states is the type of `Set`s of `M.state` and the step function is `M.stepSet`. -/
def toDFA : DFA α (Set σ) where
  step := M.stepSet
  start := M.start
  accept := { S | ∃ s ∈ S, s ∈ M.accept }
#align NFA.to_DFA NFA.toDFA

@[simp]
theorem toDFA_correct : M.toDFA.accepts = M.accepts := by
  ext x
  rw [mem_accepts, DFA.mem_accepts]
  constructor <;> · exact fun ⟨w, h2, h3⟩ => ⟨w, h3, h2⟩
#align NFA.to_DFA_correct NFA.toDFA_correct

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by
  rw [← toDFA_correct] at hx ⊢
  exact M.toDFA.pumping_lemma hx hlen
#align NFA.pumping_lemma NFA.pumping_lemma

end NFA

namespace DFA

/-- `M.toNFA` is an `NFA` constructed from a `DFA` `M` by using the same start and accept
  states and a transition function which sends `s` with input `a` to the singleton `M.step s a`. -/
@[simps] def toNFA (M : DFA α σ') : NFA α σ' where
  step s a := {M.step s a}
  start := {M.start}
  accept := M.accept
#align DFA.to_NFA DFA.toNFA

@[simp]
theorem toNFA_evalFrom_match (M : DFA α σ) (start : σ) (s : List α) :
    M.toNFA.evalFrom {start} s = {M.evalFrom start s} := by
  change List.foldl M.toNFA.stepSet {start} s = {List.foldl M.step start s}
  induction' s with a s ih generalizing start
  · tauto
  · rw [List.foldl, List.foldl,
      show M.toNFA.stepSet {start} a = {M.step start a} by simp [NFA.stepSet] ]
    tauto
#align DFA.to_NFA_eval_from_match DFA.toNFA_evalFrom_match

@[simp]
theorem toNFA_correct (M : DFA α σ) : M.toNFA.accepts = M.accepts := by
  ext x
  rw [NFA.mem_accepts, toNFA_start, toNFA_evalFrom_match]
  constructor
  · rintro ⟨S, hS₁, hS₂⟩
    rwa [Set.mem_singleton_iff.mp hS₂] at hS₁
  · exact fun h => ⟨M.eval x, h, rfl⟩
#align DFA.to_NFA_correct DFA.toNFA_correct

end DFA
