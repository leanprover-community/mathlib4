/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
import Mathlib.Computability.Language
import Mathlib.Algebra.Ring.Defs
import Mathlib.Computability.WeightedPath

/-!
# Weighted Deterministic Finite Automata

TODO: explain stuff.
-/

universe k u v

open Computability

/-- A Weighted DFA (`𝓐`) over a semiring (`𝓦 = (κ, ⊕, ⊗, 0, 1)`)
is a 5-tuple (`(α, σ, step, start, final)`) where
* (`α`) is a (finite) alphabet.
* (`σ`) is a (finite) set of states.
* (`step : σ → α → σ × κ`) is a (finite) set of transitions.
* (`start : σ × κ`) the start state and its weight.
* (`final : σ → κ`) is a weighting function assigning states their final values.
-/
structure WDFA (α : Type u) (σ : Type v) (κ : Type k) where
  /-- A transition function from state to state labelled by the alphabet producing a weight.  -/
  step : σ → α → σ × κ
  /-- Starting state and weight. -/
  start : σ × κ
  /-- Final weights. -/
  final : σ → κ

namespace WDFA

variable {α : Type u} {σ : Type v} {κ : Type k} (M : WDFA α σ κ) [W : Semiring κ]

instance [Inhabited σ] [Inhabited κ] : Inhabited (WDFA α σ κ) :=
⟨WDFA.mk (fun _ _ => ⟨default, default⟩) ⟨default, default⟩ (fun _ ↦ 0)⟩

def PathInWDFA {s₁ s₃ : σ} : WeightedPath α κ s₁ s₃ → Prop :=
  WeightedPath.All (fun q₁ a w q₂ ↦ M.step q₁ a = (q₂, w))

def AcceptingPathInWDFA {s₁ s₂ : σ} (π : WeightedPath α κ s₁ s₂) (w : κ) : Prop :=
  s₁ = M.start.1 ∧
  M.PathInWDFA π ∧
  w = M.start.2 * π.innerWeight * M.final s₂

/--
`M.evalFromL s x` evaluates `M` with input `x` starting from
the state `s` left-associatively.
-/
def evalFromL : σ × κ → List α → σ × κ :=
  List.foldl (fun sw a ↦ Prod.map id (W.mul sw.2) (M.step sw.1 a))

@[simp]
lemma evalFromL_nil (sw : σ × κ) : M.evalFromL sw [] = sw := rfl

@[simp]
lemma evalFromL_singleton (sw : σ × κ) (a : α) :
  M.evalFromL sw [a] = Prod.map id (W.mul sw.2) (M.step sw.1 a) := rfl

@[simp]
lemma evalFromL_append_singleton (sw : σ × κ) (x : List α) (a : α) :
  M.evalFromL sw (x ++ [a]) =
  Prod.map id (W.mul (M.evalFromL sw x).2) (M.step (M.evalFromL sw x).1 a) := by
  simp only [evalFromL, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp]
lemma evalFromL_cons (sw : σ × κ) (a : α) (x : List α) :
  M.evalFromL sw (a :: x) = M.evalFromL (Prod.map id (W.mul sw.2) (M.step sw.1 a)) x := by
  simp only [evalFromL, List.foldl_cons]

lemma evalFromL_append (sw : σ × κ) (x y : List α) :
  M.evalFromL sw (x ++ y) = M.evalFromL (M.evalFromL sw x) y := by
  simp only [evalFromL, List.foldl_append]

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval : List α → σ × κ :=
  M.evalFromL M.start

@[simp]
lemma eval_nil : M.eval [] = M.start := rfl

@[simp]
lemma eval_singleton (a : α) : M.eval [a] = Prod.map id (W.mul M.start.2) (M.step M.start.1 a) := by
  simp only [eval, evalFromL_singleton]

@[simp]
lemma eval_append_singleton (x : List α) (a : α) :
  M.eval (x ++ [a]) = Prod.map id (W.mul (M.eval x).2) (M.step (M.eval x).1 a) := by
  simp only [eval, evalFromL_append_singleton]

end WDFA
