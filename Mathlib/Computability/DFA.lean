/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Chris Wong
-/
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.NormNum

#align_import computability.DFA from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

/-!
# Deterministic Finite Automata

This file contains the definition of a Deterministic Finite Automaton (DFA), a state machine which
determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular set
in linear time.
Note that this definition allows for Automaton with infinite states, a `Fintype` instance must be
supplied for true DFA's.
-/


open Computability

universe u v

set_option linter.uppercaseLean3 false

/-- A DFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`). -/
structure DFA (α : Type u) (σ : Type v) where
  /-- A transition function from state to state labelled by the alphabet. -/
  step : σ → α → σ
  /-- Starting state. -/
  start : σ
  /-- Set of acceptance states. -/
  accept : Set σ
#align DFA DFA

namespace DFA

variable {α : Type u} {σ : Type v} (M : DFA α σ)

instance [Inhabited σ] : Inhabited (DFA α σ) :=
  ⟨DFA.mk (fun _ _ => default) default ∅⟩

/-- `M.evalFrom s x` evaluates `M` with input `x` starting from the state `s`. -/
def evalFrom (start : σ) : List α → σ :=
  List.foldl M.step start
#align DFA.eval_from DFA.evalFrom

@[simp]
theorem evalFrom_nil (s : σ) : M.evalFrom s [] = s :=
  rfl
#align DFA.eval_from_nil DFA.evalFrom_nil

@[simp]
theorem evalFrom_singleton (s : σ) (a : α) : M.evalFrom s [a] = M.step s a :=
  rfl
#align DFA.eval_from_singleton DFA.evalFrom_singleton

@[simp]
theorem evalFrom_append_singleton (s : σ) (x : List α) (a : α) :
    M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]
#align DFA.eval_from_append_singleton DFA.evalFrom_append_singleton

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval : List α → σ :=
  M.evalFrom M.start
#align DFA.eval DFA.eval

@[simp]
theorem eval_nil : M.eval [] = M.start :=
  rfl
#align DFA.eval_nil DFA.eval_nil

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.step M.start a :=
  rfl
#align DFA.eval_singleton DFA.eval_singleton

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.step (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _
#align DFA.eval_append_singleton DFA.eval_append_singleton

theorem evalFrom_of_append (start : σ) (x y : List α) :
    M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y :=
  x.foldl_append _ _ y
#align DFA.eval_from_of_append DFA.evalFrom_of_append

/--
`M.acceptsFrom start` is the language of `x` such that `M.evalFrom start x` is an accept state.
-/
def acceptsFrom (start : σ) : Language α := {x | M.evalFrom start x ∈ M.accept}

theorem mem_acceptsFrom (start : σ) (x : List α) :
    x ∈ M.acceptsFrom start ↔ M.evalFrom start x ∈ M.accept := by rfl

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
def accepts : Language α := M.acceptsFrom M.start
#align DFA.accepts DFA.accepts

theorem mem_accepts (x : List α) : x ∈ M.accepts ↔ M.eval x ∈ M.accept := by rfl

theorem mem_accepts' (x : List α) : x ∈ M.accepts ↔ M.evalFrom M.start x ∈ M.accept := by rfl
#align DFA.mem_accepts DFA.mem_accepts'

theorem evalFrom_split [Fintype σ] {x : List α} {s t : σ} (hlen : Fintype.card σ ≤ x.length)
    (hx : M.evalFrom s x = t) :
    ∃ q a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧
          b ≠ [] ∧ M.evalFrom s a = q ∧ M.evalFrom q b = q ∧ M.evalFrom q c = t := by
  obtain ⟨n, m, hneq, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card σ + 1) => M.evalFrom s (x.take n)) (by norm_num)
  wlog hle : (n : ℕ) ≤ m generalizing n m
  · exact this m n hneq.symm heq.symm (le_of_not_le hle)
  have hm : (m : ℕ) ≤ Fintype.card σ := Fin.is_le m
  refine
    ⟨M.evalFrom s ((x.take m).take n), (x.take m).take n, (x.take m).drop n,
                    x.drop m, ?_, ?_, ?_, by rfl, ?_⟩
  · rw [List.take_append_drop, List.take_append_drop]
  · simp only [List.length_drop, List.length_take]
    rw [min_eq_left (hm.trans hlen), min_eq_left hle, add_tsub_cancel_of_le hle]
    exact hm
  · intro h
    have hlen' := congr_arg List.length h
    simp only [List.length_drop, List.length, List.length_take] at hlen'
    rw [min_eq_left, tsub_eq_zero_iff_le] at hlen'
    · apply hneq
      apply le_antisymm
      assumption'
    exact hm.trans hlen
  have hq : M.evalFrom (M.evalFrom s ((x.take m).take n)) ((x.take m).drop n) =
      M.evalFrom s ((x.take m).take n) := by
    rw [List.take_take, min_eq_left hle, ← evalFrom_of_append, heq, ← min_eq_left hle, ←
      List.take_take, min_eq_left hle, List.take_append_drop]
  use hq
  rwa [← hq, ← evalFrom_of_append, ← evalFrom_of_append, ← List.append_assoc,
    List.take_append_drop, List.take_append_drop]
#align DFA.eval_from_split DFA.evalFrom_split

theorem evalFrom_of_pow {x y : List α} {s : σ} (hx : M.evalFrom s x = s)
    (hy : y ∈ ({x} : Language α)∗) : M.evalFrom s y = s := by
  rw [Language.mem_kstar] at hy
  rcases hy with ⟨S, rfl, hS⟩
  induction' S with a S ih
  · rfl
  · have ha := hS a (List.mem_cons_self _ _)
    rw [Set.mem_singleton_iff] at ha
    rw [List.join, evalFrom_of_append, ha, hx]
    apply ih
    intro z hz
    exact hS z (List.mem_cons_of_mem a hz)
#align DFA.eval_from_of_pow DFA.evalFrom_of_pow

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card σ ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := M.evalFrom_split (s := M.start) hlen rfl
  use a, b, c, hx, hlen, hnil
  intro y hy
  rw [Language.mem_mul] at hy
  rcases hy with ⟨ab, hab, c', hc', rfl⟩
  rw [Language.mem_mul] at hab
  rcases hab with ⟨a', ha', b', hb', rfl⟩
  rw [Set.mem_singleton_iff] at ha' hc'
  substs ha' hc'
  have h := M.evalFrom_of_pow hb hb'
  rwa [mem_accepts', evalFrom_of_append, evalFrom_of_append, h, hc]
#align DFA.pumping_lemma DFA.pumping_lemma

section Maps

universe u' v'
variable {α' : Type u'} {σ' : Type v'} (f : α ≃ α') (g : σ ≃ σ') (s : σ') (a : α') (x : List α')

/-- Transforms the alphabet and states of a DFA. -/
@[simps]
def map (f : α' → α) (g : σ → σ') (h : σ' → σ) : DFA α' σ' where
  step s a := g (M.step (h s) (f a))
  start := g M.start
  accept := g '' M.accept

/-- Lifts equivalences on the alphabet and states to an equivalence on DFAs. -/
def equiv (f : α ≃ α') (g : σ ≃ σ') : DFA α σ ≃ DFA α' σ' where
  toFun M := M.map f.symm g g.symm
  invFun M := M.map f g.symm g
  left_inv M := by simp [map]
  right_inv M := by simp [map]

@[simp]
theorem equiv_step : (equiv f g M).step s a = g (M.step (g.symm s) (f.symm a)) := by simp [equiv]

@[simp] theorem equiv_start : (equiv f g M).start = g M.start := by simp [equiv]

@[simp] theorem equiv_accept : (equiv f g M).accept = g '' M.accept := by simp [equiv]

@[simp]
theorem equiv_evalFrom : (equiv f g M).evalFrom s x = g (M.evalFrom (g.symm s) (x.map f.symm)) := by
  induction x using List.list_reverse_induction with
  | base => simp
  | ind x a ih => simp [ih]

@[simp]
theorem equiv_eval : (equiv f g M).eval x = g (M.eval (x.map f.symm)) := by simp [eval]

@[simp]
theorem equiv_accepts : (equiv f g M).accepts = List.map f '' M.accepts := by
  ext x
  suffices List.map f.symm x ∈ M.accepts ↔ x ∈ List.map f '' M.accepts by simpa [mem_accepts]
  exact Set.mem_image_equiv (f := Equiv.listEquivOfEquiv f) |>.symm

end Maps

end DFA
