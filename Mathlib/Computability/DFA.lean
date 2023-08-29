/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Computability.Language
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

-- Porting note: Required as `DFA` is used in mathlib3
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
  -- 🎉 no goals
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

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
def accepts : Language α := {x | M.eval x ∈ M.accept}
#align DFA.accepts DFA.accepts

theorem mem_accepts (x : List α) : x ∈ M.accepts ↔ M.evalFrom M.start x ∈ M.accept := by rfl
                                                                                         -- 🎉 no goals
#align DFA.mem_accepts DFA.mem_accepts

theorem evalFrom_split [Fintype σ] {x : List α} {s t : σ} (hlen : Fintype.card σ ≤ x.length)
    (hx : M.evalFrom s x = t) :
    ∃ q a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧
          b ≠ [] ∧ M.evalFrom s a = q ∧ M.evalFrom q b = q ∧ M.evalFrom q c = t := by
  obtain ⟨n, m, hneq, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card σ + 1) => M.evalFrom s (x.take n)) (by norm_num)
  wlog hle : (n : ℕ) ≤ m
  -- ⊢ ∃ q a b c, x = a ++ b ++ c ∧ List.length a + List.length b ≤ Fintype.card σ  …
  · exact this _ hlen hx _ _ hneq.symm heq.symm (le_of_not_le hle)
    -- 🎉 no goals
  have hm : (m : ℕ) ≤ Fintype.card σ := Fin.is_le m
  -- ⊢ ∃ q a b c, x = a ++ b ++ c ∧ List.length a + List.length b ≤ Fintype.card σ  …
  refine'
    ⟨M.evalFrom s ((x.take m).take n), (x.take m).take n, (x.take m).drop n, x.drop m, _, _, _, by
      rfl, _⟩
  · rw [List.take_append_drop, List.take_append_drop]
    -- 🎉 no goals
  · simp only [List.length_drop, List.length_take]
    -- ⊢ min (↑n) (min (↑m) (List.length x)) + (min (↑m) (List.length x) - ↑n) ≤ Fint …
    rw [min_eq_left (hm.trans hlen), min_eq_left hle, add_tsub_cancel_of_le hle]
    -- ⊢ ↑m ≤ Fintype.card σ
    exact hm
    -- 🎉 no goals
  · intro h
    -- ⊢ False
    have hlen' := congr_arg List.length h
    -- ⊢ False
    simp only [List.length_drop, List.length, List.length_take] at hlen'
    -- ⊢ False
    rw [min_eq_left, tsub_eq_zero_iff_le] at hlen'
    -- ⊢ False
    · apply hneq
      -- ⊢ n = m
      apply le_antisymm
      -- ⊢ n ≤ m
      assumption'
      -- 🎉 no goals
    exact hm.trans hlen
    -- 🎉 no goals
  have hq : M.evalFrom (M.evalFrom s ((x.take m).take n)) ((x.take m).drop n) =
      M.evalFrom s ((x.take m).take n) := by
    rw [List.take_take, min_eq_left hle, ← evalFrom_of_append, heq, ← min_eq_left hle, ←
      List.take_take, min_eq_left hle, List.take_append_drop]
  use hq
  -- ⊢ evalFrom M (evalFrom M s (List.take (↑n) (List.take (↑m) x))) (List.drop (↑m …
  rwa [← hq, ← evalFrom_of_append, ← evalFrom_of_append, ← List.append_assoc,
    List.take_append_drop, List.take_append_drop]
#align DFA.eval_from_split DFA.evalFrom_split

theorem evalFrom_of_pow {x y : List α} {s : σ} (hx : M.evalFrom s x = s)
    (hy : y ∈ ({x} : Language α)∗) : M.evalFrom s y = s := by
  rw [Language.mem_kstar] at hy
  -- ⊢ evalFrom M s y = s
  rcases hy with ⟨S, rfl, hS⟩
  -- ⊢ evalFrom M s (List.join S) = s
  induction' S with a S ih
  -- ⊢ evalFrom M s (List.join []) = s
  · rfl
    -- 🎉 no goals
  · have ha := hS a (List.mem_cons_self _ _)
    -- ⊢ evalFrom M s (List.join (a :: S)) = s
    rw [Set.mem_singleton_iff] at ha
    -- ⊢ evalFrom M s (List.join (a :: S)) = s
    rw [List.join, evalFrom_of_append, ha, hx]
    -- ⊢ evalFrom M s (List.join S) = s
    apply ih
    -- ⊢ ∀ (y : List α), y ∈ S → y ∈ {x}
    intro z hz
    -- ⊢ z ∈ {x}
    exact hS z (List.mem_cons_of_mem a hz)
    -- 🎉 no goals
#align DFA.eval_from_of_pow DFA.evalFrom_of_pow

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card σ ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := M.evalFrom_split hlen rfl
  -- ⊢ ∃ a b c, x = a ++ b ++ c ∧ List.length a + List.length b ≤ Fintype.card σ ∧  …
  use a, b, c, hx, hlen, hnil
  -- ⊢ {a} * {b}∗ * {c} ≤ accepts M
  intro y hy
  -- ⊢ y ∈ accepts M
  rw [Language.mem_mul] at hy
  -- ⊢ y ∈ accepts M
  rcases hy with ⟨ab, c', hab, hc', rfl⟩
  -- ⊢ ab ++ c' ∈ accepts M
  rw [Language.mem_mul] at hab
  -- ⊢ ab ++ c' ∈ accepts M
  rcases hab with ⟨a', b', ha', hb', rfl⟩
  -- ⊢ a' ++ b' ++ c' ∈ accepts M
  rw [Set.mem_singleton_iff] at ha' hc'
  -- ⊢ a' ++ b' ++ c' ∈ accepts M
  substs ha' hc'
  -- ⊢ a' ++ b' ++ c' ∈ accepts M
  have h := M.evalFrom_of_pow hb hb'
  -- ⊢ a' ++ b' ++ c' ∈ accepts M
  rwa [mem_accepts, evalFrom_of_append, evalFrom_of_append, h, hc]
  -- 🎉 no goals
#align DFA.pumping_lemma DFA.pumping_lemma

end DFA
