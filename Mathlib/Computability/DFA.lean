/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Chris Wong
-/
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.NormNum

/-!
# Deterministic Finite Automata

This file contains the definition of a Deterministic Finite Automaton (DFA), a state machine which
determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular set
in linear time.
Note that this definition allows for Automaton with infinite states, a `Fintype` instance must be
supplied for true DFA's.

## Implementation notes

Currently, there are two disjoint sets of simp lemmas: one for `DFA.eval`, and another for
`DFA.evalFrom`. You can switch from the former to the latter using `simp [eval]`.

## TODO

- Should we unify these simp sets, such that `eval` is rewritten to `evalFrom` automatically?
- Should `mem_accepts` and `mem_acceptsFrom` be marked `@[simp]`?
-/

universe u v

open Computability

/-- A DFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`). -/
structure DFA (α : Type u) (σ : Type v) where
  /-- A transition function from state to state labelled by the alphabet. -/
  step : σ → α → σ
  /-- Starting state. -/
  start : σ
  /-- Set of acceptance states. -/
  accept : Set σ

namespace DFA

variable {α : Type u} {σ : Type v} (M : DFA α σ)

instance [Inhabited σ] : Inhabited (DFA α σ) :=
  ⟨DFA.mk (fun _ _ => default) default ∅⟩

/-- `M.evalFrom s x` evaluates `M` with input `x` starting from the state `s`. -/
def evalFrom (s : σ) : List α → σ :=
  List.foldl M.step s

@[simp]
theorem evalFrom_nil (s : σ) : M.evalFrom s [] = s :=
  rfl

@[simp]
theorem evalFrom_singleton (s : σ) (a : α) : M.evalFrom s [a] = M.step s a :=
  rfl

@[simp]
theorem evalFrom_append_singleton (s : σ) (x : List α) (a : α) :
    M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval : List α → σ :=
  M.evalFrom M.start

@[simp]
theorem eval_nil : M.eval [] = M.start :=
  rfl

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.step M.start a :=
  rfl

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.step (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _

theorem evalFrom_of_append (start : σ) (x y : List α) :
    M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y :=
  x.foldl_append _ _ y

/--
`M.acceptsFrom s` is the language of `x` such that `M.evalFrom s x` is an accept state.
-/
def acceptsFrom (s : σ) : Language α := {x | M.evalFrom s x ∈ M.accept}

theorem mem_acceptsFrom {s : σ} {x : List α} :
    x ∈ M.acceptsFrom s ↔ M.evalFrom s x ∈ M.accept := by rfl

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
def accepts : Language α := M.acceptsFrom M.start

theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ M.eval x ∈ M.accept := by rfl

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
  rwa [mem_accepts, eval, evalFrom_of_append, evalFrom_of_append, h, hc]

section Maps

variable {α' σ' : Type*}

/--
`M.comap f` pulls back the alphabet of `M` along `f`. In other words, it applies `f` to the input
before passing it to `M`.
-/
@[simps]
def comap (f : α' → α) (M : DFA α σ) : DFA α' σ where
  step s a := M.step s (f a)
  start := M.start
  accept := M.accept

@[simp]
theorem comap_id : M.comap id = M := rfl

@[simp]
theorem evalFrom_comap (f : α' → α) (s : σ) (x : List α') :
    (M.comap f).evalFrom s x = M.evalFrom s (x.map f) := by
  induction x using List.list_reverse_induction with
  | base => simp
  | ind x a ih => simp [ih]

@[simp]
theorem eval_comap (f : α' → α) (x : List α') : (M.comap f).eval x = M.eval (x.map f) := by
  simp [eval]

@[simp]
theorem accepts_comap (f : α' → α) : (M.comap f).accepts = List.map f ⁻¹' M.accepts := by
  ext x
  conv =>
    rhs
    rw [Set.mem_preimage, mem_accepts]
  simp [mem_accepts]

/-- Lifts an equivalence on states to an equivalence on DFAs. -/
@[simps apply_step apply_start apply_accept]
def reindex (g : σ ≃ σ') : DFA α σ ≃ DFA α σ' where
  toFun M := {
    step := fun s a => g (M.step (g.symm s) a)
    start := g M.start
    accept := g.symm ⁻¹' M.accept
  }
  invFun M := {
    step := fun s a => g.symm (M.step (g s) a)
    start := g.symm M.start
    accept := g ⁻¹' M.accept
  }
  left_inv M := by simp
  right_inv M := by simp

@[simp]
theorem reindex_refl : reindex (Equiv.refl σ) M = M := rfl

@[simp]
theorem symm_reindex (g : σ ≃ σ') : (reindex (α := α) g).symm = reindex g.symm := rfl

@[simp]
theorem evalFrom_reindex (g : σ ≃ σ') (s : σ') (x : List α) :
    (reindex g M).evalFrom s x = g (M.evalFrom (g.symm s) x) := by
  induction x using List.list_reverse_induction with
  | base => simp
  | ind x a ih => simp [ih]

@[simp]
theorem eval_reindex (g : σ ≃ σ') (x : List α) : (reindex g M).eval x = g (M.eval x) := by
  simp [eval]

@[simp]
theorem accepts_reindex (g : σ ≃ σ') : (reindex g M).accepts = M.accepts := by
  ext x
  simp [mem_accepts]

theorem comap_reindex (f : α' → α) (g : σ ≃ σ') :
    (reindex g M).comap f = reindex g (M.comap f) := by
  simp [comap, reindex]

end Maps

end DFA

/-- A regular language is a language that is defined by a DFA with finite states. -/
def Language.IsRegular {T : Type u} (L : Language T) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L

proof_wanted Language.isRegular_iff {T : Type u} {L : Language T} :
    L.IsRegular ↔ ∃ σ : Type v, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L
-- probably needs `import Mathlib.Data.Countable.Small`
