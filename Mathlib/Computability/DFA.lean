/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Chris Wong, Rudy Peterson
-/
module

public import Mathlib.Computability.Language
public import Mathlib.Data.Countable.Small
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.NormNum

/-!
# Deterministic Finite Automata

A Deterministic Finite Automaton (DFA) is a state machine which
decides membership in a particular `Language`, by following a path
uniquely determined by an input string.

We define regular languages to be ones for which a DFA exists, other formulations
are later proved equivalent.

Note that this definition allows for automata with infinite states,
a `Fintype` instance must be supplied for true DFAs.

## Main definitions

- `DFA α σ`: automaton over alphabet `α` and set of states `σ`
- `M.accepts`: the language accepted by the DFA `M`
- `Language.IsRegular L`: a predicate stating that `L` is a regular language, i.e. there exists
  a DFA that recognizes the language

## Main theorems

- `DFA.pumping_lemma` : every sufficiently long string accepted by the DFA has a substring that can
  be repeated arbitrarily many times (and have the overall string still be accepted)

## Implementation notes

Currently, there are two disjoint sets of simp lemmas: one for `DFA.eval`, and another for
`DFA.evalFrom`. You can switch from the former to the latter using `simp [eval]`.

## TODO

- Should we unify these simp sets, such that `eval` is rewritten to `evalFrom` automatically?
- Should `mem_accepts` and `mem_acceptsFrom` be marked `@[simp]`?
-/

@[expose] public section

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
theorem evalFrom_cons (s : σ) (a : α) (x : List α) :
    M.evalFrom s (a :: x) = M.evalFrom (M.step s a) x :=
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
  List.foldl_append

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
      (fun n : Fin (Fintype.card σ + 1) => M.evalFrom s (x.take n)) (by simp)
  wlog hle : (n : ℕ) ≤ m generalizing n m
  · exact this m n hneq.symm heq.symm (le_of_not_ge hle)
  refine
    ⟨M.evalFrom s ((x.take m).take n), (x.take m).take n, (x.take m).drop n,
                    x.drop m, ?_, ?_, ?_, by rfl, ?_⟩
  · rw [List.take_append_drop, List.take_append_drop]
  · simp only [List.length_drop, List.length_take]
    omega
  · intro h
    have hlen' := congr_arg List.length h
    simp only [List.length_drop, List.length, List.length_take] at hlen'
    omega
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
  induction S with
  | nil => rfl
  | cons a S ih =>
    have ha := hS a List.mem_cons_self
    rw [Set.mem_singleton_iff] at ha
    rw [List.flatten_cons, evalFrom_of_append, ha, hx]
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
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

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
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

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

section compl

/-- DFAs are closed under complement:
Given a DFA `M`, `Mᶜ` is also a DFA such that `L(Mᶜ) = {x ∣ x ∉ L(M)}`. -/
instance : Compl (DFA α σ) where
  compl M := ⟨M.step, M.start, M.acceptᶜ⟩

theorem compl_def : Mᶜ = ⟨M.step, M.start, M.acceptᶜ⟩ :=
  rfl

@[simp]
theorem acceptsFrom_compl (s : σ) : (Mᶜ).acceptsFrom s = (M.acceptsFrom s)ᶜ :=
  rfl

@[simp]
theorem accepts_compl : (Mᶜ).accepts = (M.accepts)ᶜ :=
  rfl

end compl

section union

variable {σ1 σ2 : Type v}

/-- DFAs are closed under union. -/
@[simps]
def union (M1 : DFA α σ1) (M2 : DFA α σ2) : DFA α (σ1 × σ2) where
  step (s : σ1 × σ2) (a : α) : σ1 × σ2 := (M1.step s.1 a, M2.step s.2 a)
  start := (M1.start, M2.start)
  accept := {s : σ1 × σ2 | s.1 ∈ M1.accept ∨ s.2 ∈ M2.accept}

@[simp]
theorem acceptsFrom_union (M1 : DFA α σ1) (M2 : DFA α σ2) (s1 : σ1) (s2 : σ2) :
    (M1.union M2).acceptsFrom (s1, s2) = M1.acceptsFrom s1 + M2.acceptsFrom s2 := by
  ext x
  simp only [acceptsFrom]
  rw [Language.add_def, Set.mem_union]
  simp_rw [↑Set.mem_setOf]
  induction x generalizing s1 s2 with
  | nil => simp
  | cons a x ih => simp only [evalFrom_cons, union_step, ih]

@[simp]
theorem accepts_union (M1 : DFA α σ1) (M2 : DFA α σ2) :
    (M1.union M2).accepts = M1.accepts + M2.accepts := by
  simp [accepts]

end union

section inter

variable {σ1 σ2 : Type v} (M1 : DFA α σ1) (M2 : DFA α σ2)

/-- DFAs are closed under intersection. -/
@[simps]
def inter : DFA α (σ1 × σ2) where
  step (s : σ1 × σ2) (a : α) : σ1 × σ2 := (M1.step s.1 a, M2.step s.2 a)
  start := (M1.start, M2.start)
  accept := {s : σ1 × σ2 | s.1 ∈ M1.accept ∧ s.2 ∈ M2.accept}

@[simp]
theorem acceptsFrom_inter (s1 : σ1) (s2 : σ2) :
    (M1.inter M2).acceptsFrom (s1, s2) = M1.acceptsFrom s1 ⊓ M2.acceptsFrom s2 := by
  ext x
  simp only [acceptsFrom, Language.mem_inf]
  simp_rw [↑Set.mem_setOf]
  induction x generalizing s1 s2 with
  | nil => simp
  | cons a x ih => simp only [evalFrom_cons, inter_step, ih]

@[simp]
theorem accepts_inter : (M1.inter M2).accepts = M1.accepts ⊓ M2.accepts := by
  simp [accepts]

end inter

end DFA

namespace Language

/-- A regular language is a language that is defined by a DFA with finite states. -/
def IsRegular {T : Type u} (L : Language T) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L

/-- Lifts the state type `σ` inside `Language.IsRegular` to a different universe. -/
private lemma isRegular_iff.helper.{v'} {T : Type u} {L : Language T}
    (hL : ∃ σ : Type v, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L) :
    ∃ σ' : Type v', ∃ _ : Fintype σ', ∃ M : DFA T σ', M.accepts = L :=
  have ⟨σ, _, M, hM⟩ := hL
  have ⟨σ', ⟨f⟩⟩ := Small.equiv_small.{v', v} (α := σ)
  ⟨σ', Fintype.ofEquiv σ f, M.reindex f, hM ▸ DFA.accepts_reindex M f⟩

/--
A language is regular if and only if it is defined by a DFA with finite states.

This is more general than using the definition of `Language.IsRegular` directly, as the state type
`σ` is universe-polymorphic.
-/
theorem isRegular_iff {T : Type u} {L : Language T} :
    L.IsRegular ↔ ∃ σ : Type v, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L :=
  ⟨Language.isRegular_iff.helper, Language.isRegular_iff.helper⟩

protected theorem IsRegular.compl {T : Type u} {L : Language T} (h : L.IsRegular) : Lᶜ.IsRegular :=
  have ⟨σ, _, M, hM⟩ := h
  ⟨σ, inferInstance, Mᶜ, by simp [hM]⟩

protected theorem IsRegular.of_compl {T : Type u} {L : Language T} (h : Lᶜ.IsRegular) :
  L.IsRegular :=
  L.compl_compl ▸ h.compl

/-- Regular languages are closed under complement. -/
@[simp]
theorem IsRegular_compl {T : Type u} {L : Language T} : Lᶜ.IsRegular ↔ L.IsRegular :=
  ⟨.of_compl, .compl⟩

/-- Regular languages are closed under union. -/
theorem IsRegular.add {T : Type u} {L1 L2 : Language T} (h1 : L1.IsRegular) (h2 : L2.IsRegular) :
    (L1 + L2).IsRegular :=
  have ⟨σ1, _, M1, hM1⟩ := h1
  have ⟨σ2, _, M2, hM2⟩ := h2
  ⟨σ1 × σ2, inferInstance, M1.union M2, by simp [hM1, hM2]⟩

/-- Regular languages are closed under intersection. -/
theorem IsRegular.inf {T : Type u} {L1 L2 : Language T} (h1 : L1.IsRegular) (h2 : L2.IsRegular) :
    (L1 ⊓ L2).IsRegular :=
  have ⟨σ1, _, M1, hM1⟩ := h1
  have ⟨σ2, _, M2, hM2⟩ := h2
  ⟨σ1 × σ2, inferInstance, M1.inter M2, by simp [hM1, hM2]⟩

end Language
