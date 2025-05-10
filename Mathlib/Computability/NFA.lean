/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Maja Kądziołka
-/
import Mathlib.Computability.DFA

/-!
# Nondeterministic Finite Automata

A Nondeterministic Finite Automaton (NFA) is a state machine which
decides membership in a particular `Language`, by following every
possible path that describes an input string.

We show that DFAs and NFAs can decide the same languages, by constructing
an equivalent DFA for every NFA, and vice versa.

As constructing a DFA from an NFA uses an exponential number of states,
we re-prove the pumping lemma instead of lifting `DFA.pumping_lemma`,
in order to obtain the optimal bound on the minimal length of the string.

Like `DFA`, this definition allows for automata with infinite states;
a `Fintype` instance must be supplied for true NFAs.

## Main definitions

* `NFA α σ`: automaton over alphabet `α` and set of states `σ`
* `M.evalFrom S x`: set of possible ending states for an input word `x`
  and set of initial states `S`
* `M.accepts`: the language accepted by the NFA `M`
* `M.Path s t x`: a specific path from `s` to `t` for an input word `x`
* `p.supp`: set of states visited by the path `p`

## Main theorems

* `NFA.pumping_lemma`: every sufficiently long string accepted by the NFA has a substring that can
  be repeated arbitrarily many times
-/

open Set

open Computability

universe u v


/-- An NFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a set of starting states (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `Set` of states. These are the states that it
  may be sent to. -/
structure NFA (α : Type u) (σ : Type v) where
  /-- The NFA's transition function -/
  step : σ → α → Set σ
  /-- Set of starting states -/
  start : Set σ
  /-- Set of accepting states -/
  accept : Set σ

variable {α : Type u} {σ σ' : Type v} (M : NFA α σ)

namespace NFA

instance : Inhabited (NFA α σ) :=
  ⟨NFA.mk (fun _ _ => ∅) ∅ ∅⟩

/-- `M.stepSet S a` is the union of `M.step s a` for all `s ∈ S`. -/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.step s a

theorem mem_stepSet (s : σ) (S : Set σ) (a : α) : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.step t a := by
  simp [stepSet]

@[simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by simp [stepSet]

@[simp]
theorem stepSet_singleton (s : σ) (a : α) : M.stepSet {s} a = M.step s a := by
  simp [stepSet]

/-- `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element
  of `S`. -/
def evalFrom (start : Set σ) : List α → Set σ :=
  List.foldl M.stepSet start

@[simp]
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = S :=
  rfl

@[simp]
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet S a :=
  rfl

@[simp]
theorem evalFrom_cons (S : Set σ) (a : α) (x : List α) :
    M.evalFrom S (a :: x) = M.evalFrom (M.stepSet S a) x :=
  rfl

@[simp]
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem evalFrom_biUnion {ι : Type*} (t : Set ι) (f : ι → Set σ) (x : List α) :
    M.evalFrom (⋃ i ∈ t, f i) x = ⋃ i ∈ t, M.evalFrom (f i) x := by
  induction x generalizing ι with
  | nil => simp
  | cons a x ih => simp [stepSet, ih]

theorem evalFrom_eq_biUnion (S : Set σ) (x : List α) :
    M.evalFrom S x = ⋃ s ∈ S, M.evalFrom {s} x := by
  simp [← evalFrom_biUnion]

theorem mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} :
    s ∈ M.evalFrom S x ↔ ∃ t ∈ S, s ∈ M.evalFrom {t} x := by
  rw [evalFrom_eq_biUnion]
  simp

/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start`. -/
def eval : List α → Set σ :=
  M.evalFrom M.start

@[simp]
theorem eval_nil : M.eval [] = M.start :=
  rfl

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet M.start a :=
  rfl

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α := {x | ∃ S ∈ M.accept, S ∈ M.eval x}

theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ ∃ S ∈ M.accept, S ∈ M.evalFrom M.start x := by
  rfl

/-- `M.Path` represents a concrete path through the NFA from a start state to an end state
for a particular word. -/
inductive Path : σ → σ → List α → Type (max u v)
  | nil (s : σ) : Path s s []
  | cons (t s u : σ) (a : α) (x : List α) :
      t ∈ M.step s a → Path t u x → Path s u (a :: x)

/-- Knowing that a path must exist, construct one particular example. -/
noncomputable def path_of_evalFrom {s t : σ} {x : List α} (h : t ∈ M.evalFrom {s} x) :
    M.Path s t x :=
  match x with
  | [] =>
    have h : s = t := by simp at h; tauto
    h ▸ Path.nil s
  | a :: x =>
    have h : ∃ s' ∈ M.step s a, t ∈ M.evalFrom {s'} x :=
      by rw [evalFrom_cons, mem_evalFrom_iff_exists, stepSet_singleton] at h; exact h
    have ⟨s', h₁, h₂⟩ := Classical.indefiniteDescription _ h
    Path.cons s' _ _ _ _ h₁ (path_of_evalFrom h₂)

theorem evalFrom_of_path {s t : σ} {x : List α} (h : M.Path s t x) : t ∈ M.evalFrom {s} x := by
  induction h with
  | nil => simp
  | cons s' s t a x h₁ h₂ ih =>
    simp [M.mem_evalFrom_iff_exists (S := M.step _ _)]
    tauto

/-- Knowing that the NFA accepts a word, choose a concrete start state, path, and accept state. -/
noncomputable def path_of_accepts {x : List α} (h : x ∈ M.accepts) :
    (s t : σ) × M.Path s t x ×' s ∈ M.start ∧ t ∈ M.accept :=
  have ⟨t, ht, h⟩ := Classical.indefiniteDescription _ (M.mem_accepts.1 h)
  have ⟨s, hs, h⟩ := Classical.indefiniteDescription _ (M.mem_evalFrom_iff_exists.1 h)
  ⟨s, t, M.path_of_evalFrom h, hs, ht⟩

theorem accepts_of_path {s t : σ} {x : List α} (p : M.Path s t x)
    (hs : s ∈ M.start) (ht : t ∈ M.accept) : x ∈ M.accepts := by
  apply M.evalFrom_of_path at p
  simp [mem_accepts, M.mem_evalFrom_iff_exists (S := M.start)]
  tauto

section
variable {M}

/-- Append two paths. -/
def Path.append {s t u : σ} {x y : List α} (p : M.Path s t x) (q : M.Path t u y) :
    M.Path s u (x ++ y) :=
  match p with
  | nil _ => q
  | cons s' _ _ _ _ h p' =>
    cons s' _ _ _ _ h (p'.append q)

/-- Split `p` at the point just after it has matched `x`. -/
def Path.splitAfter {s u : σ} {y : List α} (x : List α) (p : M.Path s u (x ++ y)) :
    (t : σ) × M.Path s t x × M.Path t u y :=
  match x, p with
  | [], p => ⟨s, nil s, p⟩
  | _ :: x, cons s' _ _ _ _ h p =>
    let ⟨t, p', q⟩ := p.splitAfter x
    ⟨t, cons s' _ _ _ _ h p', q⟩

/-- Set of states visited by a path. -/
@[simp]
def Path.supp [DecidableEq σ] {s t : σ} {x : List α} (p : M.Path s t x) : Finset σ :=
  match p with
  | nil s => {s}
  | cons _ _ _ _ _ _ p => {s} ∪ p.supp

/-- Split `p` at the point where `t` occurs in `p.supp`. -/
def Path.split_of_mem_supp [DecidableEq σ] {x : List α} {s t u : σ}
    (p : M.Path s u x) (h : t ∈ p.supp) :
    (x₁ x₂ : List α) × M.Path s t x₁ × M.Path t u x₂ ×' x₁ ++ x₂ = x :=
  if e : s = t then
    ⟨[], x, e ▸ nil s, e ▸ p, rfl⟩
  else
    match p with
    | nil _ => by simp at h; tauto
    | cons s' _ _ a x h' p =>
      have : t ∈ p.supp := by simp at h; tauto
      have ⟨x₁, x₂, p', q, e'⟩ := p.split_of_mem_supp this
      ⟨a :: x₁, x₂, cons s' _ _ _ _ h' p', q, e' ▸ rfl⟩

/-- Knowing that the length of the word guarantees that a state will repeat
somewhere along the path, find one such state and split the path around it. -/
def Path.split_of_supp_le_length [DecidableEq σ] {x : List α} {s u : σ}
    (p : M.Path s u x) (h : p.supp.card ≤ x.length) :
    (t : σ) × (x₁ x₂ x₃ : List α) × M.Path s t x₁ × M.Path t t x₂ × M.Path t u x₃ ×'
    x = x₁ ++ x₂ ++ x₃ ∧ x₂ ≠ [] :=
  match p with
  | nil _ => by simp at h
  | cons s₁ _ _ a x h₁ p =>
    if h' : s ∈ p.supp then
      have ⟨x₂, x₃, p₂, p₃, e⟩ := p.split_of_mem_supp h'
      have p₂ : M.Path s s (a :: x₂) := cons s₁ _ _ _ _ h₁ p₂
      ⟨s, [], a :: x₂, x₃, nil s, p₂, p₃, e ▸ rfl, by simp⟩
    else
      have hle : p.supp.card ≤ x.length := by simpa [h', add_comm 1] using h
      have ⟨t, x₁, x₂, x₃, p₁, p₂, p₃, e, hne⟩ := p.split_of_supp_le_length hle
      ⟨t, a :: x₁, x₂, x₃, cons s₁ _ _ _ _ h₁ p₁, p₂, p₃, e ▸ rfl, hne⟩

/-- Repeat a looping path to construct a path for `x∗`. -/
noncomputable def Path.of_mem_kstar {x x' : List α} {s : σ} (p : M.Path s s x)
    (h : x' ∈ ({x}∗ : Language α)) : M.Path s s x' := by
  rw [Language.mem_kstar] at h
  apply Classical.indefiniteDescription at h
  rcases h with ⟨xs, rfl, hxs⟩
  induction xs with
  | nil => exact nil s
  | cons a xs ih =>
    have := hxs a List.mem_cons_self |> Set.mem_singleton_iff.1
    subst a
    rw [List.flatten_cons]
    apply p.append
    apply ih
    tauto

end

theorem pumping_lemma [Fintype σ] [DecidableEq σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card σ ≤ x.length) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by
  have ⟨s, u, p, hs, hu⟩ := M.path_of_accepts hx
  let k := Fintype.card σ
  have e₁ : x.take k ++ x.drop k = x := x.take_append_drop k
  have ⟨u', p, p₄⟩ := (e₁ ▸ p).splitAfter (x.take k)
  have hle : p.supp.card ≤ (x.take k).length := calc
    p.supp.card ≤ Fintype.card σ := p.supp.card_le_univ
    _           = (x.take k).length := by simp [hlen, k]
  have ⟨t, a, b, c, p₁, p₂, p₃, e₂, hne⟩ := p.split_of_supp_le_length hle
  refine ⟨a, b, c ++ x.drop k, ?eq, ?le, hne, ?mem⟩
  · nth_rw 1 [← e₁, e₂]
    simp
  · calc
      a.length + b.length ≤ (a ++ b ++ c).length := by simp
      _                   = (x.take k).length := by rw [e₂]
      _                   = Fintype.card σ := by simp [hlen, k]
  · intro y hy
    rcases Language.mem_mul.1 hy with ⟨ab, hab, c', hc', rfl⟩
    rcases Language.mem_mul.1 hab with ⟨a', ha', b', hb', rfl⟩
    rw [Set.mem_singleton_iff] at ha' hc'
    substs a' c'
    have p₂' := p₂.of_mem_kstar hb'
    have p' := p₁.append p₂' |>.append p₃ |>.append p₄
    have := M.accepts_of_path p' hs hu
    simp at this ⊢; exact this

/-- `M.toDFA` is a `DFA` constructed from an `NFA` `M` using the subset construction. The
  states is the type of `Set`s of `M.state` and the step function is `M.stepSet`. -/
def toDFA : DFA α (Set σ) where
  step := M.stepSet
  start := M.start
  accept := { S | ∃ s ∈ S, s ∈ M.accept }

@[simp]
theorem toDFA_correct : M.toDFA.accepts = M.accepts := by
  ext x
  rw [mem_accepts, DFA.mem_accepts]
  constructor <;> · exact fun ⟨w, h2, h3⟩ => ⟨w, h3, h2⟩

end NFA

namespace DFA

/-- `M.toNFA` is an `NFA` constructed from a `DFA` `M` by using the same start and accept
  states and a transition function which sends `s` with input `a` to the singleton `M.step s a`. -/
@[simps] def toNFA (M : DFA α σ') : NFA α σ' where
  step s a := {M.step s a}
  start := {M.start}
  accept := M.accept

@[simp]
theorem toNFA_evalFrom_match (M : DFA α σ) (start : σ) (s : List α) :
    M.toNFA.evalFrom {start} s = {M.evalFrom start s} := by
  change List.foldl M.toNFA.stepSet {start} s = {List.foldl M.step start s}
  induction' s with a s ih generalizing start
  · tauto
  · rw [List.foldl, List.foldl,
      show M.toNFA.stepSet {start} a = {M.step start a} by simp [NFA.stepSet] ]
    tauto

@[simp]
theorem toNFA_correct (M : DFA α σ) : M.toNFA.accepts = M.accepts := by
  ext x
  rw [NFA.mem_accepts, toNFA_start, toNFA_evalFrom_match]
  constructor
  · rintro ⟨S, hS₁, hS₂⟩
    rwa [Set.mem_singleton_iff.mp hS₂] at hS₁
  · exact fun h => ⟨M.eval x, h, rfl⟩

end DFA
