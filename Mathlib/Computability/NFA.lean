/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Maja Kądziołka
-/
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Powerset

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
* `NFA.evalFrom M S x`: set of possible ending states for an input word `x`
  and set of initial states `S`
* `NFA.accepts M`: the language accepted by the NFA `M`
* `NFA.Path M s t x`: a specific path from `s` to `t` for an input word `x`
* `NFA.Path.supp p`: set of states visited by the path `p`

## Main theorems

* `NFA.pumping_lemma`: every sufficiently long string accepted by the NFA has a substring that can
  be repeated arbitrarily many times (and have the overall string still be accepted)
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

variable {α : Type u} {σ : Type v} {M : NFA α σ}

namespace NFA

instance : Inhabited (NFA α σ) :=
  ⟨NFA.mk (fun _ _ => ∅) ∅ ∅⟩

variable (M) in
/-- `M.stepSet S a` is the union of `M.step s a` for all `s ∈ S`. -/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.step s a

theorem mem_stepSet {s : σ} {S : Set σ} {a : α} : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.step t a := by
  simp [stepSet]

variable (M) in
@[simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by simp [stepSet]

variable (M) in
@[simp]
theorem stepSet_singleton (s : σ) (a : α) : M.stepSet {s} a = M.step s a := by
  simp [stepSet]

variable (M) in
/-- `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element
  of `S`. -/
def evalFrom (S : Set σ) : List α → Set σ :=
  List.foldl M.stepSet S

variable (M) in
@[simp]
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = S :=
  rfl

variable (M) in
@[simp]
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet S a :=
  rfl

variable (M) in
@[simp]
theorem evalFrom_cons (S : Set σ) (a : α) (x : List α) :
    M.evalFrom S (a :: x) = M.evalFrom (M.stepSet S a) x :=
  rfl

@[simp]
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

variable (M) in
@[simp]
theorem evalFrom_biUnion {ι : Type*} (t : Set ι) (f : ι → Set σ) :
    ∀ (x : List α), M.evalFrom (⋃ i ∈ t, f i) x = ⋃ i ∈ t, M.evalFrom (f i) x
  | [] => by simp
  | a :: x => by simp [stepSet, evalFrom_biUnion _ _ x]

variable (M) in
theorem evalFrom_eq_biUnion_singleton (S : Set σ) (x : List α) :
    M.evalFrom S x = ⋃ s ∈ S, M.evalFrom {s} x := by
  simp [← evalFrom_biUnion]

theorem mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} :
    s ∈ M.evalFrom S x ↔ ∃ t ∈ S, s ∈ M.evalFrom {t} x := by
  rw [evalFrom_eq_biUnion_singleton]
  simp

variable (M) in
/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start`. -/
def eval : List α → Set σ :=
  M.evalFrom M.start

variable (M) in
@[simp]
theorem eval_nil : M.eval [] = M.start :=
  rfl

variable (M) in
@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet M.start a :=
  rfl

variable (M) in
@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton ..

variable (M) in
/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α := {x | ∃ S ∈ M.accept, S ∈ M.eval x}

theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ ∃ S ∈ M.accept, S ∈ M.evalFrom M.start x := by
  rfl

variable (M) in
/-- `M.Path` represents a concrete path through the NFA from a start state to an end state
for a particular word.

Note that due to the non-deterministic nature of the automata, there can be more than one `Path`
for a given word.

Also note that this is `Type` and not a `Prop`, so that we can speak about the properties
of a particular `Path`, such as the set of states visited along the way (defined as `Path.supp`). -/
inductive Path : σ → σ → List α → Type (max u v)
  | nil (s : σ) : Path s s []
  | cons (t s u : σ) (a : α) (x : List α) :
      t ∈ M.step s a → Path t u x → Path s u (a :: x)

/-- Set of states visited by a path. -/
@[simp]
def Path.supp [DecidableEq σ] {s t : σ} {x : List α} : M.Path s t x → Finset σ
  | nil s => {s}
  | cons _ _ _ _ _ _ p => {s} ∪ p.supp

theorem mem_evalFrom_iff_nonempty_path {s t : σ} {x : List α} :
    t ∈ M.evalFrom {s} x ↔ Nonempty (M.Path s t x) where
  mp h := match x with
    | [] =>
      have h : s = t := by simp at h; tauto
      ⟨h ▸ Path.nil s⟩
    | a :: x =>
      have h : ∃ s' ∈ M.step s a, t ∈ M.evalFrom {s'} x :=
        by rw [evalFrom_cons, mem_evalFrom_iff_exists, stepSet_singleton] at h; exact h
      let ⟨s', h₁, h₂⟩ := h
      let ⟨p'⟩ := mem_evalFrom_iff_nonempty_path.1 h₂
      ⟨Path.cons s' _ _ _ _ h₁ p'⟩
  mpr p := match p with
    | ⟨Path.nil s⟩ => by simp
    | ⟨Path.cons s' s t a x h₁ h₂⟩ => by
      rw [evalFrom_cons, stepSet_singleton, mem_evalFrom_iff_exists]
      exact ⟨s', h₁, mem_evalFrom_iff_nonempty_path.2 ⟨h₂⟩⟩

theorem accepts_iff_exists_path {x : List α} :
    x ∈ M.accepts ↔ ∃ s ∈ M.start, ∃ t ∈ M.accept, Nonempty (M.Path s t x) := by
  simp only [← mem_evalFrom_iff_nonempty_path, mem_accepts, mem_evalFrom_iff_exists (S := M.start)]
  tauto

/-- Append two paths. -/
def Path.append {s t u : σ} {x y : List α} (p : M.Path s t x) (q : M.Path t u y) :
    M.Path s u (x ++ y) :=
  match p with
  | nil _ => q
  | cons s' _ _ _ _ h p' => cons s' _ _ _ _ h (p'.append q)

/-- Split `p` at the point just after it has matched `x`. -/
def Path.splitAfter {s u : σ} {y : List α} (x : List α) (p : M.Path s u (x ++ y)) :
    (t : σ) × M.Path s t x × M.Path t u y :=
  match x, p with
  | [], p => ⟨s, nil s, p⟩
  | _ :: x, cons s' _ _ _ _ h p =>
    let ⟨t, p', q⟩ := p.splitAfter x
    ⟨t, cons s' _ _ _ _ h p', q⟩

/-- Split `p` at the intermediate state `t`. -/
def Path.splitAt [DecidableEq σ] {x : List α} {s u : σ}
    (p : M.Path s u x) (t : σ) (h : t ∈ p.supp) :
    (x₁ x₂ : List α) × M.Path s t x₁ × M.Path t u x₂ ×' x₁ ++ x₂ = x :=
  if e : s = t then
    ⟨[], x, e ▸ nil s, e ▸ p, rfl⟩
  else
    match p with
    | nil _ => by simp at h; tauto
    | cons s' _ _ a x h' p =>
      have ⟨x₁, x₂, p', q, e'⟩ := p.splitAt t (by simp at h; tauto)
      ⟨a :: x₁, x₂, cons s' _ _ _ _ h' p', q, e' ▸ rfl⟩

/-- Knowing that the length of the word guarantees that a state will repeat
somewhere along the path, find one such state and split the path around it. -/
def Path.splitAtRepeatingState [DecidableEq σ] {x : List α} {s u : σ}
    (p : M.Path s u x) (h : p.supp.card ≤ x.length) :
    (t : σ) × (x₁ x₂ x₃ : List α) × M.Path s t x₁ × M.Path t t x₂ × M.Path t u x₃ ×'
    x = x₁ ++ x₂ ++ x₃ ∧ x₂ ≠ [] :=
  match p with
  | nil _ => by simp at h
  | cons s₁ _ _ a x h₁ p =>
    if h' : s ∈ p.supp then
      have ⟨x₂, x₃, p₂, p₃, e⟩ := p.splitAt s h'
      have p₂ : M.Path s s (a :: x₂) := cons s₁ _ _ _ _ h₁ p₂
      ⟨s, [], a :: x₂, x₃, nil s, p₂, p₃, e ▸ rfl, by simp⟩
    else
      have hle : p.supp.card ≤ x.length := by simpa [h', add_comm 1] using h
      have ⟨t, x₁, x₂, x₃, p₁, p₂, p₃, e, hne⟩ := p.splitAtRepeatingState hle
      ⟨t, a :: x₁, x₂, x₃, cons s₁ _ _ _ _ h₁ p₁, p₂, p₃, e ▸ rfl, hne⟩

/-- Repeat a looping path to construct a path for `x∗`. -/
noncomputable def Path.ofMemKStar {x : List α} {s : σ} (p : M.Path s s x) (x' : List α)
    (h : x' ∈ ({x}∗ : Language α)) : M.Path s s x' := by
  rw [Language.mem_kstar] at h
  -- NOTE: This could be made computable with some effort, there's no fundamental reason
  -- to invoke choice here.
  obtain ⟨xs, rfl, hxs⟩ := Classical.indefiniteDescription _ h; clear h
  induction xs with
  | nil => exact nil s
  | cons a xs ih =>
    obtain rfl := hxs a List.mem_cons_self |> Set.mem_singleton_iff.1
    rw [List.flatten_cons]
    apply p.append
    apply ih
    tauto

variable (M) in
theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card σ ≤ x.length) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by
  classical -- Discharge the DecidableEq assumptions
  have ⟨s, hs, u, hu, ⟨p⟩⟩ := accepts_iff_exists_path.1 hx
  let k := Fintype.card σ
  -- To make sure that the repeated state occurs within the first `k` steps, split
  -- the path and carry out the rest of the argument on the first `k` characters of the word.
  have e₁ : x.take k ++ x.drop k = x := x.take_append_drop k
  have ⟨u', p, p₄⟩ := (e₁ ▸ p).splitAfter (x.take k)
  have hle : p.supp.card ≤ (x.take k).length := calc
    p.supp.card ≤ Fintype.card σ := p.supp.card_le_univ
    _           = (x.take k).length := by simp [hlen, k]
  -- Find the repeating state `t`.
  have ⟨t, a, b, c, p₁, p₂, p₃, e₂, hne⟩ := p.splitAtRepeatingState hle
  refine ⟨a, b, c ++ x.drop k, ?eq, ?le, hne, ?mem⟩
  case eq =>
    nth_rw 1 [← e₁, e₂]
    simp
  case le => calc
    a.length + b.length ≤ (a ++ b ++ c).length := by simp
    _                   = (x.take k).length := by rw [e₂]
    _                   = Fintype.card σ := by simp [hlen, k]
  case mem =>
    intro y hy
    obtain ⟨ab, hab, c', hc', rfl⟩ := Language.mem_mul.1 hy; clear hy
    obtain ⟨a', ha', b', hb', rfl⟩ := Language.mem_mul.1 hab; clear hab
    rw [Set.mem_singleton_iff] at ha' hc'
    substs a' c'
    have p₂' := p₂.ofMemKStar b' hb'
    have p' := p₁.append p₂' |>.append p₃ |>.append p₄
    simpa using accepts_iff_exists_path.2 ⟨s, hs, u, hu, ⟨p'⟩⟩

variable (M) in
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
@[simps] def toNFA (M : DFA α σ) : NFA α σ where
  step s a := {M.step s a}
  start := {M.start}
  accept := M.accept

@[simp]
theorem toNFA_evalFrom_match (M : DFA α σ) (start : σ) (s : List α) :
    M.toNFA.evalFrom {start} s = {M.evalFrom start s} := by
  change List.foldl M.toNFA.stepSet {start} s = {List.foldl M.step start s}
  induction s generalizing start with
  | nil => tauto
  | cons a s ih =>
    rw [List.foldl, List.foldl,
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

namespace NFA

variable (M) in
/-- `M.reverse` constructs an NFA with the same states as `M`, but all the transitions reversed. The
resulting automaton accepts a word `x` if and only if `M` accepts `List.reverse x`. -/
@[simps]
def reverse : NFA α σ where
  step s a := { s' | s ∈ M.step s' a }
  start := M.accept
  accept := M.start

variable (M) in
@[simp]
theorem reverse_reverse : M.reverse.reverse = M := by
  simp [reverse]

theorem disjoint_stepSet_reverse {a : α} {S S' : Set σ} :
    Disjoint S (M.reverse.stepSet S' a) ↔ Disjoint S' (M.stepSet S a) := by
  rw [← not_iff_not]
  simp only [Set.not_disjoint_iff, mem_stepSet, reverse_step, Set.mem_setOf_eq]
  tauto

theorem disjoint_evalFrom_reverse {x : List α} {S S' : Set σ}
    (h : Disjoint S (M.reverse.evalFrom S' x)) : Disjoint S' (M.evalFrom S x.reverse) := by
  simp only [evalFrom, List.foldl_reverse] at h ⊢
  induction x generalizing S S' with
  | nil =>
    rw [disjoint_comm]
    exact h
  | cons x xs ih =>
    rw [List.foldl_cons] at h
    rw [List.foldr_cons, ← NFA.disjoint_stepSet_reverse, disjoint_comm]
    exact ih h

theorem disjoint_evalFrom_reverse_iff {x : List α} {S S' : Set σ} :
    Disjoint S (M.reverse.evalFrom S' x) ↔ Disjoint S' (M.evalFrom S x.reverse) :=
  ⟨disjoint_evalFrom_reverse, fun h ↦ List.reverse_reverse x ▸ disjoint_evalFrom_reverse h⟩

@[simp]
theorem mem_accepts_reverse {x : List α} : x ∈ M.reverse.accepts ↔ x.reverse ∈ M.accepts := by
  simp [mem_accepts, ← Set.not_disjoint_iff, not_iff_not, disjoint_evalFrom_reverse_iff]

end NFA

namespace Language

protected theorem IsRegular.reverse {L : Language α} (h : L.IsRegular) : L.reverse.IsRegular :=
  have ⟨σ, _, M, hM⟩ := h
  ⟨_, inferInstance, M.toNFA.reverse.toDFA, by ext; simp [hM]⟩

protected theorem IsRegular.of_reverse {L : Language α} (h : L.reverse.IsRegular) : L.IsRegular :=
  L.reverse_reverse ▸ h.reverse

/-- Regular languages are closed under reversal. -/
@[simp]
theorem isRegular_reverse_iff {L : Language α} : L.reverse.IsRegular ↔ L.IsRegular :=
  ⟨.of_reverse, .reverse⟩

end Language
