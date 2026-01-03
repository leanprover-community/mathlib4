/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Maja Kądziołka, Chris Wong, Rudy Peterson
-/
module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Powerset

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

@[expose] public section

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
@[simp]
theorem stepSet_union {S T : Set σ} {a : α} :
    M.stepSet (S ∪ T) a = M.stepSet S a ∪ M.stepSet T a := by
  ext s
  simp [mem_stepSet, or_and_right, exists_or]

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

variable (M) in
@[simp]
theorem evalFrom_append (S : Set σ) (x y : List α) :
    M.evalFrom S (x ++ y) = M.evalFrom (M.evalFrom S x) y := by
  simp only [evalFrom, List.foldl_append]

@[deprecated "Use evalFrom_append, evalFrom_cons, and evalFrom_nil" (since := "2025-11-17")]
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  simp only [evalFrom_append, evalFrom_cons, evalFrom_nil]

variable (M) in
@[simp]
theorem evalFrom_union (S T : Set σ) (x : List α) :
    M.evalFrom (S ∪ T) x = M.evalFrom S x ∪ M.evalFrom T x := by
  induction x generalizing S T with
  | nil => simp
  | cons a x ih => simp [ih]

variable (M) in
@[simp]
theorem evalFrom_iUnion {ι : Sort*} (s : ι → Set σ) (x : List α) :
    M.evalFrom (⋃ i, s i) x = ⋃ i, M.evalFrom (s i) x := by
  induction x generalizing s with
  | nil => simp
  | cons a x ih => simp [stepSet, Set.iUnion_comm (ι:=σ) (ι':=ι), ih]

variable (M) in
theorem evalFrom_iUnion₂ {ι : Sort*} {κ : ι → Sort*} (f : ∀ i, κ i → Set σ) (x : List α) :
    M.evalFrom (⋃ (i) (j), f i j) x = ⋃ (i) (j), M.evalFrom (f i j) x := by
  simp

variable (M) in
@[deprecated evalFrom_iUnion₂ (since := "2025-11-17")]
theorem evalFrom_biUnion {ι : Type*} (t : Set ι) (f : ι → Set σ) :
    ∀ (x : List α), M.evalFrom (⋃ i ∈ t, f i) x = ⋃ i ∈ t, M.evalFrom (f i) x
  | [] => by simp
  | a :: x => by simp [stepSet, evalFrom_biUnion _ _ x]

variable (M) in
theorem evalFrom_eq_biUnion_singleton (S : Set σ) (x : List α) :
    M.evalFrom S x = ⋃ s ∈ S, M.evalFrom {s} x := by
  simp [← evalFrom_iUnion₂]

theorem mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} :
    s ∈ M.evalFrom S x ↔ ∃ t ∈ S, s ∈ M.evalFrom {t} x := by
  rw [evalFrom_eq_biUnion_singleton]
  simp

variable (M) in
/-- `M.acceptsFrom S` is the language of `x` such that there is an accept state
in `M.evalFrom S x`. -/
def acceptsFrom (S : Set σ) : Language α := {x | ∃ s ∈ M.accept, s ∈ M.evalFrom S x}

theorem mem_acceptsFrom {S : Set σ} {x : List α} :
    x ∈ M.acceptsFrom S ↔ ∃ s ∈ M.accept, s ∈ M.evalFrom S x := by
  rfl

variable (M) in
@[simp]
theorem nil_mem_acceptsFrom {S : Set σ} : [] ∈ M.acceptsFrom S ↔ ∃ s ∈ S, s ∈ M.accept := by
  simp only [mem_acceptsFrom, evalFrom_nil]; tauto

variable (M) in
@[simp]
theorem cons_mem_acceptsFrom {S : Set σ} {a : α} {x : List α} :
    a :: x ∈ M.acceptsFrom S ↔ x ∈ M.acceptsFrom (M.stepSet S a) := by
  simp [mem_acceptsFrom]

variable (M) in
theorem cons_preimage_acceptsFrom {S : Set σ} {a : α} :
    (a :: ·) ⁻¹' M.acceptsFrom S = M.acceptsFrom (M.stepSet S a) := by
  ext x; simp [cons_mem_acceptsFrom M]

variable (M) in
@[simp]
theorem append_mem_acceptsFrom {S : Set σ} {x y : List α} :
    x ++ y ∈ M.acceptsFrom S ↔ y ∈ M.acceptsFrom (M.evalFrom S x) := by
  simp [mem_acceptsFrom]

variable (M) in
theorem append_preimage_acceptsFrom {S : Set σ} {x : List α} :
    (x ++ ·) ⁻¹' M.acceptsFrom S = M.acceptsFrom (M.evalFrom S x) := by
  ext y; simp [append_mem_acceptsFrom M]

variable (M) in
@[simp]
theorem acceptsFrom_union {S T : Set σ} :
    M.acceptsFrom (S ∪ T) = M.acceptsFrom S + M.acceptsFrom T := by
  rw [Language.add_def]; ext x
  simp only [mem_acceptsFrom, evalFrom_union, mem_union]
  constructor
  · rintro ⟨s, hs, h | h⟩
    · left; tauto
    · right; tauto
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩) <;> exists s <;> tauto

variable (M) in
@[simp]
theorem acceptsFrom_iUnion {ι : Sort*} (s : ι → Set σ) :
    M.acceptsFrom (⋃ i, s i) = ⋃ i, M.acceptsFrom (s i) := by
  ext x
  simp only [acceptsFrom, evalFrom_iUnion, mem_iUnion]
  simp_rw [↑mem_iUnion, ↑mem_setOf_eq]; tauto

variable (M) in
theorem acceptsFrom_iUnion₂ {ι : Sort*} {κ : ι → Sort*} (f : ∀ i, κ i → Set σ) :
    M.acceptsFrom (⋃ (i) (j), f i j) = ⋃ (i) (j), M.acceptsFrom (f i j) := by
  simp

variable (M) in
@[simp]
private theorem mem_acceptsFrom_sep_fact {S : Set σ} {p : Prop} {x : List α} :
    x ∈ M.acceptsFrom {s ∈ S | p} ↔ x ∈ M.acceptsFrom S ∧ p := by
  induction x generalizing S with
  | nil => simp only [nil_mem_acceptsFrom, mem_setOf_eq]; tauto
  | cons a x ih =>
    have h : M.stepSet {s ∈ S | p} a = {s ∈ M.stepSet S a | p} := by
      ext s; simp only [stepSet, mem_setOf_eq, mem_iUnion, exists_prop]; tauto
    simp [h, ih]

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
theorem eval_append_singleton (x : List α) (a : α) :
    M.eval (x ++ [a]) = M.stepSet (M.eval x) a := by
  simp [eval]

variable (M) in
/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α := {x | ∃ S ∈ M.accept, S ∈ M.eval x}

theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ ∃ S ∈ M.accept, S ∈ M.evalFrom M.start x := by
  rfl

theorem accepts_eq_acceptsFrom_start : M.accepts = M.acceptsFrom M.start := rfl

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

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by
  rw [← toDFA_correct] at hx ⊢
  exact M.toDFA.pumping_lemma hx hlen

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
      show M.toNFA.stepSet {start} a = {M.step start a} by simp [NFA.stepSet]]
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
  simp [mem_accepts, ← Set.not_disjoint_iff, disjoint_evalFrom_reverse_iff]

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
