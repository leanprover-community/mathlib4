/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Maja Kądziołka, Chris Wong, Rudy Peterson
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

theorem stepSet_union {S1 S2 : Set σ} {a : α} :
    M.stepSet (S1 ∪ S2) a = M.stepSet S1 a ∪ M.stepSet S2 a := by
  ext s
  simp [mem_stepSet]
  constructor
  · rintro ⟨s', (h1 | h2), hstep⟩
    · left; tauto
    · right; tauto
  · rintro (⟨s', h, hstep⟩ | ⟨s', h, hstep⟩) <;> exists s' <;> tauto

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
theorem evalFrom_append (S : Set σ) (x y : List α) :
    M.evalFrom S (x ++ y) = M.evalFrom (M.evalFrom S x) y := by
  simp only [evalFrom, List.foldl_append]

theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  simp only [evalFrom_append, evalFrom_cons, evalFrom_nil]

theorem evalFrom_union (S1 S2 : Set σ) (x : List α) :
    M.evalFrom (S1 ∪ S2) x = M.evalFrom S1 x ∪ M.evalFrom S2 x := by
  induction x generalizing S1 S2
  case nil => simp
  case cons a x ih => simp [stepSet_union, ih]

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
/-- `M.acceptsFrom S` is the language of `x` such that there is an accept state
in `M.evalFrom S x`. -/
def acceptsFrom (S : Set σ) : Language α := {x | ∃ s ∈ M.accept, s ∈ M.evalFrom S x}

theorem mem_acceptsFrom {S : Set σ} {x : List α} :
    x ∈ M.acceptsFrom S ↔ ∃ s ∈ M.accept, s ∈ M.evalFrom S x := by
  rfl

@[simp]
theorem mem_acceptsFrom_nil {S : Set σ} : [] ∈ M.acceptsFrom S ↔ ∃ s ∈ S, s ∈ M.accept := by
  simp [mem_acceptsFrom]; tauto

@[simp]
theorem mem_acceptsFrom_cons {S : Set σ} {a : α} {x : List α} :
    a :: x ∈ M.acceptsFrom S ↔ x ∈ M.acceptsFrom (M.stepSet S a) := by
  simp [mem_acceptsFrom]

@[simp]
theorem mem_acceptsFrom_append {S : Set σ} {x y : List α} :
    x ++ y ∈ M.acceptsFrom S ↔ y ∈ M.acceptsFrom (M.evalFrom S x) := by
  simp [mem_acceptsFrom]

theorem acceptsFrom_union {S1 S2 : Set σ} :
    M.acceptsFrom (S1 ∪ S2) = M.acceptsFrom S1 + M.acceptsFrom S2 := by
  rw [Language.add_def]; ext x
  rw [Set.mem_union]; simp_rw [↑mem_acceptsFrom, evalFrom_union]
  constructor
  · rintro ⟨s, hs, h | h⟩
    · left; tauto
    · right; tauto
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩) <;> exists s <;> tauto

theorem mem_acceptsFrom_biUnion {ι : Type*} (t : Set ι) (f : ι → Set σ) (x : List α) :
    x ∈ M.acceptsFrom (⋃ i ∈ t, f i) ↔ x ∈ ⋃ i ∈ t, M.acceptsFrom (f i) := by
  simp [acceptsFrom]; rw [Set.mem_setOf]; tauto

theorem mem_acceptsFrom_setOf_fact {S : Set σ} {p : Prop} {x : List α} :
    x ∈ M.acceptsFrom {s ∈ S | p} ↔ x ∈ M.acceptsFrom S ∧ p := by
  induction x generalizing S <;> simp
  case nil => tauto
  case cons a x ih =>
    have h : M.stepSet {s ∈ S | p} a = {s ∈ M.stepSet S a | p} := by
      ext s; simp [stepSet]; tauto
    rw [h, ih]

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

theorem accepts_acceptsFrom : M.accepts = M.acceptsFrom M.start := by
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
  simp [mem_accepts, ← Set.not_disjoint_iff, disjoint_evalFrom_reverse_iff]

end NFA

namespace NFA

/-!
### Declarations about `NFA.concat`

We provide a direct construction of concatenated NFAs without ε-transitions: if `M1` accepts
language `L1` and `M2` accepts language `L2` then `M1 * M2` (`M1.concat M2`) accepts language
`L1 * L2`. In order to construct `M1 * M2`, we must create transitions from accepting states in `M1`
to states immediatately reachable after a single transition from states in `M2.start`. Furthermore,
we must include states of `M1.accept` in `(M1 * M2).accept` if `[] ∈ M2.accepts`.

Traditionally, concatenation is constructed for `εNFA`, not plain `NFA`, by adding ε-transitions
from states in `M1.accept` to `M2.start`. Since `NFA` does not include ε-transitions, we must
include the aforementioned transitions for `NFA.concatStep`:
`⋃ s2 ∈ M2.start, { s2' ∈ M2.step s2 a | s1 ∈ M1.accept }`.

This construction for unweighted `NFA` provides insight into the weighted case, where the weighted
analogue for `NFA` is different from the weighted analogue for `εNFA`.
-/

variable {σ1 σ2 : Type v} (M1 : NFA α σ1) (M2 : NFA α σ2)

/-- `M1.concatStart` is `(M1 * M2).start`, merely including `M1.start`. -/
@[simp]
def concatStart : Set (σ1 ⊕ σ2) := Sum.inl '' M1.start

/-- `concatAccept M1 M2` is `(M1 * M2).accept`, including `M2.accepts`, and if `[] ∈ M2.accepts`
then also `M1.accepts`. If [] ∈ M2.accepts`, then without including `M1.accepts`, a final state in
`M2.accept` is unreachable in `M1 * M2`. -/
@[simp]
def concatAccept : Set (σ1 ⊕ σ2) :=
  Sum.inl '' { s1 ∈ M1.accept | [] ∈ M2.accepts } ∪ Sum.inr '' M2.accept

/-- `concatStep M1 M2 s a` is `(M1 * M2).step s a`, the set of states available in `M1 * M2` by a
transition from state `s` via character `a`. We include all transitions from `M1.step` and
`M2.step`. In order to "concatenate" `M1` and `M2`, for `(M1 * M2).step (inl s1) a` when
`s1 ∈ M1.accept`, we must also include states reachable from a state in `M2.start` via `a`,
`⋃ s2 ∈ M2.start, M2.step s2 a`. -/
@[simp]
def concatStep : σ1 ⊕ σ2 → α → Set (σ1 ⊕ σ2)
| .inl s1, a =>
  Sum.inl '' M1.step s1 a ∪ Sum.inr '' ⋃ s2 ∈ M2.start, { s2' ∈ M2.step s2 a | s1 ∈ M1.accept }
| .inr s2, a =>
  Sum.inr '' M2.step s2 a

/-- `M1.concat M2` is `M1 * M2`, the concatenation of `M1` and `M2` achieved without ε-transitions.
We decline to attatch a `@[simp]` nor `@[simps]` attribute in order to avoid unfolding the entire
construction, and instead prefer the `M1 * M2` notation, and only simplify the projections for
`M1 * M2`. -/
def concat : NFA α (σ1 ⊕ σ2) where
  step := concatStep M1 M2
  start := concatStart M1
  accept := concatAccept M1 M2

instance : HMul (NFA α σ1) (NFA α σ2) (NFA α (σ1 ⊕ σ2)) :=
  ⟨concat⟩

lemma hmul_eq_conat : M1 * M2 = concat M1 M2 := rfl

@[simp]
lemma hmul_concatStart : (M1 * M2).start = concatStart M1 := rfl

@[simp]
lemma hmul_concatAccept : (M1 * M2).accept = concatAccept M1 M2 := rfl

@[simp]
lemma hmul_concatStep : (M1 * M2).step = concatStep M1 M2 := rfl

lemma concat_stepSet_inr {S2 : Set σ2} {a : α} :
    (M1 * M2).stepSet (Sum.inr '' S2) a = Sum.inr '' M2.stepSet S2 a := by
  ext (s1 | s2) <;> simp [stepSet]

lemma concat_acceptsFrom_inr {S2 : Set σ2} :
    (M1 * M2).acceptsFrom (Sum.inr '' S2) = M2.acceptsFrom S2 := by
  ext y
  induction y generalizing S2
  case nil => simp
  case cons a y ih => simp [←ih, concat_stepSet_inr]

theorem concat_acceptsFrom {S1 : Set σ1} :
    (M1 * M2).acceptsFrom (Sum.inl '' S1) = M1.acceptsFrom S1 * M2.accepts := by
  ext z
  rw [Language.mul_def, Set.mem_image2]
  induction z generalizing S1
  case nil =>
    simp; rw [mem_acceptsFrom_nil]; tauto
  case cons a z ih =>
    simp [stepSet, mem_acceptsFrom_biUnion, acceptsFrom_union, max, SemilatticeSup.sup]
    simp [ih, concat_acceptsFrom_inr]; clear ih
    simp_rw [↑mem_acceptsFrom_biUnion]
    simp
    simp_rw [↑mem_acceptsFrom_setOf_fact]
    constructor
    · rintro ⟨s1, hs1, ⟨x, hx, y, hy, rfl⟩ | ⟨s2, hstart2, hz, haccept1⟩⟩
      · exists (a :: x); rw [mem_acceptsFrom_cons]
        simp [stepSet, mem_acceptsFrom_biUnion]; tauto
      · exists []; rw [mem_acceptsFrom_nil]
        simp [accepts_acceptsFrom]; rw [mem_acceptsFrom_cons]
        simp [stepSet, mem_acceptsFrom_biUnion]; tauto
    · rintro ⟨x, hx, y, hy, heq⟩
      cases x
      case nil =>
        rw [mem_acceptsFrom_nil] at hx
        obtain ⟨s1, hs1, haccept1⟩ := hx
        exists s1
        simp at heq; subst y
        rw [accepts_acceptsFrom, mem_acceptsFrom_cons] at hy
        simp [stepSet, mem_acceptsFrom_biUnion] at hy
        tauto
      case cons b x =>
        obtain ⟨rfl, rfl⟩ := heq
        rw [mem_acceptsFrom_cons] at hx
        simp [stepSet, mem_acceptsFrom_biUnion] at hx
        obtain ⟨s1, hs1, hx⟩ := hx
        exists s1
        constructor; next => assumption
        left; tauto

/-- If `M1` accepts language `L1` and `M2` accepts language `L2`, then the language `L` of `M1 * M2`
(`M1.concat M2`) is exactly equal to `L = L1 * L2`. -/
theorem concat_accepts : (M1 * M2).accepts = M1.accepts * M2.accepts := by
  simp [concat_acceptsFrom, accepts_acceptsFrom]

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

/-- Regular languages are closed under concatenation. -/
theorem IsRegular.concat {L1 L2 : Language α}
  (h1 : L1.IsRegular) (h2 : L2.IsRegular) : (L1 * L2).IsRegular :=
  have ⟨σ1, _, M1, hM1⟩ := h1
  have ⟨σ2, _, M2, hM2⟩ := h2
  ⟨_, inferInstance, (M1.toNFA * M2.toNFA).toDFA, by simp [NFA.concat_accepts, hM1, hM2]⟩

end Language
