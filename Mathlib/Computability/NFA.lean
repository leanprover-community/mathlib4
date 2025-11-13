/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Maja Kądziołka, Chris Wong, Rudy Peterson
-/
module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Option

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
theorem evalFrom_empty (x : List α) : M.evalFrom ∅ x = ∅ := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih]

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
theorem mem_acceptsFrom_iff_exists {S : Set σ} {x : List α} :
    x ∈ M.acceptsFrom S ↔ ∃ s ∈ S, x ∈ M.acceptsFrom {s} := by
  simp [mem_acceptsFrom, mem_evalFrom_iff_exists (S:=S) (x:=x)]
  tauto

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
    (x ++ ·) ⁻¹'  M.acceptsFrom S = M.acceptsFrom (M.evalFrom S x) := by
  ext y; simp [append_mem_acceptsFrom M]

variable (M) in
@[simp]
theorem acceptsFrom_empty : M.acceptsFrom ∅ = 0 := by
  ext x
  simp [mem_acceptsFrom]

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

section kstar

/-!
### Declarations about `NFA.kstar`

This construction and proof idea are by Tom Kranz from PR Mathlib#15651.

We provide the Kleene closure for non-epsilon NFAs under Kleene star: if NFA `M` accepts language
`L`, then `M.kstar` accepts language `M∗`. In order to construct `M.kstar`, we must create
transitions from *penultimate states* to the start state: for all states `s1` and `s2` and any
character `a` such that `s2 ∈ M.step s1 a` and `s2 ∈ M.accept`, we must add a transition from `s1`
to every state in `M.start`. Furthermore, we must add a special state `none` that is both a start
and accept state in order to ensure that `M.kstar` accepts the empty string. This is how we
"close the loop" for the Kleene closure.

The key idea of this construction: in `M.kstar` we must include:
* an empty path from state `none` to accept the empty string.
* all transitions originally from `M`, injected with `some`.
* new transitions from *penultimate states* to start states to enable looping.
This gives the new machine `M.kstar` the options to accept a string `x` accepting by `M`, and to
continue looping after consuming a prefix of `x` accepted by `M`. This choice is reflected in the
definition `M.kstarStates`, which is used in `M.ktar.step`.
-/

open Option

variable (M) in
/- `M.kstarStates S` is the set of states including both `S`, and `M.start` if there exists an
`s ∈ S` such that `s ∈ M.accept`. This definition is used in `M.kstarStep` in order to obtain the
set of states reachable from a given state in `M.kstar` for exactly a single transition. In order to
compute `M.kstar.step (some s) a`, we compute `M.kstarStates (M.step s a)`. This creates a
transition from `s` to every `s' ∈ M.step s a`, and if `M.step s a` includes a state in `M.accept`,
then it also creates a transition from `s` to every state in `M.start`. Thus `M.kstarStates` is the
core definition in our construction that "closes the loop" for the Kleene closure. -/
def kstarStates (S : Set σ) : Set (Option σ) :=
  some '' (S ∪ ⋃ s ∈ S ∩ M.accept, M.start)

@[simp]
/- `M.kstarStart` is the set of start states in `M.kstar`. We include both `M.start` and a new state
`{none}` to accept the empty string. -/
def kstarStart : Set (Option σ) := {none} ∪ some '' M.start

@[simp]
/- `M.kstarAccept` is the set of accept states in `M.kstar`. We include both `M.accept` and a new
state `{none}` to accept the empty string. -/
def kstarAccept : Set (Option σ) := {none} ∪ some '' M.accept

theorem kstartStates_start : M.kstarStates M.start = some '' M.start := by
  simp [kstarStates, Set.image_union, Set.subset_preimage_image]

theorem kstarStart_eq_kstarStates : M.kstarStart = {none} ∪ M.kstarStates M.start := by
  ext s
  cases s <;> simp [kstarStates]

variable (M) in
/- `M.kstarStep` is the set of transitions in `M.kstar`. Via `M.kstarStates`, this definition covers
the following cases:
* `M.kstarStep none a`: Gives no transitions. The state `none` is reserved for the empty path to
  accept the empty string.
* `M.kstarStep (some s) a` when `s` *is NOT a penultimate state*: only includes transitions
  `M.step s a` if forall `s' ∈ M.step s a` then `s' ∉ M.accept`.
* `M.kstarStep (some s) a` when `s` *is INDEED a penultimate state*: in addition to including
  transitions for `M.step s a`, we also *create* transitions `some s' ∈ M.kstarStep (some s) a` for
  every state `s' ∈ M.start` such that there exists some `s'' ∈ M.accept` and `s'' ∈ M.step s a`.
  This cases "closes the loop" for the Kleene closure. -/
@[simp]
def kstarStep : Option σ → α → Set (Option σ)
| none, _ => ∅
| some s, a => M.kstarStates <| M.step s a

variable (M) in
/- `M.kstar` is the Kleene closure of NFA `M`: if `M` accepts langauge `L`, then `M.kstar` accepts
language `L∗`. Construction from Mathlib#15651 by Tom Kranz. -/
@[simps]
def kstar : NFA α (Option σ) where
  step := M.kstarStep
  start := M.kstarStart
  accept := M.kstarAccept

theorem mem_acceptsFrom_impl_mem_acceptsFrom_kstar {S : Set σ} {x : List α} :
    x ∈ M.acceptsFrom S →
    x ∈ M.kstar.acceptsFrom (M.kstarStates S) := by
  induction x generalizing S with
  | nil =>
    simp only [mem_acceptsFrom_nil]
    rintro ⟨s, hs, haccept⟩
    exists (some s)
    apply (fun x ↦ And.intro x (by simpa))
    rw [kstarStates, Function.Injective.mem_set_image (Option.some_injective _)]
    tauto
  | cons a x ih =>
    simp_rw [mem_acceptsFrom_cons, stepSet, kstarStates, acceptsFrom_biUnion, ↑Set.mem_iUnion₂,
      exists_prop, mem_image]
    tauto

/- State `none` is only reachable from itself in `M.kstar`. -/
theorem mem_kstarStates_not_none {S : Set σ} : none ∉ M.kstarStates S := by
  simp [kstarStates]

/- State `none` is only reachable from itself in `M.kstar`. -/
theorem mem_stepSet_kstar_not_none {S : Set (Option σ)} {a : α} :
    none ∉ M.kstar.stepSet S a := by
  simp [stepSet]
  intro so
  cases so with
  | none =>
    simp
  | some s =>
    simp [mem_kstarStates_not_none]

/- State `none` is only reachable from itself in `M.kstar`. -/
theorem mem_evalFrom_kstar_not_none {S : Set (Option σ)} {x : List α} :
    x ≠ [] →
    none ∉ M.kstar.evalFrom S x := by
  induction x using List.twoStepInduction generalizing S with
  | nil =>
    simp
  | singleton a =>
    simp [mem_stepSet_kstar_not_none]
  | cons_cons a b x _ ih =>
    intro _
    rw [evalFrom_cons]
    apply ih
    tauto

/- State `none` is only reachable from itself in `M.kstar`. -/
theorem evalFrom_kstar_none {S : Set (Option σ)} {x : List α} :
    none ∈ M.kstar.evalFrom S x → x = [] ∧ none ∈ S := by
  cases x with
  | nil =>
    simp
  | cons a x =>
    intro h
    obtain ⟨⟩ := mem_evalFrom_kstar_not_none (by tauto) h

/- State `none` is only reachable from itself in `M.kstar`. -/
theorem acceptsFrom_kstar_none : M.kstar.acceptsFrom {none} = {[]} := by
  ext x
  constructor
  · cases x with
    | nil =>
      simp [Set.mem_singleton_iff]
      tauto
    | cons a x =>
      simp
  · rw [acceptsFrom, Set.mem_setOf, Set.mem_singleton_iff]
    rintro rfl
    simp

/-- When a state `t ∈ M.evalFrom S x`, then `some t ∈ M.kstar.evalFrom (some '' S) x`. In this
proof, we only require paths originally in `M`, and ignore any transitions from penultimate states
to start states from [M.kstarStates]. Essentially, we demonstrate that any paths in `M` are also
in `M.kstar`. -/
theorem mem_evalFrom_impl_mem_evalFrom_kstar {x : List α} {S : Set σ} {t : σ} :
    t ∈ M.evalFrom S x →
    some t ∈ M.kstar.evalFrom (some '' S) x := by
  induction x generalizing S t with
  | nil =>
    simp
  | cons a x ih =>
    simp only [evalFrom_cons, stepSet, evalFrom_biUnion, kstar_step, kstarStep,
      Set.biUnion_image, kstarStates, Set.image_union, Set.image_iUnion₂,
      exists_prop, mem_inter_iff, forall_exists_index, and_imp,
      evalFrom_union, mem_union, mem_iUnion, exists_prop]
    tauto

/-- For any non-empty string `x`, if `t ∈ M.evalFrom S x` and `t ∈ M.accept`, then for any start
state `s ∈ M.start`, this start state `s` is included in the states obtained from
'some s ∈ M.kstar.evalFrom (some '' S) x'. This follows by definition of `M.kstarStates`, where
pentultimate states have transitions to start states in `M.kstar`. Essentially, we demonstrate that
for any accepting path in `M` from any set of states `S` for any string `x`, there is also a path
from `S` for `x` to any start state. This key property allows a non-empty string `x` with an
accepting path to return to the start. By enabling this "restart", we enable Kleene closure
looping. In each case, we select the accepting path as follows:
* vacuous case `M.evalFrom S []`: we violate the assumption that `x` is non-empty.
* base case `M.evalFrom S [a]`: we reach the end, so we must end the path at a start state from a
  penultimate state.
* inductive case `M.evalFrom S (a :: x)` where `x ≠ []`: we must continue the path via transitions
originally from `M`, avoiding the transition from a pentulitmate state to a start state.
Note that this property fails to hold if we allow `x = []`, since some arbitrary `S` may not
include the start states. We require at least one transition in order to ensure the path may lead
to any start state to enable looping. -/
theorem mem_evalFrom_impl_mem_evalFrom_kstar_start {x : List α} {S : Set σ} {s t : σ} :
    x ≠ [] →
    t ∈ M.accept →
    t ∈ M.evalFrom S x →
    s ∈ M.start →
    some s ∈ M.kstar.evalFrom (some '' S) x := by
  induction x generalizing S s t with
  | nil => simp
  | cons a x ih =>
    intro _
    simp only [evalFrom_cons, stepSet, kstar_step, kstarStep, kstarStates, Set.biUnion_image]
    simp only [evalFrom_union, evalFrom_biUnion, Set.image_union, Set.image_iUnion₂,
      Set.mem_iUnion₂, exists_prop, Set.mem_union]
    simp only [mem_inter_iff, exists_and_right, forall_exists_index, and_imp]
    by_cases hnil : x = []
    · subst x
      simp only [evalFrom_nil]
      intro ht q hq hstep hstart
      exists q
      tauto
    · intro ht q hq hx hs
      exists q
      specialize ih hnil ht hx hs
      tauto

/- If every `z ∈ zs` is accepted by `M` for some list of strings `zs`, then `zs.flatten` is
accpeted by `M.kstar`. In order to ensure that we may loop through `M` from a penultimate state to
a start state at the end of each `z ∈ zs`, we require that every `z ≠ []`. Otherwise, `zs.flatten`
may have no accepting path in `M.kstar` by lacking transitions from a penultimate state to a start
state.

The conclusion of the goal is `zs.flatten ∈ M.kstar.acceptsFrom (some '' (insert s M.start))` for
some `s ∈ M.accept`, rather than simply `zs.flatten ∈ M.kstar.acceptsFrom (some '' M.start)`, in
order to prove the base case when `zs = []`.

In each case, we select the accepting path as follows:
* base case `[]`: since `s ∈ M.accept`, we may choose this `s` as the final accepting state.
* inductive case `z :: zs`: our path must always go through some penultimate state to some
  start state, since to accept `zs.flatten` in `M.kstar` we must reset to a start state after
  processing string `z`.
 -/
theorem Forall_mem_accepts_impl_mem_flatten_kstar_acceptsFrom {s : σ} {zs : List (List α)} :
    s ∈ M.accept →
    List.Forall (fun z ↦ z ∈ M.accepts ∧ z ≠ []) zs →
    zs.flatten ∈ M.kstar.acceptsFrom (some '' (insert s M.start)) := by
  intro haccept hzs
  simp only [mem_acceptsFrom, kstar_accept, kstarAccept, Set.mem_union, Set.mem_singleton_iff,
    mem_image, exists_eq_or_imp, ↓existsAndEq, and_true]
  right
  simp_rw [Set.insert_eq, Set.image_union, evalFrom_union, Set.mem_union, Set.image_singleton]
  induction zs generalizing s haccept with
  | nil =>
    tauto
  | cons z zs ih =>
    simp only [List.flatten_cons, evalFrom_append]
    simp only [ne_eq, List.forall_cons] at hzs
    rcases hzs with ⟨⟨hz, hznil⟩, hzs⟩
    rw [mem_accepts] at hz
    rcases hz with ⟨q, hq, hz⟩
    simp_rw [mem_evalFrom_iff_exists (S:=M.kstar.evalFrom {some s} z)]
    simp_rw [mem_evalFrom_iff_exists (S:=M.kstar.evalFrom (some '' M.start) z)]
    rcases (ih hq hzs) with ⟨t, ht, hflatten⟩
    exists t
    apply (fun x ↦ And.intro ht x)
    right
    rcases hflatten with (hflatten | hflatten)
    · exists q
      constructor
      · apply mem_evalFrom_impl_mem_evalFrom_kstar
        assumption
      · assumption
    · rw [mem_evalFrom_iff_exists] at hflatten
      simp_rw [Set.mem_image] at hflatten
      obtain ⟨so', ⟨s', hs', rfl⟩, hflatten⟩ := hflatten
      exists s'
      constructor
      · apply mem_evalFrom_impl_mem_evalFrom_kstar_start hznil hq hz hs'
      · assumption

/- Proof idea from Mathlib#15651 by Tom Kranz.

If some string `y` is accepted in `M` from `S`, `y ∈ M.acceptsFrom S`, and some list of strings
`zs`, such that for all `z ∈ zs` we have `z ∈ M.accepts` and `z ≠ []`, then `y ++ zs.flatten` is
accepted by `M.kstar` from `M.kstarStates S`.

We proceed by induction on `y`, where `y` represents the suffix of some string `zʸ` in `zʸ :: zs`:
* base case `[]`: since we know every member of `zs` is independently accepted by `M`, `zs.flatten`
  is accepted by `M.kstar`. Crucially, we must isoloate some accepting state `s ∈ M.accept`, and
  proceed to show that `zs.flatten ∈ M.kstar.acceptsFrom (some '' insert s M.start)`.
* inductive case `a :: y`: when stepping for the transition for character `a`, we *must* choose the
  transition originally from `M`, not the transition from a pentultimate state to a start state.
  `a :: y` is not at the boundary of the Kleene loop, but in the middle of a single loop, thus for
  these inductive steps we must traverse through transitions originally from `M`. This is regardless
  of whether `y ++ zs.flatten` (from the inductive hypothesis) was accepted from `M.step s a` or
  `M.start`.
 -/
theorem mem_kstar_acceptsFrom {S : Set σ} {y : List α} {zs : List (List α)} :
    y ∈ M.acceptsFrom S →
    List.Forall (fun z ↦ z ∈ M.accepts ∧ z ≠ []) zs →
    y ++ zs.flatten ∈ M.kstar.acceptsFrom (M.kstarStates S) := by
  intro hy hzs
  induction y generalizing S zs with
  | nil =>
    simp only [mem_acceptsFrom_nil] at hy
    rcases hy with ⟨s, hs, haccept⟩
    have hnonempty : (S ∩ M.accept).Nonempty := by exists s
    have hsub : {s} ⊆ S := by simpa [Set.singleton_subset_iff]
    simp only [List.nil_append, kstarStates, Set.biUnion_const hnonempty]
    rw [←Set.diff_union_of_subset (s:=S) (t:={s}) hsub, Set.union_assoc, Set.image_union,
      acceptsFrom_union, Language.add_def, Set.mem_union]
    right
    apply Forall_mem_accepts_impl_mem_flatten_kstar_acceptsFrom haccept hzs
  | cons a y ih =>
    rw [mem_acceptsFrom_cons] at hy
    specialize ih hy hzs
    simp only [stepSet, kstarStates, Set.image_union, Set.image_iUnion₂, acceptsFrom_union,
      acceptsFrom_biUnion, Language.add_def] at *
    simp_rw [↑Set.mem_union] at ih
    left
    simp only [List.cons_append, mem_acceptsFrom_cons (M:=M.kstar), stepSet, kstar_step,
      kstarStep, kstarStates, Set.biUnion_image, Set.image_union, acceptsFrom_biUnion,
      acceptsFrom_union, Language.add_def, Set.iUnion_union_distrib]
    rcases ih with (ih | ih)
    · simp [-append_mem_acceptsFrom, Set.mem_union_left _ ih]
    · simp only [mem_inter_iff, mem_iUnion, exists_prop, exists_and_right] at ih
      obtain ⟨⟨s', ⟨⟨s, hs, hstep⟩, haccept⟩⟩, ih⟩ := ih
      rw [Set.mem_union]
      right
      simp only [Set.image_iUnion₂, acceptsFrom_iUnion, Set.mem_iUnion₂,
        mem_inter_iff, exists_prop, exists_and_right]
      tauto

-- Proof idea from Mathlib#15651 by Tom Kranz
theorem mem_acceptsFrom_kstar_impl_exists_flatten {S : Set σ} {x : List α} :
    x ∈ M.kstar.acceptsFrom (some '' S) →
    ∃ (y : List α) (L : List (List α)),
    x = y ++ L.flatten ∧ y ∈ M.acceptsFrom S ∧ ∀ z ∈ L, z ∈ M.accepts := by
  induction x generalizing S with
  | nil =>
    simp
    rintro s hs haccept
    exists []
    tauto
  | cons a x ih =>
    simp [stepSet, kstarStates, Set.image_union, max, SemilatticeSup.sup, Set.image_iUnion₂]
    rw [Set.mem_iUnion₂]
    simp [Set.mem_union]
    rintro s hs (hx | ⟨⟨s', hs', haccept'⟩, hx⟩) <;>
    obtain ⟨y, L, rfl, hy, hL⟩ := ih hx <;> clear ih
    · exists (a :: y), L
      simp [stepSet] at *
      simp_rw [↑Set.mem_iUnion₂]
      tauto
    · exists [a], y :: L
      simp [stepSet]
      simp_rw [↑Set.mem_iUnion₂, ↑mem_acceptsFrom_nil]
      tauto

theorem accepts_kstar : M.kstar.accepts = M.accepts∗ := by
  ext x
  rw [accepts_acceptsFrom]
  rw [kstar_start]
  constructor
  · rw [Language.mem_kstar]
    simp only [kstarStart, acceptsFrom_union, acceptsFrom_union, Language.add_def]
    rw [acceptsFrom_kstar_none, Set.mem_union, Set.mem_singleton_iff]
    rintro (rfl | hx)
    · exists []
      tauto
    · obtain ⟨y, L, rfl, hy, hL⟩ := mem_acceptsFrom_kstar_impl_exists_flatten hx
      exists y :: L
      simp [accepts_acceptsFrom] at *
      tauto
  · rw [Language.mem_kstar_iff_exists_nonempty]
    rw [kstarStart_eq_kstarStates, acceptsFrom_union, Language.add_def, Set.mem_union]
    rw [acceptsFrom_kstar_none, Set.mem_singleton_iff]
    rintro ⟨zs, rfl, hzs⟩
    rw [←List.forall_iff_forall_mem] at hzs
    cases zs with
    | nil =>
      tauto
    | cons z zs =>
      right
      simp at hzs
      obtain ⟨⟨hz,hznil⟩,hzs⟩ := hzs
      apply mem_kstar_acceptsFrom hz hzs

end kstar

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

/-- Regular languages are closed under Kleene star. -/
theorem IsRegular_kstar {L : Language α} (h : L.IsRegular) : L∗.IsRegular :=
  have ⟨σ, _, M, hM⟩ := h
  ⟨_, inferInstance, M.toNFA.kstar.toDFA, by simp [hM, NFA.accepts_kstar]⟩

end Language
