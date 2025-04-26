/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Rudy Peterson
-/
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Powerset

/-!
# Nondeterministic Finite Automata
This file contains the definition of a Nondeterministic Finite Automaton (NFA), a state machine
which determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular
set by evaluating the string over every possible path.
We show that DFA's are equivalent to NFA's however the construction from NFA to DFA uses an
exponential number of states.
Note that this definition allows for Automaton with infinite states; a `Fintype` instance must be
supplied for true NFA's.
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
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

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

/-- `M.acceptsFrom S` is the language of `x` such that there is an accept state
   in `M.evalFrom S x`. -/
def acceptsFrom (S : Set σ) : Language α := {x | ∃ s ∈ M.accept, s ∈ M.evalFrom S x}

theorem mem_acceptsFrom {S : Set σ} {x : List α} :
    x ∈ M.acceptsFrom S ↔ ∃ s ∈ M.accept, s ∈ M.evalFrom S x := Iff.rfl

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α :=  M.acceptsFrom M.start

theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ ∃ S ∈ M.accept, S ∈ M.evalFrom M.start x := by
  rfl

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

section Closure

/-!
### NFA Closure Properties

Constructions of NFAs corresponding to operations on languages.
-/

section Reversal

section Auxilary

/-- `M.unstep` is the reverse of `M.step`. -/
def unstep (s : σ) (a : α) : Set σ := {s' | s ∈ M.step s' a}

theorem mem_unstep {s t : σ} {a : α} : s ∈ M.unstep t a ↔ t ∈ M.step s a := Iff.rfl

/-- Reversed analog of `M.stepSet S a`:
  `M.unstepSet S a` is the union of `unstep M s a` for all `s ∈ S`.
  It computes the set of states that have a transition in `M`
  to a state in `S`. -/
def unstepSet (S : Set σ) (a : α) : Set σ := ⋃ s ∈ S, M.unstep s a

theorem mem_unstepSet {s : σ} {S : Set σ} {a : α} :
    s ∈ M.unstepSet S a ↔ ∃ t ∈ S, s ∈ M.unstep t a := by
  simp [unstepSet]

theorem mem_unstepSet_step {s : σ} {S : Set σ} {a : α} :
    s ∈ M.unstepSet S a ↔ ∃ t ∈ S, t ∈ M.step s a := by
  simp [mem_unstepSet, mem_unstep]

/-- Reversed analog of `M.evalFrom S x`:
  `M.rewindFrom S x` computes all possible reversed paths through `M` with
  input `x` starting at an element of `S`.
  Even though `M.rewindFrom S x` voyages across `M` in reverse, `x` is processed
  forward, from left to right. -/
def rewindFrom : Set σ → List α → Set σ := List.foldl M.unstepSet

/-- `M.rewind x` computes all possible reversed paths through `M` with input `x`
    starting at an element of `M.accept`. -/
def rewind : List α → Set σ := M.rewindFrom M.accept

/-- `M.rewindsToStart S` is the language of `x`
  such that starting from `S` we rewind to `M.start`. -/
def rewindsToStart (S : Set σ) : Language α :=
  { x | ∃ s ∈ M.start, s ∈ M.rewindFrom S x }

lemma mem_rewindsToStart {S : Set σ} {x : List α} :
    x ∈ M.rewindsToStart S ↔ ∃ s ∈ M.start, s ∈ M.rewindFrom S x := Iff.rfl

end Auxilary

/-- NFAs are closed under reversal:
Given NFA `M`, there is an NFA `M.reverse` such that
`M.reverse.accepts = M.accepts.reverse`. -/
def reverse (M : NFA α σ) : NFA α σ where
  step := M.unstep
  start := M.accept
  accept := M.start

lemma reverse_acceptsFrom_rewindsToStart {M : NFA α σ} :
    M.reverse.acceptsFrom = M.rewindsToStart := by
  ext xs
  rfl

lemma rewindFrom_iff_evalFrom_reverse {xs : List α} {S1 S2 : Set σ} {M : NFA α σ} :
    (∃ s1 ∈ S1, s1 ∈ M.rewindFrom S2 xs) ↔
    (∃ s2 ∈ S2, s2 ∈ M.evalFrom S1 xs.reverse) := by
  dsimp [evalFrom, rewindFrom]
  rw [List.foldl_reverse]
  induction xs generalizing S1 S2
  case nil => tauto
  case cons x xs ih =>
    simp [ih, unstepSet, stepSet, Set.mem_iUnion]
    tauto

lemma mem_rewindsToStart_iff_reverse_mem_acceptsFrom {xs : List α} {M : NFA α σ} :
    xs ∈ M.rewindsToStart M.accept ↔ xs.reverse ∈ M.acceptsFrom M.start := by
  simp [mem_rewindsToStart, mem_acceptsFrom, rewindFrom_iff_evalFrom_reverse]

theorem reverse_accepts {M : NFA α σ} :
    M.reverse.accepts = M.accepts.reverse := by
  ext xs
  simp [NFA.accepts, reverse_acceptsFrom_rewindsToStart]
  simp [NFA.reverse, mem_rewindsToStart_iff_reverse_mem_acceptsFrom]

end Reversal

section Union

variable {σ1 : Type v} {σ2 : Type v}

/-- `stepSum M₁ M₂` computes the transition for `M₁ ∪ M₂`. -/
def stepSum (M1 : NFA α σ1) (M2 : NFA α σ2)
  (s : σ1 ⊕ σ2) (a : α) : Set (σ1 ⊕ σ2) :=
    { s' : σ1 ⊕ σ2 |
      Sum.LiftRel
        (fun s1 s1' ↦ s1' ∈ M1.step s1 a)
        (fun s2 s2' ↦ s2' ∈ M2.step s2 a)
        s s' }

/-- NFAs are closed under union:
  Given NFAs `M₁` and `M₂`, `M₁ ∪ M₂` is a NFA such that
  `L(M₁ ∪ M₂) = L(M₁) ∪ L(M₂)`. -/
def union (M1 : NFA α σ1) (M2 : NFA α σ2) : NFA α (σ1 ⊕ σ2) where
  start : Set (σ1 ⊕ σ2) := { s : σ1 ⊕ σ2 | s.casesOn M1.start M2.start }
  step : σ1 ⊕ σ2 → α → Set (σ1 ⊕ σ2) := stepSum M1 M2
  accept : Set (σ1 ⊕ σ2) := { s : σ1 ⊕ σ2 | s.casesOn M1.accept M2.accept }

lemma union_biUnion_spec
  {x : α} {S1 : Set σ1} {S2 : Set σ2} {M1 : NFA α σ1} {M2 : NFA α σ2} :
    (⋃ s, ⋃ (_ : Sum.rec S1 S2 s), stepSum M1 M2 s x)
    =
    {s' | Sum.rec
      (fun s1' ↦ s1' ∈ ⋃ (s1 ∈ S1), M1.step s1 x)
      (fun s2' ↦ s2' ∈ ⋃ (s2 ∈ S2), M2.step s2 x) s'} := by
  ext s'
  rw [Set.mem_iUnion, Set.mem_setOf]
  dsimp [stepSum]
  cases s' <;> simp <;> tauto

lemma union_start_spec {M1 : NFA α σ1} {M2 : NFA α σ2} :
    (union M1 M2).start = { s : σ1 ⊕ σ2 | s.casesOn M1.start M2.start } := by rfl

lemma union_acceptsFrom
 {S1 : Set σ1} {S2 : Set σ2} {M1 : NFA α σ1} {M2 : NFA α σ2} :
    acceptsFrom (union M1 M2)
      { s : σ1 ⊕ σ2 | s.casesOn S1 S2 }
    = M1.acceptsFrom S1 + M2.acceptsFrom S2 := by
  apply Set.ext
  intros xs
  dsimp [acceptsFrom, evalFrom, union, accept]
  unfold stepSet
  dsimp [NFA.step]
  rw [Language.add_def, Set.mem_union, Set.mem_setOf, Set.mem_setOf]
  induction xs generalizing S1 S2
  case nil =>
    simp
    simp [Set.mem_def]
  case cons x xs ih =>
    simp [List.foldl_cons, List.foldl_cons, List.foldl_cons, ←ih, union_biUnion_spec]
    simp [←Set.mem_def (s:=⋃ (s : σ1) (_ : s ∈ S1), M1.step s x)]
    simp [←Set.mem_def (s:=⋃ (s : σ2) (_ : s ∈ S2), M2.step s x)]

theorem union_accepts {M1 : NFA α σ1} {M2 : NFA α σ2} :
    accepts (union M1 M2) = M1.accepts + M2.accepts := by
    simp only [NFA.accepts, union_start_spec]
    rw [union_acceptsFrom]

end Union

section Intersection

variable {σ1 : Type v} {σ2 : Type v}

/-- `stepProd M₁ M₂` computes the transition for `M₁ ∩ M₂`. -/
def stepProd (M1 : NFA α σ1) (M2 : NFA α σ2)
  (s : σ1 × σ2) (a : α) : Set (σ1 × σ2) :=
    M1.step s.1 a ×ˢ M2.step s.2 a

/-- NFAs are closed under intersection:
  Given NFAs `M₁` and `M₂`, `M₁ ∩ M₂` is a NFA such that
  `L(M₁ ∩ M₂) = L(M₁) ∩ L(M₂)`. -/
def intersect (M1 : NFA α σ1) (M2 : NFA α σ2) : NFA α (σ1 × σ2) where
  start : Set (σ1 × σ2) := M1.start ×ˢ M2.start
  step : σ1 × σ2 → α → Set (σ1 × σ2) := stepProd M1 M2
  accept : Set (σ1 × σ2) := M1.accept ×ˢ M2.accept

lemma intersect_start_spec {M1 : NFA α σ1} {M2 : NFA α σ2} :
    (intersect M1 M2).start = M1.start ×ˢ M2.start := by rfl

lemma intersect_biUnion_spec
  {a : α} {S1 : Set σ1} {S2 : Set σ2} {M1 : NFA α σ1} {M2 : NFA α σ2} :
    (⋃ s : σ1 × σ2,
      ⋃ (_ : s.1 ∈ S1 ∧ s.2 ∈ S2),
        stepProd M1 M2 s a) =
      (⋃ s1 ∈ S1, M1.step s1 a) ×ˢ (⋃ s2 ∈ S2, M2.step s2 a) := by
  ext ⟨s1', s2'⟩
  simp [Set.mem_setOf, Set.mem_iUnion₂, Set.mem_iUnion₂, stepProd]
  tauto

lemma intersect_acceptsFrom
  {S1 : Set σ1} {S2 : Set σ2} {M1 : NFA α σ1} {M2 : NFA α σ2} :
    acceptsFrom (intersect M1 M2) (S1 ×ˢ S2)
    = M1.acceptsFrom S1 ∩ M2.acceptsFrom S2 := by
  ext xs
  dsimp [acceptsFrom, evalFrom, intersect, accept]
  unfold stepSet
  dsimp [NFA.step]
  rw [Set.mem_inter_iff, Set.mem_setOf, Set.mem_setOf, Set.mem_setOf]
  induction xs generalizing S1 S2 <;> simp at *
  case nil => tauto
  case cons x xs ih =>
    rw [intersect_biUnion_spec, ih]

theorem intersect_accepts {M1 : NFA α σ1} {M2 : NFA α σ2} :
    (intersect M1 M2).accepts = M1.accepts ∩ M2.accepts := by
  simp only [NFA.accepts]
  rw [intersect_start_spec, intersect_acceptsFrom]

end Intersection

end Closure

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
