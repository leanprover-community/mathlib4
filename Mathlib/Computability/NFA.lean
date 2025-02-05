/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
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
  step : σ → α → Set σ
  start : Set σ
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

/-- `M.evalFrom S x` computes all possible paths though `M` with input `x` starting at an element
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

/--
`M.acceptsFrom S` is the language of `x` such that `M.evalFrom S x` is an accept state.
-/
def acceptsFrom (S : Set σ) : Language α := {x | ∃ s ∈ M.accept, s ∈ M.evalFrom S x}

theorem mem_acceptsFrom {S : Set σ} {x : List α} :
  x ∈ M.acceptsFrom S ↔ ∃ s ∈ M.accept, s ∈ M.evalFrom S x := by rfl

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α := {x | ∃ S ∈ M.accept, S ∈ M.eval x}

theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ ∃ S ∈ M.accept, S ∈ M.evalFrom M.start x := by
  rfl

lemma accepts_acceptsFrom :
  M.accepts = M.acceptsFrom M.start := by
  dsimp [accepts, acceptsFrom, eval]

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

/-! ### NFA Closure Properties -/

section Reversal

section Auxilary

/-- `M unstep` is the reverse of `M.step`
-/
def unstep (s : σ) (a : α) : Set σ :=
  fun s' ↦ M.step s' a s

theorem mem_unstep (s t : σ) (a : α) :
  s ∈ M.unstep t a ↔ t ∈ M.step s a := by
  rfl

/-- `M.unstepSet S a` is the union of `unstep M s a` for all `s ∈ S`. -/
def unstepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.unstep s a

theorem mem_unstepSet (s : σ) (S : Set σ) (a : α) :
  s ∈ M.unstepSet S a ↔ ∃ t ∈ S, s ∈ M.unstep t a := by
  simp [unstepSet]

theorem mem_unstepSet_step (s : σ) (S : Set σ) (a : α) :
  s ∈ M.unstepSet S a ↔ ∃ t ∈ S, t ∈ M.step s a := by
  rw [mem_unstepSet]
  apply exists_congr
  intro t
  rw [mem_unstep]

/-- `M.rewindFrom S x` computes all possible paths though `M` with input `x` ending at an element
  of `S`. -/
def rewindFrom (final : Set σ) : List α → Set σ :=
  List.foldl M.unstepSet final


/-- `M.rewind x` computes all possible paths though `M` with input `x` ending at an element of
  `M.accept`. -/
def rewind : List α → Set σ :=
  M.rewindFrom M.accept

/-- `startsTo M S` is the language of `x`
such that starting from `S` we arrive at `M.start`.
-/
def startsTo (S : Set σ) : Language α :=
  { x | ∃ s ∈ M.start, s ∈ M.rewindFrom S x }

lemma mem_startsTo {S : Set σ} {x : List α} :
  x ∈ M.startsTo S ↔ ∃ s ∈ M.start, s ∈ M.rewindFrom S x := by
    rfl

end Auxilary

/-- NFAs are closed under reversal:
Given NFA `M`, there is an NFA `reverse(M)` such that `L(reverse(M)) = reverse(L(M))`.
-/
def reverse (M : NFA α σ) : NFA α σ :=
  NFA.mk M.unstep M.accept M.start

lemma reverse.SpecFrom (S : Set σ) (M : NFA α σ) :
  M.reverse.acceptsFrom S =
  { xs : List α | xs ∈ M.startsTo S } := by
  ext xs
  dsimp [NFA.reverse, acceptsFrom, startsTo, NFA.evalFrom, rewindFrom]
  unfold NFA.stepSet
  unfold NFA.unstepSet
  simp
  rw [Set.mem_setOf, Set.mem_setOf, Set.mem_setOf]

lemma reverse.rewindFromSpec (xs : List α) (S1 S2 : Set σ) (M : NFA α σ) :
  (∃ s1 ∈ S1, s1 ∈ M.rewindFrom S2 xs) ↔
  (∃ s2 ∈ S2, s2 ∈ M.evalFrom S1 xs.reverse) := by
  dsimp [evalFrom, rewindFrom]
  rw [List.foldl_reverse]
  revert S1 S2
  induction xs <;> intros S1 S2 <;> simp
  case nil =>
    constructor <;> rintro ⟨s, h1, h2⟩ <;> exists s
  case cons x xs ih =>
    rw [ih]
    clear ih
    unfold unstepSet
    unfold stepSet
    constructor
    · rintro ⟨s3, h, h1⟩
      simp [Set.mem_iUnion] at h
      rcases h with ⟨s2,h2,h3⟩
      exists s2
      constructor <;> try assumption
      simp [Set.mem_iUnion]
      exists s3
    · rintro ⟨s2, h2, h⟩
      simp [Set.mem_iUnion] at h
      rcases h with ⟨s3, h1, h3⟩
      exists s3
      simp [Set.mem_iUnion]
      constructor <;> try assumption
      exists s2

lemma reverse.startsToSpec (xs : List α) (M : NFA α σ) :
  xs ∈ M.startsTo M.reverse.start ↔ xs.reverse ∈ M.acceptsFrom M.start := by
  rw [mem_startsTo, mem_acceptsFrom]
  apply reverse.rewindFromSpec

theorem reverse.Spec (M : NFA α σ) :
  M.reverse.accepts
  = { xs : List α | xs.reverse ∈ M.accepts } := by
  ext xs
  rw [accepts_acceptsFrom, accepts_acceptsFrom, reverse.SpecFrom]
  rw [Set.mem_setOf, Set.mem_setOf]
  apply reverse.startsToSpec

end Reversal

section Union

variable {σ1 : Type v} {σ2 : Type v}

private instance Language.instUnion : Union (Language α) := by
  apply Set.instUnion

/--`stepSum M₁ M₂` computes the transition for `M₁ ∪ M₂`.
-/
def stepSum (M1 : NFA α σ1) (M2 : NFA α σ2)
  (s : σ1 ⊕ σ2) (a : α) : Set (σ1 ⊕ σ2) :=
    { s' : σ1 ⊕ σ2 |
      Sum.LiftRel
        (fun s1 s1' ↦ M1.step s1 a s1')
        (fun s2 s2' ↦ M2.step s2 a s2')
        s s' }

/-- NFAs are closed under union:
Given NFAs `M₁` and `M₂`, `M₁ ∪ M₂` is a NFA such that `L(M₁ ∪ M₂) = L(M₁) ∪ L(M₂)`.
-/
def union (M1 : NFA α σ1) (M2 : NFA α σ2) : NFA α (σ1 ⊕ σ2) :=
  { start : Set (σ1 ⊕ σ2) :=
      { s : σ1 ⊕ σ2 | s.casesOn M1.start M2.start }
    step : σ1 ⊕ σ2 → α → Set (σ1 ⊕ σ2) :=
      stepSum M1 M2
    accept : Set (σ1 ⊕ σ2) :=
      { s : σ1 ⊕ σ2 | s.casesOn M1.accept M2.accept } }

lemma union.biUnionSpec
  (x : α) (S1 : Set σ1) (S2 : Set σ2) (M1 : NFA α σ1) (M2 : NFA α σ2) :
  (⋃ s,
    ⋃ (_ : Sum.rec (fun s1 ↦ S1 s1) (fun s2 ↦ S2 s2) s),
    stepSum M1 M2 s x)
  =
  {s' | Sum.rec
    (fun s1' ↦ (⋃ (s1 : σ1) (_ : s1 ∈ S1), M1.step s1 x) s1')
    (fun s2' ↦ (⋃ (s2 : σ2) (_ : s2 ∈ S2), M2.step s2 x) s2') s'}
  := by
  ext s'
  rw [Set.mem_iUnion, Set.mem_setOf]
  dsimp [stepSum]
  cases s'
  case inl s1' =>
    simp
    rw [←Set.mem_def (a := s1') (s := (⋃ (s1 : σ1) (_ : s1 ∈ S1), M1.step s1 x))]
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨s1, hs1, h1⟩
      exists s1
      rw [Set.mem_iUnion]
      exists hs1
    · rintro ⟨s1, hs1⟩
      rw [Set.mem_iUnion] at hs1
      rcases hs1 with ⟨hs1,h1⟩
      exists s1
  case inr s2' =>
    simp
    rw [←Set.mem_def (a:=s2') (s:=(⋃ (s2 : σ2) (_ : s2 ∈ S2), M2.step s2 x)), Set.mem_iUnion]
    constructor
    · rintro ⟨s2, hs2, h2⟩
      exists s2
      rw [Set.mem_iUnion]
      exists hs2
    · rintro ⟨s2, hs2⟩
      rw [Set.mem_iUnion] at hs2
      rcases hs2 with ⟨hs2,h2⟩
      exists s2

lemma union.startSpec (M1 : NFA α σ1) (M2 : NFA α σ2) :
  (union M1 M2).start = { s : σ1 ⊕ σ2 | s.casesOn M1.start M2.start } := by rfl

lemma union.SpecFrom
  (S1 : Set σ1) (S2 : Set σ2) (M1 : NFA α σ1) (M2 : NFA α σ2) :
    acceptsFrom (union M1 M2)
      { s : σ1 ⊕ σ2 | s.casesOn S1 S2 }
    = M1.acceptsFrom S1 ∪ M2.acceptsFrom S2 := by
    apply Set.ext
    intros xs
    dsimp [acceptsFrom, evalFrom, union, accept]
    unfold stepSet
    dsimp [NFA.step]
    rw [Set.mem_union, Set.mem_setOf, Set.mem_setOf]
    revert S1 S2
    induction xs
    case nil =>
      intro S1 S2
      simp
      simp [Set.mem_def]
    case cons x xs ih =>
      intro S1 S2
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, ←ih]
      clear ih
      simp [union.biUnionSpec]

theorem union.Spec
  (M1 : NFA α σ1) (M2 : NFA α σ2) :
  accepts (union M1 M2) = M1.accepts ∪ M2.accepts := by
  rw [accepts_acceptsFrom, accepts_acceptsFrom, accepts_acceptsFrom,
    union.startSpec, union.SpecFrom]

end Union

section Intersection

variable {σ1 : Type v} {σ2 : Type v}

private instance Language.instIntersect : Inter (Language α) := by
  apply Set.instInter

/--`stepProd M₁ M₂` computes the transition for `M₁ ∩ M₂`.
-/
def stepProd (M1 : NFA α σ1) (M2 : NFA α σ2)
  (s : σ1 × σ2) (a : α) : Set (σ1 × σ2) :=
    { s' : σ1 × σ2 | s'.1 ∈ M1.step s.1 a ∧ s'.2 ∈ M2.step s.2 a }

/-- NFAs are closed under intersection:
Given NFAs `M₁` and `M₂`, `M₁ ∩ M₂` is a NFA such that `L(M₁ ∩ M₂) = L(M₁) ∩ L(M₂)`.
-/
def intersect (M1 : NFA α σ1) (M2 : NFA α σ2) : NFA α (σ1 × σ2) :=
  { start : Set (σ1 × σ2) :=
      { s : σ1 × σ2 | s.1 ∈ M1.start ∧ s.2 ∈ M2.start }
    step : σ1 × σ2 → α → Set (σ1 × σ2) :=
      stepProd M1 M2
    accept : Set (σ1 × σ2) :=
      { s : σ1 × σ2 | s.1 ∈ M1.accept ∧ s.2 ∈ M2.accept } }

lemma intersect.startSpec (M1 : NFA α σ1) (M2 : NFA α σ2) :
  (intersect M1 M2).start =
  { s : σ1 × σ2 | s.1 ∈ M1.start ∧ s.2 ∈ M2.start } := by rfl

lemma intersect.biUnionSpec
  (a : α)
  (S1 : Set σ1) (S2 : Set σ2)
  (M1 : NFA α σ1) (M2 : NFA α σ2) :
  (⋃ s : σ1 × σ2,
    ⋃ (_ : s.1 ∈ S1 ∧ s.2 ∈ S2),
      stepProd M1 M2 s a) =
  { s' : σ1 × σ2 |
    s'.1 ∈ (⋃ s1 ∈ S1, M1.step s1 a) ∧
    s'.2 ∈ (⋃ s2 ∈ S2, M2.step s2 a) } := by
  ext ⟨s1', s2'⟩
  rw [Set.mem_setOf, Set.mem_iUnion₂, Set.mem_iUnion₂,]
  simp [stepProd]
  constructor
  · rintro ⟨s1, h1, s2, ⟨hS1, hS2⟩, h2⟩
    constructor
    · exists s1
    · exists s2
  · rintro ⟨⟨s1, hS1, h1⟩, ⟨s2, hS2, h2⟩⟩
    exists s1
    constructor
    · assumption
    · exists s2

lemma intersect.SpecFrom
  (S1 : Set σ1) (S2 : Set σ2) (M1 : NFA α σ1) (M2 : NFA α σ2) :
    acceptsFrom (intersect M1 M2)
      { s : σ1 × σ2 | s.1 ∈ S1 ∧ s.2 ∈ S2 }
    = M1.acceptsFrom S1 ∩ M2.acceptsFrom S2 := by
    ext xs
    dsimp [acceptsFrom, evalFrom, intersect, accept]
    unfold stepSet
    dsimp [NFA.step]
    rw [Set.mem_inter_iff, Set.mem_setOf, Set.mem_setOf, Set.mem_setOf]
    revert S1 S2
    induction xs <;> intros S1 S2 <;> simp at *
    case nil =>
      constructor
      · rintro ⟨x1, x2, ⟨h1, h2⟩, hS1, hS2⟩
        constructor
        · exists x1
        · exists x2
      · rintro ⟨⟨x1, h1, hS1⟩, ⟨x2, h2, hS2⟩⟩
        exists x1, x2
    case cons x xs ih =>
      rw [intersect.biUnionSpec, ih]

theorem intersect.Spec
  (M1 : NFA α σ1) (M2 : NFA α σ2) :
  (intersect M1 M2).accepts = M1.accepts ∩ M2.accepts := by
  rw [NFA.accepts_acceptsFrom, NFA.accepts_acceptsFrom, NFA.accepts_acceptsFrom]
  rw [intersect.startSpec, intersect.SpecFrom]

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
