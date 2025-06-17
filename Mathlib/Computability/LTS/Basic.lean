/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Mathlib.Tactic.Lemma
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# Labelled Transition System

A Labelled Transition System (LTS) models the observable behaviour of the possible states of a
system. They are particularly popular in the fields of concurrency theory, logic, and programming
languages.

## Main definitions

- `LTS` is a structure for labelled transition systems, consisting of a labelled transition
relation `tr` between states. We follow the style and conventions in [Sangiorgi2011].

- `lts.mtr` extends the transition relation of any LTS to a multi-step transition relation,
formalising the inference system and admissible rules for such relations in [Montesi2023].

- Definitions for all the common classes of LTSs: image-finite, finitely branching, finite-state,
finite, and deterministic.

## Main statements

- A series of results on `lts.mtr` that allow for obtaining and composing multi-step transitions in
different ways.

- `LTS.deterministic_imageFinite`: every deterministic LTS is also image-finite.

- `LTS.finiteState_imageFinite`: every finite-state LTS is also image-finite.

- `LTS.finiteState_finitelyBranching`: every finite-state LTS is also finitely-branching, if the
type of labels is finite.

## References

* [F. Montesi, *Introduction to Choreographies*] [Montesi2023]
* [D. Sangiorgi, *Introduction to Bisimulation and Coinduction*] [Sangiorgi2011]
-/

universe u v

/--
A Labelled Transition System (LTS) consists of a type of states (`State`), a type of transition
labels (`Label`), and a labelled transition relation (`tr`).
-/
structure LTS (State : Type u) (Label : Type v) where
  /-- The transition relation. -/
  tr : State → Label → State → Prop

section MultiStep

/-! ### Multi-step transitions -/

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/--
Definition of a multi-step transition.

(Implementation note: compared to [Montesi2023], we choose stepL instead of stepR as fundamental
rule. This makes working with lists of labels more convenient, because we follow the same
construction.)
-/
inductive LTS.mtr (lts : LTS State Label) : State -> List Label -> State -> Prop where
  | refl {s : State} : lts.mtr s [] s
  | stepL {s1 : State} {μ : Label} {s2 : State} {μs : List Label} {s3 : State} :
    lts.tr s1 μ s2 → lts.mtr s2 μs s3 →
    lts.mtr s1 (μ :: μs) s3

/-- Any transition is also a multi-step transition. -/
theorem LTS.mtr.single {s1 : State} {μ : Label} {s2 : State} :
  lts.tr s1 μ s2 → lts.mtr s1 [μ] s2 := by
  intro h
  apply LTS.mtr.stepL
  · exact h
  · apply LTS.mtr.refl

/-- Any multi-step transition can be extended by adding a transition. -/
theorem LTS.mtr.stepR {s1 : State} {μs : List Label} {s2 : State} {μ : Label} {s3 : State} :
  lts.mtr s1 μs s2 → lts.tr s2 μ s3 → lts.mtr s1 (μs ++ [μ]) s3 := by
  intro h1 h2
  induction h1
  case refl s1' =>
    simp
    apply LTS.mtr.single lts h2
  case stepL s1' μ' s2' μs' s3' h1' h3 ih =>
    apply LTS.mtr.stepL
    · exact h1'
    · apply ih h2

/-- Multi-step transitions can be composed. -/
theorem LTS.mtr.comp {s1 : State} {μs1 : List Label} {s2 : State} {μs2 : List Label} {s3 : State} :
  lts.mtr s1 μs1 s2 → lts.mtr s2 μs2 s3 →
  lts.mtr s1 (μs1 ++ μs2) s3 := by
  intro h1 h2
  induction h1
  case refl =>
    simp
    assumption
  case stepL s1 μ s' μs1' s'' h1' h3 ih  =>
    apply LTS.mtr.stepL
    · exact h1'
    · apply ih h2

/-- Any 1-sized multi-step transition implies a transition with the same states and label. -/
theorem LTS.mtr.single_invert (s1 : State) (μ : Label) (s2 : State) :
  lts.mtr s1 [μ] s2 → lts.tr s1 μ s2 := by
  intro h
  cases h
  case stepL s1' htr hmtr =>
    cases hmtr
    exact htr

/-- A state `s1` can reach a state `s2` if there exists a multi-step transition from
`s1` to `s2`. -/
def LTS.CanReach (s1 s2 : State) : Prop :=
  ∃ μs, lts.mtr s1 μs s2

/-- Any state can reach itself. -/
theorem LTS.CanReach.refl (s : State) : lts.CanReach s s := by
  exists []
  apply LTS.mtr.refl

end MultiStep

section Termination
/-! ### Definitions about termination -/

variable {State} {Label} (lts : LTS State Label) {Terminated : State → Prop}

/-- A state 'may terminate' if it can reach a terminated state. The definition of `Terminated`
is a parameter. -/
def LTS.MayTerminate (s : State) : Prop := ∃ s', Terminated s' ∧ lts.CanReach s s'

/-- A state 'is stuck' if it is not terminated and cannot go forward. The definition of `Terminated`
is a parameter. -/
def LTS.Stuck (s : State) : Prop :=
  ¬Terminated s ∧ ¬∃ μ s', lts.tr s μ s'

end Termination

section Union
/-! ### Definitions for the unions of LTSs

Note: there is a nontrivial balance between ergonomics and generality here. These definitions might
change in the future. -/

variable {State : Type u} {Label : Type v}

/-- The union of two LTSs that have common supertypes for states and labels. -/
def LTS.unionSubtype
{S1 : State → Prop} {L1 : Label → Prop} {S2 : State → Prop} {L2 : Label → Prop}
[DecidablePred S1] [DecidablePred L1] [DecidablePred S2] [DecidablePred L2]
(lts1 : LTS (@Subtype State S1) (@Subtype Label L1))
(lts2 : LTS (@Subtype State S2) (@Subtype Label L2)) :
  LTS State Label := {
  tr := fun s μ s' =>
    if h : S1 s ∧ L1 μ ∧ S1 s' then
      lts1.tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩
    else if h : S2 s ∧ L2 μ ∧ S2 s' then
      lts2.tr ⟨s, h.1⟩ ⟨μ, h.2.1⟩ ⟨s', h.2.2⟩
    else
      False
}

/-- TODO: move this to `Sum`? -/
def Sum.isLeftP {α} {β} (x : α ⊕ β) : Prop := Sum.isLeft x = true

/-- TODO: move this to `Sum`? -/
def Sum.isRightP {α} {β} (x : α ⊕ β) : Prop := Sum.isRight x = true

/-- TODO: move this to `True`? -/
def True.trueFun {α} (_ : α) := True

/-- Lifting of an `LTS State Label` to `LTS (State ⊕ State') Label`. -/
def LTS.inl {State'} (lts : LTS State Label) :
  LTS (@Subtype (State ⊕ State') Sum.isLeftP) (@Subtype Label True.trueFun) := {
  tr := fun s μ s' =>
    let ⟨s, _⟩ := s
    let ⟨s', _⟩ := s'
    match s, μ, s' with
    | Sum.inl s1, μ, Sum.inl s2 => lts.tr s1 μ s2
    | _, _, _ => False
}

/-- Lifting of an `LTS State Label` to `LTS (State' ⊕ State) Label`. -/
def LTS.inr {State'} (lts : LTS State Label) :
  LTS (@Subtype (State' ⊕ State) Sum.isRightP) (@Subtype Label True.trueFun) := {
  tr := fun s μ s' =>
    let ⟨s, _⟩ := s
    let ⟨s', _⟩ := s'
    match s, μ, s' with
    | Sum.inr s1, μ, Sum.inr s2 => lts.tr s1 μ s2
    | _, _, _ => False
}

/-- Union of two LTSs with the same `Label` type. The result combines the original respective state
types `State1` and `State2` into `(State1 ⊕ State2)`. -/
def LTS.unionSum {State1} {State2} (lts1 : LTS State1 Label) (lts2 : LTS State2 Label) :
  LTS (State1 ⊕ State2) Label :=
  @LTS.unionSubtype
    (State1 ⊕ State2) Label
    Sum.isLeftP
    True.trueFun
    Sum.isRightP
    True.trueFun
    (by
      simp [DecidablePred]
      intro s
      cases h : s
      · apply Decidable.isTrue
        trivial
      · simp [Sum.isLeftP]
        apply Decidable.isFalse
        trivial)
    (by
      intro μ
      simp [True.trueFun]
      apply Decidable.isTrue
      trivial)
    (by
      simp [DecidablePred]
      intro s
      cases h : s
      · simp [Sum.isRightP]
        apply Decidable.isFalse
        trivial
      · apply Decidable.isTrue
        trivial)
    (by
      intro μ
      simp [True.trueFun]
      apply Decidable.isTrue
      trivial)
    lts1.inl
    lts2.inr

end Union

section Classes
/-!
### Classes of LTSs
-/

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/-- An lts is deterministic if a state cannot reach different states with the same transition
label. -/
def LTS.Deterministic : Prop :=
  ∀ (s1 : State) (μ : Label) (s2 s3 : State),
    lts.tr s1 μ s2 → lts.tr s1 μ s3 → s2 = s3

/-- The `μ`-image of a state `s` is the set of all `μ`-derivatives of `s`. -/
def LTS.Image (s : State) (μ : Label) : Set State := { s' : State | lts.tr s μ s' }

/-- An lts is image-finite if all images of its states are finite. -/
def LTS.ImageFinite : Prop :=
  ∀ s μ, Finite (lts.Image s μ)

/-- In a deterministic LTS, if a state has a `μ`-derivative, then it can have no other
`μ`-derivative. -/
theorem LTS.deterministic_not_lto (hDet : lts.Deterministic) :
  ∀ s μ s' s'', s' ≠ s'' → lts.tr s μ s' → ¬lts.tr s μ s'' := by
  intro s μ s' s'' hneq hltos'
  by_contra hltos''
  have hDet' := hDet s μ s' s'' hltos' hltos''
  simp only [← hDet'] at hneq
  contradiction

/-- In a deterministic LTS, any image is either a singleton or the empty set. -/
theorem LTS.deterministic_image_char (hDet : lts.Deterministic) :
  ∀ s μ, (∃ s', lts.Image s μ = { s' }) ∨ (lts.Image s μ = ∅) := by
  intro s μ
  by_cases hs' : ∃ s', lts.tr s μ s'
  case pos =>
    obtain ⟨s', hs'⟩ := hs'
    left
    apply Exists.intro s'
    simp [Image]
    simp [setOf, singleton, Set.singleton]
    funext s''
    by_cases heq : s' = s''
    case pos =>
      simp [heq]
      simp [heq] at hs'
      exact hs'
    case neg =>
      have hDet' := LTS.deterministic_not_lto lts hDet s μ s' s'' heq hs'
      simp [hDet']
      exact Ne.symm heq
  case neg =>
    right
    simp [Image, hs']
    simp [setOf, singleton, Set.singleton]
    simp [EmptyCollection.emptyCollection]
    funext s''
    by_contra hf
    simp at hf
    simp [Ne] at hs'
    specialize hs' s''
    contradiction

/-- Every deterministic LTS is also image-finite. -/
theorem LTS.deterministic_imageFinite :
  lts.Deterministic → lts.ImageFinite := by
  simp only [ImageFinite]
  intro h s μ
  have hDet := LTS.deterministic_image_char lts h s μ
  cases hDet
  case inl hDet =>
    obtain ⟨s', hDet'⟩ := hDet
    simp [hDet']
    apply Set.finite_singleton
  case inr hDet =>
    simp [hDet]
    apply Set.finite_empty

/-- A state has an outgoing label `μ` if it has a `μ`-derivative. -/
def LTS.HasOutLabel (s : State) (μ : Label) : Prop :=
  ∃ s', lts.tr s μ s'

/-- The set of outgoing labels of a state. -/
def LTS.OutgoingLabels (s : State) := { μ | lts.HasOutLabel s μ }

/-- An LTS is finitely branching if it is image-finite and all states have finite sets of
outgoing labels. -/
def LTS.FinitelyBranching : Prop :=
  lts.ImageFinite ∧ ∀ s, Finite (lts.OutgoingLabels s)

/-- An LTS is finite-state if it has a finite `State` type. -/
def LTS.FiniteState (_ : LTS State Label): Prop := Finite State

/-- Every finite-state LTS is also image-finite. -/
theorem LTS.finiteState_imageFinite (hFinite : lts.FiniteState) :
  lts.ImageFinite := by
  simp [ImageFinite, Image]
  simp [FiniteState] at hFinite
  intro s μ
  apply @Subtype.finite State hFinite

/-- Every LTS with finite types for states and labels is also finitely branching. -/
theorem LTS.finiteState_finitelyBranching
  (hFiniteLabel : Finite Label) (hFiniteState : lts.FiniteState) :
  lts.FinitelyBranching := by
  simp [FinitelyBranching, OutgoingLabels, HasOutLabel]
  simp [FiniteState] at hFiniteState
  constructor
  case left =>
    apply LTS.finiteState_imageFinite lts hFiniteState
  case right =>
    intro s
    apply @Subtype.finite Label hFiniteLabel

/-- An LTS is acyclic if there are no infinite multi-step transitions. -/
def LTS.Acyclic : Prop :=
  ∃ n, ∀ s1 μs s2, lts.mtr s1 μs s2 → μs.length < n

/-- An LTS is finite if it is finite-state and acyclic. -/
def LTS.Finite : Prop :=
  lts.FiniteState ∧ lts.Acyclic

end Classes
