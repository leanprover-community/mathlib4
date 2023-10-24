import Mathlib.Computability.Language
import Mathlib.Data.Rel

open Computability
universe u v

def word (A : Type u) := ℕ → A

/-- A transducer consists of a type `state` together with a transition relation
between states and letters from the input alphabet `A`, a labeling function `out`
from transitions to the output alphabet `B`, a starting state `start` and a set of
sets of accepting states. This is a *generalized Büchi* transducer in the sense of [Gastin].-/
structure Transducer (A B : Type u) where
  state : Type v
  transition : Set (state × A × state)
  out : transition → B
  start : state
  final : Set (Set state)

variable {A B C : Type u}
/-- A run of a transducer `T` on a word `w ∈ word A`  consists of a function `stateAt` which
records the state of the transducer at time `t ∈ ℕ`, together with the initial condition
`initialCond` that the run starts in the start state, the condition `transitionCond` that the
run follows the transition relation, and the condition `finalCond` that the run visits each
of the final sets infinitely often. -/
structure Run (T : Transducer A B) (wᵢ : word A) where
  stateAt : word T.state
  initialCond : stateAt 0 = T.start
  transitionCond : ∀t, (stateAt t, wᵢ t, stateAt (t+1)) ∈ T.transition
  finalCond : ∀ F ∈ T.final, ∀ t, ∃t' ≥ t, stateAt t ∈ F

/-- The output of a run `r` is the sequence of outputs of transitions of the run. -/
def output {T : Transducer A B} {wᵢ : word A} (r : Run T wᵢ) :=
  λ t ↦ T.out (⟨(r.stateAt t, wᵢ t, r.stateAt (t+1)), r.transitionCond t⟩)

/-- The semantics of a transducer `T` is the relation which relates a word `u` to a word `v`
iff `v` is the output of a run of `T` on `u`.-/
def semantics (T : Transducer A B) : Rel (word A) (word B) :=
  λ u v ↦ ∃ r : Run T u, output r = v

section Composition
def forget (T₁ : Transducer A B) (T₂ : Transducer B C) : T₁.transition × (T₂.state × T₂.state) → (T₁.state × A × T₁.state) × (T₂.state × T₂.state) := λ ⟨⟨x,_⟩, y⟩ ↦ ⟨x,y⟩

def assemble {Q Q'} : (Q × A × Q) × (Q' × Q') → (Q × Q') × A × (Q × Q') :=
  λ ((p,a,q),(p',q')) ↦ ((p,p'),a,(q,q'))

def good (T₁ : Transducer A B) (T₂ : Transducer B C) := λ (t, (p',q')) ↦ (p', T₁.out t, q') ∈ T₂.transition

def transition_compose (T₁ : Transducer A B) (T₂ : Transducer B C) :=
  assemble '' ((forget T₁ T₂) '' (good T₁ T₂))

-- theorem comp_trans (T₁ : Transducer A B) (T₂ : Transducer B C) (p q : T₁.state) (p' q' : T₂.state)
-- (a : A) (b : B) (h : (p,a,q) ∈ T₁.transition) (hb : b = T₁.out ⟨(p,a,q),h⟩)
-- (h2 : (p',b,q') ∈ T₂.transition) : ((p,p'),a,(q,q')) ∈ transition_compose T₁ T₂ := by
--   simp_rw [transition_compose, Set.mem_image]
--   use ((p,a,q),(p',q'))
--   constructor
--   simp [good]
--   aesop
--   rw [assemble]

theorem comp_trans1 (T₁ : Transducer A B) (T₂ : Transducer B C)
(p q : T₁.state) (p' q' : T₂.state) (a : A)
: ((p,p'),a,(q,q')) ∈ transition_compose T₁ T₂ →
   (p,a,q) ∈ T₁.transition := by
  intro h
  simp_rw [transition_compose, Set.mem_image] at h
  cases' h with x hx
  simp_rw [assemble, forget] at hx
  aesop

theorem comp_trans2 (T₁ : Transducer A B) (T₂ : Transducer B C)
(p q : T₁.state) (p' q' : T₂.state)
(a : A) (h : (p,a,q) ∈ T₁.transition)
: ((p,p'),a,(q,q')) ∈ transition_compose T₁ T₂ →
   (p',T₁.out ⟨(p,a,q),h⟩,q') ∈ T₂.transition
:= by
  intro h
  simp_rw [transition_compose, Set.mem_image] at h
  cases' h with x hx
  simp_rw [assemble, forget] at hx
  aesop

def compose (T₁ : Transducer A B) (T₂ : Transducer B C) : Transducer A C :=
  { state := T₁.state × T₂.state
    transition := transition_compose T₁ T₂
    out := by
      intro ⟨a, ha⟩
      apply T₂.out
      let ((p,p'),a,(q,q')) := a
      have h1 :  (p,a,q) ∈ T₁.transition := by
        apply comp_trans1 T₁ T₂ p q p' q'
        exact ha
      have h2 := comp_trans2 T₁ T₂ p q p' q' a h1 ha
      use (p',T₁.out ⟨(p,a,q),h1⟩,q')
    start := (T₁.start, T₂.start)
    final := by sorry}

theorem compose_correct : ∀ (T₁ : Transducer A B) (T₂ : Transducer B C),
semantics (compose T₁ T₂) = Rel.comp (semantics T₁) (semantics T₂) :=
by sorry
