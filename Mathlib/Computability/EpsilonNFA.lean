/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Yaël Dillies, Anthony DeRossi
-/
module

public import Mathlib.Computability.NFA
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.List.ReduceOption

/-!
# Epsilon Nondeterministic Finite Automata

This file contains the definition of an epsilon Nondeterministic Finite Automaton (`εNFA`), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitions,
which can be followed without reading a character.
Since this definition allows for automata with infinite states, a `Fintype` instance must be
supplied for true `εNFA`'s.
-/

@[expose] public section


open Set

open Computability

-- "ε_NFA"

universe u v

/-- An `εNFA` is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `Set` of states and can make ε-transitions by
  inputting `none`.
  Since this definition allows for Automata with infinite states, a `Fintype` instance must be
  supplied for true `εNFA`'s. -/
structure εNFA (α : Type u) (σ : Type v) where
  /-- Transition function. The automaton is rendered non-deterministic by this transition function
  returning `Set σ` (rather than `σ`), and ε-transitions are made possible by taking `Option α`
  (rather than `α`). -/
  step : σ → Option α → Set σ
  /-- Starting states. -/
  start : Set σ
  /-- Set of acceptance states. -/
  accept : Set σ

variable {α : Type u} {σ : Type v} (M : εNFA α σ) {S : Set σ} {s t u : σ} {a : α}

namespace εNFA

/-- The `εClosure` of a set is the set of states which can be reached by taking a finite string of
ε-transitions from an element of the set. -/
inductive εClosure (S : Set σ) : Set σ
  | base : ∀ s ∈ S, εClosure S s
  | step : ∀ (s), ∀ t ∈ M.step s none, εClosure S s → εClosure S t

@[simp]
theorem subset_εClosure (S : Set σ) : S ⊆ M.εClosure S :=
  εClosure.base

@[simp]
theorem εClosure_empty : M.εClosure ∅ = ∅ :=
  eq_empty_of_forall_notMem fun s hs ↦ by induction hs <;> assumption

@[simp]
theorem εClosure_univ : M.εClosure univ = univ :=
  eq_univ_of_univ_subset <| subset_εClosure _ _

theorem mem_εClosure_iff_exists : s ∈ M.εClosure S ↔ ∃ t ∈ S, s ∈ M.εClosure {t} where
  mp h := by
    induction h with
    | base => tauto
    | step _ _ _ _ ih =>
      obtain ⟨s, _, _⟩ := ih
      use s
      solve_by_elim [εClosure.step]
  mpr := by
    intro ⟨t, _, h⟩
    induction h <;> subst_vars <;> solve_by_elim [εClosure.step]

/-- `M.stepSet S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`. -/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.εClosure (M.step s a)

variable {M}

@[simp]
theorem mem_stepSet_iff : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.εClosure (M.step t a) := by
  simp_rw [stepSet, mem_iUnion₂, exists_prop]

@[simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by
  simp_rw [stepSet, mem_empty_iff_false, iUnion_false, iUnion_empty]

variable (M)

/-- `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element
of `S`. -/
def evalFrom (start : Set σ) : List α → Set σ :=
  List.foldl M.stepSet (M.εClosure start)

@[simp]
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = M.εClosure S :=
  rfl

@[simp]
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet (M.εClosure S) a :=
  rfl

@[simp]
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  rw [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp]
theorem evalFrom_empty (x : List α) : M.evalFrom ∅ x = ∅ := by
  induction x using List.reverseRecOn with
  | nil => rw [evalFrom_nil, εClosure_empty]
  | append_singleton x a ih => rw [evalFrom_append_singleton, ih, stepSet_empty]

theorem mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} :
    s ∈ M.evalFrom S x ↔ ∃ t ∈ S, s ∈ M.evalFrom {t} x := by
  induction x using List.reverseRecOn generalizing s with
  | nil => apply mem_εClosure_iff_exists
  | append_singleton _ _ ih =>
    simp_rw [evalFrom_append_singleton, mem_stepSet_iff, ih]
    tauto

/-- `M.eval x` computes all possible paths through `M` with input `x` starting at an element of
`M.start`. -/
def eval :=
  M.evalFrom M.start

@[simp]
theorem eval_nil : M.eval [] = M.εClosure M.start :=
  rfl

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet (M.εClosure M.start) a :=
  rfl

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α :=
  { x | ∃ S ∈ M.accept, S ∈ M.eval x }

/-- `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list
of transitions in order. -/
@[mk_iff]
inductive IsPath : σ → σ → List (Option α) → Prop
  | nil (s : σ) : IsPath s s []
  | cons (t s u : σ) (a : Option α) (x : List (Option α)) :
      t ∈ M.step s a → IsPath t u x → IsPath s u (a :: x)

@[simp]
theorem isPath_nil : M.IsPath s t [] ↔ s = t := by
  rw [isPath_iff]
  simp [eq_comm]

alias ⟨IsPath.eq_of_nil, _⟩ := isPath_nil

@[simp]
theorem isPath_singleton {a : Option α} : M.IsPath s t [a] ↔ t ∈ M.step s a where
  mp := by
    rintro (_ | ⟨_, _, _, _, _, _, ⟨⟩⟩)
    assumption
  mpr := by tauto

alias ⟨_, IsPath.singleton⟩ := isPath_singleton

theorem isPath_append {x y : List (Option α)} :
    M.IsPath s u (x ++ y) ↔ ∃ t, M.IsPath s t x ∧ M.IsPath t u y where
  mp := by
    induction x generalizing s with
    | nil =>
      rw [List.nil_append]
      tauto
    | cons x a ih =>
      rintro (_ | ⟨t, _, _, _, _, _, h⟩)
      apply ih at h
      tauto
  mpr := by
    intro ⟨t, hx, _⟩
    induction x generalizing s <;> cases hx <;> tauto

theorem mem_εClosure_iff_exists_path {s₁ s₂ : σ} :
    s₂ ∈ M.εClosure {s₁} ↔ ∃ n, M.IsPath s₁ s₂ (.replicate n none) where
  mp h := by
    induction h with
    | base t =>
      use 0
      subst t
      apply IsPath.nil
    | step _ _ _ _ ih =>
      obtain ⟨n, _⟩ := ih
      use n + 1
      rw [List.replicate_add, isPath_append]
      tauto
  mpr := by
    intro ⟨n, h⟩
    induction n generalizing s₂
    · rw [List.replicate_zero] at h
      apply IsPath.eq_of_nil at h
      solve_by_elim
    · simp_rw [List.replicate_add, isPath_append, List.replicate_one, isPath_singleton] at h
      obtain ⟨t, _, _⟩ := h
      solve_by_elim [εClosure.step]

theorem mem_evalFrom_iff_exists_path {s₁ s₂ : σ} {x : List α} :
    s₂ ∈ M.evalFrom {s₁} x ↔ ∃ x', x'.reduceOption = x ∧ M.IsPath s₁ s₂ x' := by
  induction x using List.reverseRecOn generalizing s₂ with
  | nil =>
    rw [evalFrom_nil, mem_εClosure_iff_exists_path]
    constructor
    · intro ⟨n, _⟩
      use List.replicate n none
      rw [List.reduceOption_replicate_none]
      trivial
    · simp_rw [List.reduceOption_eq_nil_iff]
      intro ⟨_, ⟨n, rfl⟩, h⟩
      exact ⟨n, h⟩
  | append_singleton x a ih =>
    rw [evalFrom_append_singleton, mem_stepSet_iff]
    constructor
    · intro ⟨t, ht, h⟩
      obtain ⟨x', _, _⟩ := ih.mp ht
      rw [mem_εClosure_iff_exists] at h
      simp_rw [mem_εClosure_iff_exists_path] at h
      obtain ⟨u, _, n, _⟩ := h
      use x' ++ some a :: List.replicate n none
      rw [List.reduceOption_append, List.reduceOption_cons_of_some,
        List.reduceOption_replicate_none, isPath_append]
      tauto
    · simp_rw [← List.concat_eq_append, List.reduceOption_eq_concat_iff,
        List.reduceOption_eq_nil_iff]
      intro ⟨_, ⟨x', _, rfl, _, n, rfl⟩, h⟩
      rw [isPath_append] at h
      obtain ⟨t, _, _ | u⟩ := h
      use t
      rw [mem_εClosure_iff_exists, ih]
      simp_rw [mem_εClosure_iff_exists_path]
      tauto

theorem mem_accepts_iff_exists_path {x : List α} :
    x ∈ M.accepts ↔
      ∃ s₁ s₂ x', s₁ ∈ M.start ∧ s₂ ∈ M.accept ∧ x'.reduceOption = x ∧ M.IsPath s₁ s₂ x' where
  mp := by
    intro ⟨s₂, _, h⟩
    rw [eval, mem_evalFrom_iff_exists] at h
    obtain ⟨s₁, _, h⟩ := h
    rw [mem_evalFrom_iff_exists_path] at h
    tauto
  mpr := by
    intro ⟨s₁, s₂, x', hs₁, hs₂, h⟩
    have := M.mem_evalFrom_iff_exists.mpr ⟨_, hs₁, M.mem_evalFrom_iff_exists_path.mpr ⟨_, h⟩⟩
    exact ⟨s₂, hs₂, this⟩

/-! ### Conversions between `εNFA` and `NFA` -/


/-- `M.toNFA` is an `NFA` constructed from an `εNFA` `M`. -/
def toNFA : NFA α σ where
  step S a := M.εClosure (M.step S a)
  start := M.εClosure M.start
  accept := M.accept

@[simp]
theorem toNFA_evalFrom_match (start : Set σ) :
    M.toNFA.evalFrom (M.εClosure start) = M.evalFrom start :=
  rfl

@[simp]
theorem toNFA_correct : M.toNFA.accepts = M.accepts :=
  rfl

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c, x = a ++ b ++ c ∧
      a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts :=
  M.toNFA.pumping_lemma hx hlen

end εNFA

namespace NFA

/-- `M.toεNFA` is an `εNFA` constructed from an `NFA` `M` by using the same start and accept
  states and transition functions. -/
def toεNFA (M : NFA α σ) : εNFA α σ where
  step s a := a.casesOn' ∅ fun a ↦ M.step s a
  start := M.start
  accept := M.accept

@[simp]
theorem toεNFA_εClosure (M : NFA α σ) (S : Set σ) : M.toεNFA.εClosure S = S := by
  ext a
  refine ⟨?_, εNFA.εClosure.base _⟩
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩)
  · exact h
  · cases h

@[simp]
theorem toεNFA_evalFrom_match (M : NFA α σ) (start : Set σ) :
    M.toεNFA.evalFrom start = M.evalFrom start := by
  rw [evalFrom, εNFA.evalFrom, toεNFA_εClosure]
  suffices εNFA.stepSet (toεNFA M) = stepSet M by rw [this]
  ext S s
  simp only [stepSet, εNFA.stepSet, exists_prop, Set.mem_iUnion]
  apply exists_congr
  simp only [and_congr_right_iff]
  intro _ _
  rw [M.toεNFA_εClosure]
  rfl

@[simp]
theorem toεNFA_correct (M : NFA α σ) : M.toεNFA.accepts = M.accepts := by
  rw [εNFA.accepts, εNFA.eval, toεNFA_evalFrom_match]
  rfl

end NFA

/-! ### Regex-like operations -/


namespace εNFA

instance : Zero (εNFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, ∅, ∅⟩⟩

instance : One (εNFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, univ, univ⟩⟩

instance : Inhabited (εNFA α σ) :=
  ⟨0⟩

@[simp]
theorem step_zero (s a) : (0 : εNFA α σ).step s a = ∅ :=
  rfl

@[simp]
theorem step_one (s a) : (1 : εNFA α σ).step s a = ∅ :=
  rfl

@[simp]
theorem start_zero : (0 : εNFA α σ).start = ∅ :=
  rfl

@[simp]
theorem start_one : (1 : εNFA α σ).start = univ :=
  rfl

@[simp]
theorem accept_zero : (0 : εNFA α σ).accept = ∅ :=
  rfl

@[simp]
theorem accept_one : (1 : εNFA α σ).accept = univ :=
  rfl

end εNFA

namespace RegularExpression

theorem matches'_foldl_acc {α : Type*}
    (L : List α) (f : α → RegularExpression α) (acc : RegularExpression α) :
    (L.foldl (fun acc a => acc + f a) acc).matches' =
    acc.matches' + ⨆ x ∈ L, (f x).matches' := by
  induction L generalizing acc with
  | nil => simp
  | cons b L' ih =>
    simp only [List.foldl_cons, ih, matches', add_eq_sup, List.mem_cons, iSup_or]
    rw [iSup_sup_eq, iSup_iSup_eq_left, ← sup_assoc]

theorem matches'_foldl_sum {α : Type*} (L : List α) (f : α → RegularExpression α) :
    (L.foldl (fun acc a => acc + f a) 0).matches' =
    ⋃ x ∈ L, (f x).matches' := by
  simp only [matches'_foldl_acc, matches', add_eq_sup, zero_le, sup_of_le_right]
  rfl

theorem mem_matches_mul_star_mul {R_to R_loop R_from : RegularExpression α} {w : List α} :
    w ∈ (R_to * R_loop.star * R_from).matches' ↔
    ∃ w₁ w₂ w₃, w = w₁ ++ w₂ ++ w₃ ∧
                w₁ ∈ R_to.matches' ∧
                w₂ ∈ R_loop.star.matches' ∧
                w₃ ∈ R_from.matches' := by
  simp only [matches'_mul, Language.mem_mul]
  constructor
  · rintro ⟨u, ⟨w₁, hw₁, w₂, hw₂, rfl⟩, w₃, hw₃, rfl⟩
    use w₁, w₂, w₃
  · rintro ⟨w₁, w₂, w₃, rfl, hw₁, hw₂, hw₃⟩
    exact ⟨w₁ ++ w₂, ⟨w₁, hw₁, w₂, hw₂, rfl⟩, w₃, hw₃, rfl⟩

theorem mem_matches_star_concat {R : RegularExpression α} {w₁ w₂ : List α}
    (h₁ : w₁ ∈ R.star.matches') (h₂ : w₂ ∈ R.star.matches') :
    w₁ ++ w₂ ∈ R.star.matches' := by
  rw [matches'_star, Language.mem_kstar] at *
  rcases h₁ with ⟨L₁, rfl, hL₁⟩
  rcases h₂ with ⟨L₂, rfl, hL₂⟩
  exact ⟨L₁ ++ L₂, by simp, List.forall_mem_append.mpr ⟨hL₁, hL₂⟩⟩

theorem mem_matches_star_singleton {R : RegularExpression α} {w : List α}
    (h : w ∈ R.matches') : w ∈ R.star.matches' := by
  rw [matches'_star, Language.mem_kstar]
  exact ⟨[w], by simpa⟩

end RegularExpression

namespace εNFA

section toSingleεNFA

variable {σ : Type*}
variable {α : Type*}
variable {M : εNFA α σ}
variable [DecidablePred (· ∈ M.accept)]

/-- The extended state space with a new start state and accept state. -/
inductive ExtendedState (σ : Type*)
  | start : ExtendedState σ
  | accept : ExtendedState σ
  | state (s : σ) : ExtendedState σ
  deriving DecidableEq, Fintype

variable (M) in
/-- Transform any `εNFA` into an `εNFA` with a single start state and accept state. -/
@[simps]
def toSingleεNFA : εNFA α (ExtendedState σ) where
  step q oa := match q, oa with
    | .start, some _   => ∅
    | .start, none     => (M.start).image .state
    | .accept, _       => ∅
    | .state s, some a => (M.step s (some a)).image .state
    | .state s, none   =>
      (M.step s none).image .state ∪
      if s ∈ M.accept then { ExtendedState.accept } else ∅
  start := { .start }
  accept := { .accept }

theorem IsPath.toSingleεNFA_lift_extendedState {s t : σ} {x : List (Option α)}
    (h : M.IsPath s t x) :
    M.toSingleεNFA.IsPath (.state s) (.state t) x := by
  induction h with
  | nil _ => simp
  | cons t' s' u oa x' h_step h_path ih =>
    apply cons (ExtendedState.state t') (.state s') (.state u)
    · cases oa <;> simpa
    · exact ih

theorem IsPath.from_accept {u : ExtendedState σ} {x : List (Option α)}
    (h : M.toSingleεNFA.IsPath .accept u x) :
    u = .accept ∧ x = [] := by
  cases h with
  | nil => simp
  | cons _ _ _ _ _ h_step _ => simp at h_step

theorem IsPath.state_accept {s : σ} {x : List (Option α)}
    (h : M.toSingleεNFA.IsPath (.state s) .accept x) :
    ∃ t x', t ∈ M.accept ∧ x = x' ++ [none] ∧ M.IsPath s t x' := by
  generalize hs : (ExtendedState.state s) = ss at h
  generalize ha : ExtendedState.accept = a' at h
  induction h generalizing s with
  | nil _ =>
    cases hs
    cases ha
  | cons t' s' u oa x' h_step h_path ih =>
    subst hs ha
    cases oa with
    | some a =>
      simp only [toSingleεNFA_step, mem_image] at h_step
      rcases h_step with ⟨t, ht, rfl⟩
      rcases ih rfl rfl with ⟨t', x'', ht', rfl, h_before⟩
      exact ⟨t', some a :: x'', ht', by simp, cons t s t' (some a) x'' ht h_before⟩
    | none =>
      simp only [toSingleεNFA_step, mem_union, mem_image, mem_ite_empty_right,
        mem_singleton_iff] at h_step
      rcases h_step with ⟨t, ht, rfl⟩ | ⟨hs, rfl⟩
      · rcases ih rfl rfl with ⟨t', x'', ht', hx'', h_before⟩
        exact ⟨t', none :: x'', ht', by simpa, cons t s t' none x'' ht h_before⟩
      · rcases IsPath.from_accept h_path with ⟨_, rfl⟩
        exact ⟨s, [], by simpa⟩

theorem accepts_toSingleεNFA : M.toSingleεNFA.accepts = M.accepts := by
  ext x
  constructor
  · intro h
    apply (mem_accepts_iff_exists_path M).mpr
    rcases (mem_accepts_iff_exists_path (M.toSingleεNFA)).mp h with
      ⟨s₁, s₂, x', hs₁, hs₂, rfl, h_path⟩
    simp only [toSingleεNFA_start, mem_singleton_iff, toSingleεNFA_accept] at hs₁ hs₂
    subst hs₁ hs₂
    cases h_path with
    | cons t' s' u oa x'' h_step h_rest =>
      cases oa with
      | some a => simp at h_step
      | none =>
        simp only [toSingleεNFA_step, mem_image] at h_step
        rcases h_step with ⟨s, hs, rfl⟩
        rcases IsPath.state_accept h_rest with ⟨t, y, ht, rfl, h_before⟩
        exact ⟨s, t, y, hs, ht, by simp [List.reduceOption_append], h_before⟩
  · intro h
    apply (mem_accepts_iff_exists_path (M.toSingleεNFA)).mpr
    rcases (mem_accepts_iff_exists_path M).mp h with ⟨s₁, s₂, x', hs₁, hs₂, rfl, hx'⟩
    use .start, .accept, [none] ++ x' ++ [none]
    and_intros
    · simp
    · simp
    · simp [List.reduceOption_append]
    · simp only [isPath_append]
      exact ⟨.state s₂, ⟨.state s₁, by simpa, IsPath.toSingleεNFA_lift_extendedState hx'⟩, by simpa⟩

end toSingleεNFA

section Kleene

open RegularExpression

variable {σ : Type*} [FinEnum σ]
variable {α : Type*} [Fintype α] [LinearOrder α]
variable {M : εNFA α (ExtendedState σ)}
variable [∀ q oa q', Decidable (q' ∈ M.step q oa)]

local notation "n" => FinEnum.card (ExtendedState σ)

/-- An equivalence mapping the extended state space `ExtendedState σ` to the disjoint union
`Sum (Fin 2) σ`. This is a helper used to derive the `FinEnum` instance for `ExtendedState σ`. -/
def ExtendedState.equivSum (σ : Type*) : ExtendedState σ ≃ Sum (Fin 2) σ where
  toFun := fun
    | .start   => .inl 0
    | .accept  => .inl 1
    | .state s => .inr s
  invFun := fun
    | .inl ⟨0, _⟩ => .start
    | .inl ⟨1, _⟩ => .accept
    | .inl _      => .start
    | .inr s      => .state s
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with ⟨_ | _ | _⟩ | s
    all_goals first | rfl | contradiction

instance [FinEnum σ] : FinEnum (ExtendedState σ) :=
  FinEnum.ofEquiv (Sum (Fin 2) σ) (ExtendedState.equivSum σ)

/-- The bijection indexing every state in the extended NFA with a unique integer in `Fin n`.
This allows `pathRegex` to implement Kleene's algorithm. -/
def e : ExtendedState σ ≃ Fin n := FinEnum.equiv

variable (M) in
/-- The regex matching the union of all single symbols that results in a single transition from a
state indexed `i` to a state indexed `j` and the empty string if there also exists an epsilon
transition. -/
def directRegex (i j : Fin n) : RegularExpression α :=
  let char_transitions : RegularExpression α :=
    Finset.univ.sort.foldl (fun acc a =>
      acc + (if (e.symm j) ∈ M.step (e.symm i) (some a) then char a else 0)
    ) 0
  let epsilon_transitions : RegularExpression α :=
    if (e.symm j) ∈ M.step (e.symm i) none ∨ i = j then 1 else 0
  char_transitions + epsilon_transitions

theorem mem_matches'_directRegex {i j : Fin n} {x : List α} :
    x ∈ (M.directRegex i j).matches' ↔
    (∃ a, x = [a] ∧ e.symm j ∈ M.step (e.symm i) (some a)) ∨
    (x = [] ∧ ((e.symm j ∈ M.step (e.symm i) none) ∨ i = j)) := by
  simp only [directRegex, matches'_add, Language.mem_add, matches'_foldl_sum, Finset.mem_sort,
    Finset.mem_univ, iUnion_true]
  constructor
  · rintro (⟨s, ⟨a, ha⟩, hx⟩ | hε)
    · left
      simp only at ha
      subst ha
      split_ifs at hx with h_step
      · simp only [matches'] at hx
        exact ⟨a, mem_singleton_iff.mp hx, h_step⟩
      · simp [Language.zero_def] at hx
    · right
      split_ifs at hε with h_step
      · simp only [matches', Language.mem_one] at hε
        rcases h_step with h_step | rfl
        · exact ⟨hε, Or.inl h_step⟩
        · simp [hε]
      · simp [Language.zero_def] at hε
        contradiction
  · rintro (⟨a, rfl, h_step⟩ | ⟨rfl, h_step⟩)
    · left
      use { [a] }
      simp only [mem_range, mem_singleton_iff, and_true]
      use a
      simp [h_step]
    · right
      simp [h_step]

variable (M) in
/-- The regex matching all words that result in a path from a state indexed `i` to a state indexed
`j` using no intermediate state with index greater than or equal to `k`.

Implements Kleene's algorithm for computing the regex. -/
@[simp]
def pathRegex (k : ℕ) (i j : Fin n) : RegularExpression α :=
  match k, i, j with
  | 0, i, j     => directRegex M i j
  | k + 1, i, j =>
    if hk : k < n then
      let k' : Fin n := ⟨k, hk⟩
      let R_to_k := pathRegex k i k'
      let R_loop := pathRegex k k' k'
      let R_from := pathRegex k k' j
      let R_old  := pathRegex k i j
      R_to_k * R_loop.star * R_from + R_old
    else
      pathRegex k i j

theorem pathRegex_mono {k k' : ℕ} {i j : Fin n} {x : List α}
    (hle : k ≤ k') (h : x ∈ (pathRegex M k i j).matches') :
    x ∈ (pathRegex M k' i j).matches' := by
  induction hle with
  | refl => exact h
  | step hn ih =>
    simp only [pathRegex]
    split_ifs
    · exact Or.inr ih
    · exact ih

theorem pathRegex_trans {k : ℕ} {i j m : Fin n} (hm : m.val < k)
    {x₁ x₂ : List α}
    (h₁ : x₁ ∈ (pathRegex M k i m).matches')
    (h₂ : x₂ ∈ (pathRegex M k m j).matches') :
    x₁ ++ x₂ ∈ (pathRegex M k i j).matches' := by
  induction k generalizing i j m x₁ x₂ with
  | zero => contradiction
  | succ k' ih =>
    simp only [pathRegex] at *
    split_ifs at * with hk'
    · rw [matches'_add, Language.mem_add, mem_matches_mul_star_mul] at *
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm | rfl
      <;> rcases h₁ with ⟨y₁, y₂, y₃, rfl, hy₁, hy₂, hy₃⟩ | h_old₁
      <;> rcases h₂ with ⟨z₁, z₂, z₃, rfl, hz₁, hz₂, hz₃⟩ | h_old₂
      · left
        refine ⟨y₁, y₂ ++ y₃ ++ z₁ ++ z₂, z₃, by simp, hy₁, ?_, hz₃⟩
        have h₁ := ih hm hy₃ hz₁
        have h₂ := mem_matches_star_concat hy₂ (mem_matches_star_singleton h₁)
        rw [← List.append_assoc] at h₂
        exact mem_matches_star_concat h₂ hz₂
      · left
        exact ⟨y₁, y₂, y₃ ++ x₂, by simp, hy₁, hy₂, ih hm hy₃ h_old₂⟩
      · left
        exact ⟨x₁ ++ z₁, z₂, z₃, by simp, ih hm h_old₁ hz₁, hz₂, hz₃⟩
      · right
        exact ih hm h_old₁ h_old₂
      · left
        refine ⟨y₁, y₂ ++ y₃ ++ z₁ ++ z₂, z₃, by simp, hy₁, ?_, hz₃⟩
        have h₁ := mem_matches_star_concat hy₂ (mem_matches_star_singleton hy₃)
        have h₂ := mem_matches_star_concat h₁ (mem_matches_star_singleton hz₁)
        exact mem_matches_star_concat h₂ hz₂
      · left
        refine ⟨y₁, y₂ ++ y₃, x₂, by simp, hy₁, ?_, h_old₂⟩
        exact mem_matches_star_concat hy₂ (mem_matches_star_singleton hy₃)
      · left
        refine ⟨x₁, z₁ ++ z₂, z₃, by simp, h_old₁, ?_, hz₃⟩
        exact mem_matches_star_concat (mem_matches_star_singleton hz₁) hz₂
      · left
        exact ⟨x₁, [], x₂, by simp, h_old₁, ⟨[], rfl, by simp⟩, h_old₂⟩
    · rcases lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm | rfl
      · exact ih hm h₁ h₂
      · simp at hk'

variable (M) in
/-- A path in the NFA restricted to intermediate states < k. -/
inductive IsRestrictedPath (k : ℕ) : Fin n → Fin n → List (Option α) → Prop
  | nil (i: Fin n) : IsRestrictedPath k i i []
  | step (i j : Fin n) (oa : Option α) :
      e.symm j ∈ M.step (e.symm i) oa →
      IsRestrictedPath k i j [oa]
  | trans (i j m : Fin n) (x₁ x₂ : List (Option α)) :
      IsRestrictedPath k i m x₁ →
      m.val < k →
      IsRestrictedPath k m j x₂ →
      IsRestrictedPath k i j (x₁ ++ x₂)

omit [Fintype α] [LinearOrder α] [∀ q oa q', Decidable (q' ∈ M.step q oa)] in
theorem isRestrictedPath_iff_isPath {i j : Fin n} {x : List (Option α)} :
    M.IsRestrictedPath n i j x ↔ M.IsPath (e.symm i) (e.symm j) x := by
  constructor
  · intro h
    induction h with
    | nil _ => exact (isPath_nil M).mpr rfl
    | step _ _ _ ih => exact IsPath.singleton M ih
    | trans _ _ m _ _ _ _ _ ih₁ ih₂ =>
      rw [isPath_append]
      use e.symm m
  · intro h
    generalize hs : e.symm i = s at h
    generalize hu : e.symm j = u at h
    induction h generalizing i with
    | nil _ =>
      subst hs
      rw [Equiv.apply_eq_iff_eq] at hu
      subst hu
      exact IsRestrictedPath.nil j
    | cons t s' u' oa x' h_step h_path ih =>
      subst hs hu
      rw [← List.singleton_append]
      apply IsRestrictedPath.trans (m := e t)
      · apply IsRestrictedPath.step
        simp [h_step]
      · exact (e t).isLt
      · exact ih (Equiv.symm_apply_apply _ _) rfl

variable (M) in
/-- A match by a path regex in the NFA restricted to intermediate states < k. -/
inductive IsRestrictedMatch (k : ℕ) : Fin n → Fin n → List α → Prop
  | direct (i j : Fin n) (x : List α) :
      x ∈ (directRegex M i j).matches' →
      IsRestrictedMatch k i j x
  | trans (i j m : Fin (n)) (x₁ x₂ : List α) :
      IsRestrictedMatch k i m x₁ →
      m.val < k →
      IsRestrictedMatch k m j x₂ →
      IsRestrictedMatch k i j (x₁ ++ x₂)

theorem isRestrictedMatch_nil {k : ℕ} {i : Fin n} : M.IsRestrictedMatch k i i [] := by
  apply IsRestrictedMatch.direct
  rw [mem_matches'_directRegex]
  right
  simp

theorem isRestrictedMatch_iff_exists_isRestrictedPath
    {k : ℕ} {i j : Fin n} {x : List α} :
    M.IsRestrictedMatch k i j x ↔
    ∃ y, y.reduceOption = x ∧ M.IsRestrictedPath k i j y := by
  constructor
  · intro h
    induction h with
    | direct i' j' x' h_match =>
      rw [mem_matches'_directRegex] at h_match
      rcases h_match with ⟨a, rfl, h_step⟩ | ⟨rfl, h_step | rfl⟩
      · exact ⟨[a], by simpa using IsRestrictedPath.step i' j' (some a) h_step⟩
      · exact ⟨[none], by simpa using IsRestrictedPath.step i' j' none h_step⟩
      · exact ⟨[], by simpa using IsRestrictedPath.nil i'⟩
    | trans i' j' m y₁ y₂ h₁ hlt h₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨x₁, rfl, hx₁⟩
      rcases ih₂ with ⟨x₂, rfl, hx₂⟩
      exact ⟨x₁ ++ x₂, by rw [List.reduceOption_append],
        IsRestrictedPath.trans i' j' m x₁ x₂ hx₁ hlt hx₂⟩
  · rintro ⟨y, rfl, h⟩
    induction h with
    | nil i' => exact isRestrictedMatch_nil
    | step i' j' oa h_step =>
      apply IsRestrictedMatch.direct
      rw [mem_matches'_directRegex]
      cases oa with
      | some a => exact Or.inl ⟨a, rfl, h_step⟩
      | none   => exact Or.inr ⟨rfl, Or.inl h_step⟩
    | trans i' j' m x₁ x₂ hx₁ hlt hx₂ ih₁ ih₂ =>
      rw [List.reduceOption_append]
      exact IsRestrictedMatch.trans i' j' m x₁.reduceOption x₂.reduceOption ih₁ hlt ih₂

theorem isRestrictedMatch_iff_exists_isPath {i j : Fin n} {x : (List α)} :
    IsRestrictedMatch M n i j x ↔
    ∃ y : List (Option α),
      y.reduceOption = x ∧
      M.IsPath (e.symm i) (e.symm j) y := by
  rw [isRestrictedMatch_iff_exists_isRestrictedPath]
  simp_rw [isRestrictedPath_iff_isPath]

theorem IsRestrictedMatch.mono {k k' : ℕ} {i j : Fin n} {w : List α}
    (h : IsRestrictedMatch M k i j w) (hle : k ≤ k') : IsRestrictedMatch M k' i j w := by
  induction h with
  | direct i' j' x hx => exact direct i' j' x hx
  | trans i' j' m x₁ x₂ _ hlt _ ih₁ ih₂ =>
    exact trans i' j' m x₁ x₂ ih₁ (lt_of_lt_of_le hlt hle) ih₂

lemma isRestrictedMatch_star {k : ℕ} {m : Fin n} {w : List α}
    (h : w ∈ (pathRegex M k m m).star.matches')
    (ih : ∀ {x}, x ∈ (pathRegex M k m m).matches' → IsRestrictedMatch M k m m x)
    (hm : m.val < k + 1) :
    IsRestrictedMatch M (k + 1) m m w := by
  rw [matches'_star, Language.mem_kstar] at h
  rcases h with ⟨L, rfl, hL⟩
  induction L with
  | nil => exact isRestrictedMatch_nil
  | cons z L' ih' =>
    simp only [List.forall_mem_cons] at hL
    apply IsRestrictedMatch.trans m m m
    · exact IsRestrictedMatch.mono (ih hL.left) (Nat.le_succ k)
    · exact hm
    · exact ih' hL.right

lemma isRestrictedMatch_of_mem_pathRegex {k : ℕ} {i j : Fin n} {w : List α}
    (h : w ∈ (pathRegex M k i j).matches') :
    IsRestrictedMatch M k i j w := by
  induction k generalizing i j w with
  | zero =>
    apply IsRestrictedMatch.direct
    simp_all
  | succ k' ih =>
    simp only [pathRegex] at h
    split_ifs at h with hlt
    · rw [matches'_add, Language.mem_add, mem_matches_mul_star_mul] at h
      rcases h with ⟨w₁, w₂, w₃, rfl, hw₁, hw₂, hw₃⟩ | h_old
      · apply IsRestrictedMatch.trans (m := ⟨k', hlt⟩)
        · apply IsRestrictedMatch.trans (m := ⟨k', hlt⟩)
          · exact IsRestrictedMatch.mono (ih hw₁) (Nat.le_succ k')
          · simp
          · exact isRestrictedMatch_star hw₂ ih (lt_add_one _)
        · simp
        · exact IsRestrictedMatch.mono (ih hw₃) (Nat.le_succ k')
      · exact IsRestrictedMatch.mono (ih h_old) (Nat.le_succ k')
    · exact IsRestrictedMatch.mono (ih h) (Nat.le_succ k')

lemma mem_pathRegex_of_isRestrictedMatch {k : ℕ} {i j : Fin n} {w : List α}
    (h : IsRestrictedMatch M k i j w) :
    w ∈ (pathRegex M k i j).matches' := by
  induction h with
  | direct i' j' x hx => exact pathRegex_mono (Nat.zero_le k) hx
  | trans i' j' m x₁ x₂ hx₁ hlt hx₂ ih₁ ih₂ => exact pathRegex_trans hlt ih₁ ih₂

theorem mem_pathRegex_iff_isRestrictedMatch {k : ℕ} {i j : Fin n} {w : List α} :
    w ∈ (pathRegex M k i j).matches' ↔ IsRestrictedMatch M k i j w :=
  ⟨isRestrictedMatch_of_mem_pathRegex, mem_pathRegex_of_isRestrictedMatch⟩

instance {M : εNFA α σ}
    [DecidablePred (· ∈ M.start)]
    [DecidablePred (· ∈ M.accept)]
    [∀ q oa q', Decidable (q' ∈ M.step q oa)]
    (q : ExtendedState σ) (oa : Option α) (q' : ExtendedState σ) :
    Decidable (q' ∈ M.toSingleεNFA.step q oa) := by
  cases q <;> cases oa
  <;> simp only [toSingleεNFA_step, mem_union, mem_image, mem_ite_empty_right, mem_singleton_iff]
  <;> infer_instance

/-- The regular expression that matches the language of `M`. -/
def toRegex (M : εNFA α σ)
    [∀ q oa q', Decidable (q' ∈ M.step q oa)]
    [DecidablePred (· ∈ M.start)]
    [DecidablePred (· ∈ M.accept)] :
    RegularExpression α :=
  pathRegex M.toSingleεNFA n (e .start) (e .accept)

theorem accepts_toRegex (M : εNFA α σ)
    [∀ q oa q', Decidable (q' ∈ M.step q oa)]
    [DecidablePred (· ∈ M.start)]
    [DecidablePred (· ∈ M.accept)] :
    (toRegex M).matches' = M.accepts := by
  ext x
  unfold toRegex
  rw [mem_pathRegex_iff_isRestrictedMatch, isRestrictedMatch_iff_exists_isPath,
    ← accepts_toSingleεNFA, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    mem_accepts_iff_exists_path]
  simp

end Kleene

end εNFA
