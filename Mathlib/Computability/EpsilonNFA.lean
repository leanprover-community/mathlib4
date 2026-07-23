/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Yaël Dillies, Anthony DeRossi
-/
module

public import Mathlib.Computability.NFA
public import Mathlib.Computability.RegularExpressions
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

section concat

variable {σ₁ σ₂ : Type v}
variable {M₁ : εNFA α σ₁} {M₂ : εNFA α σ₂}
variable [DecidablePred (· ∈ M₁.accept)]

/-- εNFA which accepts the concatenation of the languages of `M₁` and `M₂`. -/
@[simps]
def concat (M₁ : εNFA α σ₁) (M₂ : εNFA α σ₂) [DecidablePred (· ∈ M₁.accept)] :
    εNFA α (σ₁ ⊕ σ₂) where
  step q oa := match q, oa with
    | Sum.inl q₁, some _ => (M₁.step q₁ oa).image Sum.inl
    | Sum.inl q₁, none   =>
      (M₁.step q₁ none).image Sum.inl ∪
      (if q₁ ∈ M₁.accept then (M₂.start.image Sum.inr) else ∅)
    | Sum.inr q₂, _      => (M₂.step q₂ oa).image Sum.inr
  start := M₁.start.image Sum.inl
  accept := M₂.accept.image Sum.inr

lemma IsPath.concat_lift_inl {s t : σ₁} {x : List (Option α)} (h : M₁.IsPath s t x) :
    (concat M₁ M₂).IsPath (Sum.inl s) (Sum.inl t) x := by
  induction h with
  | nil _ => exact (isPath_nil (concat M₁ M₂)).mpr rfl
  | cons t' s' u oa x' h_step h_path ih =>
    apply IsPath.cons (Sum.inl t') (Sum.inl s') (Sum.inl u)
    · cases oa <;> simpa
    · exact ih

lemma IsPath.concat_lift_inr {s t : σ₂} {x : List (Option α)} (h : M₂.IsPath s t x) :
    (concat M₁ M₂).IsPath (Sum.inr s) (Sum.inr t) x := by
  induction h with
  | nil _ => exact (isPath_nil (concat M₁ M₂)).mpr rfl
  | cons t' s' u _ _ h_step _ ih =>
    apply IsPath.cons (Sum.inr t') (Sum.inr s') (Sum.inr u)
    · simpa
    · exact ih

lemma IsPath.concat_proj_inr {s t : σ₂} {x : List (Option α)}
    (h : (concat M₁ M₂).IsPath (Sum.inr s) (Sum.inr t) x) : M₂.IsPath s t x := by
  generalize hs' : Sum.inr s = s' at h
  generalize ht' : Sum.inr t = t' at h
  induction h generalizing s with
  | nil u =>
    subst hs'
    simp_all
  | cons _ s'' t'' _ _ h_step _ ih =>
    subst hs' ht'
    simp only [concat, mem_image] at h_step
    rcases h_step with ⟨q, hq, rfl⟩
    apply IsPath.cons q s t
    · exact hq
    · simp [ih]

lemma IsPath.concat_split_inl_inr {s : σ₁} {t : σ₂} {x : List (Option α)}
    (h : (concat M₁ M₂).IsPath (Sum.inl s) (Sum.inr t) x) :
    ∃ u v s_acc s_start,
      x = u ++ [none] ++ v ∧
      M₁.IsPath s s_acc u ∧
      s_acc ∈ M₁.accept ∧
      s_start ∈ M₂.start ∧
      M₂.IsPath s_start t v := by
  generalize hs' : Sum.inl s = s' at h
  generalize ht' : Sum.inr t = t' at h
  induction h generalizing s with
  | nil u =>
    cases ht'
    cases hs'
  | cons _ _ _ oa x' h_step h_path ih =>
    subst hs' ht'
    cases oa with
    | some a =>
      simp only [concat_step, mem_image] at h_step
      rcases h_step with ⟨q, hq, rfl⟩
      rcases ih rfl rfl with ⟨u, v, s_acc, s_start, hx', h_path_rest, h_acc, h_bridge, h_path_M₂⟩
      use some a :: u, v, s_acc, s_start
      and_intros
      · simp [hx']
      · exact cons q s s_acc (some a) u hq h_path_rest
      · exact h_acc
      · exact h_bridge
      · exact h_path_M₂
    | none =>
      simp only [concat_step, mem_union, mem_image, mem_ite_empty_right] at h_step
      rcases h_step with ⟨q, hq, rfl⟩ | ⟨hs, q, hq, rfl⟩
      · rcases ih rfl rfl with ⟨u, v, s_acc, s_start, hx', h_path_rest, h_acc, h_bridge, h_path_M₂⟩
        use none :: u, v, s_acc, s_start
        and_intros
        · simp [hx']
        · exact cons q s s_acc none u hq h_path_rest
        · exact h_acc
        · exact h_bridge
        · exact h_path_M₂
      · use [], x', s, q
        and_intros
        · simp
        · exact (isPath_nil M₁).mpr rfl
        · exact hs
        · exact hq
        · exact concat_proj_inr h_path

@[simp]
theorem accepts_concat : (concat M₁ M₂).accepts = M₁.accepts * M₂.accepts := by
  ext x
  simp only [Language.mem_mul]
  constructor
  · intro h
    rcases (mem_accepts_iff_exists_path (concat M₁ M₂)).mp h with ⟨q₁, q₂, x', hq₁, hq₂, hx', hM⟩
    simp only [concat, mem_image] at hq₁ hq₂
    rcases hq₁ with ⟨s, hs, rfl⟩
    rcases hq₂ with ⟨t, ht, rfl⟩
    rcases IsPath.concat_split_inl_inr hM with
      ⟨u', v', s_acc, s_start, hx, h_path_M₁, h_acc_M₁, h_start_M₂, h_path_M₂⟩
    apply Language.mem_mul.mpr
    refine ⟨u'.reduceOption, ?_, v'.reduceOption, ?_, ?_⟩
    · apply (mem_accepts_iff_exists_path M₁).mpr
      use s, s_acc, u'
    · apply (mem_accepts_iff_exists_path M₂).mpr
      use s_start, t, v'
    · subst hx' hx
      simp [List.reduceOption_append, List.reduceOption_cons_of_none]
  · intro ⟨u, hu, v, hv, hx⟩
    rcases (mem_accepts_iff_exists_path M₁).mp hu with ⟨uq₁, uq₂, u', huq₁, huq₂, hu', hM₁⟩
    rcases (mem_accepts_iff_exists_path M₂).mp hv with ⟨vq₁, vq₂, v', hvq₁, hvq₂, hv', hM₂⟩
    apply (mem_accepts_iff_exists_path (concat M₁ M₂)).mpr
    use Sum.inl uq₁, Sum.inr vq₂, u' ++ [none] ++ v'
    and_intros
    · simpa
    · simpa
    · simp [List.reduceOption_append, hx, hu', hv']
    · simp only [isPath_append]
      use Sum.inr vq₁
      constructor
      · exact ⟨Sum.inl uq₂, IsPath.concat_lift_inl hM₁, by simp [huq₂, hvq₁]⟩
      · exact IsPath.concat_lift_inr hM₂

end concat

section kstar

variable {M : εNFA α σ}
variable [DecidablePred (· ∈ M.accept)]

/-- DFA which accepts the Kleene star of the language of `M`. -/
@[simps]
def kstar (M : εNFA α σ) [DecidablePred (· ∈ M.accept)] : εNFA α (Option σ) where
  step oq oa := match oq, oa with
    | none,   some _ => ∅
    | none,   none   => M.start.image some
    | some q, some a => (M.step q (some a)).image some
    | some q, none   =>
      (M.step q none).image some ∪
      (if q ∈ M.accept then M.start.image some else ∅)
  start := { none }
  accept := { none } ∪ M.accept.image some

lemma kstar_step_some (q : σ) (a : Option α) :
    (kstar M).step (some q) a =
    (M.step q a).image some ∪
    (if a = none ∧ q ∈ M.accept then M.start.image some else ∅) := by
  cases a <;> simp

lemma IsPath.kstar_lift_some {s t : σ} {x : List (Option α)} (h : M.IsPath s t x) :
    M.kstar.IsPath (some s) (some t) x := by
  induction h with
  | nil _ => exact (isPath_nil M.kstar).mpr rfl
  | cons t' s' u oa x' h_step h_path ih =>
    apply cons (some t') (some s') (some u)
    · cases oa <;> simp [h_step]
    · exact ih

lemma kstar_exists_path_some
    (L : List (List α)) (h_nonempty : L ≠ []) (h_all : ∀ y ∈ L, y ∈ M.accepts) :
    ∃ (s : σ) (q : Option σ) (x : List (Option α)),
      s ∈ M.start ∧
      q ∈ M.kstar.accept ∧
      x.reduceOption = L.flatten ∧
      M.kstar.IsPath (some s) q x := by
  induction L with
  | nil => contradiction
  | cons y L' ih =>
    have hy := h_all y List.mem_cons_self
    have ⟨s, t, x, hs, ht, hy', hx⟩ := (mem_accepts_iff_exists_path M).mp hy
    subst hy'
    cases L' with
    | nil => exact ⟨s, some t, x, hs, by simpa, by simp, IsPath.kstar_lift_some hx⟩
    | cons z L'' =>
      have h_nonempty' : z :: L'' ≠ [] := by simp
      have h_all' : ∀ y ∈ z :: L'', y ∈ M.accepts := by aesop
      rcases ih h_nonempty' h_all' with ⟨s', q, x', hs', hq, hL'', hx'⟩
      refine ⟨s, q, x ++ [none] ++ x', hs, hq, ?_, ?_⟩
      · simp [hL'', List.reduceOption_append]
      · rw [List.append_assoc, isPath_append]
        use some t
        constructor
        · exact IsPath.kstar_lift_some hx
        · apply IsPath.cons (some s')
          · simp [ht, hs']
          · simpa

lemma IsPath.kstar_path_from_none {t : Option σ} {x : List (Option α)}
    (h : (kstar M).IsPath none t x) :
    t = none ∧ x = [] ∨
    ∃ s_start x',
      x = none :: x' ∧
      s_start ∈ M.start ∧
      (kstar M).IsPath (some s_start) t x' := by
  cases h with
  | nil _ => simp
  | cons _ _ _ oa _ h_step h_path =>
    cases oa with
    | some a => simpa
    | none =>
      simp only [kstar_step, mem_image] at h_step
      rcases h_step with ⟨s_start, hs_start, rfl⟩
      aesop

lemma IsPath.kstar_split_some {s t : σ} {x : List (Option α)}
    (h : (kstar M).IsPath (some s) (some t) x) :
    (∃ x', x'.reduceOption = x.reduceOption ∧ M.IsPath s t x') ∨
    (∃ (u v : List (Option α)) (s_acc s_next : σ),
      x = u ++ [none] ++ v ∧
      M.IsPath s s_acc u ∧
      s_acc ∈ M.accept ∧
      s_next ∈ M.start ∧
      (kstar M).IsPath (some s_next) (some t) v ∧
      v.length < x.length) := by
    generalize hs : some s = os at h
    generalize ht : some t = ot at h
    induction h generalizing s with
    | nil _ =>
      left
      subst hs
      exact ⟨[], by simp_all⟩
    | cons _ _ _ oa x' h_step h_path ih =>
      subst hs ht
      simp only [kstar_step_some, mem_union, mem_image, mem_ite_empty_right] at h_step
      rcases h_step with
        ⟨s_next, h_step_M, rfl⟩ |
        ⟨⟨rfl, hs_acc⟩, s_next, h_start, rfl⟩
      · rcases ih rfl rfl with
          ⟨y, hx'', hy⟩ |
          ⟨u, v, q_acc, q_next, rfl, hu, hq_acc, hq_next, hv, hlt⟩
        · left
          use oa :: y
          constructor
          · change ([oa] ++ y).reduceOption = ([oa] ++ x').reduceOption
            rw [List.reduceOption_append, hx'', ← List.reduceOption_append]
          · exact cons s_next s t oa y h_step_M hy
        · right
          use oa :: u, v, q_acc, q_next
          and_intros
          · simp
          · exact cons s_next s q_acc oa u h_step_M hu
          · exact hq_acc
          · exact hq_next
          · exact hv
          · simpa using Nat.lt_add_right 1 hlt
      · right
        use [], x', s, s_next
        and_intros
        · simp
        · exact (isPath_nil M).mpr rfl
        · exact hs_acc
        · exact h_start
        · exact h_path
        · simp

lemma IsPath.kstar_no_return {q : σ} {x : List (Option α)} :
    ¬ (kstar M).IsPath (some q) none x := by
  intro h
  generalize hq : some q = oq at h
  generalize hn : none = n at h
  induction h generalizing q with
  | nil =>
    cases hq
    cases hn
  | cons _ _ _ _ _ h_step _ ih =>
    subst hq hn
    simp only [kstar_step_some, mem_union, mem_image, mem_ite_empty_right] at h_step
    rcases h_step with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> exact ih rfl rfl

lemma IsPath.kstar_exists_decomp {s t : σ} {x : List (Option α)}
    (h : (kstar M).IsPath (some s) (some t) x)
    (hs : s ∈ M.start) (ht : t ∈ M.accept) :
    ∃ (L : List (List α)), L.flatten = x.reduceOption ∧ ∀ y ∈ L, y ∈ M.accepts := by
  generalize h_len : x.length = n
  induction n using Nat.strong_induction_on generalizing s x with
  | h n ih =>
    rcases IsPath.kstar_split_some h with
      ⟨x', hx, hx'⟩ |
      ⟨u, v, q_acc, s_next, hx, hu, h_acc, h_next, hv, hlt⟩
    · use [x'.reduceOption]
      constructor
      · simpa
      · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
        apply (mem_accepts_iff_exists_path M).mpr
        use s, t, x'
    · have hu_acc : u.reduceOption ∈ M.accepts := by
        apply (mem_accepts_iff_exists_path M).mpr
        use s, q_acc, u
      subst h_len
      rcases ih v.length hlt hv h_next rfl with ⟨L', hv', hL'⟩
      use u.reduceOption :: L'
      constructor
      · subst hx
        simp [hv', List.reduceOption_append]
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy
        · simp [hu_acc, hy]
        · exact hL' y hy

@[simp]
theorem accepts_kstar : (kstar M).accepts = (M.accepts)∗ := by
  ext x
  constructor
  · intro h
    rcases (mem_accepts_iff_exists_path (kstar M)).mp h with
      ⟨s_start, s_end, x', h_start, h_end, hx', h_path⟩
    simp only [kstar, singleton_union, mem_singleton_iff] at h_start
    subst h_start
    simp only [Language.mem_kstar]
    simp only [kstar, singleton_union, mem_insert_iff, mem_image] at h_end
    rcases h_end with rfl | ⟨q_start, hq_start, rfl⟩
    · cases h_path with
      | nil _ =>
        use []
        simpa using hx'
      | cons t' s' u oa x'' h_step h_rest =>
        cases oa with
        | some a => simp at h_step
        | none =>
          exfalso
          simp only [kstar_step, mem_image] at h_step
          rcases h_step with ⟨y, _, rfl⟩
          exact IsPath.kstar_no_return h_rest
    · cases h_path with
      | cons t' s' u oa x'' h_step h_rest =>
        cases oa with
        | some a => simp at h_step
        | none =>
          simp only [kstar, singleton_union, mem_image] at h_step
          rcases h_step with ⟨u', hu', rfl⟩
          rcases IsPath.kstar_exists_decomp h_rest hu' hq_start with ⟨L, hx'', hL⟩
          exact ⟨L, by simp_all, hL⟩
  · intro h
    simp only [Language.mem_kstar] at h
    rcases h with ⟨L, hx, hL⟩
    apply (mem_accepts_iff_exists_path (kstar M)).mpr
    induction L generalizing x with
    | nil => exact ⟨none, none, [], by simp [hx]⟩
    | cons w L' ih =>
      expose_names
      have h_nonempty : w :: L' ≠ [] := by simp
      rcases kstar_exists_path_some (w :: L') h_nonempty hL with ⟨s, q, x', hs, hq, hL', hx'⟩
      use none, q, none :: x'
      and_intros
      · simp
      · exact hq
      · simp [hx, hL']
      · apply IsPath.cons (some s)
        · simpa
        · exact hx'

end kstar

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

namespace Language

/-- Regular languages are closed under concatenation. -/
theorem IsRegular.mul {L₁ L₂ : Language α} (h₁ : IsRegular L₁) (h₂ : IsRegular L₂) :
    IsRegular (L₁ * L₂) := by
  classical
  have ⟨σ₁, _, M₁, hM₁⟩ := h₁
  have ⟨σ₂, _, M₂, hM₂⟩ := h₂
  let M := εNFA.concat M₁.toNFA.toεNFA M₂.toNFA.toεNFA
  exact ⟨Set (σ₁ ⊕ σ₂), inferInstance, M.toNFA.toDFA, by aesop⟩

/-- Regular languages are closed under Kleene star. -/
theorem IsRegular.kstar {L : Language α} (h : IsRegular L) : IsRegular L∗ := by
  classical
  have ⟨σ, _, M, hM⟩ := h
  let M := εNFA.kstar M.toNFA.toεNFA
  exact ⟨Set (Option σ), inferInstance, M.toNFA.toDFA, by aesop⟩

end Language

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

namespace RegularExpressions

/-- The language matched by a regular expression is a regular language. -/
theorem IsRegular.matches' (P : RegularExpression α) : Language.IsRegular (P.matches') := by
  induction P with
  | zero             => simp [Language.IsRegular.zero]
  | epsilon          => simp [Language.IsRegular.one]
  | char             => simp [Language.IsRegular.singleton]
  | plus _ _ ih₁ ih₂ => simp only [RegularExpression.matches', Language.IsRegular.add ih₁ ih₂]
  | comp _ _ ih₁ ih₂ => simp [Language.IsRegular.mul ih₁ ih₂]
  | star _ ih        => simp [Language.IsRegular.kstar ih]

end RegularExpressions
