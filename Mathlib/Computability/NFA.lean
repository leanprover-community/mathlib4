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

universe u v w


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

variable {α : Type u} {σ : Type v} {σ' : Type w} (M : NFA α σ)

namespace NFA

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

/-- Evaluations can be staggered. -/
theorem evalFrom_append (S : Set σ) (x y : List α) :
    M.evalFrom S (x ++ y) = M.evalFrom (M.evalFrom S x) y := by
  simp only [evalFrom, List.foldl_append]

/-- Evaluations are monotone. -/
theorem evalFrom_subset {σ : Type v} (M : NFA α σ) (x : List α) {qs ps : Set σ}
    (subs : qs ⊆ ps) : M.evalFrom qs x ⊆ M.evalFrom ps x := x.reverseRecOn subs <| by
  simp only [evalFrom_append_singleton, mem_stepSet, subset_def]
  rintro _ _ ih _ ⟨t, eval, step⟩
  exact ⟨t, ih t eval, step⟩

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

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α := {x | ∃ S ∈ M.accept, S ∈ M.eval x}

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

/-! ### Regex-like operations

Since NFAs are models for regular languages, they provide decision procedures for the empty set,
singleton sets with members of at most length 1 as well as a notion of closedness under union,
concatenation and application of the Kleene star.

Cf. <https://en.wikipedia.org/wiki/Thompson%27s_construction> for the basic idea in a setting
permitting ε-moves.
-/
instance : Zero (NFA α σ) :=
  ⟨NFA.mk (fun _ _ ↦ ∅) ∅ ∅⟩

instance : Inhabited (NFA α σ) :=
  ⟨0⟩

@[simp]
theorem zero_correct : (0 : NFA α σ).accepts = 0 := by
  ext
  refine ⟨?_, False.elim⟩
  rintro ⟨_, ⟨⟩, _⟩

instance : One (NFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, univ, univ⟩⟩

@[simp]
theorem one_correct [Inhabited σ] :
    (1 : NFA α σ).accepts = 1 := by
  ext x
  constructor
  · rintro ⟨q, _, eval⟩
    rcases x.eq_nil_or_concat with rfl | ⟨_, _, rfl⟩
    · exact rfl
    rw [List.concat_eq_append, eval_append_singleton, mem_stepSet] at eval
    rcases eval with ⟨_, _, ⟨⟩⟩
  · rintro rfl
    exact ⟨default, Set.mem_univ _, Set.mem_univ _⟩

/-- An NFA accepting just a single word of length 1, given by the underlying character. -/
def char (a : α) : NFA α (σ ⊕ σ') :=
  ⟨fun p c q ↦ p.isLeft ∧ a = c ∧ q.isRight, (Sum.isLeft ·), (Sum.isRight ·)⟩

@[simp]
theorem char_correct [Inhabited σ] [Inhabited σ'] (a : α) :
    (char a : NFA α (σ ⊕ σ')).accepts = {[a]} := by
  ext x
  constructor
  · rintro ⟨_ | _, accept, eval⟩
    · cases accept
    rcases x.eq_nil_or_concat with rfl | ⟨as, c, rfl⟩
    · cases eval
    rw [List.concat_eq_append, eval_append_singleton, mem_stepSet] at eval
    rcases eval with ⟨_ | _, mem, step⟩; rotate_left
    · rcases step with ⟨⟨⟩, _, _⟩
    rcases as.eq_nil_or_concat with rfl | ⟨_, _, rfl⟩
    · rcases step with ⟨_, rfl, _⟩; exact rfl
    rw [List.concat_eq_append, eval_append_singleton, mem_stepSet] at mem
    rcases mem with ⟨_, _, _, _, ⟨⟩⟩
  · rintro rfl
    refine ⟨.inr default, rfl, ?_⟩
    rw [← List.nil_append [a], eval_append_singleton, mem_stepSet]
    exact ⟨.inl default, by repeat fconstructor⟩

instance : HAdd (NFA α σ) (NFA α σ') (NFA α (σ ⊕ σ')) :=
  ⟨fun P₁ P₂ ↦
    ⟨fun p c q ↦
      match (p, q) with
      | (.inl p, .inl q) => P₁.step p c q
      | (.inr p, .inr q) => P₂.step p c q
      | _ => False,
      Sum.elim P₁.start P₂.start,
      Sum.elim P₁.accept P₂.accept⟩⟩

@[simp]
theorem hadd_correct (P₁ : NFA α σ) (P₂ : NFA α σ') :
    (P₁ + P₂).accepts = P₁.accepts + P₂.accepts := by
  ext x
  constructor
  · rintro ⟨q | q, accept, eval⟩ <;> [left; right] <;>
    · refine ⟨q, accept, ?_⟩
      clear accept
      induction x using List.reverseRecOn generalizing q
      · exact eval
      rename_i as a ih
      rw [eval_append_singleton, mem_stepSet] at eval ⊢
      rcases eval with ⟨p | p, mem, step⟩ <;>
        first | exact ⟨p, ih p mem, step⟩ | cases step
  · rintro (⟨q, accept, eval⟩ | ⟨q, accept, eval⟩) <;> [exists .inl q; exists .inr q] <;>
    · refine ⟨accept, ?_⟩
      clear accept
      induction x using List.reverseRecOn generalizing q
      · exact eval
      rename_i as a ih
      rw [eval_append_singleton, mem_stepSet] at eval ⊢
      rcases eval with ⟨p, mem, step⟩
      first | exists .inl p | exists .inr p
      exact ⟨ih p mem, step⟩

instance : HMul (NFA α σ) (NFA α σ') (NFA α (σ ⊕ σ')) :=
  ⟨fun P₁ P₂ ↦
    ⟨fun p c q ↦
      match (p, q) with
      | (.inl p, .inl q) => P₁.step p c q
      | (.inl p, .inr q) => P₂.start q ∧ ∃ r, P₁.accept r ∧ P₁.step p c r
      | (.inr p, .inr q) => P₂.step p c q
      | _ => False,
      Sum.elim P₁.start (P₂.start · ∧ ∃ p, P₁.accept p ∧ P₁.start p),
      Sum.elim (P₁.accept · ∧ ∃ p, P₂.accept p ∧ P₂.start p) P₂.accept⟩⟩

lemma hmul_eval₁ {P₂ : NFA α σ'} {P₁ : NFA α σ} {x : List α} (q : σ) :
    q ∈ P₁.eval x ↔ .inl q ∈ (P₁ * P₂).eval x := by
  induction x using List.reverseRecOn generalizing q
  · exact ⟨id, id⟩
  rename_i as a ih
  constructor <;> simp only [eval_append_singleton, mem_stepSet] <;> rintro ⟨p, eval, step⟩
  · rw [ih p] at eval
    exact ⟨.inl p, eval, step⟩
  · rcases p with p | p
    · rw [← ih p] at eval; exact ⟨p, eval, step⟩
    · cases step

lemma hmul_eval₂ {P₁ : NFA α σ} {P₂ : NFA α σ'} {x y : List α} (q : σ')
    (accepts : P₁.accepts x) :
    q ∈ P₂.eval y →
    .inr q ∈ (P₁ * P₂).evalFrom ((P₁ * P₂).eval x) y := by
  induction y using List.reverseRecOn generalizing q
  · intro h
    rcases accepts with ⟨p, accept, eval⟩
    rw [P₂.hmul_eval₁ p] at eval
    rcases x.eq_nil_or_concat with rfl | ⟨as, a, rfl⟩
    · exact ⟨h, p, accept, eval⟩
    rw [evalFrom_nil]
    rw [List.concat_eq_append, eval_append_singleton, mem_stepSet] at eval ⊢
    rcases eval with ⟨r, mem, step⟩
    refine ⟨r, mem, ?_⟩
    rcases r with _ | _
    · exact ⟨h, p, accept, step⟩
    · cases step
  · rename_i _ _ ih
    simp only [eval_append_singleton, evalFrom_append_singleton, mem_stepSet]
    rintro ⟨p, mem, step⟩
    exact ⟨.inr p, ih p mem, step⟩

@[simp]
theorem hmul_correct (P₁ : NFA α σ) (P₂ : NFA α σ') :
    (P₁ * P₂).accepts = P₁.accepts * P₂.accepts := by
  ext x
  constructor
  · rintro ⟨q | q, accept, eval⟩
    · rcases accept with ⟨accept, niltail⟩
      refine ⟨x, ⟨q, accept, ?_⟩, [], niltail, x.append_nil⟩
      clear accept
      induction x using List.reverseRecOn generalizing q
      · exact eval
      rename_i _ _ ih
      rw [eval_append_singleton, mem_stepSet] at eval ⊢
      rcases eval with ⟨p | p, mem, step⟩
      · exact ⟨p, ih p mem, step⟩
      · cases step
    · suffices ∃ y z, y ∈ P₁.accepts ∧ q ∈ P₂.eval z ∧ y ++ z = x by
        rcases this with ⟨y, z, y_accepts, z_eval, append⟩
        exact ⟨y, y_accepts, z, ⟨q, accept, z_eval⟩, append⟩
      clear accept
      induction x using List.reverseRecOn generalizing q
      · rcases eval with ⟨start, niltail⟩; exact ⟨[], [], niltail, start, rfl⟩
      rename_i as a ih
      rw [eval_append_singleton, mem_stepSet] at eval
      rcases eval with ⟨p | p, mem, step⟩
      · rcases step with ⟨start, r, accept, step⟩
        refine ⟨as ++ [a], [], ⟨r, accept, ?_⟩, start, (as ++ [a]).append_nil⟩
        rw [eval_append_singleton, mem_stepSet]
        rw [← hmul_eval₁ p] at mem
        exact ⟨p, mem, step⟩
      · rcases ih p mem with ⟨y, z, accepts, eval, rfl⟩
        refine ⟨y, z ++ [a], accepts, ?_, (y.append_assoc _ _).symm⟩
        rw [eval_append_singleton, mem_stepSet]
        exact ⟨p, eval, step⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    rcases z.eq_nil_or_concat with rfl | ⟨bs, b, rfl⟩
    · rcases hy with ⟨q, accept, eval⟩
      simp only [y.append_nil]
      rw [hmul_eval₁ q] at eval
      exact ⟨.inl q, ⟨accept, hz⟩, eval⟩
    · rcases hz with ⟨q, accept, eval⟩
      refine ⟨.inr q, accept, ?_⟩
      simp only [List.concat_eq_append, ← y.append_assoc] at eval ⊢
      rw [eval_append_singleton, mem_stepSet] at eval ⊢
      rcases eval with ⟨p, mem, step⟩
      refine ⟨.inr p, ?_, step⟩
      rw [eval, evalFrom_append]
      exact hmul_eval₂ p hy mem

/-- Kleene-starring adds a state and there is no heterogeneous `KStar` class, so we fall back to
a function definition. -/
def kstar (P : NFA α σ) : (NFA α (Option σ)) :=
  ⟨fun p c q ↦
    match (p, q) with
    | (some p, some q) => P.step p c q ∨ ∃ r, P.accept r ∧ P.step p c r ∧ P.start q
    | _ => False,
    Option.rec True P.start,
    Option.rec True P.accept⟩

/-- All start states of an unstarred NFA can be reached in a starred NFA by a string in the
original's language. -/
lemma kstar_eval_aux {P : NFA α σ} {y} (h : y ∈ P.accepts) :
    P.kstar.start \ {none} ⊆ P.kstar.eval y := by
  rintro (⟨⟩ | s) ⟨selem, snelem⟩
  · simp only [mem_singleton_iff, not_true_eq_false] at snelem
  rcases y.eq_nil_or_concat with rfl | ⟨as, a, rfl⟩
  · exact selem
  simp only [List.concat_eq_append, mem_accepts, evalFrom_append_singleton, mem_stepSet] at h
  rcases h with ⟨q, accept, p, eval, step⟩
  simp only [List.concat_eq_append, eval_append_singleton, mem_stepSet]
  refine ⟨some p, ?_, .inr ⟨q, accept, step, selem⟩⟩
  clear step
  induction as using List.reverseRecOn generalizing p
  · exact eval
  rename_i _ _ ih
  simp only [evalFrom_append_singleton, mem_stepSet] at eval
  rcases eval with ⟨t, eval, step⟩
  simp only [eval_append_singleton, mem_stepSet]
  exact ⟨some t, ih t eval, .inl step⟩

/-- A state of an unstarred NFA can be reached in the starred NFA by any word that has prefixes
accepted by the original NFA and a suffix that would have reached the state anyway. -/
lemma kstar_eval {P : NFA α σ} {x : List α} {q : σ} :
    some q ∈ P.kstar.eval x ↔
    ∃ (ys : List (List α)) (z : List α),
    x = ys.join ++ z ∧ q ∈ P.eval z ∧ ∀ y ∈ ys, y ∈ P.accepts := by
  constructor
  · induction x using List.reverseRecOn generalizing q
    · rintro h; exact ⟨[], [], rfl, h, List.forall_mem_nil _⟩
    rename_i as a ih
    rw [eval_append_singleton, mem_stepSet]
    rintro ⟨⟨⟩ | p, eval, step⟩
    · cases step
    specialize ih eval
    rcases ih with ⟨ys, z, rfl, evalz, allys⟩
    rcases step with step | ⟨t, accept, step, start⟩
    · refine ⟨ys, z ++ [a], ys.join.append_assoc _ _, ?_, allys⟩
      rw [eval_append_singleton, mem_stepSet]
      exact ⟨p, evalz, step⟩
    · refine ⟨ys ++ [z ++ [a]], [], by simp, start, ?_⟩
      refine List.forall_mem_append.mpr ⟨allys, List.forall_mem_singleton.mpr ⟨t, accept, ?_⟩⟩
      rw [eval_append_singleton, mem_stepSet]
      exact ⟨p, evalz, step⟩
  · rintro ⟨ys, z, rfl, eval, allys⟩
    induction ys generalizing q
    · induction z using List.reverseRecOn generalizing q <;> simp
      · exact eval
      rename_i as a ih
      rw [eval_append_singleton, mem_stepSet] at eval
      rcases eval with ⟨t, eval, step⟩
      simp [mem_stepSet]
      refine ⟨some t, ih eval, .inl step⟩
    · rename_i y ys ih
      simp only [List.join, List.append_assoc]
      simp at allys
      rcases allys with ⟨accepty, allys⟩
      specialize ih eval allys
      generalize ys.join ++ z = ysj at ih
      rw [NFA.eval, evalFrom_append]
      refine P.kstar.evalFrom_subset ysj (kstar_eval_aux accepty) ?_
      clear eval
      induction ysj using List.reverseRecOn generalizing q
      · simp; exact ih
      rename_i _ _ iih
      simp only [eval_append_singleton, evalFrom_append_singleton, mem_stepSet] at ih ⊢
      rcases ih with ⟨⟨⟩ | t, eval, step⟩
      · simp only [kstar, Set.mem_def] at step
      · exact ⟨some t, iih eval, step⟩

theorem kstar_correct (P : NFA α σ) :
    P.kstar.accepts = P.accepts∗ := by
  ext x
  rw [Language.mem_kstar, mem_accepts]
  constructor
  · rintro ⟨⟨⟩ | q, accept, eval⟩
    · refine ⟨[], ?_, List.forall_mem_nil _⟩
      rcases x.eq_nil_or_concat with rfl | ⟨as, a, rfl⟩
      · exact rfl
      rw [List.concat_eq_append, evalFrom_append_singleton, mem_stepSet] at eval
      rcases eval with ⟨⟨⟩ | _, _, ⟨⟩⟩
    · rcases kstar_eval.mp eval with ⟨ys, z, rfl, evalz, allys⟩
      refine ⟨ys ++ [z], by simp only [List.join_append, List.join, List.append_nil], ?_⟩
      exact List.forall_mem_append.mpr ⟨allys, List.forall_mem_singleton.mpr ⟨q, accept, evalz⟩⟩
  · rintro ⟨l, rfl, h⟩
    rcases l.eq_nil_or_concat with rfl | ⟨ys, z, rfl⟩
    · exact ⟨none, trivial, trivial⟩
    rw [List.concat_eq_append, List.forall_mem_append, List.forall_mem_singleton, mem_accepts] at h
    rcases h with ⟨allys, q, accept, eval⟩
    refine ⟨some q, accept, kstar_eval.mpr ⟨ys, z, ?_, eval, allys⟩⟩
    simp only [List.concat_eq_append, List.join_append, List.join, List.append_nil]

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
