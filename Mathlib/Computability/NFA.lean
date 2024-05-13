/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Powerset

#align_import computability.NFA from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

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

-- Porting note: Required as `NFA` is used in mathlib3
set_option linter.uppercaseLean3 false

/-- An NFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a set of starting states (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `Set` of states. These are the states that it
  may be sent to. -/
structure NFA (α : Type u) (σ : Type v) where
  step : σ → α → Set σ
  start : Set σ
  accept : Set σ
#align NFA NFA

variable {α : Type u} {σ : Type v} {σ' : Type w} (M : NFA α σ)

namespace NFA

instance : Inhabited (NFA α σ) :=
  ⟨NFA.mk (fun _ _ => ∅) ∅ ∅⟩

/-- `M.stepSet S a` is the union of `M.step s a` for all `s ∈ S`. -/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.step s a
#align NFA.step_set NFA.stepSet

theorem mem_stepSet (s : σ) (S : Set σ) (a : α) : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.step t a := by
  simp [stepSet]
#align NFA.mem_step_set NFA.mem_stepSet

@[simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by simp [stepSet]
#align NFA.step_set_empty NFA.stepSet_empty

/-- `M.evalFrom S x` computes all possible paths though `M` with input `x` starting at an element
  of `S`. -/
def evalFrom (start : Set σ) : List α → Set σ :=
  List.foldl M.stepSet start
#align NFA.eval_from NFA.evalFrom

@[simp]
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = S :=
  rfl
#align NFA.eval_from_nil NFA.evalFrom_nil

@[simp]
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet S a :=
  rfl
#align NFA.eval_from_singleton NFA.evalFrom_singleton

@[simp]
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]
#align NFA.eval_from_append_singleton NFA.evalFrom_append_singleton

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
#align NFA.eval NFA.eval

@[simp]
theorem eval_nil : M.eval [] = M.start :=
  rfl
#align NFA.eval_nil NFA.eval_nil

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet M.start a :=
  rfl
#align NFA.eval_singleton NFA.eval_singleton

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _
#align NFA.eval_append_singleton NFA.eval_append_singleton

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α := {x | ∃ S ∈ M.accept, S ∈ M.eval x}
#align NFA.accepts NFA.accepts

theorem mem_accepts {x : List α} : x ∈ M.accepts ↔ ∃ S ∈ M.accept, S ∈ M.evalFrom M.start x := by
  rfl

/-- `M.toDFA` is a `DFA` constructed from an `NFA` `M` using the subset construction. The
  states is the type of `Set`s of `M.state` and the step function is `M.stepSet`. -/
def toDFA : DFA α (Set σ) where
  step := M.stepSet
  start := M.start
  accept := { S | ∃ s ∈ S, s ∈ M.accept }
#align NFA.to_DFA NFA.toDFA

@[simp]
theorem toDFA_correct : M.toDFA.accepts = M.accepts := by
  ext x
  rw [mem_accepts, DFA.mem_accepts]
  constructor <;> · exact fun ⟨w, h2, h3⟩ => ⟨w, h3, h2⟩
#align NFA.to_DFA_correct NFA.toDFA_correct

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts := by
  rw [← toDFA_correct] at hx ⊢
  exact M.toDFA.pumping_lemma hx hlen
#align NFA.pumping_lemma NFA.pumping_lemma

/-! ### Regex-like operations -/
instance : Zero (NFA α σ) :=
  ⟨default⟩

instance zeroDecidableStart : DecidablePred (· ∈ (0 : NFA α σ).start) :=
  fun _ ↦ decidableFalse
instance zeroDecidableAccept : DecidablePred (· ∈ (0 : NFA α σ).accept) :=
  fun _ ↦ decidableFalse
instance zeroDecidableStep : ∀ q a, DecidablePred (· ∈ (0 : NFA α σ).step q a) :=
  fun _ _ _ ↦ decidableFalse

@[simp]
theorem zero_correct : (0 : NFA α σ).accepts = 0 := by
  ext
  refine ⟨?_, False.elim⟩
  rintro ⟨q, ⟨⟩, _⟩

instance [Inhabited σ] : One (NFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, univ, univ⟩⟩

instance oneDecidableStart [Inhabited σ] : DecidablePred (· ∈ (1 : NFA α σ).start) :=
  fun _ ↦ decidableTrue
instance oneDecidableAccept [Inhabited σ] : DecidablePred (· ∈ (1 : NFA α σ).accept) :=
  fun _ ↦ decidableTrue
instance oneDecidableStep [Inhabited σ] : ∀ q a, DecidablePred (· ∈ (1 : NFA α σ).step q a) :=
  fun _ _ _ ↦ decidableFalse

@[simp]
theorem one_correct [Inhabited σ] :
    (1 : NFA α σ).accepts = 1 := by
  ext x
  rw[mem_accepts]
  constructor
  · rintro ⟨q, _, eval⟩
    rcases x.eq_nil_or_concat with rfl | ⟨_, _, rfl⟩
    · simp
    rw [NFA.evalFrom_append_singleton, NFA.mem_stepSet] at eval
    rcases eval with ⟨_, _, ⟨⟩⟩
  · rintro ⟨⟨⟩⟩
    exact ⟨default, Set.mem_univ _, Set.mem_univ _⟩

instance [Inhabited σ] [Inhabited σ'] : Singleton α (NFA α (σ ⊕ σ')) :=
  ⟨fun a ↦
    ⟨fun p c q ↦ p.isLeft ∧ a = c ∧ q.isRight, (Sum.isLeft ·), (Sum.isRight ·)⟩⟩

instance singletonDecidableStart [Inhabited σ] [Inhabited σ'] [DecidableEq α] (a : α) :
    DecidablePred (· ∈ ({a} : NFA α (σ ⊕ σ')).start) := fun _ ↦ Bool.decEq _ _
instance singletonDecidableAccept [Inhabited σ] [Inhabited σ'] [DecidableEq α] (a : α) :
    DecidablePred (· ∈ ({a} : NFA α (σ ⊕ σ')).accept) := fun _ ↦ Bool.decEq _ _
instance singletonDecidableStep [Inhabited σ] [Inhabited σ'] [DecidableEq α] (a' : α) :
    ∀ q a, DecidablePred (· ∈ ({a'} : NFA α (σ ⊕ σ')).step q a) :=
  fun _ _ _ ↦ And.decidable

@[simp]
theorem singleton_correct [Inhabited σ] [Inhabited σ'] (a : α) :
    ({a} : NFA α (σ ⊕ σ')).accepts = {[a]} := by
  ext x
  constructor
  · rintro ⟨⟨⟩|⟨⟩, accept, eval⟩
    · cases accept
    rcases x.eq_nil_or_concat with rfl | ⟨as, c, rfl⟩
    · cases eval
    unfold NFA.eval NFA.evalFrom at eval
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, Set.mem_singleton_iff,
      List.foldl_nil] at *
    rw [NFA.mem_stepSet] at eval
    rcases eval with ⟨⟨⟩|⟨⟩, mem, step⟩; rotate_left
    · rcases step with ⟨⟨⟩, _, _⟩
    rcases as.eq_nil_or_concat with rfl | ⟨_, _, rfl⟩
    · rcases step with ⟨_, rfl, _⟩; exact rfl
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.append_assoc, List.singleton_append] at *
    rw [NFA.mem_stepSet] at mem
    rcases mem with ⟨_, _, _, _, ⟨⟩⟩
  · rintro ⟨⟨⟩⟩
    refine ⟨.inr default, rfl, ?_⟩
    simp only [NFA.eval, NFA.evalFrom, List.foldl]
    rw [NFA.mem_stepSet]
    exact ⟨.inl default, by repeat fconstructor⟩

instance : HAdd (NFA α σ) (NFA α σ') (NFA α (σ ⊕ σ')) :=
  ⟨fun P₁ P₂ ↦
    ⟨fun p c q ↦
      match (p, q) with
      | (Sum.inl p, Sum.inl q) => P₁.step p c q
      | (Sum.inr p, Sum.inr q) => P₂.step p c q
      | _ => False,
      fun q ↦
      match q with
      | Sum.inl q => P₁.start q
      | Sum.inr q => P₂.start q,
      fun q ↦
      match q with
      | Sum.inl q => P₁.accept q
      | Sum.inr q => P₂.accept q⟩⟩

instance haddDecidableStart {P₁ : NFA α σ} {P₂ : NFA α σ'}
    [l : DecidablePred (· ∈ P₁.start)]
    [r : DecidablePred (· ∈ P₂.start)] :
    DecidablePred (· ∈ (P₁ + P₂).start) := Sum.rec l r
instance haddDecidableAccept {P₁ : NFA α σ} {P₂ : NFA α σ'}
    [l : DecidablePred (· ∈ P₁.accept)]
    [r : DecidablePred (· ∈ P₂.accept)] :
    DecidablePred (· ∈ (P₁ + P₂).accept) := Sum.rec l r
instance haddDecidableStep {P₁ : NFA α σ} {P₂ : NFA α σ'}
    [l : ∀ q a, DecidablePred (· ∈ P₁.step q a)]
    [r : ∀ q a, DecidablePred (· ∈ P₂.step q a)] :
    ∀ q a, DecidablePred (· ∈ (P₁ + P₂).step q a)
  | .inl q, a => Sum.rec (l q a) (fun _ ↦ decidableFalse)
  | .inr q, a => Sum.rec (fun _ ↦ decidableFalse) (r q a)

@[simp]
theorem hadd_correct (P₁ : NFA α σ) (P₂ : NFA α σ') :
    (P₁ + P₂).accepts = P₁.accepts + P₂.accepts := by
  ext x
  constructor
  · rintro ⟨q | q, accept, eval⟩ <;>
    · first
      | left; exists q
      | right; exists q
      refine ⟨accept, ?_⟩
      clear accept
      induction x using List.reverseRecOn generalizing q
      · exact eval
      rename_i as a ih
      unfold NFA.eval NFA.evalFrom at *
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, NFA.mem_stepSet] at *
      rcases eval with ⟨p, mem, step⟩
      rcases p with p | p <;>
        first | exact ⟨p, ih p mem, step⟩ | cases step
  · rintro (hx | hx) <;>
    · rw [NFA.mem_accepts] at *
      unfold NFA.eval NFA.evalFrom at *
      rcases hx with ⟨q, accept, eval⟩
      first | exists Sum.inl q | exists Sum.inr q
      refine' ⟨accept, _⟩; clear accept
      induction x using List.reverseRecOn generalizing q
      · exact eval
      rename_i as a ih
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, NFA.mem_stepSet] at *
      rcases eval with ⟨p, mem, step⟩
      first | exists Sum.inl p | exists Sum.inr p
      exact ⟨ih p mem, step⟩

instance : HMul (NFA α σ) (NFA α σ') (NFA α (σ ⊕ σ')) :=
  ⟨fun P₁ P₂ ↦
    ⟨fun p c q ↦
      match (p, q) with
      | (Sum.inl p, Sum.inl q) => P₁.step p c q
      | (Sum.inl p, Sum.inr q) => P₂.start q ∧ ∃ r, P₁.accept r ∧ P₁.step p c r
      | (Sum.inr p, Sum.inr q) => P₂.step p c q
      | _ => False,
      fun q ↦
      match q with
      | Sum.inl q => P₁.start q
      | Sum.inr q => P₂.start q ∧ ∃ p, P₁.accept p ∧ P₁.start p,
      fun q ↦
      match q with
      | Sum.inl q => P₁.accept q ∧ ∃ p, P₂.accept p ∧ P₂.start p
      | Sum.inr q => P₂.accept q⟩⟩

instance hmulDecidableStart {P₁ : NFA α σ} {P₂ : NFA α σ'}
    [Fintype σ]
    [L : DecidablePred (· ∈ P₁.accept)]
    [l : DecidablePred (· ∈ P₁.start)]
    [r : DecidablePred (· ∈ P₂.start)] :
    DecidablePred (· ∈ (P₁ * P₂).start) :=
  Sum.rec
    l
    (fun q ↦ @And.decidable _ _ (r q) <|
      @Fintype.decidableExistsFintype _ _ (fun p ↦ @And.decidable _ _ (L p) (l p)) _)
instance hmulDecidableAccept {P₁ : NFA α σ} {P₂ : NFA α σ'}
    [Fintype σ']
    [l : DecidablePred (· ∈ P₁.accept)]
    [R : DecidablePred (· ∈ P₂.start)]
    [r : DecidablePred (· ∈ P₂.accept)] :
    DecidablePred (· ∈ (P₁ * P₂).accept) :=
  Sum.rec
    (fun q ↦ @And.decidable _ _ (l q) <|
      @Fintype.decidableExistsFintype _ _ (fun p ↦ @And.decidable _ _ (r p) (R p)) _)
    r
instance hmulDecidableStep {P₁ : NFA α σ} {P₂ : NFA α σ'}
    [Fintype σ]
    [DecidablePred (· ∈ P₁.accept)]
    [l : ∀ q a, DecidablePred (· ∈ P₁.step q a)]
    [R : DecidablePred (· ∈ P₂.start)]
    [r : ∀ q a, DecidablePred (· ∈ P₂.step q a)] :
    ∀ q a, DecidablePred (· ∈ (P₁ * P₂).step q a)
  | .inl q, a => Sum.rec (l q a) <| by
    intro p
    have : Decidable (∃ r : σ, r ∈ P₁.accept ∧ P₁.step q a r) :=
      haveI : DecidablePred fun r : σ ↦ r ∈ P₁.accept ∧ P₁.step q a r := by
        intro r
        have : Decidable (P₁.step q a r) := l q a r
        exact And.decidable
      Fintype.decidableExistsFintype
    exact @And.decidable _ _ (R p) this
  | .inr q, a => Sum.rec (fun _ ↦ decidableFalse) (r q a)

lemma hmul_eval₁ {P₁ : NFA α σ} {P₂ : NFA α σ'} {x : List α} (q : σ) :
    q ∈ P₁.eval x ↔ Sum.inl q ∈ (P₁ * P₂).eval x := by
  induction x using List.reverseRecOn generalizing q
  · exact ⟨id, id⟩
  rename_i as a ih
  constructor <;> simp only [NFA.eval_append_singleton, NFA.mem_stepSet] <;> rintro ⟨p, eval, step⟩
  · rw [ih p] at eval
    exact ⟨Sum.inl p, eval, step⟩
  · rcases p with p | p
    case inl => rw [← ih p] at eval; exact ⟨p, eval, step⟩
    case inr => cases step

lemma hmul_eval₂ {P₁ : NFA α σ} {P₂ : NFA α σ'} {x y : List α} (q : σ')
    (accepts : P₁.accepts x) :
    q ∈ P₂.eval y →
    Sum.inr q ∈ (P₁ * P₂).evalFrom ((P₁ * P₂).eval x) y := by
  induction y using List.reverseRecOn generalizing q
  · intro h
    rcases accepts with ⟨p, accept, eval⟩
    rw [hmul_eval₁ p] at eval
    rcases x.eq_nil_or_concat with eq | ⟨as, a, eq⟩ <;> subst eq
    case inl => exact ⟨h, p, accept, eval⟩
    rw [NFA.evalFrom_nil]
    rw [NFA.eval_append_singleton, NFA.mem_stepSet] at *
    rcases eval with ⟨r, mem, step⟩
    refine' ⟨r, mem, _⟩
    cases r
    case inl => exact ⟨h, p, accept, step⟩
    case inr => cases step
  · rename_i bs b ih
    simp only [NFA.eval_append_singleton, NFA.evalFrom_append_singleton, NFA.mem_stepSet]
    rintro ⟨p, mem, step⟩
    exact ⟨Sum.inr p, ih p mem, step⟩

@[simp]
theorem hmul_correct (P₁ : NFA α σ) (P₂ : NFA α σ') :
    (P₁ * P₂).accepts = P₁.accepts * P₂.accepts := by
  ext x
  constructor
  · rintro ⟨q | q, accept, eval⟩
    · rcases accept with ⟨accept, nil⟩
      refine ⟨x, ?_, [], ?_, by simp⟩
      · refine ⟨q, accept, ?_⟩
        clear accept
        induction x using List.reverseRecOn generalizing q
        · exact eval
        rename_i as a ih
        unfold NFA.eval NFA.evalFrom at *
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, NFA.mem_stepSet] at *
        rcases eval with ⟨p | p, mem, step⟩
        · exact ⟨p, ih p mem, step⟩
        · cases step
      · rcases nil with ⟨q, accept, eval⟩
        exact ⟨q, accept, eval⟩
    · suffices ∃ y z, y ∈ P₁.accepts ∧ q ∈ P₂.eval z ∧ y ++ z = x by
        rcases this with ⟨y, z, y_accepts, z_eval, append⟩
        exact ⟨y, y_accepts, z, ⟨q, accept, z_eval⟩, append⟩
      clear accept
      induction x using List.reverseRecOn generalizing q
      · rcases eval with ⟨start, _⟩; exact ⟨[], [], by simpa, start, rfl⟩
      rename_i as a ih
      unfold NFA.eval NFA.evalFrom
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at eval
      rcases eval with ⟨p | p, mem, step⟩
      · rcases step with ⟨start, r, accept, step⟩
        refine ⟨as ++ [a], [], ⟨r, accept, ?_⟩, start, by simp⟩
        rw [NFA.eval_append_singleton, NFA.mem_stepSet]
        rw [← hmul_eval₁ p] at mem
        exact ⟨p, mem, step⟩
      · rcases ih p mem with ⟨y, z, accepts, eval, append⟩
        refine ⟨y, z ++ [a], accepts, ?_, by simp [← append]⟩
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, NFA.mem_stepSet]
        exact ⟨p, eval, step⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    rcases z.eq_nil_or_concat with rfl | ⟨bs, b, rfl⟩
    · rcases hy with ⟨q, q_accept, q_eval⟩
      simp only [List.append_nil, NFA.eval_nil, List.reverse_nil] at *
      rw [hmul_eval₁ q] at q_eval
      exact ⟨Sum.inl q, ⟨q_accept, hz⟩, q_eval⟩
    · rcases hz with ⟨q, accept, eval⟩
      refine ⟨Sum.inr q, accept, ?_⟩
      simp only [← List.append_assoc]
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at *
      rcases eval with ⟨p, mem, step⟩
      refine ⟨Sum.inr p, ?_, step⟩
      unfold NFA.eval NFA.evalFrom
      rw [List.foldl_append]
      exact hmul_eval₂ p hy mem

/-- Kleene-starring adds a state and there is no heterogeneous `KStar` class, so we fall back to
a function definition. -/
def kstar (P : NFA α σ) : (NFA α (Option σ)) :=
  ⟨fun p c q ↦
    match (p, q) with
    | (some p, some q) => P.step p c q ∨ ∃ r, P.accept r ∧ P.step p c r ∧ P.start q
    | _ => False,
    fun q ↦
    match q with
    | some q => P.start q
    | none => True,
    fun q ↦
    match q with
    | some q => P.accept q
    | none => True⟩

instance kstarDecidableStart {P : NFA α σ}
    [i : DecidablePred (· ∈ P.start)] :
    DecidablePred (· ∈ P.kstar.start) := Option.rec decidableTrue i
instance kstarDecidableAccept {P : NFA α σ}
    [i : DecidablePred (· ∈ P.accept)] :
    DecidablePred (· ∈ P.kstar.accept) := Option.rec decidableTrue i
instance kstarDecidableStep {P : NFA α σ}
    [Fintype σ]
    [s : DecidablePred (· ∈ P.start)]
    [a : DecidablePred (· ∈ P.accept)]
    [i : ∀ q a, DecidablePred (· ∈ P.step q a) ] :
    ∀ q a, DecidablePred (· ∈ P.kstar.step q a)
  | .none, _ => fun _ ↦ decidableFalse
  | .some q, a => Option.rec decidableFalse <| by
    intro p
    have : Decidable (P.step q a p) := i q a p
    have :
      Decidable (∃ r_1 : σ, r_1 ∈ P.accept ∧ r_1 ∈ P.step q a ∧ p ∈ P.start) :=
      haveI :
        DecidablePred fun r_1 : σ ↦
          r_1 ∈ P.accept ∧ r_1 ∈ P.step q a ∧ p ∈ P.start := by
        intro s
        have : Decidable (s ∈ P.step q a ∧ p ∈ P.start) :=
          And.decidable
        exact And.decidable
      Fintype.decidableExistsFintype
    exact @Or.decidable _ _ _ this

/-- All start states of an unstarred NFA can be reached in a starred NFA by a string in the
original's language. -/
lemma kstar_eval_aux {P : NFA α σ} {y} (h : y ∈ P.accepts) :
    P.kstar.start \ {none} ⊆ P.kstar.eval y := by
  rintro (⟨⟩ | s) ⟨selem, snelem⟩
  · simp at snelem
  rcases y.eq_nil_or_concat with rfl | ⟨as, a, rfl⟩
  · exact selem
  simp [NFA.mem_accepts, NFA.mem_stepSet] at h
  rcases h with ⟨q, accept, p, eval, step⟩
  simp only [NFA.eval_append_singleton, NFA.mem_stepSet]
  refine ⟨some p, ?_, Or.inr ⟨q, accept, step, selem⟩⟩
  clear step
  induction as using List.reverseRecOn generalizing p
  · exact eval
  rename_i bs b ih
  simp only [NFA.evalFrom_append_singleton, NFA.mem_stepSet] at eval
  rcases eval with ⟨t, eval, step⟩
  simp only [NFA.eval_append_singleton, NFA.mem_stepSet]
  exact ⟨some t, ih t eval, Or.inl step⟩

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
    rw [NFA.eval_append_singleton,NFA.mem_stepSet]
    rintro ⟨⟨⟩ | p, eval, step⟩
    · cases step
    specialize ih eval
    rcases ih with ⟨ys, z, rfl, evalz, allys⟩
    rcases step with step | ⟨t, accept, step, start⟩
    · refine ⟨ys, z ++ [a], List.append_assoc _ _ _, ?_, allys⟩
      rw [NFA.eval_append_singleton, NFA.mem_stepSet]
      exact ⟨p, evalz, step⟩
    · refine ⟨ys ++ [z ++ [a]], [], by simp, start, ?_⟩
      refine List.forall_mem_append.mpr ⟨allys, List.forall_mem_singleton.mpr ⟨t, accept, ?_⟩⟩
      rw [NFA.eval_append_singleton, NFA.mem_stepSet]
      exact ⟨p, evalz, step⟩
  · rintro ⟨ys, z, rfl, eval, allys⟩
    unfold NFA.eval
    induction ys generalizing q
    · induction z using List.reverseRecOn generalizing q <;> simp
      · exact eval
      rename_i as a ih
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at eval
      rcases eval with ⟨t, eval, step⟩
      simp [NFA.mem_stepSet]
      refine ⟨some t, ih eval, Or.inl step⟩
    · rename_i y ys ih
      simp only [List.join, List.append_assoc]
      simp at allys
      rcases allys with ⟨accepty, allys⟩
      specialize ih eval allys
      generalize ys.join ++ z = ysj at ih
      rw [NFA.evalFrom_append]
      refine P.kstar.evalFrom_subset _ (kstar_eval_aux accepty) ?_
      clear eval
      induction ysj using List.reverseRecOn generalizing q
      · simp; exact ih
      rename_i as a iih
      simp only [NFA.evalFrom_append_singleton,NFA.mem_stepSet] at *
      rcases ih with ⟨⟨⟩ | t, eval, step⟩
      · simp[NFA.kstar, Set.mem_def] at step
      exact ⟨some t, iih eval, step⟩

theorem kstar_correct (P : NFA α σ) :
    P.kstar.accepts = P.accepts∗ := by
  ext x
  rw [Language.mem_kstar, NFA.mem_accepts]
  constructor
  · rintro ⟨⟨⟩ | q, accept, eval⟩
    · refine ⟨[], ?_, by simp⟩
      rcases x.eq_nil_or_concat with rfl | ⟨as, a, rfl⟩
      case inl => exact rfl
      simp [NFA.evalFrom_append_singleton, NFA.mem_stepSet] at eval
      rcases eval with ⟨_ | _, _, ⟨⟩⟩
    · rcases kstar_eval.mp eval with ⟨ys, z, rfl, evalz, allys⟩
      refine ⟨ys ++ [z], by simp, ?_⟩
      exact List.forall_mem_append.mpr ⟨allys, List.forall_mem_singleton.mpr ⟨q, accept, evalz⟩⟩
  · rintro ⟨l, rfl, h⟩
    rcases l.eq_nil_or_concat with rfl | ⟨ys, z, rfl⟩
    · exact ⟨none, trivial, trivial⟩
    · rw [List.forall_mem_append, List.forall_mem_singleton, NFA.mem_accepts] at h
      rcases h with ⟨allys, q, accept, eval⟩
      exact ⟨some q, accept, kstar_eval.mpr ⟨ys, z, by simp, eval, allys⟩⟩

end NFA

namespace DFA

/-- `M.toNFA` is an `NFA` constructed from a `DFA` `M` by using the same start and accept
  states and a transition function which sends `s` with input `a` to the singleton `M.step s a`. -/
@[simps] def toNFA (M : DFA α σ') : NFA α σ'
    where
  step s a := {M.step s a}
  start := {M.start}
  accept := M.accept
#align DFA.to_NFA DFA.toNFA

@[simp]
theorem toNFA_evalFrom_match (M : DFA α σ) (start : σ) (s : List α) :
    M.toNFA.evalFrom {start} s = {M.evalFrom start s} := by
  change List.foldl M.toNFA.stepSet {start} s = {List.foldl M.step start s}
  induction' s with a s ih generalizing start
  · tauto
  · rw [List.foldl, List.foldl,
      show M.toNFA.stepSet {start} a = {M.step start a} by simp [NFA.stepSet] ]
    tauto
#align DFA.to_NFA_eval_from_match DFA.toNFA_evalFrom_match

@[simp]
theorem toNFA_correct (M : DFA α σ) : M.toNFA.accepts = M.accepts := by
  ext x
  rw [NFA.mem_accepts, toNFA_start, toNFA_evalFrom_match]
  constructor
  · rintro ⟨S, hS₁, hS₂⟩
    rwa [Set.mem_singleton_iff.mp hS₂] at hS₁
  · exact fun h => ⟨M.eval x, h, rfl⟩
#align DFA.to_NFA_correct DFA.toNFA_correct

end DFA
