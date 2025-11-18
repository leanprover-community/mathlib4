/-
Copyright (c) 2022 Russell Emerine, 2024 Tom Kranz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Russell Emerine, Tom Kranz
-/
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.FinEnum.Option

/-!
# Generalized Nondeterministic Finite Automata

This file contains the definition of a Generalized Nondeterministic Finite Automaton, a state
machine which determines whether a string (implemented as a `List` over an arbitrary alphabet) is in
a regular set by evaluating the string over its net of regular expressions. We show
that GNFA's are equivalent to `NFA`'s, and that GNFA's are equivalent to smaller GNFA's with a state
"ripped" out. Through this mechanism, we show that `NFA`'s are equivalent to `RegularExpression`s.

## References
E.g. [Michael Sipser's *Introduction to the Theory of Computation*, Lemma 1.32][zbMATH05595151]
-/


universe u v

/-- A GNFA is a set of `|σ| + 2` states and a transition function between two states. The transition
function takes the starting state (represented by `Option.none` in the first argument) or any
internal state (consistently represented by `Option.some`s) as the first state, and the accepting
state (represented by `Option.none` in the second argument) or any internal state as the second
state. There is a transition between *all* of these
combinations, in the form of a `RegularExpression`. When following a transition, some matching
prefix of the input string is taken. What would be a missing transition in ordinary automata can be
achieved by yielding a `RegularExpression` matching `∅`; canonically
`RegularExpression.zero`.
-/
-- Porting note: removed Fintype instance for σ as an argument
structure GNFA (α : Type u) (σ : Type v) where
  /-- Yields the regular expression (sub)strings have to match to transition from the first to the
  second argument state. `Option.none` in the first position signifies a transition originating in
  the start state, `Option.none` in the second position signifies a transition targetting the
  accept state. -/
  step : Option σ → Option σ → RegularExpression α

variable {α : Type u} {σ : Type v}

namespace GNFA

/-- The GNFA admitting only impassable transitions (and be it only from start to accept state)
will always be available. -/
instance : Inhabited (GNFA α σ) :=
  ⟨GNFA.mk fun _ _ ↦ 0⟩

/-- A `trace` of an internal state and a string of a GNFA represents the possibility of getting to
the state via transitions that match the elements of some partitioning of the string.
This can be interpreted as the `Set` of strings that reach a certain inner state;
i.e. its `Language`.
-/
inductive trace (M : GNFA α σ) : σ → Language α
  | start : ∀ {x} q, x ∈ (M.step none (some q)).matches' → M.trace q x
  | step : ∀ {x y z} p q,
    y ∈ M.trace p → z ∈ (M.step (some p) (some q)).matches' → x = y ++ z → M.trace q x

/--
An `accepts` of a string represents the possibility of getting to the accepting state of a GNFA via
transitions of the GNFA that match the elements of some partitioning of the string.
Since this is the definition of when a GNFA accepts
a string, this also is how the accepting language of a GNFA is described.
-/
inductive accepts (M : GNFA α σ) : Language α
  | start : ∀ {x}, x ∈ (M.step none none).matches' → M.accepts x
  | step : ∀ {x y z} q,
    y ∈ M.trace q → z ∈ (M.step (some q) none).matches' → x = y ++ z → M.accepts x

theorem accepts_eq_matches_step_of_IsEmpty [IsEmpty σ] (M : GNFA α σ) :
    M.accepts = (M.step none none).matches' :=
  Set.ext fun _ ↦ ⟨(·.casesOn id ‹IsEmpty σ›.elim), .start⟩

/-- "Rips" an internal state out of a GNFA, making it smaller by one without changing its accepting
language.

The idea is to patch the transitions between all the remaining pairs of states with an alternative
`RegularExpression` that describes all the words that could've passed from the source to the target
state via the ripped state.
The `RegularExpression.star` accounts for words requiring looping transitions on the ripped state.

This is implemented as always ripping the designated inner state `Option.none` from a state space
that is already an `Option` over the state space of the result GNFA.
-/
def rip (M : GNFA α (Option σ)) : GNFA α σ :=
  ⟨fun p q ↦
    -- if start state is queried, don't layer on another some
    let p := p.map some
    -- if accept state is queried, don't layer on another some
    let q := q.map some
    -- the ripped state is always the none element in the original state space
    let r : Option (Option σ) := some none
    M.step p q + M.step p r * (M.step r r).star * M.step r q⟩

/-- Given a GNFA that's about to have a state `rip`ped, any word that reaches any internal state
will also reach that state after ripping if the state was not the ripped one.
Otherwise, the string can be partitioned into three substrings:
One that reaches some other state, one that could've moved on to the ripped state
before ripping and one that could've travelled arbitrarily many loops on the ripped state.
-/
lemma rip_trace_aux (M : GNFA α (Option σ)) {w q} (hwt : w ∈ M.trace q) :
    match q with
    | some p => w ∈ M.rip.trace p
    | none => ∃ (y z : _) (ws : List (List α)) (p : Option σ),
      p.elim (y = []) (y ∈ M.rip.trace ·) ∧
      z ∈ (M.step (p.map some) (some none)).matches' ∧
      (∀ w ∈ ws, w ∈ (M.step (some none) (some none)).matches') ∧
      w = y ++ z ++ ws.flatten := by
  refine hwt.recOn ?_ ?_
  · rintro x (⟨⟩ | q) mat
    · exact ⟨[], x, [], none, rfl, mat, List.forall_mem_nil _, by simp⟩
    · exact trace.start q (.inl mat)
  · rintro _ y z (⟨⟩ | p) (⟨⟩ | q) hyt mat rfl ih
    · rcases ih with ⟨y, z', xs, p, hyt', mat', loop, rfl⟩
      refine ⟨y, z', xs ++ [z], p, hyt', mat', ?_, by simp⟩
      rw [xs.forall_mem_append, List.forall_mem_singleton]
      exact ⟨loop, mat⟩
    · rcases ih with ⟨y, z', xs, ⟨⟩ | p, hyt', mat', loop, rfl⟩
      · subst y
        refine trace.start q <| .inr ?_
        simp only [List.nil_append, List.append_assoc, Option.map_none', Option.map_some',
          RegularExpression.matches'_mul, RegularExpression.matches'_star]
        rw [← List.append_assoc]
        exact ⟨z' ++ xs.flatten, ⟨z', mat', xs.flatten, ⟨xs, rfl, loop⟩, rfl⟩, z, mat, rfl⟩
      · simp only [List.append_assoc]
        refine trace.step _ q hyt' (.inr ?_) rfl
        rw [← List.append_assoc]
        exact ⟨z' ++ xs.flatten, ⟨z', mat', xs.flatten, ⟨xs, rfl, loop⟩, rfl⟩, z, mat, rfl⟩
    · exact ⟨y, z, [], some p, ih, mat, List.forall_mem_nil _, by simp⟩
    · exact trace.step p q ih (.inl mat) rfl

/-- Ripping a state preserves the languages of all the remaining internal states. -/
theorem rip_trace_eq_trace_some (M : GNFA α (Option σ)) {q : σ} :
    M.rip.trace q = M.trace (some q) := by
  ext
  refine ⟨?_, M.rip_trace_aux⟩
  intro hxt'
  refine hxt'.recOn ?_ ?_
  · rintro x q (hx | ⟨y, hy, z, hz, rfl⟩)
    · exact trace.start (some q) hx
    refine trace.step none (some q) ?_ hz rfl
    rcases hy with ⟨y, hy, z, ⟨xs, rfl, hxs⟩, rfl⟩
    induction xs using List.reverseRecOn
    · simp; exact trace.start none hy
    rename_i xs x ih
    rw [List.flatten_append, List.flatten_singleton]
    simp only [← List.append_assoc]
    refine trace.step none none (ih ?_) (hxs x (by simp)) rfl
    intro y mem
    exact hxs y (by simp[mem])
  · rintro x y z p q _ (hz | ⟨w, hw, x, hx, rfl⟩) rfl ih
    · exact trace.step (some p) (some q) ih hz rfl
    rw [← List.append_assoc]
    refine trace.step none (some q) ?_ hx rfl
    rcases hw with ⟨w, hw, x, hx, rfl⟩
    rw [← List.append_assoc]
    rcases hx with ⟨xs, rfl, loop⟩
    induction xs using List.reverseRecOn
    · exact trace.step (some p) none ih hw (by simp)
    rename_i xs x ih
    rw [List.flatten_append, List.flatten_singleton, ← List.append_assoc]
    refine trace.step none none (ih ?_) (loop x (by simp)) rfl
    intro y mem
    exact loop y (by simp[mem])

/-- Ripping a state preserves the language of a GNFA. -/
-- TODO: maybe mark as @simp
theorem rip_spec (M : GNFA α (Option σ)) : M.rip.accepts = M.accepts := by
  ext w
  constructor
  · rintro (hw | ⟨q, hyt, hz, rfl⟩)
    · rcases hw with hw | ⟨_, ⟨x, hx, _, ⟨ys, rfl, loop⟩, rfl⟩, z, hz, rfl⟩
      · exact accepts.start hw
      refine accepts.step _ ?_ hz rfl
      induction ys using List.reverseRecOn
      · exact trace.start none (by simpa)
      rename_i ys y ih
      rw [List.flatten_append, List.flatten_singleton]
      simp only [← List.append_assoc]
      refine trace.step none none (ih ?_) (loop y (by simp)) rfl
      intro y mem
      exact loop y (by simp[mem])
    · rcases hz with hz | ⟨_, ⟨x, hx, _, ⟨ys, rfl, loop⟩, rfl⟩, z, hz, rfl⟩
      · exact accepts.step (some q) (M.rip_trace_eq_trace_some ▸ hyt) hz rfl
      rw [← List.append_assoc]
      refine accepts.step none ?_ hz rfl
      rw [← List.append_assoc]
      induction ys using List.reverseRecOn
      · simp; exact trace.step (some q) none (M.rip_trace_eq_trace_some ▸ hyt) hx rfl
      rename_i ys y ih
      rw [List.flatten_append, List.flatten_singleton]
      rw [← List.append_assoc]
      simp only [List.mem_append] at loop
      refine trace.step none none (ih ?_) (loop y (by simp)) rfl
      intro y mem
      exact loop y (.inl mem)
  · rintro (hw | ⟨q, hyt, hz, rfl⟩)
    · exact accepts.start (.inl hw)
    rcases q with ⟨⟩ | q
    · rcases M.rip_trace_aux hyt with ⟨y, _, xs, ⟨⟩ | p, hyt', hz', loop, rfl⟩
      · subst y
        refine accepts.start <| .inr ?_
        exact ⟨_, ⟨_, hz', _, ⟨xs, rfl, loop⟩, rfl⟩, _, hz, rfl⟩
      · rw [List.append_assoc, List.append_assoc]
        refine accepts.step p hyt' (.inr ?_) rfl
        rw [← List.append_assoc]
        exact ⟨_, ⟨_, hz', _, ⟨xs, rfl, loop⟩, rfl⟩, _, hz, rfl⟩
    · exact accepts.step q (M.rip_trace_aux hyt) (.inl hz) rfl

/-- Maps a GNFA's states across an equivalence.
-/
def mapEquiv {σ τ} (M : GNFA α σ) (e : σ ≃ τ) : GNFA α τ :=
  ⟨fun p q ↦ M.step (p.map e.symm) (q.map e.symm)⟩

/-- Any string that reaches a state in one GNFA will also reach the equivalent state in the
equivalent GNFA -/
lemma mapEquiv_trace_aux {σ τ} (M : GNFA α σ) (e : σ ≃ τ) q :
    M.trace q ≤ (M.mapEquiv e).trace (e q) := by
  intro x hxt
  refine hxt.recOn
    (fun _ mat ↦ trace.start _ ?_)
    (fun p q _ mat eq ih ↦ trace.step (e p) (e q) ih ?_ eq) <;>
  · unfold mapEquiv
    dsimp
    simp only [Equiv.symm_apply_apply]
    exact mat

/-- A GNFA's equivalent will retain any internal (equivalent) state's language. -/
theorem mapEquiv_trace_equiv_eq_trace {σ τ} (M : GNFA α σ) (e : σ ≃ τ) q :
    (M.mapEquiv e).trace (e q) = M.trace q  := by
  ext
  refine ⟨?_, (M.mapEquiv_trace_aux e q ·)⟩
  intro hxt
  have := (M.mapEquiv e).mapEquiv_trace_aux e.symm (e q) hxt
  simp [Equiv.symm_apply_apply, mapEquiv] at this
  exact this

/-- Any string that reaches the accept state in one GNFA will also reach the accept state in the
equivalent GNFA -/
lemma mapEquiv_spec_mpr {σ τ} (M : GNFA α σ) (e : σ ≃ τ) :
    M.accepts ≤ (M.mapEquiv e).accepts := by
  rintro w (hw | ⟨q, hyt, hz, rfl⟩)
  · exact accepts.start hw
  refine accepts.step (e q) (M.mapEquiv_trace_equiv_eq_trace e q ▸ hyt) ?_ rfl
  unfold mapEquiv
  simpa

/-- A GNFA's equivalent will retain the original's language. -/
theorem mapEquiv_spec {σ τ} (M : GNFA α σ) (e : σ ≃ τ) :
    (M.mapEquiv e).accepts = M.accepts := by
  ext
  refine ⟨?_, (M.mapEquiv_spec_mpr e ·)⟩
  intro h
  have := (M.mapEquiv e).mapEquiv_spec_mpr e.symm h
  simp [mapEquiv] at this
  exact this

/-- For a GNFA with a `FinEnum` state space, each `rip`ping traversal of that space potentially
yields a different `RegularExpression`, though each of them matches its accepted language. -/
def toRegularExpression [FinEnum σ] (rip_choice := Fin.last) :
    (M : GNFA α σ) → { r : RegularExpression α // r.matches' = M.accepts } :=
  ‹FinEnum σ›.recOnEmptyOption
    (P := (∀ M : GNFA α ·, { r : RegularExpression α // r.matches' = M.accepts }))
    rip_choice
    (fun e₁ e₂ hc ih M ↦
      let eq := (hc ▸ e₂.equiv).trans e₁.equiv.symm
      let ⟨r, hr⟩ := ih <| M.mapEquiv eq
      ⟨r, hr ▸ M.mapEquiv_spec eq⟩)
    (fun M ↦ ⟨M.step none none, M.accepts_eq_matches_step_of_IsEmpty.symm⟩)
    (fun _ ih M ↦ let ⟨r, hr⟩ := ih M.rip; ⟨r, hr.trans M.rip_spec⟩)

end GNFA

