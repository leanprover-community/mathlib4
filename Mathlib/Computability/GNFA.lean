/-
Copyright (c) 2022 Russell Emerine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Russell Emerine
-/
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.NFA
import Mathlib.Data.Fintype.Option

#align_import computability.GNFA

/-!
# Generalized Nondeterministic Finite Automata

This file contains the definition of a Generalized Nondeterministic Finite Automaton, a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in
a regular set by evaluating the string over every possible series of regular expressions. We show 
that GNFA's are equivalent to NFA's, and that GNFA's are equivalent to smaller GNFA's with a state
"ripped" out. Through this mechanism, we show that NFA's are equivalent to regular expressions.
Unlike for DFA's and NFA's, GNFA's can only be made with a `fin` as the state type.

## References

TODO: someone please tell me how to best cite this file?
* <https://courses.engr.illinois.edu/cs373/sp2013/Lectures/lec07.pdf>
-/


universe u v

/-- A GNFA is a set of `n + 2` states and a transition function between two states. The transition
function takes the starting state or any internal state as the first state, and the accepting
state or any internal state as the second state. There is a transition between *all* of these
combinations, in the form of a regular expression. When following a transition, some matching
prefix of the input string is taken. "No transition" can be simulated by using the regular
expression `0`, which accepts no strings.
-/
structure GNFA (α : Type u) (σ : Type v) [Fintype σ] where
  step : Option σ → Option σ → RegularExpression α

variable {α : Type u} {σ : Type v} [Fintype σ]

namespace RegularExpression

/-- A string matches the sum of a list of regular expressions if and only if there is some regular
expression in the list that it matches. This is because the sum of regular expressions matches the
union of their respective languages.

TODO: probably move to computability/regular_expression
-/
theorem mem_sum_iff_exists_mem (x : List α) (rs : List (RegularExpression α)) :
    (List.sum rs).matches' x ↔ ∃ r : RegularExpression α, r ∈ rs ∧ r.matches' x :=
  by
  constructor
  · rw [← rs.reverse_reverse]
    induction rs.reverse
    case nil => rintro ⟨⟩
    case cons r rs ih =>
      intro hx
      unfold List.sum at hx
      simp only [List.reverse_cons, RegularExpression.matches'_add, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.mem_append, List.mem_singleton] at *
      cases hx
      case inl => rcases ih hx with ⟨r, mem, matches⟩; exact ⟨r, Or.inl mem, matches⟩
      case inr => exact ⟨r, Or.inr rfl, hx⟩
  · rw [← rs.reverse_reverse]
    induction' rs.reverse with r rs ih
    case nil =>
      rintro ⟨r, mem, _⟩
      exfalso
      simpa
    intro hx
    unfold List.sum
    simp only [List.reverse_cons, RegularExpression.matches'_add, forall_exists_index,
      List.foldl_append, List.foldl_cons, List.foldl_nil, List.mem_append, List.mem_singleton] at *
    rcases hx with ⟨r', hr', matches⟩
    cases hr'
    case inl =>
      left
      exact ih r' ⟨hr', matches⟩
    case inr =>
      right
      rw [hr'] at matches
      exact matches

end RegularExpression

namespace GNFA

instance : Inhabited (GNFA α σ) :=
  ⟨GNFA.mk fun _ _ => 0⟩

/-- A `trace` of a string and an internal state of a GNFA represents a way to get to the state via
transitions of the GNFA that match parts of the string.
-/
inductive Trace (M : GNFA α σ) : List α → σ → Prop
  | start : ∀ {x q}, x ∈ (M.step none (some q)).matches' → trace x q
  |
  step : ∀ {x y z p q}, trace y p → z ∈ (M.step (some p) (some q)).matches' → x = y ++ z → trace x q

/--
An `accepts` of a string represents a way to get to the accepting state of a GNFA via transitions
of the GNFA that match parts of the string. Since this is the definition of when a GNFA accepts
a string, this also is how the accepting language of a GNFA is described.

TODO: make description clearer
-/
inductive accepts (M : GNFA α σ) : Language α
  | start : ∀ {x}, x ∈ (M.step none none).matches' → accepts x
  | step : ∀ {x y z} (q), M.trace y q → z ∈ (M.step (some q) none).matches' → x = y ++ z → accepts x

/-- "Rips" an internal state out of a GNFA, making it smaller by one without changing its accepting
language.
-/
def rip (M : GNFA α (Option σ)) : GNFA α σ :=
  ⟨fun p q =>
    let p := p.map some
    let q := q.map some
    let r : Option (Option σ) := some none
    M.step p q + M.step p r * (M.step r r).unit * M.step r q⟩

theorem rip_trace_aux (M : GNFA α (Option σ)) {x q} (t : M.trace x q) :
    (∃ p, q = some p ∧ M.rip.trace x p) ∨
      q = none ∧
        ∃ (y z : _) (xs : List (List α)) (p : Option σ),
          (Option.map (M.rip.trace y) p).getD (y = []) ∧
            z ∈ (M.step (Option.map some p) (some none)).matches' ∧
              (∀ x ∈ xs, x ∈ (M.step (some none) (some none)).matches') ∧ x = y ++ z ++ xs.join :=
  by
  induction t
  case start x q matches =>
    revert matches
    cases q
    case none =>
      intro matches
      right
      refine' ⟨rfl, _⟩
      refine' ⟨[], x, [], none, by dsimp <;> rfl, matches, _, by simp⟩
      intro x mem
      cases mem
    case some q =>
      intro matches
      left
      refine' ⟨q, rfl, _⟩
      exact trace.start (Or.inl matches)
  case step x y z p q t matches eq ih =>
    rw [Eq]; clear eq x
    revert ih matches
    cases' p with p <;> cases' q with q
    case none.none =>
      intro ih matches
      right
      refine' ⟨rfl, _⟩
      cases ih
      case inl =>
        rcases ih with ⟨p, eq, t⟩
        cases Eq
      rcases ih with ⟨_, y, z', xs, p, t', matches', x_matches, eq⟩
      rw [Eq]; clear eq
      refine' ⟨y, z', xs ++ [z], p, t', matches', _, by simp⟩
      intro x mem
      simp at mem
      cases mem
      case inl => exact x_matches x mem
      case inr => rw [mem]; exact matches
    case none.some =>
      intro ih matches
      left
      refine' ⟨q, rfl, _⟩
      cases ih
      case inl =>
        rcases ih with ⟨p, eq, t⟩
        cases Eq
      rcases ih with ⟨_, y, z', xs, p, t', matches', x_matches, eq⟩
      rw [Eq]; clear eq
      cases p
      case none =>
        simp at t'
        rw [t']; clear t' y
        refine' trace.start (Or.inr _)
        simp
        rw [← List.append_assoc]
        refine' ⟨_, _, _, matches, rfl⟩
        refine' ⟨_, _, matches', _, rfl⟩
        exact ⟨_, rfl, x_matches⟩
      case some =>
        simp at t'
        rw [List.append_assoc]
        rw [List.append_assoc]
        refine' trace.step t' _ rfl
        right
        rw [← List.append_assoc]
        refine' ⟨_, _, _, matches, rfl⟩
        refine' ⟨_, _, matches', _, rfl⟩
        exact ⟨_, rfl, x_matches⟩
    · intro ih matches
      right
      refine' ⟨rfl, _⟩
      cases ih
      case inl =>
        rcases ih with ⟨p', eq, t⟩
        simp at eq; rw [← Eq] at t; clear eq p'
        refine' ⟨y, z, [], some p, by simp [t], matches, _, by simp⟩
        intro x mem
        cases mem
      case inr =>
        rcases ih with ⟨eq, _⟩
        cases Eq
    · intro ih matches
      cases ih
      case inl =>
        rcases ih with ⟨p', eq, t⟩
        simp at eq; rw [← Eq] at t; clear eq p'
        left
        refine' ⟨q, rfl, _⟩
        exact trace.step t (Or.inl matches) rfl
      case inr =>
        rcases ih with ⟨eq, _⟩
        cases Eq

theorem rip_trace_correct (M : GNFA α (Option σ)) {x} {q : σ} :
    M.trace x (some q) ↔ M.rip.trace x q := by
  constructor
  · intro t
    cases M.rip_trace_aux t
    case inl =>
      rcases h with ⟨p, eq, t⟩
      simp at eq
      rw [Eq]
      exact t
    case inr =>
      cases' h with eq _
      cases Eq
  · intro t
    induction t
    case start x q matches =>
      cases matches
      case inl => exact trace.start matches
      rcases matches with ⟨y, z, hy, hz, eq⟩
      rw [← Eq]; clear eq x
      refine' trace.step _ hz rfl
      clear hz z
      rcases hy with ⟨y, z, hy, hz, eq⟩
      rw [← Eq]; clear eq
      rcases hz with ⟨xs, join, matches⟩
      rw [join]; clear join
      revert matches
      rw [← xs.reverse_reverse]
      induction xs.reverse
      case nil => simp [trace.start hy]
      case cons x xs ih =>
        intro matches
        rw [List.reverse_cons, List.join_append]
        unfold List.join
        rw [List.append_nil, ← List.append_assoc]
        simp only [List.mem_reverse, List.mem_cons] at matches
        refine' trace.step (ih _) (matches x (Or.inl rfl)) rfl
        intro y mem
        rw [List.mem_reverse] at mem
        exact matches y (Or.inr mem)
    case step x y z p q t matches eq ih =>
      cases matches
      case inl => exact trace.step ih matches Eq
      rw [Eq]; clear eq x
      rcases matches with ⟨w, x, hw, hx, eq⟩
      rw [← Eq]; clear eq z
      rw [← List.append_assoc]
      refine' trace.step _ hx rfl
      rcases hw with ⟨w, x, hw, hx, eq⟩
      rw [← Eq]; clear eq
      rw [← List.append_assoc]
      rcases hx with ⟨xs, join, matches⟩
      rw [join]; clear join x
      revert matches
      rw [← xs.reverse_reverse]
      induction xs.reverse
      case nil =>
        intro matches
        simp at *
        exact trace.step ih hw rfl
      case cons x xs ih =>
        intro matches
        rw [List.reverse_cons, List.join_append]
        unfold List.join
        rw [List.append_nil, ← List.append_assoc]
        simp only [List.mem_reverse, List.mem_cons] at matches
        refine' trace.step _ (matches x (Or.inl rfl)) rfl
        apply ih
        intro y mem
        rw [List.mem_reverse] at mem
        exact matches y (Or.inr mem)

-- TODO: maybe mark as @simp
theorem rip_correct (M : GNFA α (Option σ)) : M.rip.accepts = M.accepts :=
  by
  ext
  constructor
  · intro t
    cases t
    case start x matches =>
      cases matches
      case inl => exact accepts.start matches
      rcases matches with ⟨y, z, y_matches, z_matches, eq⟩
      rw [← Eq]; clear eq x
      refine' accepts.step _ _ z_matches rfl; clear z_matches z
      rcases y_matches with ⟨y, z, y_matches, z_matches, eq⟩
      rw [← Eq]; clear eq
      rcases z_matches with ⟨xs, join, x_matches⟩
      rw [join]; clear join z
      revert x_matches
      rw [← xs.reverse_reverse]
      induction xs.reverse
      case nil =>
        intro x_matches
        refine' trace.start _
        simpa
      case cons x xs ih =>
        intro x_matches
        rw [List.reverse_cons, List.join_append]
        unfold List.join
        rw [List.append_nil, ← List.append_assoc]
        simp only [List.mem_reverse, List.mem_cons] at x_matches
        refine' trace.step _ (x_matches x (Or.inl rfl)) rfl
        apply ih
        intro x mem
        rw [List.mem_reverse] at mem
        exact x_matches x (Or.inr mem)
    case step x y z q t matches eq =>
      rw [Eq]; clear eq x
      cases matches
      case inl =>
        refine' accepts.step _ _ matches rfl
        rw [rip_trace_correct]
        exact t
      rcases matches with ⟨z, x, z_matches, x_matches, eq⟩
      rw [← Eq]; clear eq
      rw [← List.append_assoc]
      refine' accepts.step _ _ x_matches rfl; clear x_matches x
      rcases z_matches with ⟨z, x, z_matches, x_matches, eq⟩
      rw [← Eq]; clear eq
      rw [← List.append_assoc]
      rcases x_matches with ⟨xs, join, x_matches⟩
      rw [join]; clear join x
      revert x_matches
      rw [← xs.reverse_reverse]
      induction xs.reverse
      case nil =>
        intro matches
        rw [List.reverse_nil]
        unfold List.join
        rw [List.append_nil]
        refine' trace.step _ z_matches rfl
        rw [rip_trace_correct]
        exact t
      case cons x xs ih =>
        intro matches
        rw [List.reverse_cons, List.join_append]
        unfold List.join
        rw [List.append_nil, ← List.append_assoc]
        simp only [List.mem_reverse, List.mem_cons] at matches
        refine' trace.step _ (matches x (Or.inl rfl)) rfl
        apply ih
        intro x mem
        rw [List.mem_reverse] at mem
        exact matches x (Or.inr mem)
  · intro t
    cases t
    case start x matches => exact accepts.start (Or.inl matches)
    case step x y z q t matches eq =>
      rw [Eq]; clear eq x
      cases M.rip_trace_aux t
      case inl =>
        rcases h with ⟨q, eq, t⟩
        rw [Eq] at matches; clear eq
        exact accepts.step _ t (Or.inl matches) rfl
      rcases h with ⟨eq, h⟩
      rw [Eq] at *; clear eq
      rcases h with ⟨y, w, xs, p, t, w_matches, x_matches, eq⟩
      rw [Eq]; clear eq
      cases p
      case none =>
        rw [Option.map_none', Option.getD_none] at t
        rw [t]; clear t y
        refine' accepts.start _
        right
        refine' ⟨_, _, _, matches, rfl⟩
        refine' ⟨_, _, w_matches, _, rfl⟩
        exact ⟨xs, rfl, x_matches⟩
      case some =>
        rw [Option.map_some', Option.getD_some] at t
        rw [List.append_assoc, List.append_assoc]
        refine' accepts.step _ t _ rfl
        right
        rw [← List.append_assoc]
        refine' ⟨_, _, _, matches, rfl⟩
        refine' ⟨_, _, w_matches, _, rfl⟩
        exact ⟨xs, rfl, x_matches⟩

/-- Maps a GNFA's states across an equivalence.
-/
def mapEquiv {σ τ} [Fintype σ] [Fintype τ] (M : GNFA α σ) (e : σ ≃ τ) : GNFA α τ :=
  ⟨fun p q => M.step (p.map e.symm) (q.map e.symm)⟩

theorem mapEquiv_trace_aux {σ τ} [Fintype σ] [Fintype τ] (M : GNFA α σ) (e : σ ≃ τ) :
    ∀ q x, M.trace x q → (M.mapEquiv e).trace x (e q) :=
  by
  intro q x t
  induction t
  case start x q matches =>
    apply trace.start
    unfold map_equiv
    dsimp
    rw [Equiv.symm_apply_apply]
    exact matches
  case step x y z p q t matches eq
    ih =>
    refine' trace.step ih _ Eq
    unfold map_equiv
    dsimp
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact matches

theorem mapEquiv_trace {σ τ} [Fintype σ] [Fintype τ] (M : GNFA α σ) (e : σ ≃ τ) :
    ∀ q x, M.trace x q ↔ (M.mapEquiv e).trace x (e q) :=
  by
  intro q x
  constructor
  · intro t
    exact M.map_equiv_trace_aux e q x t
  · intro t
    have := (M.map_equiv e).mapEquiv_trace_aux e.symm (e q) x t
    rw [Equiv.symm_apply_apply] at this
    unfold map_equiv at this
    simp at this
    cases M
    exact this

theorem mapEquiv_correct_aux {σ τ} [Fintype σ] [Fintype τ] (M : GNFA α σ) (e : σ ≃ τ) :
    M.accepts ≤ (M.mapEquiv e).accepts := by
  intro x t
  cases t
  case start x matches => exact accepts.start matches
  case step x y z q t matches eq =>
    refine' accepts.step _ _ _ Eq
    exact e q
    rw [M.map_equiv_trace e] at t
    exact t
    unfold map_equiv
    simpa

theorem mapEquiv_correct {σ τ} [Fintype σ] [Fintype τ] (M : GNFA α σ) (e : σ ≃ τ) :
    M.accepts = (M.mapEquiv e).accepts := by
  ext
  constructor
  · intro h
    exact M.map_equiv_correct_aux e h
  · intro h
    have := (M.map_equiv e).mapEquiv_correct_aux e.symm h
    unfold map_equiv at this
    simp at this
    cases M
    exact this

theorem exists_to_regularExpression :
    ∀ M : GNFA α σ, ∃ r : RegularExpression α, M.accepts = r.matches' :=
  by
  refine' Fintype.induction_empty_option _ _ _ σ
  · clear _inst_1 σ
    intro σ τ
    intro
    intro e h M
    let this.1 : Fintype σ := Fintype.ofEquiv _ e.symm
    specialize h (M.map_equiv e.symm)
    rcases h with ⟨r, hr⟩
    use r
    rw [← hr]
    exact M.map_equiv_correct e.symm
  · intro M
    use M.step none none
    ext
    constructor
    · intro t
      induction t
      case start x matches => exact matches
      case step _ _ _ empty => cases Empty
    · intro matches
      exact accepts.start matches
  · clear _inst_1 σ
    intro σ
    intro
    intro h M
    specialize h M.rip
    rcases h with ⟨r, hr⟩
    use r
    rw [rip_correct] at hr
    exact hr

end GNFA

namespace NFA

variable (M : NFA α σ) [dec_start : DecidablePred M.start] [dec_accept : DecidablePred M.accept]
  [dec_step : ∀ p a q, Decidable (M.step p a q)] (as : List α)

/-- Convert an NFA to the corresponding GNFA.

Note: needs decidability for each of the NFA's functions, and a list of all the elements of the
alphabet.

TODO: would it be a good idea to make a separate "decidable NFA" structure?
-/
def toGNFA : GNFA α σ :=
  ⟨fun p q =>
    match (p, q) with
    | (none, none) => 0
    | (none, some q) => if M.start q then 1 else 0
    | (some p, none) => if M.accept p then 1 else 0
    | (some p, some q) =>
      List.sum <|
        (List.map fun a => RegularExpression.char a) <| List.filter (fun a => M.step p a q) as⟩

-- TODO: maybe mark as @simp
theorem toGNFA_correct (univ : ∀ a, a ∈ as) : M.accepts = (M.toGNFA as).accepts :=
  by
  ext
  constructor
  · rintro ⟨q, accept, eval⟩
    refine' GNFA.accepts.step q _ _ x.append_nil.symm
    swap
    · unfold to_GNFA; simp only; unfold to_GNFA._match_1
      rw [Set.mem_def] at accept
      simp [accept]
    clear accept
    revert eval
    rw [← x.reverse_reverse]
    induction x.reverse generalizing q
    case nil =>
      intro hx
      refine' GNFA.Trace.start _
      unfold to_GNFA; simp only; unfold to_GNFA._match_1
      rw [Set.mem_def, List.reverse_nil, NFA.eval_nil] at hx
      simp [hx]
    case cons a as ih =>
      intro hx
      rw [List.reverse_cons] at *
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hx
      rcases hx with ⟨p, mem, step⟩
      refine' GNFA.Trace.step (ih p mem) _ rfl
      rw [Set.mem_def]
      unfold to_GNFA; simp only; unfold to_GNFA._match_1
      rw [RegularExpression.mem_sum_iff_exists_mem]
      refine' ⟨RegularExpression.char a, _, rfl⟩
      simpa [univ]
  · intro hx
    cases' hx with x step x y z q t step eq
    case start => cases step
    unfold to_GNFA at step; simp only at step; unfold to_GNFA._match_1 at step
    by_cases M.accept q; swap; simp [h] at step; contradiction
    simp [h] at step
    cases step; clear step
    refine' ⟨q, h, _⟩
    rw [List.append_nil] at eq; cases Eq; clear h eq
    revert t
    rw [← x.reverse_reverse]
    induction x.reverse generalizing q
    case nil =>
      intro hx
      rw [List.reverse_nil] at *
      rw [NFA.eval_nil]
      cases hx
      case start x step =>
        unfold to_GNFA at step; simp only at step; unfold to_GNFA._match_1 at step
        by_cases M.start x
        · exact h
        · simp [h] at step
          contradiction
      case step x y z p t step eq =>
        rw [List.nil_eq_append] at eq
        cases Eq.2; clear eq _x t x x
        unfold to_GNFA at step; simp only at step; unfold to_GNFA._match_1 at step
        rw [Set.mem_def, RegularExpression.mem_sum_iff_exists_mem] at step
        rcases step with ⟨r, mem, matches⟩
        rw [List.mem_map] at mem
        rcases mem with ⟨a, _, eq⟩
        rw [← Eq] at matches
        cases matches
    case cons a as ih =>
      intro hx
      simp at *
      rw [NFA.mem_stepSet]
      cases hx
      case start q step =>
        unfold to_GNFA at step; simp only at step; unfold to_GNFA._match_1 at step
        by_cases M.start q
        · rw [if_pos h, RegularExpression.matches'_epsilon, Language.mem_one] at step
          replace step : as.reverse ++ [a] = List.nil := step
          rw [List.append_eq_nil] at step
          cases step.2
        · rw [if_neg h] at step
          cases step
      case step y z p q t step eq =>
        unfold to_GNFA at step; simp at step; unfold to_GNFA._match_1 at step
        replace eq : as.reverse ++ [a] = y ++ z := Eq
        rw [Set.mem_def, RegularExpression.mem_sum_iff_exists_mem] at step
        rcases step with ⟨r, mem, matches⟩
        simp only [List.mem_map, List.mem_filter] at mem
        rcases mem with ⟨b, ⟨_, step⟩, eq⟩
        rw [← Eq] at matches
        cases matches
        rw [← List.reverse_inj] at eq
        simp only [List.reverse_append, List.reverse_singleton, List.reverse_reverse,
          List.singleton_append] at eq
        cases Eq.1; clear _x
        cases Eq.2; clear eq _x
        refine' ⟨p, _, step⟩
        rw [← y.reverse_reverse] at t
        exact ih p t

/--
Given an NFA with a `fintype` state, there is a regular expression that matches the same language.
-/
theorem exists_to_regularExpression {σ} [Finite α] [Finite σ] (M : NFA α σ) :
    ∃ r : RegularExpression α, M.accepts = r.matches' := by
  classical
  rcases Finite.exists_univ_list α with ⟨as, _, univ⟩
  cases nonempty_fintype σ
  rcases(M.to_GNFA as).exists_to_regularExpression with ⟨r, hr⟩
  use r
  rw [← hr]
  exact M.to_GNFA_correct as univ

/-- Noncomputably finds the regular expression equivalent to the NFA.
-/
noncomputable def toRegularExpression [Fintype α] (M : NFA α σ) : RegularExpression α :=
  Classical.choose M.exists_to_regularExpression

theorem toRegularExpression_correct [Fintype α] (M : NFA α σ) :
    M.accepts = M.toRegularExpression.matches' :=
  Classical.choose_spec M.exists_to_regularExpression

end NFA

