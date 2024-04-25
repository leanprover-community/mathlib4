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
-- Porting note: removed Fintype instance for σ as an argument
structure GNFA (α : Type u) (σ : Type v) where
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
      case inl hx => rcases ih hx with ⟨r, mem, mat⟩; exact ⟨r, Or.inl mem, mat⟩
      case inr hx => exact ⟨r, Or.inr rfl, hx⟩
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
    rcases hx with ⟨r', hr', mat⟩
    cases hr'
    case inl hr' =>
      left
      exact ih r' ⟨hr', mat⟩
    case inr hr' =>
      right
      rw [hr'] at mat
      exact mat

end RegularExpression

namespace GNFA

instance : Inhabited (GNFA α σ) :=
  ⟨GNFA.mk fun _ _ => 0⟩

/-- A `trace` of a string and an internal state of a GNFA represents a way to get to the state via
transitions of the GNFA that match parts of the string.
-/
inductive trace (M : GNFA α σ) : List α → σ → Prop
  | start : ∀ {x q}, x ∈ (M.step none (some q)).matches' → M.trace x q
  |
  step : ∀ {x y z p q}, M.trace y p → z ∈ (M.step (some p) (some q)).matches' → x = y ++ z → M.trace x q

/--
An `accepts` of a string represents a way to get to the accepting state of a GNFA via transitions
of the GNFA that match parts of the string. Since this is the definition of when a GNFA accepts
a string, this also is how the accepting language of a GNFA is described.

TODO: make description clearer
-/
inductive accepts (M : GNFA α σ) : Language α
  | start : ∀ {x}, x ∈ (M.step none none).matches' → M.accepts x
  | step : ∀ {x y z} (q), M.trace y q → z ∈ (M.step (some q) none).matches' → x = y ++ z → M.accepts x

/-- "Rips" an internal state out of a GNFA, making it smaller by one without changing its accepting
language.
-/
def rip (M : GNFA α (Option σ)) : GNFA α σ :=
  ⟨fun p q =>
    let p := p.map some
    let q := q.map some
    let r : Option (Option σ) := some none
    M.step p q + M.step p r * (M.step r r).star * M.step r q⟩

theorem rip_trace_aux (M : GNFA α (Option σ)) {x q} (t : M.trace x q) :
    (∃ p, q = some p ∧ M.rip.trace x p) ∨
      q = none ∧
        ∃ (y z : _) (xs : List (List α)) (p : Option σ),
          (Option.map (M.rip.trace y) p).getD (y = []) ∧
            z ∈ (M.step (Option.map some p) (some none)).matches' ∧
              (∀ x ∈ xs, x ∈ (M.step (some none) (some none)).matches') ∧ x = y ++ z ++ xs.join :=
  by
  induction t
  case start x q mat =>
    revert mat
    cases q
    case none =>
      intro mat
      right
      refine' ⟨rfl, _⟩
      refine' ⟨[], x, [], none, by dsimp <;> rfl, mat, _, by simp⟩
      intro x mem
      cases mem
    case some q =>
      intro mat
      left
      refine' ⟨q, rfl, _⟩
      exact trace.start (Or.inl mat)
  case step x y z p q t mat eq ih =>
    rw [eq]; clear eq x
    revert mat
    revert ih
    cases' p with p <;> cases' q with q
    case none.none =>
      intro ih mat
      right
      refine' ⟨rfl, _⟩
      cases ih
      case inl ih =>
        rcases ih with ⟨p, eq, t⟩
        cases eq
      case inr ih =>
      rcases ih with ⟨_, y, z', xs, p, t', matches', x_matches, eq⟩
      rw [eq]; clear eq
      refine' ⟨y, z', xs ++ [z], p, t', matches', _, by simp⟩
      intro x mem
      simp at mem
      cases mem
      case inl mem => exact x_matches x mem
      case inr mem => rw [mem]; exact mat
    case none.some =>
      intro ih mat
      left
      refine' ⟨q, rfl, _⟩
      cases ih
      case inl ih =>
        rcases ih with ⟨p, eq, t⟩
        cases eq
      case inr ih =>
      rcases ih with ⟨_, y, z', xs, p, t', matches', x_matches, eq⟩
      rw [eq]; clear eq
      cases p
      case none =>
        simp at t'
        rw [t']; clear t' y
        refine' trace.start (Or.inr _)
        simp
        rw [← List.append_assoc]
        refine' ⟨_, _, _, mat, rfl⟩
        refine' ⟨_, matches', _, _, rfl⟩
        exact ⟨_, rfl, x_matches⟩
      case some =>
        simp at t'
        rw [List.append_assoc]
        rw [List.append_assoc]
        refine' trace.step t' _ rfl
        right
        rw [← List.append_assoc]
        refine' ⟨_, _, _, mat, rfl⟩
        refine' ⟨_, matches', _, _, rfl⟩
        exact ⟨_, rfl, x_matches⟩
    · intro ih mat
      right
      refine' ⟨rfl, _⟩
      cases ih
      case inl ih =>
        rcases ih with ⟨p', eq, t⟩
        simp at eq; rw [← eq] at t; clear eq p'
        refine' ⟨y, z, [], some p, by simp [t], mat, _, by simp⟩
        intro x mem
        cases mem
      case inr ih =>
        rcases ih with ⟨eq, _⟩
        cases eq
    · intro ih mat
      cases ih
      case inl ih =>
        rcases ih with ⟨p', eq, t⟩
        simp at eq; rw [← eq] at t; clear eq p'
        left
        refine' ⟨q, rfl, _⟩
        exact trace.step t (Or.inl mat) rfl
      case inr ih =>
        rcases ih with ⟨eq, _⟩
        cases eq

theorem rip_trace_correct (M : GNFA α (Option σ)) {x} {q : σ} :
    M.trace x (some q) ↔ M.rip.trace x q := by
  constructor
  · intro t
    cases M.rip_trace_aux t
    case inl h =>
      rcases h with ⟨p, eq, t⟩
      simp at eq
      rw [eq]
      exact t
    case inr h =>
      cases' h with eq _
      cases eq
  · intro t
    induction t
    case start x q mat =>
      cases mat
      case inl mat => exact trace.start mat
      case inr mat =>
      rcases mat with ⟨y, hy, z, hz, eq⟩
      rw [← eq]; clear eq x
      refine' trace.step _ hz rfl
      clear hz z
      rcases hy with ⟨y, hy, z, hz, eq⟩
      simp only at eq
      rw [← eq]; clear eq
      rcases hz with ⟨xs, join, mat⟩
      rw [join]; clear join
      revert mat
      rw [← xs.reverse_reverse]
      induction xs.reverse
      case nil => simp [trace.start hy]
      case cons x xs ih =>
        intro mat
        rw [List.reverse_cons, List.join_append, List.join_singleton]
        rw [← List.append_assoc]
        simp only [List.mem_reverse, List.mem_cons] at mat
        refine' trace.step (ih _) (mat x (Or.inl rfl)) rfl
        intro y mem
        rw [List.mem_reverse] at mem
        exact mat y (Or.inr mem)
    case step x y z p q t mat eq ih =>
      cases mat
      case inl mat => exact trace.step ih mat eq
      case inr mat =>
      rw [eq]; clear eq x
      rcases mat with ⟨w, hw, x, hx, eq⟩
      rw [← eq]; clear eq z
      rw [← List.append_assoc]
      refine' trace.step _ hx rfl
      rcases hw with ⟨w, hw, x, hx, eq⟩
      rw [← eq]; clear eq
      rw [← List.append_assoc]
      rcases hx with ⟨xs, join, mat⟩
      rw [join]; clear join x
      revert mat
      rw [← xs.reverse_reverse]
      induction xs.reverse
      case nil =>
        intro mat
        simp at *
        exact trace.step ih hw rfl
      case cons x xs ih =>
        intro mat
        rw [List.reverse_cons, List.join_append, List.join_singleton]
        rw [← List.append_assoc]
        simp only [List.mem_reverse, List.mem_cons] at mat
        refine' trace.step _ (mat x (Or.inl rfl)) rfl
        apply ih
        intro y mem
        rw [List.mem_reverse] at mem
        exact mat y (Or.inr mem)

-- TODO: maybe mark as @simp
theorem rip_correct (M : GNFA α (Option σ)) : M.rip.accepts = M.accepts :=
  by
  ext
  constructor
  · intro t
    cases t
    case start x mat =>
      cases mat
      case inl mat => exact accepts.start mat
      case inr mat =>
      rcases mat with ⟨y, y_matches, z, z_matches, eq⟩
      rw [← eq]; clear eq x
      refine' accepts.step _ _ z_matches rfl; clear z_matches z
      rcases y_matches with ⟨y, z, y_matches, z_matches, eq⟩
      simp only at eq
      rw [← eq]; clear eq
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
        rw [List.reverse_cons, List.join_append, List.join_singleton]
        rw [← List.append_assoc]
        simp only [List.mem_reverse, List.mem_cons] at x_matches
        refine' trace.step _ (x_matches x (Or.inl rfl)) rfl
        apply ih
        intro x mem
        rw [List.mem_reverse] at mem
        exact x_matches x (Or.inr mem)
    case step x y z q t mat eq =>
      rw [eq]; clear eq x
      cases mat
      case inl mat =>
        refine' accepts.step _ _ mat rfl
        rw [rip_trace_correct]
        exact t
      case inr mat =>
      rcases mat with ⟨z, z_matches, x, x_matches, eq⟩
      rw [← eq]; clear eq
      rw [← List.append_assoc]
      refine' accepts.step _ _ x_matches rfl; clear x_matches x
      rcases z_matches with ⟨z, z_matches, x, x_matches, eq⟩
      rw [← eq]; clear eq
      rw [← List.append_assoc]
      rcases x_matches with ⟨xs, join, x_matches⟩
      rw [join]; clear join x
      revert x_matches
      rw [← xs.reverse_reverse]
      induction xs.reverse
      case nil =>
        intro mat
        rw [List.reverse_nil]
        unfold List.join
        rw [List.append_nil]
        refine' trace.step _ z_matches rfl
        rw [rip_trace_correct]
        exact t
      case cons x xs ih =>
        intro mat
        rw [List.reverse_cons, List.join_append, List.join_singleton]
        rw [← List.append_assoc]
        simp only [List.mem_reverse, List.mem_cons] at mat
        refine' trace.step _ (mat x (Or.inl rfl)) rfl
        apply ih
        intro x mem
        rw [List.mem_reverse] at mem
        exact mat x (Or.inr mem)
  · intro t
    cases t
    case start x mat => exact accepts.start (Or.inl mat)
    case step x y z q t mat eq =>
      rw [eq]; clear eq x
      cases M.rip_trace_aux t
      case inl h =>
        rcases h with ⟨q, eq, t⟩
        rw [eq] at mat; clear eq
        exact accepts.step _ t (Or.inl mat) rfl
      case inr h =>
      rcases h with ⟨eq, h⟩
      -- Porting note: rw[eq] at * didn't catch every occurence of q
      subst eq
      rcases h with ⟨y, w, xs, p, t, w_matches, x_matches, eq⟩
      rw [eq]; clear eq
      cases p
      case none =>
        rw [Option.map_none', Option.getD_none] at t
        rw [t]; clear t y
        refine' accepts.start _
        right
        refine' ⟨_, _, _, mat, rfl⟩
        refine' ⟨_, w_matches, _, _, rfl⟩
        exact ⟨xs, rfl, x_matches⟩
      case some =>
        rw [Option.map_some', Option.getD_some] at t
        rw [List.append_assoc, List.append_assoc]
        refine' accepts.step _ t _ rfl
        right
        rw [← List.append_assoc]
        refine' ⟨_, _, _, mat, rfl⟩
        refine' ⟨_, w_matches, _, _, rfl⟩
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
  case start x q mat =>
    apply trace.start
    unfold mapEquiv
    dsimp
    rw [Equiv.symm_apply_apply]
    exact mat
  case step x y z p q t mat eq
    ih =>
    refine' trace.step ih _ eq
    unfold mapEquiv
    dsimp
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact mat

theorem mapEquiv_trace {σ τ} [Fintype σ] [Fintype τ] (M : GNFA α σ) (e : σ ≃ τ) :
    ∀ q x, M.trace x q ↔ (M.mapEquiv e).trace x (e q) :=
  by
  intro q x
  constructor
  · intro t
    exact M.mapEquiv_trace_aux e q x t
  · intro t
    have := (M.mapEquiv e).mapEquiv_trace_aux e.symm (e q) x t
    rw [Equiv.symm_apply_apply] at this
    unfold mapEquiv at this
    simp at this
    cases M
    exact this

theorem mapEquiv_correct_aux {σ τ} [Fintype σ] [Fintype τ] (M : GNFA α σ) (e : σ ≃ τ) :
    M.accepts ≤ (M.mapEquiv e).accepts := by
  intro x t
  cases t
  case start x mat => exact accepts.start mat
  case step x y z q t mat eq =>
    refine' accepts.step _ _ _ eq
    exact e q
    rw [M.mapEquiv_trace e] at t
    exact t
    unfold mapEquiv
    simpa

theorem mapEquiv_correct {σ τ} [Fintype σ] [Fintype τ] (M : GNFA α σ) (e : σ ≃ τ) :
    M.accepts = (M.mapEquiv e).accepts := by
  ext
  constructor
  · intro h
    exact M.mapEquiv_correct_aux e h
  · intro h
    have := (M.mapEquiv e).mapEquiv_correct_aux e.symm h
    unfold mapEquiv at this
    simp at this
    cases M
    exact this

theorem exists_toRegularExpression :
    ∀ M : GNFA α σ, ∃ r : RegularExpression α, M.accepts = r.matches' :=
  by
  refine' Fintype.induction_empty_option _ _ _ σ
  ·
    intro σ τ
    intro
    intro e h M
    letI _ : Fintype σ := Fintype.ofEquiv _ e.symm
    specialize h (M.mapEquiv e.symm)
    rcases h with ⟨r, hr⟩
    use r
    rw [← hr]
    exact M.mapEquiv_correct e.symm
  · intro M
    use M.step none none
    ext
    constructor
    · intro t
      induction t
      case start x mat => exact mat
      case step empty _ _ _ => cases empty
    · intro mat
      exact accepts.start mat
  ·
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
  ext x
  constructor
  · rintro ⟨q, accept, eval⟩
    refine' GNFA.accepts.step q _ _ x.append_nil.symm
    swap
    · unfold toGNFA; simp only
      rw [Set.mem_def] at accept
      simp [accept]
    clear accept
    revert eval
    rw [← x.reverse_reverse]
    induction x.reverse generalizing q
    case nil =>
      intro hx
      refine' GNFA.trace.start _
      unfold toGNFA; simp only
      rw [Set.mem_def, List.reverse_nil, NFA.eval_nil] at hx
      simp [hx]
    case cons a as ih =>
      intro hx
      rw [List.reverse_cons] at *
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hx
      rcases hx with ⟨p, mem, step⟩
      refine' GNFA.trace.step (ih p mem) _ rfl
      rw [Set.mem_def]
      unfold toGNFA; simp only
      rw [RegularExpression.mem_sum_iff_exists_mem]
      refine' ⟨RegularExpression.char a, _, rfl⟩
      simpa [univ]
  · intro hx
    cases' hx with x step x y z q t step eq
    case start => cases step
    unfold toGNFA at step; simp only at step
    by_cases h : M.accept q; swap; simp [h] at step
    simp [h] at step
    cases step
    refine' ⟨q, h, _⟩
    rw [List.append_nil] at eq; cases eq; clear h
    revert t
    rw [← x.reverse_reverse]
    induction x.reverse generalizing q
    /- Porting note: To fix error
      Case tag 'nil' not found.

      Available tags:
        'pos.refl.refl.nil._@.Mathlib.Computability.GNFA._hyg.4615',
        'pos.refl.refl.cons._@.Mathlib.Computability.GNFA._hyg.4615'
    -/
    case pos.refl.refl.nil =>
      intro hx
      rw [List.reverse_nil] at *
      rw [NFA.eval_nil]
      cases hx
      case start x step =>
        unfold toGNFA at step; simp only at step
        by_cases h : M.start q
        · exact h
        · simp [h] at step
      case step x y z p t eq step =>
        rw [List.nil_eq_append] at eq
        cases eq.2; clear eq t x
        unfold toGNFA at step; simp only at step
        rw [Set.mem_def, RegularExpression.mem_sum_iff_exists_mem] at step
        rcases step with ⟨r, mem, mat⟩
        rw [List.mem_map] at mem
        rcases mem with ⟨a, _, eq⟩
        rw [← eq] at mat
        cases mat
    /- Porting note: To fix error
      Case tag 'cons' not found.

      The only available case tag is 'pos.refl.refl.cons._@.Mathlib.Computability.GNFA._hyg.4615'.
    -/
    case pos.refl.refl.cons a as ih =>
      intro hx
      simp at *
      rw [NFA.mem_stepSet]
      cases hx
      case start q step =>
        unfold toGNFA at step; simp only at step
        by_cases h : M.start q
        · rw [if_pos h, RegularExpression.matches'_epsilon, Language.mem_one] at step
          replace step : as.reverse ++ [a] = List.nil := step
          rw [List.append_eq_nil] at step
          cases step.2
        · rw [if_neg h] at step
          cases step
      case step y z p t eq step =>
        unfold toGNFA at step; simp only at step
        replace eq : as.reverse ++ [a] = y ++ z := eq
        rw [Set.mem_def, RegularExpression.mem_sum_iff_exists_mem] at step
        rcases step with ⟨r, mem, mat⟩
        simp only [List.mem_map, List.mem_filter] at mem
        rcases mem with ⟨b, ⟨_, step⟩, eq⟩
        rw [← eq] at mat
        cases mat
        rw [← List.reverse_inj] at eq
        simp only [List.reverse_append, List.reverse_singleton, List.reverse_reverse,
          List.singleton_append, List.cons_eq_cons] at eq
        cases eq.1
        cases eq.2
        conv in q ∈ _ => rw[Set.mem_def]
        refine' ⟨p, _, Bool.of_decide_true step⟩
        rw [← y.reverse_reverse] at t
        exact ih p t

/--
Given an NFA with a `fintype` state, there is a regular expression that matches the same language.
-/
theorem exists_toRegularExpression {σ} [Finite α] [Finite σ] (M : NFA α σ) :
    ∃ r : RegularExpression α, M.accepts = r.matches' := by
  classical
  rcases Finite.exists_univ_list α with ⟨as, _, univ⟩
  cases nonempty_fintype σ
  rcases(M.toGNFA as).exists_toRegularExpression with ⟨r, hr⟩
  use r
  rw [← hr]
  exact M.toGNFA_correct as univ

/-- Noncomputably finds the regular expression equivalent to the NFA.
-/
noncomputable def toRegularExpression [Fintype α] (M : NFA α σ) : RegularExpression α :=
  Classical.choose M.exists_toRegularExpression

theorem toRegularExpression_correct [Fintype α] (M : NFA α σ) :
    M.accepts = M.toRegularExpression.matches' :=
  Classical.choose_spec M.exists_toRegularExpression

end NFA

