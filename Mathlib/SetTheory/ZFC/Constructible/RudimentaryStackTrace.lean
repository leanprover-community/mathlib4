/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.IndexedSequenceValidity
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramZFCode

/-!
# Finite execution traces for rudimentary stack programs

The object-language evaluator quantifies over a set-coded finite trace. This
file isolates the corresponding external machine theorem: successful
evaluation is equivalent to a finite chain of local `runStackToken` steps.
It also records constructibility of every state and of the indexed trace code.
-/

@[expose] public section

universe u v

namespace Constructible.Godel.RudimentaryTerm

/-! ## Recursive traces and their endpoint semantics -/

/--
A trace contains the input state, every intermediate state, and the final
state.  Consequently a trace for `program` has `program.length + 1` entries.
-/
inductive ExecutionTrace {A : Type u} (rho : A → ZFSet.{v}) :
    List (StackToken A) → List (List ZFSet.{v}) → Prop
  | nil (stack : List ZFSet.{v}) : ExecutionTrace rho [] [stack]
  | cons {token : StackToken A} {program : List (StackToken A)}
      {input next : List ZFSet.{v}} {states : List (List ZFSet.{v})}
      (step : runStackToken rho token input = some next)
      (tail : ExecutionTrace rho program (next :: states)) :
      ExecutionTrace rho (token :: program) (input :: next :: states)

theorem ExecutionTrace.length {A : Type u} {rho : A → ZFSet.{v}}
    {program : List (StackToken A)} {states : List (List ZFSet.{v})}
    (htrace : ExecutionTrace rho program states) :
    states.length = program.length + 1 := by
  induction htrace with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem ExecutionTrace.nonempty {A : Type u} {rho : A → ZFSet.{v}}
    {program : List (StackToken A)} {states : List (List ZFSet.{v})}
    (htrace : ExecutionTrace rho program states) : states ≠ [] := by
  intro hnil
  have hlength := htrace.length
  simp only [hnil, List.length_nil] at hlength
  omega

/-- A trace determines the ordinary recursive evaluator and its last state. -/
theorem ExecutionTrace.run_eq_getLast {A : Type u} {rho : A → ZFSet.{v}}
    {program : List (StackToken A)} {input : List ZFSet.{v}}
    {states : List (List ZFSet.{v})}
    (htrace : ExecutionTrace rho program (input :: states)) :
    runStackProgram rho program input =
      some ((input :: states).getLast htrace.nonempty) := by
  induction program generalizing input states with
  | nil =>
      cases htrace with
      | nil => rfl
  | cons token program ih =>
      cases htrace with
      | cons hstep htail =>
          rw [runStackProgram, hstep]
          simp only [Option.bind_some]
          rw [ih htail]
          congr 1

/-- Every successful run has its canonical finite chain of local steps. -/
theorem exists_executionTrace_of_run {A : Type u} (rho : A → ZFSet.{v})
    (program : List (StackToken A)) (input output : List ZFSet.{v})
    (hrun : runStackProgram rho program input = some output) :
    ∃ states : List (List ZFSet.{v}),
      ExecutionTrace rho program states ∧
        states.head? = some input ∧ states.getLast? = some output := by
  induction program generalizing input with
  | nil =>
      simp only [runStackProgram_nil, Option.some.injEq] at hrun
      subst output
      exact ⟨[input], .nil input, rfl, rfl⟩
  | cons token program ih =>
      simp only [runStackProgram] at hrun
      cases hstep : runStackToken rho token input with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep, Option.bind_some] at hrun
          rcases ih next hrun with ⟨tail, htail, hhead, hlast⟩
          cases tail with
          | nil => simp at hhead
          | cons first rest =>
              simp only [List.head?_cons, Option.some.injEq] at hhead
              subst first
              refine ⟨input :: next :: rest, .cons hstep htail, rfl, ?_⟩
              simpa only [List.getLast?_cons_cons] using hlast

/-- A trace with specified endpoints yields the ordinary successful run. -/
theorem run_of_executionTrace {A : Type u} (rho : A → ZFSet.{v})
    (program : List (StackToken A)) (states : List (List ZFSet.{v}))
    (input output : List ZFSet.{v})
    (htrace : ExecutionTrace rho program states)
    (hhead : states.head? = some input)
    (hlast : states.getLast? = some output) :
    runStackProgram rho program input = some output := by
  cases states with
  | nil => exact False.elim (htrace.nonempty rfl)
  | cons first rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst first
      rw [htrace.run_eq_getLast]
      have hne : input :: rest ≠ [] := List.cons_ne_nil input rest
      rw [List.getLast?_eq_some_getLast hne] at hlast
      exact hlast

/-- Successful evaluation is exactly existence of a finite local trace. -/
theorem run_iff_exists_executionTrace {A : Type u} (rho : A → ZFSet.{v})
    (program : List (StackToken A)) (input output : List ZFSet.{v}) :
    runStackProgram rho program input = some output ↔
      ∃ states : List (List ZFSet.{v}),
        ExecutionTrace rho program states ∧
          states.head? = some input ∧ states.getLast? = some output := by
  constructor
  · exact exists_executionTrace_of_run rho program input output
  · rintro ⟨states, htrace, hhead, hlast⟩
    exact run_of_executionTrace rho program states input output
      htrace hhead hlast

/-! ## Indexed characterization -/

/--
The form directly mirrored by an object-language trace formula: the state
sequence has one more entry than the program, and instruction `k` takes state
`k` to state `k+1`.
-/
def IndexedExecutionTrace {A : Type u} (rho : A → ZFSet.{v})
    (program : List (StackToken A)) (states : List (List ZFSet.{v})) : Prop :=
  ∃ hlength : states.length = program.length + 1,
    ∀ k : Fin program.length,
      runStackToken rho (program.get k)
          (states.get ⟨k.1, by omega⟩) =
        some (states.get ⟨k.1 + 1, by omega⟩)

/-- Recursive traces satisfy the indexed local-step characterization. -/
theorem ExecutionTrace.indexed {A : Type u} {rho : A → ZFSet.{v}}
    {program : List (StackToken A)} {states : List (List ZFSet.{v})}
    (htrace : ExecutionTrace rho program states) :
    IndexedExecutionTrace rho program states := by
  induction htrace with
  | nil stack =>
      refine ⟨rfl, ?_⟩
      intro k
      exact Fin.elim0 k
  | @cons token program input next tailStates hstep htail ih =>
      rcases ih with ⟨hlength, hsteps⟩
      refine ⟨by simp only [List.length_cons, hlength], ?_⟩
      intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · simpa using hstep
      · simpa using hsteps j

/-- The indexed local-step conditions reconstruct the recursive trace. -/
theorem executionTrace_of_indexed {A : Type u} {rho : A → ZFSet.{v}}
    {program : List (StackToken A)} {states : List (List ZFSet.{v})}
    (htrace : IndexedExecutionTrace rho program states) :
    ExecutionTrace rho program states := by
  induction program generalizing states with
  | nil =>
      rcases htrace with ⟨hlength, _hsteps⟩
      cases states with
      | nil => simp at hlength
      | cons stack tail =>
          cases tail with
          | nil => exact .nil stack
          | cons next rest =>
              simp only [List.length_cons, List.length_nil] at hlength
              omega
  | cons token program ih =>
      rcases htrace with ⟨hlength, hsteps⟩
      cases states with
      | nil => simp at hlength
      | cons input tail =>
          cases tail with
          | nil =>
              simp only [List.length_cons, List.length_nil] at hlength
              omega
          | cons next rest =>
              have hstep := hsteps (0 : Fin (token :: program).length)
              have htailLength :
                  (next :: rest).length = program.length + 1 := by
                simp only [List.length_cons] at hlength ⊢
                omega
              have htailSteps :
                  ∀ k : Fin program.length,
                    runStackToken rho (program.get k)
                        ((next :: rest).get ⟨k.1, by omega⟩) =
                      some ((next :: rest).get ⟨k.1 + 1, by omega⟩) := by
                intro k
                have hk := hsteps k.succ
                simpa using hk
              apply ExecutionTrace.cons (by simpa using hstep)
              exact ih ⟨htailLength, htailSteps⟩

/-- Recursive and indexed finite traces are equivalent. -/
theorem executionTrace_iff_indexed {A : Type u} {rho : A → ZFSet.{v}}
    {program : List (StackToken A)} {states : List (List ZFSet.{v})} :
    ExecutionTrace rho program states ↔
      IndexedExecutionTrace rho program states :=
  ⟨ExecutionTrace.indexed, executionTrace_of_indexed⟩

/-! ## Constructibility of successful traces -/

/-- One successful local step preserves constructibility of stack entries. -/
theorem runStackToken_entries_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (hstep : runStackToken (rudimentaryGenerator U) token input = some output) :
    ∀ x ∈ output, x ∈ L := by
  cases token with
  | inl generator =>
      simp only [runStackToken, Option.some.injEq] at hstep
      subst output
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact rudimentaryGenerator_mem_L hU generator
      · exact hinput x hx
  | inr operation =>
      cases input with
      | nil => simp [runStackToken] at hstep
      | cons right tail =>
          cases tail with
          | nil => simp [runStackToken] at hstep
          | cons left rest =>
              simp only [runStackToken, Option.some.injEq] at hstep
              subst output
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact op_mem_L (i := operation)
                  (hinput left (by simp)) (hinput right (by simp))
              · exact hinput x (by simp [hx])

/-- Every state occurring in a successful constructible-seed trace is finite
and consists entirely of constructible sets. -/
theorem ExecutionTrace.entries_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    {program : List (StackToken (Option (Constructible.ZFCarrier U)))}
    {states : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    {input : List ZFSet.{u}} (hhead : states.head? = some input)
    (hinput : ∀ x ∈ input, x ∈ L) :
    ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L := by
  induction htrace generalizing input with
  | nil stack =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst input
      simpa using hinput
  | @cons token program input next tailStates hstep htail ih =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst input
      have hnext : ∀ x ∈ next, x ∈ L :=
        runStackToken_entries_mem_L hU token _ _ hinput hstep
      intro stack hstack
      simp only [List.mem_cons] at hstack
      rcases hstack with rfl | hstack
      · exact hinput
      · exact ih rfl hnext stack
          (by simpa only [List.mem_cons] using hstack)

/-- Encode a trace as an indexed sequence of structural stack codes. -/
noncomputable def executionTraceZFCode
    (states : List (List ZFSet.{u})) : ZFSet.{u} :=
  IndexedSequenceZF.sequenceCode
    (states.map FiniteSequenceZF.listCode)

/-- A successful trace over a constructible seed has a constructible code. -/
theorem executionTraceZFCode_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    {program : List (StackToken (Option (Constructible.ZFCarrier U)))}
    {states : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    {input : List ZFSet.{u}} (hhead : states.head? = some input)
    (hinput : ∀ x ∈ input, x ∈ L) :
    executionTraceZFCode states ∈ L := by
  apply IndexedSequenceZF.sequenceCode_mem_L
  intro stackCode hstackCode
  rcases List.mem_map.mp hstackCode with ⟨stack, hstack, rfl⟩
  apply FiniteSequenceZF.listCode_mem_L
  exact htrace.entries_mem_L hU hhead hinput stack hstack

end Constructible.Godel.RudimentaryTerm
