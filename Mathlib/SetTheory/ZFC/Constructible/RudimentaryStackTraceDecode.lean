/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackStepDecode
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackTrace

/-!
# Decoding raw formula-certified stack traces

Starting from a genuine input stack code, the one-step decoding theorem can
be iterated along raw token and state-code lists.  This reconstructs an actual
typed stack program and an `ExecutionTrace`.  Conversely, encoding any real
execution trace makes every adjacent triple satisfy `stackStepFormula`.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

open FiniteSequenceZF

noncomputable section

/-- Raw token codes of a typed stack program. -/
def encodedStackProgram (U : ZFSet.{u})
    (program : List (StackToken (Option (Constructible.ZFCarrier U)))) :
    List ZFSet.{u} :=
  program.map (stackTokenZFCode U)

/-- Raw structural list codes of a list of stack states. -/
def encodedStackStates (states : List (List ZFSet.{u})) : List ZFSet.{u} :=
  states.map listCode

/--
The local formula-chain condition on raw token and state-code lists.  The
state list has one more entry, and token `k` relates states `k` and `k + 1`.
-/
def RawStackFormulaChain (U : ZFSet.{u})
    (rawTokens rawStates : List ZFSet.{u}) : Prop :=
  ∃ hlength : rawStates.length = rawTokens.length + 1,
    ∀ k : Fin rawTokens.length,
      FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
        (stackStepAssignment U
          (rawTokens.get k)
          (rawStates.get ⟨k.1, by omega⟩)
          (rawStates.get ⟨k.1 + 1, by omega⟩))

/--
Strong decoding theorem with an arbitrary already-decoded initial stack.
The returned state tail is chosen so that the decoded trace starts exactly at
`input`.
-/
theorem exists_executionTrace_decoding_of_formula_chain
    (U : ZFSet.{u}) (input : List ZFSet.{u})
    (rawTokens rawStates : List ZFSet.{u})
    (hlength : rawStates.length = rawTokens.length + 1)
    (hhead : rawStates.head? = some (listCode input))
    (hsteps : ∀ k : Fin rawTokens.length,
      FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
        (stackStepAssignment U
          (rawTokens.get k)
          (rawStates.get ⟨k.1, by omega⟩)
          (rawStates.get ⟨k.1 + 1, by omega⟩))) :
    ∃ program : List
        (StackToken (Option (Constructible.ZFCarrier U))),
      ∃ stateTail : List (List ZFSet.{u}),
        rawTokens = encodedStackProgram U program ∧
          rawStates = encodedStackStates (input :: stateTail) ∧
          ExecutionTrace (rudimentaryGenerator U)
            program (input :: stateTail) := by
  induction rawTokens generalizing input rawStates with
  | nil =>
      cases rawStates with
      | nil =>
          simp only [List.length_nil] at hlength
          omega
      | cons first tail =>
          cases tail with
          | nil =>
              simp only [List.head?_cons, Option.some.injEq] at hhead
              subst first
              exact ⟨[], [], rfl, rfl, .nil input⟩
          | cons second rest =>
              simp only [List.length_cons, List.length_nil] at hlength
              omega
  | cons tokenCode rawTokens ih =>
      cases rawStates with
      | nil =>
          simp only [List.length_nil, List.length_cons] at hlength
          omega
      | cons inputCode tail =>
          cases tail with
          | nil =>
              simp only [List.length_cons, List.length_nil] at hlength
              omega
          | cons nextCode rest =>
              simp only [List.head?_cons, Option.some.injEq] at hhead
              subst inputCode
              have hfirst :=
                hsteps (0 : Fin (tokenCode :: rawTokens).length)
              have hfirstDecoded :
                  FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
                    (stackStepAssignment U tokenCode
                      (listCode input) nextCode) := by
                simpa using hfirst
              rcases exists_decoding_of_satisfies_stackStepFormula
                  U tokenCode nextCode input hfirstDecoded with
                ⟨token, next, htokenCode, hnextCode, hrun⟩
              have htailLength :
                  (nextCode :: rest).length = rawTokens.length + 1 := by
                simp only [List.length_cons] at hlength ⊢
                omega
              have htailHead :
                  (nextCode :: rest).head? = some (listCode next) := by
                simp only [List.head?_cons, Option.some.injEq]
                exact hnextCode
              have htailSteps : ∀ k : Fin rawTokens.length,
                  FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
                    (stackStepAssignment U
                      (rawTokens.get k)
                      ((nextCode :: rest).get ⟨k.1, by omega⟩)
                      ((nextCode :: rest).get
                        ⟨k.1 + 1, by omega⟩)) := by
                intro k
                have hk := hsteps k.succ
                simpa using hk
              rcases ih next (nextCode :: rest) htailLength
                  htailHead htailSteps with
                ⟨program, stateTail, hprogram, hstates, htrace⟩
              refine ⟨token :: program, next :: stateTail, ?_, ?_, ?_⟩
              · simp only [encodedStackProgram, List.map_cons] at hprogram ⊢
                rw [htokenCode, hprogram]
              · calc
                  listCode input :: nextCode :: rest =
                      listCode input :: encodedStackStates
                        (next :: stateTail) := by rw [hstates]
                  _ = encodedStackStates (input :: next :: stateTail) := rfl
              · exact .cons hrun htrace

/--
Decode a raw formula-certified chain whose first state is the empty stack.
-/
theorem exists_executionTrace_decoding_of_empty_formula_chain
    (U : ZFSet.{u}) (rawTokens rawStates : List ZFSet.{u})
    (hlength : rawStates.length = rawTokens.length + 1)
    (hhead : rawStates.head? = some (listCode []))
    (hsteps : ∀ k : Fin rawTokens.length,
      FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
        (stackStepAssignment U
          (rawTokens.get k)
          (rawStates.get ⟨k.1, by omega⟩)
          (rawStates.get ⟨k.1 + 1, by omega⟩))) :
    ∃ program : List
        (StackToken (Option (Constructible.ZFCarrier U))),
      ∃ states : List (List ZFSet.{u}),
        rawTokens = program.map (stackTokenZFCode U) ∧
          rawStates = states.map listCode ∧
          ExecutionTrace (rudimentaryGenerator U) program states := by
  rcases exists_executionTrace_decoding_of_formula_chain
      U [] rawTokens rawStates hlength hhead hsteps with
    ⟨program, stateTail, hprogram, hstates, htrace⟩
  exact ⟨program, [] :: stateTail,
    by simpa only [encodedStackProgram] using hprogram,
    by simpa only [encodedStackStates] using hstates,
    htrace⟩

/-- Predicate-packaged form of empty-stack raw trace decoding. -/
theorem exists_executionTrace_decoding_of_rawStackFormulaChain
    (U : ZFSet.{u}) (rawTokens rawStates : List ZFSet.{u})
    (hhead : rawStates.head? = some (listCode []))
    (hchain : RawStackFormulaChain U rawTokens rawStates) :
    ∃ program : List
        (StackToken (Option (Constructible.ZFCarrier U))),
      ∃ states : List (List ZFSet.{u}),
        rawTokens = program.map (stackTokenZFCode U) ∧
          rawStates = states.map listCode ∧
          ExecutionTrace (rudimentaryGenerator U) program states := by
  rcases hchain with ⟨hlength, hsteps⟩
  exact exists_executionTrace_decoding_of_empty_formula_chain
    U rawTokens rawStates hlength hhead hsteps

/-- Every indexed step of a genuine trace satisfies `stackStepFormula`. -/
theorem ExecutionTrace.satisfies_stackStepFormula_at
    {U : ZFSet.{u}}
    {program : List
      (StackToken (Option (Constructible.ZFCarrier U)))}
    {states : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (k : Fin program.length) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
      (stackStepAssignment U
        (stackTokenZFCode U (program.get k))
        (listCode (states.get ⟨k.1, by
          have hlength := htrace.length
          omega⟩))
        (listCode (states.get ⟨k.1 + 1, by
          have hlength := htrace.length
          omega⟩))) := by
  rcases htrace.indexed with ⟨_hlength, hsteps⟩
  apply (satisfies_stackStepFormula_iff_run U
    (program.get k)
    (states.get ⟨k.1, by
      have hlength := htrace.length
      omega⟩)
    (states.get ⟨k.1 + 1, by
      have hlength := htrace.length
      omega⟩)).mpr
  simpa using hsteps k

/-- Encoding a genuine execution trace produces a raw formula chain. -/
theorem ExecutionTrace.encoded_rawStackFormulaChain
    {U : ZFSet.{u}}
    {program : List
      (StackToken (Option (Constructible.ZFCarrier U)))}
    {states : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states) :
    RawStackFormulaChain U
      (encodedStackProgram U program) (encodedStackStates states) := by
  refine ⟨?_, ?_⟩
  · simp only [encodedStackProgram, encodedStackStates,
      List.length_map, htrace.length]
  · intro rawIndex
    let k : Fin program.length :=
      ⟨rawIndex.1, by
        simpa only [encodedStackProgram, List.length_map]
          using rawIndex.2⟩
    have hstep := htrace.satisfies_stackStepFormula_at k
    have hinputBound : k.1 < states.length := by
      have hlength := htrace.length
      omega
    have houtputBound : k.1 + 1 < states.length := by
      have hlength := htrace.length
      omega
    have htoken :
        (encodedStackProgram U program).get rawIndex =
          stackTokenZFCode U (program.get k) := by
      change (program.map (stackTokenZFCode U))[rawIndex.1] =
        stackTokenZFCode U program[k.1]
      rw [List.getElem_map]
    have hinput :
        (encodedStackStates states).get ⟨rawIndex.1, by
          simp only [encodedStackStates, List.length_map]
          have hlength := htrace.length
          have hindex := rawIndex.2
          simp only [encodedStackProgram, List.length_map] at hindex
          omega⟩ =
          listCode (states.get ⟨k.1, by
            have hlength := htrace.length
            omega⟩) := by
      change (states.map listCode)[rawIndex.1]'(by
          simpa only [List.length_map, k] using hinputBound) =
        listCode (states[k.1]'hinputBound)
      rw [List.getElem_map]
    have houtput :
        (encodedStackStates states).get ⟨rawIndex.1 + 1, by
          simp only [encodedStackStates, List.length_map]
          have hlength := htrace.length
          have hindex := rawIndex.2
          simp only [encodedStackProgram, List.length_map] at hindex
          omega⟩ =
          listCode (states.get ⟨k.1 + 1, by
            have hlength := htrace.length
            omega⟩) := by
      change (states.map listCode)[rawIndex.1 + 1]'(by
          simpa only [List.length_map, k] using houtputBound) =
        listCode (states[k.1 + 1]'houtputBound)
      rw [List.getElem_map]
    rw [htoken, hinput, houtput]
    exact hstep

/--
In particular, a genuine trace beginning at the empty stack has the required
raw initial-state code as well as all local formula steps.
-/
theorem ExecutionTrace.encoded_empty_rawStackFormulaTrace
    {U : ZFSet.{u}}
    {program : List
      (StackToken (Option (Constructible.ZFCarrier U)))}
    {stateTail : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U)
      program ([] :: stateTail)) :
    (encodedStackStates ([] :: stateTail)).head? =
        some (listCode []) ∧
      RawStackFormulaChain U (encodedStackProgram U program)
        (encodedStackStates ([] :: stateTail)) := by
  exact ⟨rfl, htrace.encoded_rawStackFormulaChain⟩

end

end Constructible.Godel.RudimentaryTerm
