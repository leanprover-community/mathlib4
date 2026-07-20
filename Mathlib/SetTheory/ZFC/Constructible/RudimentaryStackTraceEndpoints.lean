/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackTraceDecode

/-!
# Endpoint semantics of raw formula-certified stack traces

For a genuine typed program, existence of a raw formula chain from the empty
stack code to the singleton output-stack code is exactly successful execution
of that program.  Soundness uses raw-chain decoding and injectivity of both
token and stack-state encodings; completeness encodes the canonical execution
trace of a successful run.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

open FiniteSequenceZF

noncomputable section

/--
A genuine program evaluates from the empty stack to `[z]` exactly when it has
a raw formula-certified state-code chain with those endpoints.
-/
theorem exists_rawStackFormulaTrace_iff_run
    (U : ZFSet.{u})
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (z : ZFSet.{u}) :
    (∃ rawStates : List ZFSet.{u},
      RawStackFormulaChain U (encodedStackProgram U program) rawStates ∧
        rawStates.head? = some (listCode []) ∧
        rawStates.getLast? = some (listCode [z])) ↔
      runStackProgram (rudimentaryGenerator U) program [] = some [z] := by
  constructor
  · rintro ⟨rawStates, hchain, hhead, hlast⟩
    rcases exists_executionTrace_decoding_of_rawStackFormulaChain
        U (encodedStackProgram U program) rawStates hhead hchain with
      ⟨decodedProgram, states, hprogramCodes, hstateCodes, htrace⟩
    have hprogramMap :
        program.map (stackTokenZFCode U) =
          decodedProgram.map (stackTokenZFCode U) := by
      simpa only [encodedStackProgram] using hprogramCodes
    have hprogram : decodedProgram = program :=
      ((stackTokenZFCode_injective U).list_map hprogramMap).symm
    subst decodedProgram
    rw [hstateCodes] at hhead hlast
    have hheadMapped :
        states.head?.map listCode = some (listCode []) := by
      simpa only [List.head?_map] using hhead
    have hheadStates : states.head? = some [] := by
      cases hstateHead : states.head? with
      | none =>
          simp only [hstateHead, Option.map_none] at hheadMapped
          cases hheadMapped
      | some first =>
          simp only [hstateHead, Option.map_some,
            Option.some.injEq] at hheadMapped
          have hfirst : first = [] :=
            listCode_injective hheadMapped
          exact congrArg some hfirst
    have hlastMapped :
        states.getLast?.map listCode = some (listCode [z]) := by
      simpa only [List.getLast?_map] using hlast
    have hlastStates : states.getLast? = some [z] := by
      cases hstateLast : states.getLast? with
      | none =>
          simp only [hstateLast, Option.map_none] at hlastMapped
          cases hlastMapped
      | some last =>
          simp only [hstateLast, Option.map_some,
            Option.some.injEq] at hlastMapped
          have hlastStack : last = [z] :=
            listCode_injective hlastMapped
          exact congrArg some hlastStack
    exact run_of_executionTrace (rudimentaryGenerator U)
      program states [] [z] htrace hheadStates hlastStates
  · intro hrun
    rcases exists_executionTrace_of_run
        (rudimentaryGenerator U) program [] [z] hrun with
      ⟨states, htrace, hhead, hlast⟩
    refine ⟨encodedStackStates states,
      htrace.encoded_rawStackFormulaChain, ?_, ?_⟩
    · simp only [encodedStackStates, List.head?_map,
        hhead, Option.map_some]
    · simp only [encodedStackStates, List.getLast?_map,
        hlast, Option.map_some]

end

end Constructible.Godel.RudimentaryTerm
