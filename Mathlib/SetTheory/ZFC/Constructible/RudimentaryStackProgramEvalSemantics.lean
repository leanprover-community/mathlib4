/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalFormula
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackTraceEndpoints

/-!
# Semantic correctness of the fixed postfix-program evaluator

The evaluator accepts arbitrary indexed-sequence representations, not only
the canonical graph produced by `sequenceCode`. This ensures correctness when
program codes are quantified over by a first-order formula.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open FiniteSequenceZF
open IndexedSequenceZF

private theorem valueAt_zero_iff_head?_eq
    {sequence : ZFSet.{u}} {xs : List ZFSet.{u}}
    (hrep : Represents sequence xs) (hne : xs ≠ []) (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequence, (∅ : ZFSet.{u}), value] <->
      xs.head? = some value := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      simpa [natCode, Ordinal.toZFSet_zero, eq_comm] using
        (satisfies_valueAt_represents_iff hrep 0 value)

private theorem valueAt_last_iff_getLast?_eq
    {sequence : ZFSet.{u}} {xs : List ZFSet.{u}}
    (hrep : Represents sequence xs) (n : Nat)
    (hlength : xs.length = n + 1) (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequence, natCode n, value] <->
      xs.getLast? = some value := by
  have hn : n < xs.length := by omega
  have hlast : xs.getLast? = some (xs.get ⟨n, hn⟩) := by
    rw [List.getLast?_eq_getElem?]
    have hindex : xs.length - 1 = n := by omega
    rw [hindex, List.getElem?_eq_getElem hn]
    rfl
  rw [satisfies_valueAt_represents_iff hrep, hlast,
    Option.some.injEq]
  constructor
  · rintro ⟨hn', hvalue⟩
    simpa only using hvalue.symm
  · intro hvalue
    refine ⟨hn, ?_⟩
    simpa only using hvalue.symm

/-- A valid indexed code represents at most one finite list. -/
private theorem represents_list_unique
    {sequence : ZFSet.{u}} {xs ys : List ZFSet.{u}}
    (hxs : Represents sequence xs) (hys : Represents sequence ys) :
    xs = ys := by
  rcases hxs with ⟨xsGraph, hxsCode, hxsGraph⟩
  rcases hys with ⟨ysGraph, hysCode, hysGraph⟩
  have hparts := ZFSet.pair_inj.mp (hxsCode.symm.trans hysCode)
  have hlength : xs.length = ys.length := natCode_injective hparts.1
  apply List.ext_get hlength
  intro k hkx hky
  let ix : Fin xs.length := ⟨k, hkx⟩
  let iy : Fin ys.length := ⟨k, hky⟩
  have hmem :
      ZFSet.pair (xs.get ix) (natCode k) ∈ ysGraph := by
    rw [← hparts.2]
    simpa only [ix] using (hxsGraph ix).1
  simpa only [ix, iy] using (hysGraph iy).2 (xs.get ix) hmem

/-- Raw codes accepted by the evaluator decode to genuine typed programs. -/
theorem satisfies_stackProgramEvalFormula_iff_exists_run
    (U programCode result : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
        (stackProgramEvalAssignment U programCode result) <->
      ∃ program : List
          (StackToken (Option (Constructible.ZFCarrier U))),
        Represents programCode (encodedStackProgram U program) ∧
          runStackProgram (rudimentaryGenerator U) program [] =
            some [result] := by
  rw [satisfies_stackProgramEvalFormula]
  constructor
  · rintro ⟨hprogramValid, traceCode, htraceValid,
      programLength, traceLength, finalStack,
      hprogramLength, htraceLength, hsuccessor,
      hinitial, hfinal, hfinalStack, hsteps⟩
    rcases
        (satisfies_sequenceValidityFormula_iff_exists_represents
          programCode).mp hprogramValid with
      ⟨rawTokens, hprogramRep⟩
    rcases
        (satisfies_sequenceValidityFormula_iff_exists_represents
          traceCode).mp htraceValid with
      ⟨rawStates, htraceRep⟩
    have hprogramLengthEq :
        programLength = natCode rawTokens.length :=
      (satisfies_hasLength_represents_iff hprogramRep
        programLength).mp hprogramLength
    have htraceLengthEq :
        traceLength = natCode rawStates.length :=
      (satisfies_hasLength_represents_iff htraceRep
        traceLength).mp htraceLength
    have hrawLength : rawStates.length = rawTokens.length + 1 := by
      apply natCode_injective
      rw [← htraceLengthEq, hsuccessor, hprogramLengthEq]
      exact (natCode_succ_eq_insert rawTokens.length).symm
    have hhead : rawStates.head? = some (listCode []) := by
      apply (valueAt_zero_iff_head?_eq htraceRep (by
        intro hnil
        simp only [hnil, List.length_nil] at hrawLength
        omega) (listCode [])).mp
      simpa only [listCode] using hinitial
    have hlast : rawStates.getLast? = some (listCode [result]) := by
      apply (valueAt_last_iff_getLast?_eq htraceRep
        rawTokens.length hrawLength (listCode [result])).mp
      rw [← hprogramLengthEq]
      simpa only [listCode, hfinalStack] using hfinal
    have hchain : RawStackFormulaChain U rawTokens rawStates := by
      refine ⟨hrawLength, ?_⟩
      intro k
      have hkMem : natCode k.1 ∈ programLength := by
        rw [hprogramLengthEq]
        exact (mem_natCode_iff _ _).mpr ⟨k.1, k.2, rfl⟩
      have hkFormula := hsteps (natCode k.1) hkMem
      rcases
          (satisfies_traceStepFormula_represents_iff
            U hprogramRep htraceRep k.1).mp hkFormula with
        ⟨hp, hi, ho, hstep⟩
      simpa only using hstep
    rcases exists_executionTrace_decoding_of_rawStackFormulaChain
        U rawTokens rawStates hhead hchain with
      ⟨program, states, hprogramCodes, hstateCodes, htrace⟩
    have hrun :
        runStackProgram (rudimentaryGenerator U) program [] =
          some [result] := by
      apply (exists_rawStackFormulaTrace_iff_run U program result).mp
      refine ⟨rawStates, ?_, hhead, hlast⟩
      simpa only [encodedStackProgram, hprogramCodes] using hchain
    refine ⟨program, ?_, hrun⟩
    simpa only [encodedStackProgram, hprogramCodes] using hprogramRep
  · rintro ⟨program, hprogramRep, hrun⟩
    rcases (exists_rawStackFormulaTrace_iff_run U program result).mpr
        hrun with
      ⟨rawStates, hchain, hhead, hlast⟩
    let traceCode : ZFSet.{u} := IndexedSequenceZF.sequenceCode rawStates
    have htraceRep : Represents traceCode rawStates := by
      exact represents_sequenceCode rawStates
    refine ⟨
      (satisfies_sequenceValidityFormula_iff_exists_represents
        programCode).mpr ⟨_, hprogramRep⟩,
      traceCode,
      (satisfies_sequenceValidityFormula_iff_exists_represents
        traceCode).mpr ⟨_, htraceRep⟩,
      natCode (encodedStackProgram U program).length,
      natCode rawStates.length,
      listCode [result], ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · exact (satisfies_hasLength_represents_iff hprogramRep _).mpr rfl
    · exact (satisfies_hasLength_represents_iff htraceRep _).mpr rfl
    · rcases hchain with ⟨hlength, _hsteps⟩
      rw [hlength]
      exact natCode_succ_eq_insert _
    · apply (valueAt_zero_iff_head?_eq htraceRep (by
        rcases hchain with ⟨hlength, _hsteps⟩
        intro hnil
        simp only [hnil, List.length_nil] at hlength
        omega) (listCode [])).mpr
      exact hhead
    · rcases hchain with ⟨hlength, _hsteps⟩
      apply (valueAt_last_iff_getLast?_eq htraceRep
        (encodedStackProgram U program).length hlength
        (listCode [result])).mpr
      exact hlast
    · intro index hindex
      rcases (mem_natCode_iff index
          (encodedStackProgram U program).length).mp hindex with
        ⟨k, hk, rfl⟩
      rcases hchain with ⟨hlength, hrawSteps⟩
      apply (satisfies_traceStepFormula_represents_iff
        U hprogramRep htraceRep k).mpr
      refine ⟨hk, by omega, by omega, ?_⟩
      simpa only using hrawSteps ⟨k, hk⟩

/-- Canonical program codes have exactly the intended execution semantics. -/
theorem satisfies_stackProgramEvalFormula_iff_run
    (U : ZFSet.{u})
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
        (stackProgramEvalAssignment U
          (stackProgramZFCode U program) result) <->
      runStackProgram (rudimentaryGenerator U) program [] =
        some [result] := by
  rw [satisfies_stackProgramEvalFormula_iff_exists_run]
  constructor
  · rintro ⟨decoded, hrep, hrun⟩
    have hencoded :
        encodedStackProgram U program = encodedStackProgram U decoded :=
      represents_list_unique
        (represents_sequenceCode (encodedStackProgram U program)) hrep
    have hprogram : program = decoded := by
      apply (stackTokenZFCode_injective U).list_map
      simpa only [encodedStackProgram] using hencoded
    simpa only [hprogram] using hrun
  · intro hrun
    exact ⟨program, represents_sequenceCode _, hrun⟩

end

end Constructible.Godel.RudimentaryTerm
