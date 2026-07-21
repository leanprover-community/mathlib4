/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalSemantics
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramOrderAbsolute
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackStepAbsolute

/-!
# Absoluteness of the fixed postfix-program evaluator

The ambient evaluator accepts arbitrary finite indexed codes.  For the
constructible universe we need more: every unbounded witness used by an
evaluation certificate must itself belong to `L`.  This file proves the
restricted semantics for genuine program codes by projecting restricted
certificates to the ambient universe and, conversely, by encoding the
canonical execution trace of a successful run.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF
open Constructible.FiniteSequenceZF

local notation "LMem" => Model.lCarrierMem

/-- Satisfaction depends only on the pointwise values of an assignment. -/
private theorem satisfies_congr_assignment {A : Type u}
    (E : A → A → Prop) {n : Nat} (phi : FOFormula n)
    (s t : Tuple A n) (h : ∀ i, s i = t i) :
    FOFormula.Satisfies E phi s ↔ FOFormula.Satisfies E phi t := by
  induction phi with
  | mem i j =>
      change E (s i) (s j) ↔ E (t i) (t j)
      rw [h i, h j]
  | eq i j =>
      change s i = s j ↔ t i = t j
      rw [h i, h j]
  | neg phi ih =>
      exact not_congr (ih s t h)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi s t h) (ihPsi s t h)
  | ex phi ih =>
      simp only [FOFormula.Satisfies]
      apply exists_congr
      intro x
      apply ih
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [snoc_last]
      · simpa only [snoc_castSucc] using h j

@[simp, nolint simpNF]
private theorem subtypeVal_snoc_apply {n : Nat}
    (s : Tuple Model.LCarrier.{u} n) (x : Model.LCarrier.{u})
    (i : Fin (n + 1)) :
    (snoc s x i).1 = snoc (fun j => (s j).1) x.1 i := by
  exact congrFun (Model.subtypeVal_snoc s x) i

/-! ## One-way projection to the ambient universe -/

/-- Restricted validity of a constructible sequence implies ambient validity. -/
private theorem sequenceValidity_lCarrier_to_ambient
    (omega sequence : Model.LCarrier.{u})
    (hvalid :
      FOFormula.Satisfies LMem sequenceValidityFormula ![omega, sequence]) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
      ![omega.1, sequence.1] := by
  rw [satisfies_sequenceValidityFormula_lCarrier] at hvalid
  rw [IndexedSequenceZF.satisfies_sequenceValidityFormula]
  rcases hvalid with
    ⟨length, graph, hsequence, hlength, hfunctional⟩
  refine ⟨length.1, graph.1, hsequence, hlength, ?_⟩
  intro index hindex
  let indexL : Model.LCarrier.{u} :=
    ⟨index, mem_L_of_mem hindex length.2⟩
  rcases hfunctional indexL hindex with
    ⟨value, hvalue, hunique⟩
  refine ⟨value.1, hvalue, ?_⟩
  intro other hother
  let otherL : Model.LCarrier.{u} :=
    ⟨other,
      mem_L_of_mem (pair_left_mem_pairField hother)
        (pairField_mem_L graph.2)⟩
  exact hunique otherL hother

private theorem sequenceValidityAssignment_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 2)
    (hvalid : FOFormula.Satisfies LMem sequenceValidityFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
      (fun i => (s i).1) := by
  have hstandard :
      FOFormula.Satisfies LMem sequenceValidityFormula ![s 0, s 1] := by
    apply (satisfies_congr_assignment LMem sequenceValidityFormula
      s ![s 0, s 1] ?_).mp hvalid
    intro i
    fin_cases i <;> rfl
  have hambient := sequenceValidity_lCarrier_to_ambient
    (s 0) (s 1) hstandard
  apply (satisfies_congr_assignment Delta0Formula.ZFMem
    sequenceValidityFormula ![(s 0).1, (s 1).1]
      (fun i => (s i).1) ?_).mp hambient
  intro i
  fin_cases i <;> rfl

/-- The sole graph witness of `hasLengthFormula` also projects to the ambient universe. -/
private theorem hasLength_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 2)
    (hlength : FOFormula.Satisfies LMem hasLengthFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
      (fun i => (s i).1) := by
  simp only [hasLengthFormula, FOFormula.Satisfies] at hlength ⊢
  rcases hlength with ⟨graph, hgraph⟩
  refine ⟨graph.1, ?_⟩
  have hraw :=
    (Delta0Formula.satisfies_toFO_lCarrier_absolute _
      (snoc s graph)).mp hgraph
  simpa only [Model.subtypeVal_snoc] using hraw

/-- The variable branch has no new ambient witnesses beyond its `L` witness. -/
private theorem variableStackStep_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 16)
    (hstep : FOFormula.Satisfies LMem variableStackStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem variableStackStepFormula
      (fun i => (s i).1) := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    FOFormula.satisfies_disj] at hstep ⊢
  rcases hstep with ⟨generator, htoken, hgenerator, houtput⟩
  refine ⟨generator.1, ?_, ?_, ?_⟩
  · have htokenRaw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc s generator)).mp htoken
    simpa only [Model.subtypeVal_snoc] using htokenRaw
  · rcases hgenerator with hgenerator | hgenerator
    · exact Or.inl (congrArg Subtype.val hgenerator)
    · exact Or.inr hgenerator
  · have houtputRaw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc s generator)).mp houtput
    simpa only [Model.subtypeVal_snoc] using houtputRaw

/-- Each operation branch likewise projects all of its constructible witnesses. -/
private theorem operationStackStep_lCarrier_to_ambient (i : Fin 9)
    (s : Tuple Model.LCarrier.{u} 16)
    (hstep : FOFormula.Satisfies LMem (operationStackStepFormula i) s) :
    FOFormula.Satisfies Delta0Formula.ZFMem (operationStackStepFormula i)
      (fun j => (s j).1) := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies, FOFormula.satisfies_rename] at hstep ⊢
  rcases hstep with
    ⟨right, left, rest, result, inner,
      htoken, hinput, hinner, houtput, hop⟩
  refine ⟨right.1, left.1, rest.1, result.1, inner.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc (snoc (snoc (snoc (snoc s right) left) rest)
          result) inner)).mp htoken
    simpa only [Model.subtypeVal_snoc] using hraw
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc (snoc (snoc (snoc (snoc s right) left) rest)
          result) inner)).mp hinput
    simpa only [Model.subtypeVal_snoc] using hraw
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc (snoc (snoc (snoc (snoc s right) left) rest)
          result) inner)).mp hinner
    simpa only [Model.subtypeVal_snoc] using hraw
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _
        (snoc (snoc (snoc (snoc (snoc s right) left) rest)
          result) inner)).mp houtput
    simpa only [Model.subtypeVal_snoc] using hraw
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp hop
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      (opGraphFormula i).toFO _ _ ?_).mp hraw
    intro j
    simp only [subtypeVal_snoc_apply]

/-- A restricted raw stack step is always an ambient raw stack step. -/
private theorem stackStep_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 16)
    (hstep : FOFormula.Satisfies LMem stackStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
      (fun i => (s i).1) := by
  simp only [stackStepFormula, anyOperationStackStepFormula,
    FOFormula.satisfies_disj] at hstep ⊢
  rcases hstep with hvariable | hoperation
  · exact Or.inl (variableStackStep_lCarrier_to_ambient s hvariable)
  · right
    rcases hoperation with h | h | h | h | h | h | h | h | h
    · exact Or.inl (operationStackStep_lCarrier_to_ambient 0 s h)
    · exact Or.inr (Or.inl
        (operationStackStep_lCarrier_to_ambient 1 s h))
    · exact Or.inr (Or.inr (Or.inl
        (operationStackStep_lCarrier_to_ambient 2 s h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_lCarrier_to_ambient 3 s h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_lCarrier_to_ambient 4 s h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_lCarrier_to_ambient 5 s h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (operationStackStep_lCarrier_to_ambient 6 s h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl
          (operationStackStep_lCarrier_to_ambient 7 s h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr
          (operationStackStep_lCarrier_to_ambient 8 s h))))))))

/-- A restricted local trace transition projects to the ambient transition. -/
private theorem traceStep_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 16)
    (hstep : FOFormula.Satisfies LMem traceStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
      (fun i => (s i).1) := by
  simp only [traceStepFormula, traceStepBody, FOFormula.Satisfies,
    FOFormula.satisfies_rename] at hstep ⊢
  rcases hstep with
    ⟨token, input, succ, output,
      htoken, hinput, hsucc, houtput, hstack⟩
  refine ⟨token.1, input.1, succ.1, output.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp htoken
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    simp only [subtypeVal_snoc_apply]
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp hinput
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    simp only [subtypeVal_snoc_apply]
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp hsucc
    change FOFormula.Satisfies Delta0Formula.ZFMem
      (Delta0Formula.successorFOAt (18 : Fin 20) (15 : Fin 20)) _ at hraw
    simpa only [Model.subtypeVal_snoc] using hraw
  · have hraw :=
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp houtput
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    simp only [subtypeVal_snoc_apply]
  · have hraw := stackStep_lCarrier_to_ambient _ hstack
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      stackStepFormula _ _ ?_).mp hraw
    intro i
    simp only [subtypeVal_snoc_apply]

/-- The evaluator core projects one conjunct at a time, avoiding large tuple reduction. -/
private theorem stackProgramEvalCore_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 20)
    (hcore : FOFormula.Satisfies LMem stackProgramEvalCore s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalCore
      (fun i => (s i).1) := by
  rw [stackProgramEvalCore] at hcore ⊢
  rcases hcore with
    ⟨hprogramLength, htraceLength, hsuccessor,
      hinitial, hfinal, hfinalStack, hsteps⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FOFormula.satisfies_rename] at hprogramLength ⊢
    exact hasLength_lCarrier_to_ambient _ hprogramLength
  · rw [FOFormula.satisfies_rename] at htraceLength ⊢
    exact hasLength_lCarrier_to_ambient _ htraceLength
  · exact
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ s).mp hsuccessor
  · rw [FOFormula.satisfies_rename] at hinitial ⊢
    exact
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp hinitial
  · rw [FOFormula.satisfies_rename] at hfinal ⊢
    exact
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ _).mp hfinal
  · exact
      (Delta0Formula.satisfies_toFO_lCarrier_absolute _ s).mp hfinalStack
  · rw [FOFormula.satisfies_boundedAll] at hsteps ⊢
    intro index hindex
    let indexL : Model.LCarrier.{u} :=
      ⟨index, mem_L_of_mem hindex (s 17).2⟩
    have hrestricted := hsteps indexL hindex
    rw [FOFormula.satisfies_rename] at hrestricted ⊢
    have hambient := traceStep_lCarrier_to_ambient _ hrestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      traceStepFormula _ _ ?_).mp hambient
    intro i
    simp only [subtypeVal_snoc_apply, indexL]

/-- Every restricted evaluator certificate is also an ambient certificate. -/
private theorem stackProgramEval_lCarrier_to_ambient
    (s : Tuple Model.LCarrier.{u} 16)
    (heval : FOFormula.Satisfies LMem stackProgramEvalFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
      (fun i => (s i).1) := by
  rw [stackProgramEvalFormula] at heval ⊢
  rcases heval with
    ⟨hprogramValid, trace, htraceValid,
      programLength, traceLength, finalStack, hcore⟩
  refine ⟨?_, trace.1, ?_, programLength.1, traceLength.1,
    finalStack.1, ?_⟩
  · rw [FOFormula.satisfies_rename] at hprogramValid ⊢
    exact sequenceValidityAssignment_lCarrier_to_ambient _ hprogramValid
  · rw [FOFormula.satisfies_rename] at htraceValid ⊢
    let traceValidityAssignment : Tuple Model.LCarrier.{u} 2 :=
      fun i => snoc s trace (evalTraceValidityRename i)
    have htraceRestricted :
        FOFormula.Satisfies LMem sequenceValidityFormula
          traceValidityAssignment := by
      exact htraceValid
    have htraceAmbient :=
      sequenceValidityAssignment_lCarrier_to_ambient
        traceValidityAssignment htraceRestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      sequenceValidityFormula _ _ ?_).mp htraceAmbient
    intro i
    simp only [traceValidityAssignment, subtypeVal_snoc_apply]
  · let coreAssignment : Tuple Model.LCarrier.{u} 20 :=
      snoc (snoc (snoc (snoc s trace) programLength)
        traceLength) finalStack
    have hcoreRestricted :
        FOFormula.Satisfies LMem stackProgramEvalCore coreAssignment := by
      exact hcore
    have hambient := stackProgramEvalCore_lCarrier_to_ambient
      coreAssignment hcoreRestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      stackProgramEvalCore _ _ ?_).mp hambient
    intro i
    simp only [coreAssignment, subtypeVal_snoc_apply]

/-! ## Genuine evaluator assignments -/

/-- The thirteen fixed stack-machine parameters, all packaged in `L`. -/
def stackStepPrefixLAssignment (U : ZFSet.{u}) (hU : U ∈ L) :
    Tuple Model.LCarrier.{u} 13 :=
  ![⟨U, hU⟩,
    ⟨varTag, varTag_mem_L⟩,
    ⟨appTag, appTag_mem_L⟩,
    ⟨∅, empty_mem_L⟩,
    ⟨operationCode 0, operationCode_mem_L 0⟩,
    ⟨operationCode 1, operationCode_mem_L 1⟩,
    ⟨operationCode 2, operationCode_mem_L 2⟩,
    ⟨operationCode 3, operationCode_mem_L 3⟩,
    ⟨operationCode 4, operationCode_mem_L 4⟩,
    ⟨operationCode 5, operationCode_mem_L 5⟩,
    ⟨operationCode 6, operationCode_mem_L 6⟩,
    ⟨operationCode 7, operationCode_mem_L 7⟩,
    ⟨operationCode 8, operationCode_mem_L 8⟩]

theorem stackStepPrefixLAssignment_val (U : ZFSet.{u}) (hU : U ∈ L) :
    (fun i => (stackStepPrefixLAssignment U hU i).1) =
      stackStepPrefixAssignment U := by
  funext i
  fin_cases i <;> rfl

/-- The evaluator assignment for an arbitrary constructible program code. -/
def stackProgramEvalCodeLAssignment
    (U code result : ZFSet.{u})
    (hU : U ∈ L) (hcode : code ∈ L) (hresult : result ∈ L) :
    Tuple Model.LCarrier.{u} 16 :=
  snoc (snoc (snoc (stackStepPrefixLAssignment U hU)
    ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩)
    ⟨code, hcode⟩) ⟨result, hresult⟩

theorem stackProgramEvalCodeLAssignment_val
    (U code result : ZFSet.{u})
    (hU : U ∈ L) (hcode : code ∈ L) (hresult : result ∈ L) :
    (fun i =>
      (stackProgramEvalCodeLAssignment U code result
        hU hcode hresult i).1) =
      stackProgramEvalAssignment U code result := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [stackProgramEvalCodeLAssignment,
          stackProgramEvalAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixLAssignment_val U hU) i12

/-- Restricted satisfaction for an arbitrary constructible code projects to
the ambient evaluator semantics. -/
theorem satisfies_stackProgramEvalFormula_code_lCarrier_to_ambient
    (U code result : ZFSet.{u})
    (hU : U ∈ L) (hcode : code ∈ L) (hresult : result ∈ L)
    (heval : FOFormula.Satisfies LMem stackProgramEvalFormula
      (stackProgramEvalCodeLAssignment U code result
        hU hcode hresult)) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
      (stackProgramEvalAssignment U code result) := by
  have hambient := stackProgramEval_lCarrier_to_ambient _ heval
  simpa only [stackProgramEvalCodeLAssignment_val] using hambient

/-- Every arbitrary constructible evaluator witness decodes to a genuine
postfix program with the stated result. -/
theorem satisfies_stackProgramEvalFormula_code_lCarrier_to_exists_run
    (U code result : ZFSet.{u})
    (hU : U ∈ L) (hcode : code ∈ L) (hresult : result ∈ L)
    (heval : FOFormula.Satisfies LMem stackProgramEvalFormula
      (stackProgramEvalCodeLAssignment U code result
        hU hcode hresult)) :
    ∃ program : List
        (StackToken (Option (Constructible.ZFCarrier U))),
      Represents code (encodedStackProgram U program) ∧
        runStackProgram (rudimentaryGenerator U) program [] =
          some [result] := by
  apply (satisfies_stackProgramEvalFormula_iff_exists_run
    U code result).mp
  exact satisfies_stackProgramEvalFormula_code_lCarrier_to_ambient
    U code result hU hcode hresult heval

/-- The genuine evaluator assignment, with every free coordinate in `L`. -/
def stackProgramEvalLAssignment (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L) :
    Tuple Model.LCarrier.{u} 16 :=
  snoc (snoc (snoc (stackStepPrefixLAssignment U hU)
    ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩)
    ⟨stackProgramZFCode U program,
      stackProgramZFCode_mem_L hU program⟩)
    ⟨result, hresult⟩

theorem stackProgramEvalLAssignment_val (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L) :
    (fun i =>
      (stackProgramEvalLAssignment U hU program result hresult i).1) =
      stackProgramEvalAssignment U (stackProgramZFCode U program) result := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [stackProgramEvalLAssignment,
          stackProgramEvalAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixLAssignment_val U hU) i12

private theorem stackProgramEvalLAssignment_empty
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L) :
    stackProgramEvalLAssignment U hU program result hresult (3 : Fin 16) =
      (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u}) := by
  apply Subtype.ext
  have hval := congrFun
    (stackProgramEvalLAssignment_val U hU program result hresult)
    (3 : Fin 16)
  simpa only [stackProgramEvalAssignment_empty] using hval

/-- Soundness of restricted evaluation on a genuine program code. -/
theorem satisfies_stackProgramEvalFormula_lCarrier_to_run
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (heval : FOFormula.Satisfies LMem stackProgramEvalFormula
      (stackProgramEvalLAssignment U hU program result hresult)) :
    runStackProgram (rudimentaryGenerator U) program [] =
      some [result] := by
  apply (satisfies_stackProgramEvalFormula_iff_run U program result).mp
  have hambient := stackProgramEval_lCarrier_to_ambient _ heval
  simpa only [stackProgramEvalLAssignment_val] using hambient

/-! ## Constructible canonical traces -/

private theorem encodedStackStates_entries_mem_L
    {states : List (List ZFSet.{u})}
    (hstates : ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L) :
    ∀ code ∈ encodedStackStates states, code ∈ L := by
  intro code hcode
  rcases List.mem_map.mp hcode with ⟨stack, hstack, rfl⟩
  exact listCode_mem_L (hstates stack hstack)

private def traceStepExecutionLAssignment
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat) : Tuple Model.LCarrier.{u} 16 :=
  snoc (snoc (snoc (stackStepPrefixLAssignment U hU)
    ⟨stackProgramZFCode U program,
      stackProgramZFCode_mem_L hU program⟩)
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩)
    ⟨natCode k, natCode_mem_L k⟩

private theorem traceStepExecutionLAssignment_val
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat) :
    (fun i =>
      (traceStepExecutionLAssignment U hU program states
        hstateCodes k i).1) =
      traceStepAssignment U (stackProgramZFCode U program)
        (IndexedSequenceZF.sequenceCode (encodedStackStates states))
        (natCode k) := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [traceStepExecutionLAssignment, traceStepAssignment,
          stackStepAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixLAssignment_val U hU) i12

private theorem comp_traceStepProgramValueRename_execution
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat) (token input succ output : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (traceStepExecutionLAssignment U hU program states
          hstateCodes k) token) input) succ) output
        (traceStepProgramValueRename i)) =
      ![⟨stackProgramZFCode U program,
          stackProgramZFCode_mem_L hU program⟩,
        ⟨natCode k, natCode_mem_L k⟩, token] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepInputValueRename_execution
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat) (token input succ output : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (traceStepExecutionLAssignment U hU program states
          hstateCodes k) token) input) succ) output
        (traceStepInputValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
        ⟨natCode k, natCode_mem_L k⟩, input] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepOutputValueRename_execution
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat) (token input succ output : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (traceStepExecutionLAssignment U hU program states
          hstateCodes k) token) input) succ) output
        (traceStepOutputValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
        succ, output] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepStackStepRename_execution
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (k : Nat)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L)
    (succ : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (traceStepExecutionLAssignment U hU program states
          hstateCodes k)
        ⟨stackTokenZFCode U token, stackTokenZFCode_mem_L hU token⟩)
        ⟨listCode input, listCode_mem_L hinput⟩) succ)
        ⟨listCode output, listCode_mem_L houtput⟩
        (traceStepStackStepRename i)) =
      stackStepLAssignment U hU token input output hinput houtput := by
  funext i
  apply Subtype.ext
  have hextendedVal :
      (fun j =>
        (snoc (snoc (snoc (snoc
          (traceStepExecutionLAssignment U hU program states
            hstateCodes k)
          ⟨stackTokenZFCode U token, stackTokenZFCode_mem_L hU token⟩)
          ⟨listCode input, listCode_mem_L hinput⟩) succ)
          ⟨listCode output, listCode_mem_L houtput⟩ j).1) =
        snoc (snoc (snoc (snoc
          (traceStepAssignment U (stackProgramZFCode U program)
            (IndexedSequenceZF.sequenceCode (encodedStackStates states))
            (natCode k))
          (stackTokenZFCode U token)) (listCode input)) succ.1)
          (listCode output) := by
    rw [Model.subtypeVal_snoc, Model.subtypeVal_snoc,
      Model.subtypeVal_snoc, Model.subtypeVal_snoc,
      traceStepExecutionLAssignment_val]
  have hraw := congrFun
    (comp_traceStepStackStepRename U (stackProgramZFCode U program)
      (IndexedSequenceZF.sequenceCode (encodedStackStates states))
      (natCode k) (stackTokenZFCode U token) (listCode input)
      succ.1 (listCode output)) i
  rw [congrFun hextendedVal (traceStepStackStepRename i),
    congrFun (stackStepLAssignment_val U hU token input output
      hinput houtput) i]
  exact hraw

/-- Every genuine indexed execution step has an entirely constructible certificate. -/
private theorem satisfies_traceStepFormula_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hstates : ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L)
    (k : Nat) (hk : k < program.length) :
    FOFormula.Satisfies LMem traceStepFormula
      (traceStepExecutionLAssignment U hU program states
        (encodedStackStates_entries_mem_L hstates) k) := by
  have hlength := htrace.length
  have hi : k < states.length := by omega
  have ho : k + 1 < states.length := by omega
  let token := program.get ⟨k, hk⟩
  let input := states.get ⟨k, hi⟩
  let output := states.get ⟨k + 1, ho⟩
  have hinput : ∀ x ∈ input, x ∈ L :=
    hstates input (List.get_mem states ⟨k, hi⟩)
  have houtput : ∀ x ∈ output, x ∈ L :=
    hstates output (List.get_mem states ⟨k + 1, ho⟩)
  let tokenL : Model.LCarrier.{u} :=
    ⟨stackTokenZFCode U token, stackTokenZFCode_mem_L hU token⟩
  let inputL : Model.LCarrier.{u} :=
    ⟨listCode input, listCode_mem_L hinput⟩
  let succL : Model.LCarrier.{u} :=
    ⟨natCode (k + 1), natCode_mem_L (k + 1)⟩
  let outputL : Model.LCarrier.{u} :=
    ⟨listCode output, listCode_mem_L houtput⟩
  rw [traceStepFormula]
  refine ⟨tokenL, inputL, succL, outputL, ?_⟩
  rw [traceStepBody]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [FOFormula.satisfies_rename,
      comp_traceStepProgramValueRename_execution]
    apply (satisfies_valueAtFormula_lCarrier_iff
      (encodedStackProgram U program)
      (stackTokenCodes_mem_L hU program) k tokenL).mpr
    refine ⟨by simpa only [encodedStackProgram, List.length_map] using hk, ?_⟩
    simp only [encodedStackProgram, tokenL, token,
      List.get_eq_getElem, List.getElem_map]
  · rw [FOFormula.satisfies_rename,
      comp_traceStepInputValueRename_execution]
    apply (satisfies_valueAtFormula_lCarrier_iff
      (encodedStackStates states)
      (encodedStackStates_entries_mem_L hstates) k inputL).mpr
    refine ⟨by simpa only [encodedStackStates, List.length_map] using hi, ?_⟩
    simp only [encodedStackStates, inputL, input,
      List.get_eq_getElem, List.getElem_map]
  · apply (Delta0Formula.satisfies_successorFOAt_lCarrier
      (18 : Fin 20) (15 : Fin 20) _).mpr
    exact natCode_succ_eq_insert k
  · rw [FOFormula.satisfies_rename,
      comp_traceStepOutputValueRename_execution]
    apply (satisfies_valueAtFormula_lCarrier_iff
      (encodedStackStates states)
      (encodedStackStates_entries_mem_L hstates) (k + 1) outputL).mpr
    refine ⟨by simpa only [encodedStackStates, List.length_map] using ho, ?_⟩
    simp only [encodedStackStates, outputL, output,
      List.get_eq_getElem, List.getElem_map]
  · rw [FOFormula.satisfies_rename,
      comp_traceStepStackStepRename_execution
        (hinput := hinput) (houtput := houtput)]
    apply (satisfies_stackStepFormula_lCarrier_iff_run
      U hU token input output hinput houtput).mpr
    rcases htrace.indexed with ⟨_hlength, hsteps⟩
    simpa only [token, input, output] using hsteps ⟨k, hk⟩

private def stackProgramEvalCoreExecutionLAssignment
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    Tuple Model.LCarrier.{u} 20 :=
  snoc (snoc (snoc (snoc
    (stackProgramEvalLAssignment U hU program result hresult)
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩)
    ⟨natCode program.length, natCode_mem_L program.length⟩)
    ⟨natCode states.length, natCode_mem_L states.length⟩)
    ⟨listCode [result], listCode_mem_L (by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact hresult)⟩

private theorem stackProgramEvalCoreExecutionLAssignment_val
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    (fun i =>
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes i).1) =
      snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U (stackProgramZFCode U program) result)
        (IndexedSequenceZF.sequenceCode (encodedStackStates states)))
        (natCode program.length)) (natCode states.length))
        (listCode [result]) := by
  rw [stackProgramEvalCoreExecutionLAssignment,
    Model.subtypeVal_snoc, Model.subtypeVal_snoc,
    Model.subtypeVal_snoc, Model.subtypeVal_snoc,
    stackProgramEvalLAssignment_val]

private theorem stackProgramEvalCoreExecutionLAssignment_trace
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    stackProgramEvalCoreExecutionLAssignment U hU program result hresult
        states hstateCodes (16 : Fin 20) =
      ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
        IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩ := by
  change stackProgramEvalCoreExecutionLAssignment U hU program result
      hresult states hstateCodes
      (Fin.last 16).castSucc.castSucc.castSucc = _
  rw [stackProgramEvalCoreExecutionLAssignment,
    snoc_castSucc, snoc_castSucc, snoc_castSucc, snoc_last]

private theorem stackProgramEvalCoreExecutionLAssignment_programLength
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    stackProgramEvalCoreExecutionLAssignment U hU program result hresult
        states hstateCodes (17 : Fin 20) =
      ⟨natCode program.length, natCode_mem_L program.length⟩ := by
  change stackProgramEvalCoreExecutionLAssignment U hU program result
      hresult states hstateCodes (Fin.last 17).castSucc.castSucc = _
  rw [stackProgramEvalCoreExecutionLAssignment,
    snoc_castSucc, snoc_castSucc, snoc_last]

private theorem stackProgramEvalCoreExecutionLAssignment_finalStack
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    (stackProgramEvalCoreExecutionLAssignment U hU program result hresult
        states hstateCodes (19 : Fin 20)).1 = listCode [result] := by
  change (stackProgramEvalCoreExecutionLAssignment U hU program result
      hresult states hstateCodes (Fin.last 19)).1 = _
  rw [stackProgramEvalCoreExecutionLAssignment, snoc_last]

private theorem stackProgramEvalCoreExecutionLAssignment_result
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    (stackProgramEvalCoreExecutionLAssignment U hU program result hresult
        states hstateCodes (15 : Fin 20)).1 = result := by
  change (stackProgramEvalCoreExecutionLAssignment U hU program result
      hresult states hstateCodes
      (Fin.last 15).castSucc.castSucc.castSucc.castSucc).1 = _
  rw [stackProgramEvalCoreExecutionLAssignment,
    snoc_castSucc, snoc_castSucc, snoc_castSucc, snoc_castSucc,
    stackProgramEvalLAssignment, snoc_last]

private theorem stackProgramEvalCoreExecutionLAssignment_empty
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    stackProgramEvalCoreExecutionLAssignment U hU program result hresult
        states hstateCodes (3 : Fin 20) =
      (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u}) := by
  change stackProgramEvalCoreExecutionLAssignment U hU program result
      hresult states hstateCodes
      (3 : Fin 16).castSucc.castSucc.castSucc.castSucc = _
  rw [stackProgramEvalCoreExecutionLAssignment,
    snoc_castSucc, snoc_castSucc, snoc_castSucc, snoc_castSucc]
  exact stackProgramEvalLAssignment_empty U hU program result hresult

/-- The bounded local-step conjunct of a genuine execution trace. -/
private theorem satisfies_evalTraceSteps_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hstates : ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L)
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    FOFormula.Satisfies LMem
      (FOFormula.boundedAll (17 : Fin 20)
        (FOFormula.rename evalTraceStepRename traceStepFormula))
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  rw [FOFormula.satisfies_boundedAll]
  intro index hindex
  change index.1 ∈ natCode program.length at hindex
  rcases (mem_natCode_iff index.1 program.length).mp hindex with
    ⟨k, hk, hindexValue⟩
  have hindex : index =
      (⟨natCode k, natCode_mem_L k⟩ : Model.LCarrier.{u}) :=
    Subtype.ext hindexValue
  subst index
  rw [FOFormula.satisfies_rename]
  have hlocal := satisfies_traceStepFormula_execution_lCarrier
    U hU program states htrace hstates k hk
  apply (satisfies_congr_assignment LMem traceStepFormula _ _ ?_).mpr
    hlocal
  intro i
  apply Subtype.ext
  have hextendedVal :
      (fun j =>
        (snoc (stackProgramEvalCoreExecutionLAssignment U hU program
            result hresult states hstateCodes)
          (⟨natCode k, natCode_mem_L k⟩ : Model.LCarrier.{u}) j).1) =
        snoc (snoc (snoc (snoc (snoc
          (stackProgramEvalAssignment U (stackProgramZFCode U program)
            result)
          (IndexedSequenceZF.sequenceCode (encodedStackStates states)))
          (natCode program.length)) (natCode states.length))
          (listCode [result])) (natCode k) := by
    rw [Model.subtypeVal_snoc,
      stackProgramEvalCoreExecutionLAssignment_val]
  have hraw := congrFun
    (comp_evalTraceStepRename U (stackProgramZFCode U program)
      result (IndexedSequenceZF.sequenceCode (encodedStackStates states))
      (natCode program.length) (natCode states.length)
      (listCode [result]) (natCode k)) i
  rw [congrFun hextendedVal (evalTraceStepRename i),
    congrFun (traceStepExecutionLAssignment_val U hU program states
      hstateCodes k) i]
  exact hraw

private theorem satisfies_evalProgramLength_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    FOFormula.Satisfies LMem
      (FOFormula.rename evalProgramLengthRename hasLengthFormula)
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  have hprogramCodes :
      ∀ code ∈ encodedStackProgram U program, code ∈ L := by
    simpa only [encodedStackProgram] using stackTokenCodes_mem_L hU program
  let programL : Model.LCarrier.{u} :=
    ⟨stackProgramZFCode U program,
      stackProgramZFCode_mem_L hU program⟩
  let programLengthL : Model.LCarrier.{u} :=
    ⟨natCode program.length, natCode_mem_L program.length⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i =>
        stackProgramEvalCoreExecutionLAssignment U hU program result
          hresult states hstateCodes (evalProgramLengthRename i)) =
        ![programL, programLengthL] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp]
  apply (satisfies_hasLengthFormula_lCarrier_iff
    (encodedStackProgram U program) hprogramCodes programLengthL).mpr
  simp only [programLengthL, encodedStackProgram, List.length_map]

private theorem satisfies_evalTraceLength_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    FOFormula.Satisfies LMem
      (FOFormula.rename evalTraceLengthRename hasLengthFormula)
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  let traceL : Model.LCarrier.{u} :=
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩
  let traceLengthL : Model.LCarrier.{u} :=
    ⟨natCode states.length, natCode_mem_L states.length⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i =>
        stackProgramEvalCoreExecutionLAssignment U hU program result
          hresult states hstateCodes (evalTraceLengthRename i)) =
        ![traceL, traceLengthL] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp]
  apply (satisfies_hasLengthFormula_lCarrier_iff
    (encodedStackStates states) hstateCodes traceLengthL).mpr
  simp only [traceLengthL, encodedStackStates, List.length_map]

private theorem satisfies_evalSuccessor_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (hlength : states.length = program.length + 1) :
    FOFormula.Satisfies LMem
      (Delta0Formula.successorFOAt (18 : Fin 20) (17 : Fin 20))
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  apply (Delta0Formula.satisfies_successorFOAt_lCarrier
    (18 : Fin 20) (17 : Fin 20) _).mpr
  change natCode states.length =
    insert (natCode program.length) (natCode program.length)
  rw [hlength]
  exact natCode_succ_eq_insert program.length

private theorem exists_encodedStackStates_zero_eq
    (states : List (List ZFSet.{u}))
    (hstatesNonempty : 0 < states.length)
    (hhead : states.head? = some []) :
    ∃ hzero : 0 < (encodedStackStates states).length,
      listCode [] = (encodedStackStates states).get ⟨0, hzero⟩ := by
  have hrawHead :
      (encodedStackStates states).head? = some (listCode []) := by
    simp only [encodedStackStates, List.head?_map, hhead,
      Option.map_some]
  have hzero : 0 < (encodedStackStates states).length := by
    simpa only [encodedStackStates, List.length_map] using hstatesNonempty
  refine ⟨hzero, ?_⟩
  rw [List.head?_eq_getElem?,
    List.getElem?_eq_getElem hzero] at hrawHead
  exact (Option.some.inj hrawHead).symm

private theorem comp_evalInitialValueRename_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    (fun i =>
      stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes (evalInitialValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
        (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u}),
        (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u})] := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun x => ?_) j) i
  · exact stackProgramEvalCoreExecutionLAssignment_trace
      U hU program result hresult states hstateCodes
  · exact stackProgramEvalCoreExecutionLAssignment_empty
      U hU program result hresult states hstateCodes
  · fin_cases x
    exact stackProgramEvalCoreExecutionLAssignment_empty
      U hU program result hresult states hstateCodes

private theorem satisfies_valueAt_zero_encodedStackStates_lCarrier
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (hstatesNonempty : 0 < states.length)
    (hhead : states.head? = some []) :
    FOFormula.Satisfies LMem valueAtFormula
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
        (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u}),
        (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u})] := by
  rcases exists_encodedStackStates_zero_eq states hstatesNonempty hhead with
    ⟨hrawZero, hrawHeadGet⟩
  let emptyL : Model.LCarrier.{u} := ⟨∅, empty_mem_L⟩
  let zeroL : Model.LCarrier.{u} := ⟨natCode 0, natCode_mem_L 0⟩
  have hvalue :
      FOFormula.Satisfies LMem valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
          zeroL, emptyL] := by
    exact (satisfies_valueAtFormula_lCarrier_iff
      (encodedStackStates states) hstateCodes 0 emptyL).mpr
        ⟨hrawZero, hrawHeadGet⟩
  apply (satisfies_congr_assignment LMem valueAtFormula _ _ ?_).mpr hvalue
  intro i
  fin_cases i
  · rfl
  · apply Subtype.ext
    change (∅ : ZFSet.{u}) = natCode 0
    simp [natCode]
  · rfl

private theorem satisfies_evalInitial_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (hlength : states.length = program.length + 1)
    (hhead : states.head? = some []) :
    FOFormula.Satisfies LMem
      (FOFormula.rename evalInitialValueRename valueAtFormula)
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  have hvalue :
      FOFormula.Satisfies LMem valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩,
          (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u}),
          (⟨∅, empty_mem_L⟩ : Model.LCarrier.{u})] := by
    exact satisfies_valueAt_zero_encodedStackStates_lCarrier
      states hstateCodes (by omega) hhead
  rw [FOFormula.satisfies_rename]
  apply (satisfies_congr_assignment LMem valueAtFormula _ _ ?_).mpr hvalue
  intro i
  exact congrFun
    (comp_evalInitialValueRename_execution_lCarrier U hU program result
      hresult states hstateCodes) i

private theorem satisfies_evalFinal_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L)
    (hlength : states.length = program.length + 1)
    (hlast : states.getLast? = some [result]) :
    FOFormula.Satisfies LMem
      (FOFormula.rename evalFinalValueRename valueAtFormula)
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  have hrawLast :
      (encodedStackStates states).getLast? =
        some (listCode [result]) := by
    simp only [encodedStackStates, List.getLast?_map, hlast,
      Option.map_some]
  have hrawLength :
      (encodedStackStates states).length = program.length + 1 := by
    simpa only [encodedStackStates, List.length_map] using hlength
  have hrawProgramLength :
      program.length < (encodedStackStates states).length := by omega
  have hrawLastGet :
      listCode [result] =
        (encodedStackStates states).get
          ⟨program.length, hrawProgramLength⟩ := by
    have hgetLast :
        (encodedStackStates states).getLast? =
          some ((encodedStackStates states).get
            ⟨program.length, hrawProgramLength⟩) := by
      rw [List.getLast?_eq_getElem?]
      have hindex :
          (encodedStackStates states).length - 1 = program.length := by
        omega
      rw [hindex, List.getElem?_eq_getElem hrawProgramLength]
      rfl
    rw [hgetLast] at hrawLast
    exact (Option.some.inj hrawLast).symm
  let traceL : Model.LCarrier.{u} :=
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩
  let programLengthL : Model.LCarrier.{u} :=
    ⟨natCode program.length, natCode_mem_L program.length⟩
  let finalStackL : Model.LCarrier.{u} :=
    ⟨listCode [result], listCode_mem_L (by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact hresult)⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i =>
        stackProgramEvalCoreExecutionLAssignment U hU program result
          hresult states hstateCodes (evalFinalValueRename i)) =
        ![traceL, programLengthL, finalStackL] := by
    funext i
    fin_cases i
    · exact stackProgramEvalCoreExecutionLAssignment_trace
        U hU program result hresult states hstateCodes
    · exact stackProgramEvalCoreExecutionLAssignment_programLength
        U hU program result hresult states hstateCodes
    · apply Subtype.ext
      exact stackProgramEvalCoreExecutionLAssignment_finalStack
        U hU program result hresult states hstateCodes
  rw [hcomp]
  apply (satisfies_valueAtFormula_lCarrier_iff
    (encodedStackStates states) hstateCodes program.length finalStackL).mpr
  exact ⟨hrawProgramLength, hrawLastGet⟩

private theorem satisfies_evalFinalStack_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    FOFormula.Satisfies LMem
      (Delta0Formula.kuratowskiPairEqAt
        (19 : Fin 20) (15 : Fin 20) (3 : Fin 20)).toFO
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  apply (satisfies_kuratowskiPairEqAt_lCarrier
    (19 : Fin 20) (15 : Fin 20) (3 : Fin 20) _).mpr
  rw [stackProgramEvalCoreExecutionLAssignment_finalStack,
    stackProgramEvalCoreExecutionLAssignment_result]
  have hempty := congrArg Subtype.val
    (stackProgramEvalCoreExecutionLAssignment_empty U hU program result
      hresult states hstateCodes)
  rw [hempty]
  rfl

/-- Length and endpoint checks for the canonical constructible trace. -/
private theorem satisfies_stackProgramEvalCore_execution_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hhead : states.head? = some [])
    (hlast : states.getLast? = some [result])
    (hstates : ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L)
    (hstateCodes : ∀ code ∈ encodedStackStates states, code ∈ L) :
    FOFormula.Satisfies LMem stackProgramEvalCore
      (stackProgramEvalCoreExecutionLAssignment U hU program result
        hresult states hstateCodes) := by
  rw [stackProgramEvalCore]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact satisfies_evalProgramLength_execution_lCarrier
      U hU program result hresult states hstateCodes
  · exact satisfies_evalTraceLength_execution_lCarrier
      U hU program result hresult states hstateCodes
  · exact satisfies_evalSuccessor_execution_lCarrier
      U hU program result hresult states hstateCodes htrace.length
  · exact satisfies_evalInitial_execution_lCarrier
      U hU program result hresult states hstateCodes htrace.length hhead
  · exact satisfies_evalFinal_execution_lCarrier
      U hU program result hresult states hstateCodes htrace.length hlast
  · exact satisfies_evalFinalStack_execution_lCarrier
      U hU program result hresult states hstateCodes
  · exact satisfies_evalTraceSteps_execution_lCarrier
      U hU program result hresult states htrace hstates hstateCodes

/-- Completeness: a successful run supplies a fully constructible evaluator trace. -/
theorem satisfies_stackProgramEvalFormula_lCarrier_of_run
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L)
    (hrun : runStackProgram (rudimentaryGenerator U) program [] =
      some [result]) :
    FOFormula.Satisfies LMem stackProgramEvalFormula
      (stackProgramEvalLAssignment U hU program result hresult) := by
  rcases exists_executionTrace_of_run
      (rudimentaryGenerator U) program [] [result] hrun with
    ⟨states, htrace, hhead, hlast⟩
  have hstates : ∀ stack ∈ states, ∀ x ∈ stack, x ∈ L :=
    htrace.entries_mem_L hU hhead (by simp)
  have hstateCodes :
      ∀ code ∈ encodedStackStates states, code ∈ L :=
    encodedStackStates_entries_mem_L hstates
  have hprogramCodes :
      ∀ code ∈ encodedStackProgram U program, code ∈ L := by
    simpa only [encodedStackProgram] using stackTokenCodes_mem_L hU program
  let omegaL : Model.LCarrier.{u} :=
    ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩
  let programL : Model.LCarrier.{u} :=
    ⟨stackProgramZFCode U program,
      stackProgramZFCode_mem_L hU program⟩
  let traceL : Model.LCarrier.{u} :=
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      IndexedSequenceZF.sequenceCode_mem_L hstateCodes⟩
  let programLengthL : Model.LCarrier.{u} :=
    ⟨natCode program.length, natCode_mem_L program.length⟩
  let traceLengthL : Model.LCarrier.{u} :=
    ⟨natCode states.length, natCode_mem_L states.length⟩
  let finalStackL : Model.LCarrier.{u} :=
    ⟨listCode [result], listCode_mem_L (by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact hresult)⟩
  let baseAssignment :=
    stackProgramEvalLAssignment U hU program result hresult
  let traceContext : Tuple Model.LCarrier.{u} 17 :=
    snoc baseAssignment traceL
  rw [stackProgramEvalFormula]
  refine ⟨?_, traceL, ?_, programLengthL, traceLengthL,
    finalStackL, ?_⟩
  · rw [FOFormula.satisfies_rename]
    have hcomp :
        (fun i => baseAssignment (evalProgramValidityRename i)) =
          ![omegaL, programL] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    simpa only [programL, stackProgramZFCode, encodedStackProgram] using
      (satisfies_sequenceValidity_sequenceCode_lCarrier
        (encodedStackProgram U program) hprogramCodes)
  · rw [FOFormula.satisfies_rename]
    have hcomp :
        (fun i => traceContext (evalTraceValidityRename i)) =
          ![omegaL, traceL] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    exact satisfies_sequenceValidity_sequenceCode_lCarrier
      (encodedStackStates states) hstateCodes
  · exact satisfies_stackProgramEvalCore_execution_lCarrier
      U hU program result hresult states htrace hhead hlast
        hstates hstateCodes

/-- Genuine program evaluation is absolute between `LCarrier` and the ambient universe. -/
@[simp]
theorem satisfies_stackProgramEvalFormula_lCarrier_iff_run
    (U : ZFSet.{u}) (hU : U ∈ L)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ L) :
    FOFormula.Satisfies LMem stackProgramEvalFormula
        (stackProgramEvalLAssignment U hU program result hresult) ↔
      runStackProgram (rudimentaryGenerator U) program [] =
        some [result] := by
  constructor
  · exact satisfies_stackProgramEvalFormula_lCarrier_to_run
      U hU program result hresult
  · exact satisfies_stackProgramEvalFormula_lCarrier_of_run
      U hU program result hresult

end

end Constructible.Godel.RudimentaryTerm
