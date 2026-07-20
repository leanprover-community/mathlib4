/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackTraceDecode
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackTraceStepFormula

/-!
# A fixed first-order evaluator for postfix rudimentary programs

Evaluation is certified by an internally quantified finite sequence of stack
states.  Both program and trace satisfy the indexed-sequence validity
predicate; their recorded lengths differ by one; the first trace state is the
empty stack; the final state is the singleton result stack; and every program
index satisfies `traceStepFormula`.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

/-! ## Fixed layout and renamings -/

/-
The free layout is

`[U,varTag,appTag,empty,op0,...,op8,omega,program,result]`.

Thus the three final indices are `13,14,15`.  The evaluator then quantifies
`trace, programLength, traceLength, finalStack`, at indices `16,...,19`.
-/

/-- The omega coordinate in the program-evaluation layout. -/
def evalOmegaIndex : Fin 16 := 13
/-- The program coordinate in the program-evaluation layout. -/
def evalProgramIndex : Fin 16 := 14
/-- The result coordinate in the program-evaluation layout. -/
def evalResultIndex : Fin 16 := 15

/-- Select the omega and program coordinates for program validity. -/
def evalProgramValidityRename : Fin 2 → Fin 16 :=
  ![evalOmegaIndex, evalProgramIndex]

/-- Select the omega and trace coordinates for trace validity. -/
def evalTraceValidityRename : Fin 2 → Fin 17 :=
  ![(13 : Fin 17), (16 : Fin 17)]

/-- Select the program and its length coordinate. -/
def evalProgramLengthRename : Fin 2 → Fin 20 :=
  ![(14 : Fin 20), (17 : Fin 20)]

/-- Select the trace and its length coordinate. -/
def evalTraceLengthRename : Fin 2 → Fin 20 :=
  ![(16 : Fin 20), (18 : Fin 20)]

/-- Select the coordinates describing the initial stack value. -/
def evalInitialValueRename : Fin 3 → Fin 20 :=
  Fin.cases (16 : Fin 20)
    (fun j => Fin.cases (3 : Fin 20) (fun _ => (3 : Fin 20)) j)

/-- Select the coordinates describing the final stack value. -/
def evalFinalValueRename : Fin 3 → Fin 20 :=
  ![(16 : Fin 20), (17 : Fin 20), (19 : Fin 20)]

/-- Embed the local trace-step layout into the evaluator's bounded-index body. -/
def evalTraceStepRename : Fin 16 → Fin 21 :=
  Fin.lastCases (20 : Fin 21)
    (fun i15 => Fin.lastCases (16 : Fin 21)
      (fun i14 => Fin.lastCases (14 : Fin 21)
        (fun i13 =>
          i13.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        i14) i15)

/-! ## Formula -/

/-- The body after trace, both lengths, and the final stack have been chosen. -/
def stackProgramEvalCore : FOFormula 20 :=
  .conj
    (FOFormula.rename evalProgramLengthRename hasLengthFormula)
    (.conj
      (FOFormula.rename evalTraceLengthRename hasLengthFormula)
      (.conj
        (Delta0Formula.successorFOAt (18 : Fin 20) (17 : Fin 20))
        (.conj
          (FOFormula.rename evalInitialValueRename valueAtFormula)
          (.conj
            (FOFormula.rename evalFinalValueRename valueAtFormula)
            (.conj
              (Delta0Formula.kuratowskiPairEqAt
                (19 : Fin 20) (15 : Fin 20) (3 : Fin 20)).toFO
              (FOFormula.boundedAll (17 : Fin 20)
                (FOFormula.rename evalTraceStepRename
                  traceStepFormula)))))))

/-- The complete validity-guarded finite-trace evaluator. -/
def stackProgramEvalFormula : FOFormula 16 :=
  .conj
    (FOFormula.rename evalProgramValidityRename sequenceValidityFormula)
    (.ex
      (.conj
        (FOFormula.rename evalTraceValidityRename sequenceValidityFormula)
        (.ex (.ex (.ex stackProgramEvalCore)))))

/-- Intended assignment to the evaluator's fixed free-variable context. -/
def stackProgramEvalAssignment
    (U program result : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  snoc (snoc (snoc (stackStepPrefixAssignment U)
    Ordinal.omega0.toZFSet) program) result

@[simp]
theorem stackProgramEvalAssignment_empty
    (U program result : ZFSet.{u}) :
    stackProgramEvalAssignment U program result (3 : Fin 16) = ∅ :=
  rfl

@[simp]
theorem stackProgramEvalAssignment_result
    (U program result : ZFSet.{u}) :
    stackProgramEvalAssignment U program result (15 : Fin 16) = result :=
  rfl

/-! ## Assignment computations -/

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

private abbrev evalCoreAssignment
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    Tuple ZFSet.{u} 20 :=
  snoc (snoc (snoc (snoc
    (stackProgramEvalAssignment U program result) trace)
    programLength) traceLength) finalStack

@[simp]
private theorem evalCoreAssignment_trace
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (16 : Fin 20) = trace := by
  rfl

@[simp]
private theorem evalCoreAssignment_programLength
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (17 : Fin 20) = programLength := by
  rfl

@[simp]
private theorem evalCoreAssignment_traceLength
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (18 : Fin 20) = traceLength := by
  rfl

@[simp]
private theorem evalCoreAssignment_finalStack
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (19 : Fin 20) = finalStack := by
  rfl

private theorem evalCoreAssignment_base
    (U program result trace programLength traceLength finalStack : ZFSet.{u})
    (i : Fin 16) :
    evalCoreAssignment U program result trace programLength traceLength
        finalStack i.castSucc.castSucc.castSucc.castSucc =
      stackProgramEvalAssignment U program result i := by
  simp only [evalCoreAssignment, snoc_castSucc]

@[simp]
private theorem evalCoreAssignment_empty
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (3 : Fin 20) = ∅ := by
  change evalCoreAssignment U program result trace programLength traceLength
    finalStack (3 : Fin 16).castSucc.castSucc.castSucc.castSucc = ∅
  rw [evalCoreAssignment_base, stackProgramEvalAssignment_empty]

@[simp]
private theorem evalCoreAssignment_result
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (15 : Fin 20) = result := by
  change evalCoreAssignment U program result trace programLength traceLength
    finalStack (15 : Fin 16).castSucc.castSucc.castSucc.castSucc = result
  rw [evalCoreAssignment_base, stackProgramEvalAssignment_result]

theorem comp_evalProgramValidityRename
    (U program result : ZFSet.{u}) :
    (fun i => stackProgramEvalAssignment U program result
      (evalProgramValidityRename i)) =
      ![Ordinal.omega0.toZFSet, program] := by
  funext i
  fin_cases i <;> rfl

theorem comp_evalTraceValidityRename
    (U program result trace : ZFSet.{u}) :
    (fun i => snoc (stackProgramEvalAssignment U program result) trace
      (evalTraceValidityRename i)) =
      ![Ordinal.omega0.toZFSet, trace] := by
  funext i
  fin_cases i <;> rfl

theorem comp_evalProgramLengthRename
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U program result) trace)
        programLength) traceLength) finalStack
        (evalProgramLengthRename i)) =
      ![program, programLength] := by
  funext i
  fin_cases i <;> rfl

theorem comp_evalTraceLengthRename
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U program result) trace)
        programLength) traceLength) finalStack
        (evalTraceLengthRename i)) =
      ![trace, traceLength] := by
  funext i
  fin_cases i <;> rfl

private theorem satisfies_evalInitialValueRename
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        (fun i => evalCoreAssignment U program result trace programLength
          traceLength finalStack (evalInitialValueRename i)) ↔
      FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![trace, (∅ : ZFSet.{u}), ∅] := by
  apply satisfies_congr_assignment
  intro i
  fin_cases i
  · change evalCoreAssignment U program result trace programLength traceLength
      finalStack (16 : Fin 20) = trace
    exact evalCoreAssignment_trace U program result trace programLength
      traceLength finalStack
  · change evalCoreAssignment U program result trace programLength traceLength
      finalStack (3 : Fin 20) = ∅
    exact evalCoreAssignment_empty U program result trace programLength
      traceLength finalStack
  · change evalCoreAssignment U program result trace programLength traceLength
      finalStack (3 : Fin 20) = ∅
    exact evalCoreAssignment_empty U program result trace programLength
      traceLength finalStack

theorem comp_evalFinalValueRename
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U program result) trace)
        programLength) traceLength) finalStack
        (evalFinalValueRename i)) =
      ![trace, programLength, finalStack] := by
  funext i
  fin_cases i <;> rfl

theorem comp_evalTraceStepRename
    (U program result trace programLength traceLength finalStack index :
      ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U program result) trace)
        programLength) traceLength) finalStack) index
        (evalTraceStepRename i)) =
      traceStepAssignment U program trace index := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rfl
      · simp [stackProgramEvalAssignment, traceStepAssignment,
          stackStepAssignment, evalTraceStepRename]

/-! ## Raw semantic normal form -/

/-- The evaluator decomposes into validity, length, endpoint, and local-step checks. -/
@[simp]
theorem satisfies_stackProgramEvalFormula
    (U program result : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
        (stackProgramEvalAssignment U program result) ↔
      FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
          ![Ordinal.omega0.toZFSet, program] ∧
        ∃ trace : ZFSet.{u},
          FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
              ![Ordinal.omega0.toZFSet, trace] ∧
            ∃ programLength traceLength finalStack : ZFSet.{u},
              FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
                  ![program, programLength] ∧
                FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
                  ![trace, traceLength] ∧
                traceLength = insert programLength programLength ∧
                FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
                  ![trace, (∅ : ZFSet.{u}), ∅] ∧
                FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
                  ![trace, programLength, finalStack] ∧
                finalStack = ZFSet.pair result ∅ ∧
                ∀ index : ZFSet.{u}, index ∈ programLength →
                  FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
                    (traceStepAssignment U program trace index) := by
  simp only [stackProgramEvalFormula, stackProgramEvalCore,
    FOFormula.Satisfies, FOFormula.satisfies_rename,
    FOFormula.satisfies_boundedAll,
    Delta0Formula.satisfies_successorFOAt_ambient,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    comp_evalProgramValidityRename, comp_evalTraceValidityRename,
    comp_evalProgramLengthRename, comp_evalTraceLengthRename,
    satisfies_evalInitialValueRename, comp_evalFinalValueRename,
    comp_evalTraceStepRename, evalCoreAssignment_programLength,
    evalCoreAssignment_traceLength, evalCoreAssignment_finalStack,
    evalCoreAssignment_empty, evalCoreAssignment_result]

end

end Constructible.Godel.RudimentaryTerm
