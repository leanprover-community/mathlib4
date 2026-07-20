/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.InternalWellOrder
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackStepFormula

/-!
# Absoluteness of one rudimentary stack-machine step

The ambient correctness theorem for `stackStepFormula` quantifies over all
`ZFSet`s.  This file packages its fixed assignment in `LCarrier` and proves
the corresponding correctness theorem when all stack entries are
constructible. The results are stated using both subtype semantics and the
raw-domain semantics `Model.SatisfiesIn L`.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

/-- The intended stack-step assignment, with every coordinate in `L`. -/
def stackStepLAssignment (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    Tuple Model.LCarrier.{u} 16 :=
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
    ⟨operationCode 8, operationCode_mem_L 8⟩,
    ⟨stackTokenZFCode U token, stackTokenZFCode_mem_L hU token⟩,
    ⟨FiniteSequenceZF.listCode input,
      FiniteSequenceZF.listCode_mem_L hinput⟩,
    ⟨FiniteSequenceZF.listCode output,
      FiniteSequenceZF.listCode_mem_L houtput⟩]

theorem stackStepLAssignment_val (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    (fun i =>
      (stackStepLAssignment U hU token input output hinput houtput i).1) =
      stackStepAssignment U (stackTokenZFCode U token)
        (FiniteSequenceZF.listCode input)
        (FiniteSequenceZF.listCode output) := by
  funext i
  fin_cases i <;> rfl

/-- Semantic normal form of the variable branch over `LCarrier`. -/
@[simp]
theorem satisfies_variableStackStepFormula_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        variableStackStepFormula
        (stackStepLAssignment U hU token input output hinput houtput) ↔
      ∃ generator : Model.LCarrier.{u},
        stackTokenZFCode U token = triple varTag generator.1 ∅ ∧
          (generator.1 = U ∨ generator.1 ∈ U) ∧
          FiniteSequenceZF.listCode output =
            ZFSet.pair generator.1 (FiniteSequenceZF.listCode input) := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_lCarrier_absolute,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_disj, snoc_last, snoc_castSucc,
    Model.subtypeVal_snoc, stackStepLAssignment_val,
    stackStepAssignment, stackStepLiftOne,
    stackStepTokenIndex, stackStepVarTagIndex,
    stackStepEmptyIndex, stackStepUniverseIndex,
    stackStepOutputIndex, stackStepInputIndex,
    Subtype.ext_iff]
  rfl

theorem comp_stackStepOpGraphRename_lCarrier
    (s : Tuple Model.LCarrier.{u} 16)
    (right left rest result inner : Model.LCarrier.{u}) :
    (fun i =>
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner (stackStepOpGraphRename i)).1) =
      ![result.1, left.1, right.1] := by
  funext i
  fin_cases i <;> rfl

/-- Semantic normal form of one operation branch over `LCarrier`. -/
@[simp]
theorem satisfies_operationStackStepFormula_lCarrier (i : Fin 9)
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        (operationStackStepFormula i)
        (stackStepLAssignment U hU token input output hinput houtput) ↔
      ∃ right left rest result : Model.LCarrier.{u},
        stackTokenZFCode U token =
            triple appTag (operationCode i) ∅ ∧
          FiniteSequenceZF.listCode input =
            ZFSet.pair right.1 (ZFSet.pair left.1 rest.1) ∧
          FiniteSequenceZF.listCode output =
            ZFSet.pair result.1 rest.1 ∧
          result.1 = op i left.1 right.1 := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_lCarrier_absolute,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_rename,
    snoc_castSucc, Model.subtypeVal_snoc,
    stackStepLAssignment_val,
    stackStepLiftFive,
    stackStepAssignment_operation,
    stackStepAssignment_appTag, stackStepAssignment_empty,
    stackStepAssignment_token, stackStepAssignment_input,
    stackStepAssignment_output,
    stackStepWitness_right, stackStepWitness_left,
    stackStepWitness_rest, stackStepWitness_result,
    stackStepWitness_inner]
  constructor
  · rintro ⟨right, left, rest, result, inner,
      htoken, hinputCode, hinner, houtputCode, hop⟩
    have hop' : result.1 = op i left.1 right.1 := by
      have hopRaw :
          Delta0Formula.Satisfies Delta0Formula.ZFMem (opGraphFormula i)
            ![result.1, left.1, right.1] := by
        simpa only [comp_stackStepOpGraphRename_lCarrier] using hop
      exact
        (satisfies_opGraphFormula i result.1 left.1 right.1).mp hopRaw
    exact ⟨right, left, rest, result, htoken,
      hinputCode.trans (congrArg (ZFSet.pair right.1) hinner),
      houtputCode, hop'⟩
  · rintro ⟨right, left, rest, result,
      htoken, hinputCode, houtputCode, hop⟩
    have hop' :
        Delta0Formula.Satisfies Delta0Formula.ZFMem (opGraphFormula i)
          ![result.1, left.1, right.1] :=
      (satisfies_opGraphFormula i result.1 left.1 right.1).mpr hop
    let inner : Model.LCarrier.{u} :=
      ⟨ZFSet.pair left.1 rest.1, orderedPair_mem_L left.2 rest.2⟩
    refine ⟨right, left, rest, result, inner,
      htoken, hinputCode, rfl, houtputCode, ?_⟩
    simpa only [comp_stackStepOpGraphRename_lCarrier] using hop'

/-- Semantic normal form of the finite operation disjunction over `LCarrier`. -/
@[simp]
theorem satisfies_anyOperationStackStepFormula_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        anyOperationStackStepFormula
        (stackStepLAssignment U hU token input output hinput houtput) ↔
      ∃ i : Fin 9, ∃ right left rest result : Model.LCarrier.{u},
        stackTokenZFCode U token =
            triple appTag (operationCode i) ∅ ∧
          FiniteSequenceZF.listCode input =
            ZFSet.pair right.1 (ZFSet.pair left.1 rest.1) ∧
          FiniteSequenceZF.listCode output =
            ZFSet.pair result.1 rest.1 ∧
          result.1 = op i left.1 right.1 := by
  simp only [anyOperationStackStepFormula, FOFormula.satisfies_disj,
    satisfies_operationStackStepFormula_lCarrier]
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
    · exact ⟨6, h⟩
    · exact ⟨7, h⟩
    · exact ⟨8, h⟩
  · rintro ⟨i, h⟩
    fin_cases i
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr h)))))))

/-- Raw semantic normal form of the complete transition formula over `L`. -/
@[simp]
theorem satisfies_stackStepFormula_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        stackStepFormula
        (stackStepLAssignment U hU token input output hinput houtput) ↔
      (∃ generator : Model.LCarrier.{u},
        stackTokenZFCode U token = triple varTag generator.1 ∅ ∧
          (generator.1 = U ∨ generator.1 ∈ U) ∧
          FiniteSequenceZF.listCode output =
            ZFSet.pair generator.1 (FiniteSequenceZF.listCode input)) ∨
      (∃ i : Fin 9, ∃ right left rest result : Model.LCarrier.{u},
        stackTokenZFCode U token =
            triple appTag (operationCode i) ∅ ∧
          FiniteSequenceZF.listCode input =
            ZFSet.pair right.1 (ZFSet.pair left.1 rest.1) ∧
          FiniteSequenceZF.listCode output =
            ZFSet.pair result.1 rest.1 ∧
          result.1 = op i left.1 right.1) := by
  simp only [stackStepFormula, FOFormula.satisfies_disj,
    satisfies_variableStackStepFormula_lCarrier,
    satisfies_anyOperationStackStepFormula_lCarrier]

/-- On constructible stack codes, satisfaction in `LCarrier` is one step. -/
@[simp]
theorem satisfies_stackStepFormula_lCarrier_iff_run
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        stackStepFormula
        (stackStepLAssignment U hU token input output hinput houtput) ↔
      runStackToken (rudimentaryGenerator U) token input = some output := by
  constructor
  · intro hstep
    apply (satisfies_stackStepFormula_iff_run U token input output).mp
    apply (satisfies_stackStepFormula U
      (stackTokenZFCode U token)
      (FiniteSequenceZF.listCode input)
      (FiniteSequenceZF.listCode output)).mpr
    rw [satisfies_stackStepFormula_lCarrier] at hstep
    rcases hstep with hvar | hop
    · rcases hvar with ⟨generator, htoken, hgenerator, houtputCode⟩
      exact Or.inl
        ⟨generator.1, htoken, hgenerator, houtputCode⟩
    · rcases hop with
        ⟨i, right, left, rest, result, htoken,
          hinputCode, houtputCode, hop⟩
      exact Or.inr
        ⟨i, right.1, left.1, rest.1, result.1,
          htoken, hinputCode, houtputCode, hop⟩
  · intro hrun
    rw [satisfies_stackStepFormula_lCarrier]
    cases token with
    | inl generator =>
        cases generator with
        | none =>
            have houtputEq : output = U :: input := by
              exact (Option.some.inj hrun).symm
            refine Or.inl ⟨⟨U, hU⟩, rfl, Or.inl rfl, ?_⟩
            simp only [houtputEq, FiniteSequenceZF.listCode_cons]
        | some generator =>
            have hgeneratorL : generator.1 ∈ L :=
              mem_L_of_mem generator.2 hU
            have houtputEq : output = generator.1 :: input := by
              exact (Option.some.inj hrun).symm
            refine Or.inl
              ⟨⟨generator.1, hgeneratorL⟩, rfl,
                Or.inr generator.2, ?_⟩
            simp only [houtputEq, FiniteSequenceZF.listCode_cons]
    | inr operation =>
        cases input with
        | nil =>
            cases hrun
        | cons right tail =>
            cases tail with
            | nil =>
                cases hrun
            | cons left rest =>
                have hrightL : right ∈ L :=
                  hinput right (by simp)
                have hleftL : left ∈ L :=
                  hinput left (by simp)
                have hrestEntries : ∀ x ∈ rest, x ∈ L := by
                  intro x hx
                  exact hinput x (by simp [hx])
                have hrestL : FiniteSequenceZF.listCode rest ∈ L :=
                  FiniteSequenceZF.listCode_mem_L hrestEntries
                have hresultL : op operation left right ∈ L :=
                  op_mem_L hleftL hrightL
                have houtputEq :
                    output = op operation left right :: rest := by
                  exact (Option.some.inj hrun).symm
                refine Or.inr
                  ⟨operation,
                    ⟨right, hrightL⟩,
                    ⟨left, hleftL⟩,
                    ⟨FiniteSequenceZF.listCode rest, hrestL⟩,
                    ⟨op operation left right, hresultL⟩,
                    rfl, rfl, ?_, rfl⟩
                simp only [houtputEq,
                  FiniteSequenceZF.listCode_cons]

/--
On genuine token and list codes, satisfaction with every quantifier restricted
to `L` is exactly one stack-machine transition.
-/
@[simp]
theorem satisfiesIn_L_stackStepFormula_iff_run
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    Model.SatisfiesIn L stackStepFormula
        (stackStepAssignment U (stackTokenZFCode U token)
          (FiniteSequenceZF.listCode input)
          (FiniteSequenceZF.listCode output)) ↔
      runStackToken (rudimentaryGenerator U) token input = some output := by
  have hbridge :=
    Model.satisfies_lCarrier_iff_satisfiesIn_L stackStepFormula
      (stackStepLAssignment U hU token input output hinput houtput)
  have hbridgeRaw :
      FOFormula.Satisfies
          (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
          stackStepFormula
          (stackStepLAssignment U hU token input output hinput houtput) ↔
        Model.SatisfiesIn L stackStepFormula
          (stackStepAssignment U (stackTokenZFCode U token)
            (FiniteSequenceZF.listCode input)
            (FiniteSequenceZF.listCode output)) := by
    simpa only [stackStepLAssignment_val] using hbridge
  exact hbridgeRaw.symm.trans
    (satisfies_stackStepFormula_lCarrier_iff_run
      U hU token input output hinput houtput)

end

end Constructible.Godel.RudimentaryTerm
