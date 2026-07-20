/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Delta0GodelGraph
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramZFCode

/-!
# A first-order transition formula for rudimentary stack programs

The fixed parameter layout is

`[U, varTag, appTag, empty, op0, ..., op8, token, input, output]`.

The last three coordinates are the instruction and the two stack states.  A
variable instruction pushes its generator.  An operation instruction pops the
right and left operands, applies the selected Gödel operation, and pushes the
result.  Stack states use `FiniteSequenceZF.listCode`, whose cons constructor
is precisely a Kuratowski pair.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

open Constructible.Delta0Formula

/-! ## Fixed indices -/

/-- The universe coordinate in the stack-step layout. -/
def stackStepUniverseIndex : Fin 16 := 0
/-- The variable-tag coordinate in the stack-step layout. -/
def stackStepVarTagIndex : Fin 16 := 1
/-- The application-tag coordinate in the stack-step layout. -/
def stackStepAppTagIndex : Fin 16 := 2
/-- The empty-stack coordinate in the stack-step layout. -/
def stackStepEmptyIndex : Fin 16 := 3
/-- The token coordinate in the stack-step layout. -/
def stackStepTokenIndex : Fin 16 := 13
/-- The input-stack coordinate in the stack-step layout. -/
def stackStepInputIndex : Fin 16 := 14
/-- The output-stack coordinate in the stack-step layout. -/
def stackStepOutputIndex : Fin 16 := 15

/-- The coordinate of the given rudimentary operation in the stack-step layout. -/
def stackStepOperationIndex (i : Fin 9) : Fin 16 :=
  ⟨4 + i.1, by omega⟩

/-- Lift an original free-variable index through one appended witness. -/
def stackStepLiftOne (i : Fin 16) : Fin 17 :=
  i.castSucc

/-- Lift an original free-variable index through five appended witnesses. -/
def stackStepLiftFive (i : Fin 16) : Fin 21 :=
  i.castSucc.castSucc.castSucc.castSucc.castSucc

/-- Select `[result,left,right]` in the five-witness operation context. -/
def stackStepOpGraphRename : Fin 3 → Fin 21 :=
  ![(19 : Fin 21), (17 : Fin 21), (16 : Fin 21)]

theorem comp_stackStepOpGraphRename {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    (fun i => snoc (snoc (snoc (snoc (snoc s right) left) rest)
      result) inner (stackStepOpGraphRename i)) =
      ![result, left, right] := by
  funext i
  fin_cases i <;> rfl

/-! ## Variable and operation branches -/

/-- The variable-token transition branch. -/
def variableStackStepFormula : FOFormula 16 :=
  .ex
    (.conj
      (Delta0Formula.tripleEqAt
        (stackStepLiftOne stackStepTokenIndex)
        (stackStepLiftOne stackStepVarTagIndex)
        (Fin.last 16)
        (stackStepLiftOne stackStepEmptyIndex)).toFO
      (.conj
        (FOFormula.disj
          (.eq (Fin.last 16)
            (stackStepUniverseIndex.castSucc))
          (.mem (Fin.last 16)
            (stackStepUniverseIndex.castSucc)))
        (Delta0Formula.kuratowskiPairEqAt
          (stackStepOutputIndex.castSucc)
          (Fin.last 16)
          (stackStepInputIndex.castSucc)).toFO))

/--
The operation branch for one of the nine operation indices.  The witnesses,
in order, are `right`, `left`, `rest`, `result`, and the inner input-stack
cell.
-/
def operationStackStepBody (i : Fin 9) : FOFormula 21 :=
  .conj
    (Delta0Formula.tripleEqAt
      (stackStepLiftFive stackStepTokenIndex)
      (stackStepLiftFive stackStepAppTagIndex)
      (stackStepLiftFive (stackStepOperationIndex i))
      (stackStepLiftFive stackStepEmptyIndex)).toFO
    (.conj
      (Delta0Formula.kuratowskiPairEqAt
        (stackStepLiftFive stackStepInputIndex)
        (16 : Fin 21) (20 : Fin 21)).toFO
      (.conj
        (Delta0Formula.kuratowskiPairEqAt
          (20 : Fin 21) (17 : Fin 21) (18 : Fin 21)).toFO
        (.conj
          (Delta0Formula.kuratowskiPairEqAt
            (stackStepLiftFive stackStepOutputIndex)
            (19 : Fin 21) (18 : Fin 21)).toFO
          (FOFormula.rename stackStepOpGraphRename
            (opGraphFormula i).toFO))))

/-- The stack-step formula for one rudimentary operation. -/
def operationStackStepFormula (i : Fin 9) : FOFormula 16 :=
  .ex (.ex (.ex (.ex (.ex (operationStackStepBody i)))))

/-- A finite disjunction over all nine operation branches. -/
def anyOperationStackStepFormula : FOFormula 16 :=
  FOFormula.disj (operationStackStepFormula 0)
    (FOFormula.disj (operationStackStepFormula 1)
      (FOFormula.disj (operationStackStepFormula 2)
        (FOFormula.disj (operationStackStepFormula 3)
          (FOFormula.disj (operationStackStepFormula 4)
            (FOFormula.disj (operationStackStepFormula 5)
              (FOFormula.disj (operationStackStepFormula 6)
                (FOFormula.disj (operationStackStepFormula 7)
                  (operationStackStepFormula 8))))))))

/-- The complete fixed one-step transition formula. -/
def stackStepFormula : FOFormula 16 :=
  FOFormula.disj variableStackStepFormula anyOperationStackStepFormula

/-! ## Assignments and semantics -/

/-- The thirteen parameters shared by every stack-step assignment. -/
noncomputable def stackStepPrefixAssignment (U : ZFSet.{u}) :
    Tuple ZFSet.{u} 13 :=
  ![U, varTag, appTag, ∅,
    operationCode 0, operationCode 1, operationCode 2,
    operationCode 3, operationCode 4, operationCode 5,
    operationCode 6, operationCode 7, operationCode 8]

/-- The intended assignment to the fixed transition context. -/
noncomputable def stackStepAssignment (U token input output : ZFSet.{u}) :
    Tuple ZFSet.{u} 16 :=
  snoc (snoc (snoc (stackStepPrefixAssignment U) token) input) output

@[simp]
theorem stackStepAssignment_operation
    (U token input output : ZFSet.{u}) (i : Fin 9) :
    stackStepAssignment U token input output (stackStepOperationIndex i) =
      operationCode i := by
  fin_cases i <;> rfl

@[simp] theorem stackStepAssignment_appTag
    (U token input output : ZFSet.{u}) :
    stackStepAssignment U token input output stackStepAppTagIndex = appTag :=
  rfl

@[simp] theorem stackStepAssignment_empty
    (U token input output : ZFSet.{u}) :
    stackStepAssignment U token input output stackStepEmptyIndex = ∅ :=
  rfl

@[simp] theorem stackStepAssignment_token
    (U token input output : ZFSet.{u}) :
    stackStepAssignment U token input output stackStepTokenIndex = token :=
  rfl

@[simp] theorem stackStepAssignment_input
    (U token input output : ZFSet.{u}) :
    stackStepAssignment U token input output stackStepInputIndex = input :=
  rfl

@[simp] theorem stackStepAssignment_output
    (U token input output : ZFSet.{u}) :
    stackStepAssignment U token input output stackStepOutputIndex = output :=
  rfl

@[simp] theorem stackStepWitness_right {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    snoc (snoc (snoc (snoc (snoc s right) left) rest) result) inner
        (16 : Fin 21) = right :=
  rfl

@[simp] theorem stackStepWitness_left {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    snoc (snoc (snoc (snoc (snoc s right) left) rest) result) inner
        (17 : Fin 21) = left :=
  rfl

@[simp] theorem stackStepWitness_rest {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    snoc (snoc (snoc (snoc (snoc s right) left) rest) result) inner
        (18 : Fin 21) = rest :=
  rfl

@[simp] theorem stackStepWitness_result {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    snoc (snoc (snoc (snoc (snoc s right) left) rest) result) inner
        (19 : Fin 21) = result :=
  rfl

@[simp] theorem stackStepWitness_inner {A : Type u}
    (s : Tuple A 16) (right left rest result inner : A) :
    snoc (snoc (snoc (snoc (snoc s right) left) rest) result) inner
        (20 : Fin 21) = inner :=
  rfl

@[simp]
theorem satisfies_variableStackStepFormula
    (U token input output : ZFSet.{u}) :
    FOFormula.Satisfies ZFMem variableStackStepFormula
        (stackStepAssignment U token input output) ↔
      ∃ generator : ZFSet.{u},
        token = triple varTag generator ∅ ∧
          (generator = U ∨ generator ∈ U) ∧
          output = ZFSet.pair generator input := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_disj, snoc_last, snoc_castSucc,
    stackStepAssignment, stackStepLiftOne,
    stackStepTokenIndex, stackStepVarTagIndex,
    stackStepEmptyIndex, stackStepUniverseIndex,
    stackStepOutputIndex, stackStepInputIndex]
  rfl

@[simp]
theorem satisfies_operationStackStepFormula (i : Fin 9)
    (U token input output : ZFSet.{u}) :
    FOFormula.Satisfies ZFMem (operationStackStepFormula i)
        (stackStepAssignment U token input output) ↔
      ∃ right left rest result : ZFSet.{u},
        token = triple appTag (operationCode i) ∅ ∧
          input = ZFSet.pair right (ZFSet.pair left rest) ∧
          output = ZFSet.pair result rest ∧
          result = op i left right := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_rename,
    snoc_castSucc,
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
      htoken, hinput, hinner, houtput, hop⟩
    have hop' : result = op i left right := by
      rw [comp_stackStepOpGraphRename] at hop
      exact (satisfies_opGraphFormula i result left right).mp hop
    exact ⟨right, left, rest, result, htoken,
      hinput.trans (congrArg (ZFSet.pair right) hinner),
      houtput, hop'⟩
  · rintro ⟨right, left, rest, result,
      htoken, hinput, houtput, hop⟩
    have hop' :
        Delta0Formula.Satisfies ZFMem (opGraphFormula i)
          ![result, left, right] :=
      (satisfies_opGraphFormula i result left right).mpr hop
    refine ⟨right, left, rest, result, ZFSet.pair left rest,
      htoken, hinput, rfl, houtput, ?_⟩
    simpa only [comp_stackStepOpGraphRename] using hop'

@[simp]
theorem satisfies_anyOperationStackStepFormula
    (U token input output : ZFSet.{u}) :
    FOFormula.Satisfies ZFMem anyOperationStackStepFormula
        (stackStepAssignment U token input output) ↔
      ∃ i : Fin 9, ∃ right left rest result : ZFSet.{u},
        token = triple appTag (operationCode i) ∅ ∧
          input = ZFSet.pair right (ZFSet.pair left rest) ∧
          output = ZFSet.pair result rest ∧
          result = op i left right := by
  simp only [anyOperationStackStepFormula, FOFormula.satisfies_disj,
    satisfies_operationStackStepFormula]
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

/-- Raw semantic normal form of the complete transition formula. -/
@[simp]
theorem satisfies_stackStepFormula
    (U token input output : ZFSet.{u}) :
    FOFormula.Satisfies ZFMem stackStepFormula
        (stackStepAssignment U token input output) ↔
      (∃ generator : ZFSet.{u},
        token = triple varTag generator ∅ ∧
          (generator = U ∨ generator ∈ U) ∧
          output = ZFSet.pair generator input) ∨
      (∃ i : Fin 9, ∃ right left rest result : ZFSet.{u},
        token = triple appTag (operationCode i) ∅ ∧
          input = ZFSet.pair right (ZFSet.pair left rest) ∧
          output = ZFSet.pair result rest ∧
          result = op i left right) := by
  simp only [stackStepFormula, FOFormula.satisfies_disj,
    satisfies_variableStackStepFormula,
    satisfies_anyOperationStackStepFormula]

@[simp]
theorem listCode_eq_pair_iff (xs : List ZFSet.{u}) (x : ZFSet.{u})
    (rest : List ZFSet.{u}) :
    FiniteSequenceZF.listCode xs =
        ZFSet.pair x (FiniteSequenceZF.listCode rest) ↔
      xs = x :: rest := by
  rw [← FiniteSequenceZF.listCode_cons,
    FiniteSequenceZF.listCode_inj]

@[simp]
theorem pair_eq_listCode_iff (x : ZFSet.{u}) (rest xs : List ZFSet.{u}) :
    ZFSet.pair x (FiniteSequenceZF.listCode rest) =
        FiniteSequenceZF.listCode xs ↔
      xs = x :: rest := by
  rw [eq_comm, listCode_eq_pair_iff]

theorem zfPair_ne_empty (x y : ZFSet.{u}) :
    ZFSet.pair x y ≠ ∅ := by
  intro h
  have hx : ({x} : ZFSet.{u}) ∈ ZFSet.pair x y := by
    simp [ZFSet.pair]
  rw [h] at hx
  exact ZFSet.notMem_empty _ hx

@[simp]
theorem empty_ne_zfPair (x y : ZFSet.{u}) :
    (∅ : ZFSet.{u}) ≠ ZFSet.pair x y :=
  (zfPair_ne_empty x y).symm

@[simp]
theorem appTag_ne_varTag : (appTag : ZFSet.{u}) ≠ varTag :=
  varTag_ne_appTag.symm

/-- On genuine token and stack codes, the formula is exactly one machine step. -/
@[simp]
theorem satisfies_stackStepFormula_iff_run
    (U : ZFSet.{u})
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u}) :
    FOFormula.Satisfies ZFMem stackStepFormula
        (stackStepAssignment U (stackTokenZFCode U token)
          (FiniteSequenceZF.listCode input)
          (FiniteSequenceZF.listCode output)) ↔
      runStackToken (rudimentaryGenerator U) token input = some output := by
  cases token with
  | inl generator =>
      cases generator <;>
        simp [satisfies_stackStepFormula, stackTokenZFCode,
          runStackToken, rudimentaryGenerator, triple, ZFSet.pair_inj,
          eq_comm]
  | inr operation =>
      cases input with
      | nil =>
          simp [satisfies_stackStepFormula, stackTokenZFCode,
            runStackToken, triple, ZFSet.pair_inj,
            appTag_ne_varTag, operationCode_injective.eq_iff,
            empty_ne_zfPair]
      | cons right tail =>
          cases tail with
          | nil =>
              simp [satisfies_stackStepFormula, stackTokenZFCode,
                runStackToken, triple, ZFSet.pair_inj,
                appTag_ne_varTag, operationCode_injective.eq_iff,
                empty_ne_zfPair]
          | cons left rest =>
              simp [satisfies_stackStepFormula, stackTokenZFCode,
                runStackToken, triple, ZFSet.pair_inj,
                appTag_ne_varTag, operationCode_injective.eq_iff,
                eq_comm]

end Constructible.Godel.RudimentaryTerm
