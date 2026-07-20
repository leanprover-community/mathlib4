/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryLeastProgramSemantics
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalAbsolute
public import Mathlib.SetTheory.ZFC.Constructible.RudimentarySuccessfulProgramOrder
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryConstructible

/-!
# Absoluteness of the least-successful-program value order

The combined least-program formula has unbounded program-code quantifiers.
This file proves its exact semantics in `Model.LCarrier`.  Arbitrary internal
codes are projected to the ambient evaluator and decoded; canonical codes
supply the converse witnesses.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

local notation "LMem" => Model.lCarrierMem

/-! ## Constructible assignments -/

/-- The fifteen constructible parameters of the value-order formula. -/
def leastProgramValueLtParametersLAssignment
    (U relation : Model.LCarrier.{u}) :
    Tuple Model.LCarrier.{u} 15 :=
  snoc
    (snoc (stackStepPrefixLAssignment U.1 U.2)
      ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩)
    relation

/-- The full constructible assignment, with the compared values last. -/
def leastProgramValueLtLAssignment
    (U relation left right : Model.LCarrier.{u}) :
    Tuple Model.LCarrier.{u} 17 :=
  snoc (snoc (leastProgramValueLtParametersLAssignment U relation) left)
    right

theorem leastProgramValueLtLAssignment_val
    (U relation left right : Model.LCarrier.{u}) :
    (fun i => (leastProgramValueLtLAssignment U relation left right i).1) =
      leastProgramValueLtAssignment U.1 relation.1 left.1 right.1 := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rfl
      · refine Fin.lastCases ?_ (fun i12 => ?_) i13
        · rfl
        · simpa only [leastProgramValueLtLAssignment,
            leastProgramValueLtParametersLAssignment,
            leastProgramValueLtAssignment,
            leastProgramValueLtParametersAssignment, snoc_castSucc] using
            congrFun (stackStepPrefixLAssignment_val U.1 U.2) i12

theorem comp_leastProgramLeftEvalRename_lCarrier
    (U relation left right p : Model.LCarrier.{u}) :
    (fun i =>
      snoc (leastProgramValueLtLAssignment U relation left right) p
        (leastProgramLeftEvalRename i)) =
      stackProgramEvalCodeLAssignment U.1 p.1 left.1
        U.2 p.2 left.2 := by
  funext i
  apply Subtype.ext
  have hraw := congrFun
    (comp_leastProgramLeftEvalRename
      U.1 relation.1 left.1 right.1 p.1) i
  calc
    (snoc (leastProgramValueLtLAssignment U relation left right) p
        (leastProgramLeftEvalRename i)).1 =
        snoc
          (fun j =>
            (leastProgramValueLtLAssignment U relation left right j).1)
          p.1 (leastProgramLeftEvalRename i) :=
      congrFun
        (Model.subtypeVal_snoc
          (leastProgramValueLtLAssignment U relation left right) p)
        (leastProgramLeftEvalRename i)
    _ = snoc
          (leastProgramValueLtAssignment U.1 relation.1 left.1 right.1)
          p.1 (leastProgramLeftEvalRename i) := by
      rw [leastProgramValueLtLAssignment_val]
    _ = stackProgramEvalAssignment U.1 p.1 left.1 i := hraw
    _ = (stackProgramEvalCodeLAssignment U.1 p.1 left.1
          U.2 p.2 left.2 i).1 := by
      symm
      exact congrFun
        (stackProgramEvalCodeLAssignment_val
          U.1 p.1 left.1 U.2 p.2 left.2) i

theorem comp_leastProgramRightEvalRename_lCarrier
    (U relation left right p q : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (leastProgramValueLtLAssignment U relation left right) p) q
        (leastProgramRightEvalRename i)) =
      stackProgramEvalCodeLAssignment U.1 q.1 right.1
        U.2 q.2 right.2 := by
  funext i
  apply Subtype.ext
  have hraw := congrFun
    (comp_leastProgramRightEvalRename
      U.1 relation.1 left.1 right.1 p.1 q.1) i
  calc
    (snoc (snoc (leastProgramValueLtLAssignment U relation left right) p) q
        (leastProgramRightEvalRename i)).1 =
        snoc
          (fun j =>
            (snoc (leastProgramValueLtLAssignment U relation left right) p j).1)
          q.1 (leastProgramRightEvalRename i) :=
      congrFun
        (Model.subtypeVal_snoc
          (snoc (leastProgramValueLtLAssignment U relation left right) p) q)
        (leastProgramRightEvalRename i)
    _ = snoc
          (snoc
            (fun j =>
              (leastProgramValueLtLAssignment U relation left right j).1)
            p.1) q.1 (leastProgramRightEvalRename i) := by
      rw [Model.subtypeVal_snoc]
    _ = snoc
          (snoc
            (leastProgramValueLtAssignment U.1 relation.1 left.1 right.1)
            p.1) q.1 (leastProgramRightEvalRename i) := by
      rw [leastProgramValueLtLAssignment_val]
    _ = stackProgramEvalAssignment U.1 q.1 right.1 i := hraw
    _ = (stackProgramEvalCodeLAssignment U.1 q.1 right.1
          U.2 q.2 right.2 i).1 := by
      symm
      exact congrFun
        (stackProgramEvalCodeLAssignment_val
          U.1 q.1 right.1 U.2 q.2 right.2) i

theorem comp_leastProgramOrderRename_lCarrier
    (U relation left right p q : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (leastProgramValueLtLAssignment U relation left right) p) q
        (leastProgramOrderRename i)) =
      stackProgramLtCodeLAssignment U.1 relation.1 p.1 q.1
        U.2 relation.2 p.2 q.2 := by
  funext i
  apply Subtype.ext
  have hraw := congrFun
    (comp_leastProgramOrderRename
      U.1 relation.1 left.1 right.1 p.1 q.1) i
  calc
    (snoc (snoc (leastProgramValueLtLAssignment U relation left right) p) q
        (leastProgramOrderRename i)).1 =
        snoc
          (fun j =>
            (snoc (leastProgramValueLtLAssignment U relation left right) p j).1)
          q.1 (leastProgramOrderRename i) :=
      congrFun
        (Model.subtypeVal_snoc
          (snoc (leastProgramValueLtLAssignment U relation left right) p) q)
        (leastProgramOrderRename i)
    _ = snoc
          (snoc
            (fun j =>
              (leastProgramValueLtLAssignment U relation left right j).1)
            p.1) q.1 (leastProgramOrderRename i) := by
      rw [Model.subtypeVal_snoc]
    _ = snoc
          (snoc
            (leastProgramValueLtAssignment U.1 relation.1 left.1 right.1)
            p.1) q.1 (leastProgramOrderRename i) := by
      rw [leastProgramValueLtLAssignment_val]
    _ = rawStackProgramLtAssignment U.1 relation.1 p.1 q.1 i := hraw
    _ = stackProgramLtCodeAssignment U.1 relation.1 p.1 q.1 i := by
      rw [rawStackProgramLtAssignment_eq_codeAssignment]
    _ = (stackProgramLtCodeLAssignment U.1 relation.1 p.1 q.1
          U.2 relation.2 p.2 q.2 i).1 := by
      symm
      exact congrFun
        (stackProgramLtCodeLAssignment_val U.1 relation.1 p.1 q.1
          U.2 relation.2 p.2 q.2) i

/-! ## Constructible values of the definability step -/

/-- Every member of `godelDef U` is constructible when `U` is. -/
theorem defCarrier_val_mem_L (U : Model.LCarrier.{u})
    (x : DefCarrier U.1) : x.1 ∈ L := by
  rcases (mem_godelDef_iff_exists_rudimentaryTerm.mp x.2).2 with
    ⟨term, hterm⟩
  rw [← hterm]
  exact term.eval_mem_L U.2

/-- Regard a definability-step value as an element of `LCarrier`. -/
def defCarrierToLCarrier (U : Model.LCarrier.{u})
    (x : DefCarrier U.1) : Model.LCarrier.{u} :=
  ⟨x.1, defCarrier_val_mem_L U x⟩

@[simp]
theorem defCarrierToLCarrier_val (U : Model.LCarrier.{u})
    (x : DefCarrier U.1) :
    (defCarrierToLCarrier U x).1 = x.1 := rfl

/-! ## Exact restricted semantics -/

/-- In `LCarrier`, the formula is exactly the successful-program relation. -/
@[simp]
theorem satisfies_leastProgramValueLtFormula_lCarrier_iff_successful
    (U relation : Model.LCarrier.{u}) (x y : DefCarrier U.1) :
    FOFormula.Satisfies LMem leastProgramValueLtFormula
        (leastProgramValueLtLAssignment U relation
          (defCarrierToLCarrier U x) (defCarrierToLCarrier U y)) ↔
      successfulProgramValueRel U.1 relation.1 x y := by
  simp only [leastProgramValueLtFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_rename,
    satisfies_formulaImp, comp_leastProgramLeftEvalRename_lCarrier,
    comp_leastProgramRightEvalRename_lCarrier,
    comp_leastProgramOrderRename_lCarrier,
    successfulProgramValueRel]
  constructor
  · rintro ⟨pCode, hpEval, hpBelow⟩
    rcases satisfies_stackProgramEvalFormula_code_lCarrier_to_exists_run
        U.1 pCode.1 x.1 U.2 pCode.2 (defCarrier_val_mem_L U x)
        hpEval with
      ⟨program, hpRepresents, hpRun⟩
    refine ⟨program, hpRun, ?_⟩
    intro other hotherRun
    let otherCode : Model.LCarrier.{u} :=
      ⟨stackProgramZFCode U.1 other,
        stackProgramZFCode_mem_L U.2 other⟩
    have hotherEval :
        FOFormula.Satisfies LMem stackProgramEvalFormula
          (stackProgramEvalCodeLAssignment U.1 otherCode.1 y.1
            U.2 otherCode.2 (defCarrier_val_mem_L U y)) := by
      simpa only [otherCode, stackProgramEvalCodeLAssignment,
        stackProgramEvalLAssignment] using
        (satisfies_stackProgramEvalFormula_lCarrier_of_run
          U.1 U.2 other y.1 (defCarrier_val_mem_L U y) hotherRun)
    have hlt := hpBelow otherCode hotherEval
    exact (satisfies_stackProgramLtFormula_represents_lCarrier_iff
      U.1 relation.1 pCode.1 otherCode.1 U.2 relation.2
      pCode.2 otherCode.2 program other hpRepresents
      (represents_sequenceCode _)).mp hlt
  · rintro ⟨program, hprogramRun, hbelow⟩
    let programCode : Model.LCarrier.{u} :=
      ⟨stackProgramZFCode U.1 program,
        stackProgramZFCode_mem_L U.2 program⟩
    refine ⟨programCode, ?_, ?_⟩
    · have heval :=
        satisfies_stackProgramEvalFormula_lCarrier_of_run
          U.1 U.2 program x.1 (defCarrier_val_mem_L U x) hprogramRun
      change FOFormula.Satisfies LMem stackProgramEvalFormula
        (stackProgramEvalCodeLAssignment U.1 programCode.1
          (defCarrierToLCarrier U x).1 U.2 programCode.2
          (defCarrierToLCarrier U x).2) at heval
      exact heval
    · intro qCode hqEval
      rcases satisfies_stackProgramEvalFormula_code_lCarrier_to_exists_run
          U.1 qCode.1 y.1 U.2 qCode.2 (defCarrier_val_mem_L U y)
          hqEval with
        ⟨other, hqRepresents, hotherRun⟩
      exact (satisfies_stackProgramLtFormula_represents_lCarrier_iff
        U.1 relation.1 programCode.1 qCode.1 U.2 relation.2
        programCode.2 qCode.2 program other
        (represents_sequenceCode _) hqRepresents).mpr
          (hbelow other hotherRun)

/-- With an internally represented generator order, the restricted formula
is also the canonical least-program order on `DefCarrier`. -/
theorem satisfies_leastProgramValueLtFormula_lCarrier_iff_defCarrierStackRel
    (U relation : Model.LCarrier.{u})
    (hwell : Model.InternallyWellOrders relation U)
    (x y : DefCarrier U.1) :
    FOFormula.Satisfies LMem leastProgramValueLtFormula
        (leastProgramValueLtLAssignment U relation
          (defCarrierToLCarrier U x) (defCarrierToLCarrier U y)) ↔
      @defCarrierStackRel U.1
        (generatorTokenRel U.1 relation.1)
        (generatorTokenRel_isWellOrder_of_internal U relation hwell)
        x y := by
  rw [satisfies_leastProgramValueLtFormula_lCarrier_iff_successful]
  exact Iff.of_eq (congrFun (congrFun
    (successfulProgramValueRel_eq_defCarrierStackRel_of_internal
      U relation hwell) x) y)

end

end Constructible.Godel.RudimentaryTerm
