/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.CanonicalSuccessorOrder
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryDefOutputFormula

/-!
# A deterministic first-order successor step for stage/order states

A recursion state consists of a constructible domain `U` and a constructible
relation graph `oldRelation`.  Its successor consists of `nextU = godelDef U`
and the canonical graph selected by the coherent successor-order formula on
`nextU`.  Both outputs are specified by one fixed first-order formula.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## Formula and assignments -/

/-
The combined layout is

`[U,varTag,appTag,empty,op0,...,op8,omega,oldRelation,nextU,nextRelation]`.

The `godelDef` output formula omits coordinates `oldRelation` and
`nextRelation`; its final output coordinate is therefore sent to `nextU`.
-/

/-- Embed the fifteen-coordinate definability-step output formula into the
seventeen-coordinate successor-state layout. -/
def successorStageGodelDefRename : Fin 15 → Fin 17 :=
  Fin.lastCases (15 : Fin 17)
    (fun i14 => i14.castSucc.castSucc.castSucc)

/-- The fixed first-order graph of one complete successor-state transition. -/
def successorStageStateFormula : FOFormula 17 :=
  .conj
    (FOFormula.rename successorStageGodelDefRename
      Godel.RudimentaryTerm.godelDefOutputFormula)
    canonicalSuccessorOutputFormula

/-- The intended constructible assignment to the combined formula. -/
def successorStageStateLAssignment
    (U oldRelation nextU nextRelation : LCarrier.{u}) :
    Tuple LCarrier.{u} 17 :=
  snoc
    (snoc
      (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
        U oldRelation)
      nextU)
    nextRelation

theorem comp_successorStageGodelDefRename
    (U oldRelation nextU nextRelation : LCarrier.{u}) :
    (fun i => successorStageStateLAssignment
      U oldRelation nextU nextRelation (successorStageGodelDefRename i)) =
      Godel.RudimentaryTerm.godelDefOutputLAssignment U nextU := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · simp only [successorStageGodelDefRename,
      Fin.lastCases_castSucc, successorStageStateLAssignment,
      Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment,
      Godel.RudimentaryTerm.godelDefOutputLAssignment,
      snoc_castSucc]

/-- The canonical graph determined by arbitrary predecessor and successor
domains in the state-transition layout. -/
def canonicalSuccessorStateRelation
    (U oldRelation nextU : LCarrier.{u}) : LCarrier.{u} :=
  canonicalDefinableRelationGraph successorExtensionLtFormula
    (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
      U oldRelation)
    nextU

/-! ## Exact semantics -/

/-- Satisfaction of the combined formula is exactly the intended pair of
output equations. -/
@[simp]
theorem satisfies_successorStageStateFormula_iff
    (U oldRelation nextU nextRelation : LCarrier.{u}) :
    FOFormula.Satisfies LMem successorStageStateFormula
        (successorStageStateLAssignment
          U oldRelation nextU nextRelation) ↔
      nextU.1 = Godel.godelDef U.1 ∧
        nextRelation =
          canonicalSuccessorStateRelation U oldRelation nextU := by
  rw [successorStageStateFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename,
    comp_successorStageGodelDefRename,
    Godel.RudimentaryTerm.satisfies_godelDefOutputFormula_iff]
  change
    nextU.1 = Godel.godelDef U.1 ∧
      FOFormula.Satisfies LMem
        (canonicalGraphOutputFormula successorExtensionLtFormula)
        (snoc
          (snoc
            (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
              U oldRelation)
            nextU)
          nextRelation) ↔
      nextU.1 = Godel.godelDef U.1 ∧
        nextRelation =
          canonicalDefinableRelationGraph successorExtensionLtFormula
            (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
              U oldRelation)
            nextU
  rw [satisfies_canonicalGraphOutputFormula_iff_eq]

/-- On actual constructible stages, the domain equation is automatic and the
second output is the previously defined canonical successor relation. -/
@[simp]
theorem satisfies_successorStageStateFormula_stage_iff
    (alpha : Ordinal.{u}) (relation nextRelation : LCarrier.{u}) :
    FOFormula.Satisfies LMem successorStageStateFormula
        (successorStageStateLAssignment
          (stageLCarrier alpha) relation
          (stageLCarrier (Order.succ alpha)) nextRelation) ↔
      nextRelation = canonicalSuccessorRelation alpha relation := by
  rw [satisfies_successorStageStateFormula_iff]
  have hdomain :
      (stageLCarrier (Order.succ alpha)).1 =
        Godel.godelDef (stageLCarrier alpha).1 := by
    simp only [stageLCarrier_val, LStageZF_succ,
      Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha)]
  simp only [hdomain, true_and]
  rfl

/-! ## Functionality and existence -/

/-- For fixed predecessor data, any two satisfying output pairs coincide. -/
theorem successorStageStateFormula_outputs_unique
    (U oldRelation nextU nextRelation nextU' nextRelation' :
      LCarrier.{u})
    (houtput : FOFormula.Satisfies LMem successorStageStateFormula
      (successorStageStateLAssignment
        U oldRelation nextU nextRelation))
    (houtput' : FOFormula.Satisfies LMem successorStageStateFormula
      (successorStageStateLAssignment
        U oldRelation nextU' nextRelation')) :
    nextU = nextU' ∧ nextRelation = nextRelation' := by
  have h := (satisfies_successorStageStateFormula_iff
    U oldRelation nextU nextRelation).mp houtput
  have h' := (satisfies_successorStageStateFormula_iff
    U oldRelation nextU' nextRelation').mp houtput'
  have hnextU : nextU = nextU' := Subtype.ext (h.1.trans h'.1.symm)
  subst nextU'
  exact ⟨rfl, h.2.trans h'.2.symm⟩

/-- Whenever the next definability layer is constructible, the combined
formula has a unique pair of outputs. -/
theorem existsUnique_successorStageStateFormula
    (U oldRelation : LCarrier.{u})
    (hdef : Godel.godelDef U.1 ∈ L) :
    ∃! output : LCarrier.{u} × LCarrier.{u},
      FOFormula.Satisfies LMem successorStageStateFormula
        (successorStageStateLAssignment
          U oldRelation output.1 output.2) := by
  let nextU : LCarrier.{u} := ⟨Godel.godelDef U.1, hdef⟩
  let nextRelation : LCarrier.{u} :=
    canonicalSuccessorStateRelation U oldRelation nextU
  refine ⟨(nextU, nextRelation), ?_, ?_⟩
  · exact (satisfies_successorStageStateFormula_iff
      U oldRelation nextU nextRelation).mpr ⟨rfl, rfl⟩
  · rintro ⟨otherU, otherRelation⟩ hother
    have hunique := successorStageStateFormula_outputs_unique
      U oldRelation otherU otherRelation nextU nextRelation hother
        ((satisfies_successorStageStateFormula_iff
          U oldRelation nextU nextRelation).mpr ⟨rfl, rfl⟩)
    exact Prod.ext hunique.1 hunique.2

/-- Every actual constructible stage has an unconditional unique successor
state output. -/
theorem existsUnique_successorStageStateFormula_stage
    (alpha : Ordinal.{u}) (relation : LCarrier.{u}) :
    ∃! output : LCarrier.{u} × LCarrier.{u},
      FOFormula.Satisfies LMem successorStageStateFormula
        (successorStageStateLAssignment
          (stageLCarrier alpha) relation output.1 output.2) := by
  have hdef : Godel.godelDef (stageLCarrier alpha).1 ∈ L := by
    rw [stageLCarrier_val,
      ← Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha),
      ← LStageZF_succ]
    exact LStageZF_mem_L (Order.succ alpha)
  exact existsUnique_successorStageStateFormula
    (stageLCarrier alpha) relation hdef

end

end Constructible.Model
