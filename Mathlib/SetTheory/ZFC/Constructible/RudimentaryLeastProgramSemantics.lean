/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryLeastProgramFormula
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalSemantics
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramOrderRepresented

/-!
# Semantics of the least-successful-program value order

The formula from `RudimentaryLeastProgramFormula` quantifies over arbitrary
set codes.  Evaluator satisfaction first decodes such a code to a genuine
postfix program; represented-code invariance of the program-order formula then
compares those decoded programs.  This proves that the formula is exactly the
existing `defCarrierStackRel` defined using `leastStackProgram`.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

/-! ## Assignment compatibility -/

/-- The raw comparison assignment used by the combined formula is the general
represented-code assignment used by the program-order semantics theorem. -/
@[simp]
theorem rawStackProgramLtAssignment_eq_codeAssignment
    (U relation leftCode rightCode : ZFSet.{u}) :
    rawStackProgramLtAssignment U relation leftCode rightCode =
      stackProgramLtCodeAssignment U relation leftCode rightCode := by
  funext i
  fin_cases i <;> rfl

/-! ## Minimality of successful programs -/

/-- No successful program is strictly below the chosen least successful one. -/
private theorem not_stackProgramRel_leastStackProgram_of_run
    (U z : ZFSet.{u}) (hz : z ∈ godelDef U)
    (r : Option (Constructible.ZFCarrier U) ->
      Option (Constructible.ZFCarrier U) -> Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r]
    {program : List
      (StackToken (Option (Constructible.ZFCarrier U)))}
    (hrun : runStackProgram (rudimentaryGenerator U) program [] =
      some [z]) :
    Not (stackProgramRel r program (leastStackProgram U z hz r)) := by
  letI : IsWellOrder
      (List (StackToken (Option (Constructible.ZFCarrier U))))
      (stackProgramRel r) := stackProgramRel_isWellOrder r
  exact
    (IsWellFounded.wf : WellFounded (stackProgramRel r)).not_lt_min
      (representingStackPrograms U z) hrun

/-- The least successful program is equal to, or strictly below, every
successful program. -/
private theorem leastStackProgram_eq_or_stackProgramRel_of_run
    (U z : ZFSet.{u}) (hz : z ∈ godelDef U)
    (r : Option (Constructible.ZFCarrier U) ->
      Option (Constructible.ZFCarrier U) -> Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r]
    {program : List
      (StackToken (Option (Constructible.ZFCarrier U)))}
    (hrun : runStackProgram (rudimentaryGenerator U) program [] =
      some [z]) :
    leastStackProgram U z hz r = program \/
      stackProgramRel r (leastStackProgram U z hz r) program := by
  letI : IsWellOrder
      (List (StackToken (Option (Constructible.ZFCarrier U))))
      (stackProgramRel r) := stackProgramRel_isWellOrder r
  rcases trichotomous_of (stackProgramRel r)
      (leastStackProgram U z hz r) program with
    hlt | heq | hgt
  · exact Or.inr hlt
  · exact Or.inl heq
  · exact (not_stackProgramRel_leastStackProgram_of_run
      U z hz r hrun hgt).elim

/-! ## Exact ambient semantics -/

/--
On the definability step, ambient satisfaction of the fixed formula is exactly
the external least-program order already used to well-order `DefCarrier U`.
-/
theorem satisfies_leastProgramValueLtFormula_iff_defCarrierStackRel
    (U relation : ZFSet.{u}) (x y : DefCarrier U)
    [IsWellOrder (Option (Constructible.ZFCarrier U))
      (generatorTokenRel U relation)] :
    FOFormula.Satisfies Delta0Formula.ZFMem leastProgramValueLtFormula
        (leastProgramValueLtAssignment U relation x.1 y.1) <->
      defCarrierStackRel U (generatorTokenRel U relation) x y := by
  letI : IsWellOrder
      (List (StackToken (Option (Constructible.ZFCarrier U))))
      (stackProgramRel (generatorTokenRel U relation)) :=
    stackProgramRel_isWellOrder (generatorTokenRel U relation)
  rw [satisfies_leastProgramValueLtFormula]
  change
    (exists pCode : ZFSet.{u},
      FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
          (stackProgramEvalAssignment U pCode x.1) /\
        forall qCode : ZFSet.{u},
          FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
              (stackProgramEvalAssignment U qCode y.1) ->
            FOFormula.Satisfies Delta0Formula.ZFMem stackProgramLtFormula
              (rawStackProgramLtAssignment U relation pCode qCode)) <->
      stackProgramRel (generatorTokenRel U relation)
        (leastStackProgram U x.1 x.2 (generatorTokenRel U relation))
        (leastStackProgram U y.1 y.2 (generatorTokenRel U relation))
  constructor
  · rintro ⟨pCode, hpEval, hpBelowEveryY⟩
    rcases
        (satisfies_stackProgramEvalFormula_iff_exists_run
          U pCode x.1).mp hpEval with
      ⟨p, hpRepresents, hpRun⟩
    let leastY :=
      leastStackProgram U y.1 y.2 (generatorTokenRel U relation)
    have hleastYRun :
        runStackProgram (rudimentaryGenerator U) leastY [] =
          some [y.1] := by
      simpa only [leastY] using
        (run_leastStackProgram U y.1 y.2
          (generatorTokenRel U relation))
    have hleastYEval :
        FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
          (stackProgramEvalAssignment U
            (stackProgramZFCode U leastY) y.1) :=
      (satisfies_stackProgramEvalFormula_iff_run U leastY y.1).mpr
        hleastYRun
    have hpLtFormula :=
      hpBelowEveryY (stackProgramZFCode U leastY) hleastYEval
    rw [rawStackProgramLtAssignment_eq_codeAssignment] at hpLtFormula
    have hpLtLeastY :
        stackProgramRel (generatorTokenRel U relation) p leastY :=
      (satisfies_stackProgramLtFormula_represents_iff
        U relation pCode (stackProgramZFCode U leastY)
        p leastY hpRepresents (represents_sequenceCode _)).mp
          hpLtFormula
    rcases leastStackProgram_eq_or_stackProgramRel_of_run
        U x.1 x.2 (generatorTokenRel U relation) hpRun with
      hleastXEq | hleastXLt
    · simpa only [hleastXEq, leastY] using hpLtLeastY
    · exact IsTrans.trans _ _ _ hleastXLt hpLtLeastY
  · intro hleastXLtLeastY
    let leastX :=
      leastStackProgram U x.1 x.2 (generatorTokenRel U relation)
    have hleastXRun :
        runStackProgram (rudimentaryGenerator U) leastX [] =
          some [x.1] := by
      simpa only [leastX] using
        (run_leastStackProgram U x.1 x.2
          (generatorTokenRel U relation))
    refine ⟨stackProgramZFCode U leastX, ?_, ?_⟩
    · exact
        (satisfies_stackProgramEvalFormula_iff_run U leastX x.1).mpr
          hleastXRun
    · intro qCode hqEval
      rcases
          (satisfies_stackProgramEvalFormula_iff_exists_run
            U qCode y.1).mp hqEval with
        ⟨q, hqRepresents, hqRun⟩
      have hleastXLtQ :
          stackProgramRel (generatorTokenRel U relation) leastX q := by
        rcases leastStackProgram_eq_or_stackProgramRel_of_run
            U y.1 y.2 (generatorTokenRel U relation) hqRun with
          hleastYEq | hleastYLt
        · simpa only [leastX, hleastYEq] using hleastXLtLeastY
        · exact IsTrans.trans _ _ _
            (by simpa only [leastX] using hleastXLtLeastY) hleastYLt
      rw [rawStackProgramLtAssignment_eq_codeAssignment]
      exact
        (satisfies_stackProgramLtFormula_represents_iff
          U relation (stackProgramZFCode U leastX) qCode
          leastX q (represents_sequenceCode _) hqRepresents).mpr
            hleastXLtQ

end

end Constructible.Godel.RudimentaryTerm
