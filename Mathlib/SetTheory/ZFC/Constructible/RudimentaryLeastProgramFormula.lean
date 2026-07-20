/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalFormula
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramOrderFormula

/-!
# The least-successful-program order on rudimentary values

This file combines the fixed postfix-program evaluator with the fixed
Shortlex program order.  The free-variable layout is

`[U, varTag, appTag, empty, op0, ..., op8, omega, relation, left, right]`.

The first fifteen coordinates are parameters.  The final two coordinates are
the values being compared, so the formula can be passed directly to the
definable-relation graph construction.  Internally it says

`exists p, Eval(p, left) and forall q, Eval(q, right) -> ProgramLt(p, q)`.

When the program order is a well-order and both values have successful
programs, this is equivalent to comparing their least successful programs.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

/-! ## Fixed layout and assignments -/

/-- The fifteen parameters shared by the least-program value relation. -/
def leastProgramValueLtParametersAssignment
    (U relation : ZFSet.{u}) : Tuple ZFSet.{u} 15 :=
  snoc
    (snoc (stackStepPrefixAssignment U) Ordinal.omega0.toZFSet)
    relation

/-- The intended raw assignment, with the compared values in the last slots. -/
def leastProgramValueLtAssignment
    (U relation left right : ZFSet.{u}) : Tuple ZFSet.{u} 17 :=
  snoc (snoc (leastProgramValueLtParametersAssignment U relation) left) right

/--
Select `[U, relation, varTag, appTag, empty, omega]` from the fifteen
least-program parameters.
-/
def rawStackProgramLtParameterRename : Fin 6 -> Fin 15 :=
  ![(0 : Fin 15), (14 : Fin 15), (1 : Fin 15), (2 : Fin 15),
    (3 : Fin 15), (13 : Fin 15)]

/-- The six fixed coordinates used by a raw program comparison. -/
def rawStackProgramLtPrefixAssignment
    (U relation : ZFSet.{u}) : Tuple ZFSet.{u} 6 :=
  fun i => leastProgramValueLtParametersAssignment U relation
    (rawStackProgramLtParameterRename i)

/-- The raw eight-coordinate assignment used by `stackProgramLtFormula`. -/
def rawStackProgramLtAssignment
    (U relation leftProgram rightProgram : ZFSet.{u}) : Tuple ZFSet.{u} 8 :=
  snoc (snoc (rawStackProgramLtPrefixAssignment U relation) leftProgram)
    rightProgram

/-! ## Renamings -/

/--
Embed `Eval(program, result)` into the context extended by the witness `p`.
The evaluator's fourteen fixed coordinates are unchanged, its program is `p`,
and its result is the left value at coordinate `15`.
-/
def leastProgramLeftEvalRename : Fin 16 -> Fin 18 :=
  Fin.lastCases (15 : Fin 18)
    (fun i14 => Fin.lastCases (17 : Fin 18)
      (fun i13 => i13.castSucc.castSucc.castSucc.castSucc) i14)

/--
Embed `Eval(program, result)` under the subsequent universal witness `q`.
Its program is `q` and its result is the right value at coordinate `16`.
-/
def leastProgramRightEvalRename : Fin 16 -> Fin 19 :=
  Fin.lastCases (16 : Fin 19)
    (fun i14 => Fin.lastCases (18 : Fin 19)
      (fun i13 =>
        i13.castSucc.castSucc.castSucc.castSucc.castSucc) i14)

/-- Embed the six fixed program-order coordinates into the large context. -/
def leastProgramOrderPrefixRename : Fin 6 -> Fin 19 :=
  fun i =>
    (rawStackProgramLtParameterRename i).castSucc.castSucc.castSucc.castSucc

/--
Embed the raw program comparison under both program witnesses.  In the
nineteen-coordinate context, `p` and `q` occupy coordinates `17` and `18`.
-/
def leastProgramOrderRename : Fin 8 -> Fin 19 :=
  Fin.lastCases (18 : Fin 19)
    (fun i7 => Fin.lastCases (17 : Fin 19)
      leastProgramOrderPrefixRename i7)

/-! ## Formula -/

/--
Compare values by their least successful postfix programs, expressed without
choosing a least program in the object language.
-/
def leastProgramValueLtFormula : FOFormula 17 :=
  .ex
    (.conj
      (FOFormula.rename leastProgramLeftEvalRename stackProgramEvalFormula)
      (.all
        (formulaImp
          (FOFormula.rename leastProgramRightEvalRename
            stackProgramEvalFormula)
          (FOFormula.rename leastProgramOrderRename
            stackProgramLtFormula))))

/-! ## Assignment computations -/

theorem comp_leastProgramLeftEvalRename
    (U relation left right p : ZFSet.{u}) :
    (fun i =>
      snoc (leastProgramValueLtAssignment U relation left right) p
        (leastProgramLeftEvalRename i)) =
      stackProgramEvalAssignment U p left := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · simp [leastProgramLeftEvalRename, leastProgramValueLtAssignment,
        leastProgramValueLtParametersAssignment, stackProgramEvalAssignment]

theorem comp_leastProgramRightEvalRename
    (U relation left right p q : ZFSet.{u}) :
    (fun i =>
      snoc
        (snoc (leastProgramValueLtAssignment U relation left right) p) q
        (leastProgramRightEvalRename i)) =
      stackProgramEvalAssignment U q right := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · simp [leastProgramRightEvalRename, leastProgramValueLtAssignment,
        leastProgramValueLtParametersAssignment, stackProgramEvalAssignment]

theorem comp_leastProgramOrderRename
    (U relation left right p q : ZFSet.{u}) :
    (fun i =>
      snoc
        (snoc (leastProgramValueLtAssignment U relation left right) p) q
        (leastProgramOrderRename i)) =
      rawStackProgramLtAssignment U relation p q := by
  funext i
  refine Fin.lastCases ?_ (fun i7 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i6 => ?_) i7
    · rfl
    · simp only [leastProgramOrderRename, Fin.lastCases_castSucc,
        leastProgramOrderPrefixRename, leastProgramValueLtAssignment,
        rawStackProgramLtAssignment, rawStackProgramLtPrefixAssignment,
        snoc_castSucc]

/-! ## Ambient raw semantic normal form -/

/--
The combined formula is exactly the expected relation between the two raw
evaluator predicates and the raw program-order predicate.
-/
@[simp]
theorem satisfies_leastProgramValueLtFormula
    (U relation left right : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem leastProgramValueLtFormula
        (leastProgramValueLtAssignment U relation left right) <->
      exists p : ZFSet.{u},
        FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
            (stackProgramEvalAssignment U p left) /\
          forall q : ZFSet.{u},
            FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
                (stackProgramEvalAssignment U q right) ->
              FOFormula.Satisfies Delta0Formula.ZFMem stackProgramLtFormula
                (rawStackProgramLtAssignment U relation p q) := by
  simp only [leastProgramValueLtFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_rename,
    satisfies_formulaImp, comp_leastProgramLeftEvalRename,
    comp_leastProgramRightEvalRename, comp_leastProgramOrderRename]

end

end Constructible.Godel.RudimentaryTerm
