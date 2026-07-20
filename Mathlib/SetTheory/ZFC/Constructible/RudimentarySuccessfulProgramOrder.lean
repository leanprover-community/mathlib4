/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryGeneratorInternalOrder

/-!
# Ordering definable values by successful stack programs

This module gives a formula-independent presentation of the canonical order
on one Gödel-definability step. A value `x` precedes `y` when some program
evaluating to `x` precedes every program evaluating to `y`.  Once the
generator relation is a well-order, this is exactly the existing order by
least successful programs, `defCarrierStackRel`.
-/

@[expose] public section

universe u

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section

/--
`x` precedes `y` if a successful program for `x` is earlier than every
successful program for `y` in the structural program order.
-/
def successfulProgramValueRel (U relation : ZFSet.{u}) :
    DefCarrier U -> DefCarrier U -> Prop :=
  fun x y =>
    exists program : List (StackToken (Option (ZFCarrier U))),
      runStackProgram (rudimentaryGenerator U) program [] = some [x.1] /\
        forall other : List (StackToken (Option (ZFCarrier U))),
          runStackProgram (rudimentaryGenerator U) other [] = some [y.1] ->
            stackProgramRel (generatorTokenRel U relation) program other

/-- No successful program for `z` lies below its canonical least program. -/
theorem leastStackProgram_minimal
    (U z : ZFSet.{u}) (hz : z ∈ godelDef U)
    (r : Option (ZFCarrier U) -> Option (ZFCarrier U) -> Prop)
    [IsWellOrder (Option (ZFCarrier U)) r]
    {program : List (StackToken (Option (ZFCarrier U)))}
    (hprogram :
      runStackProgram (rudimentaryGenerator U) program [] = some [z]) :
    Not (stackProgramRel r program (leastStackProgram U z hz r)) := by
  letI : IsWellOrder
      (List (StackToken (Option (ZFCarrier U))))
      (stackProgramRel r) := stackProgramRel_isWellOrder r
  exact
    (IsWellFounded.wf : WellFounded (stackProgramRel r)).not_lt_min
      (representingStackPrograms U z) hprogram

/--
The successful-program presentation is exactly comparison of the two least
successful programs.
-/
theorem successfulProgramValueRel_eq_defCarrierStackRel
    (U relation : ZFSet.{u})
    [IsWellOrder (Option (ZFCarrier U))
      (generatorTokenRel U relation)] :
    successfulProgramValueRel U relation =
      defCarrierStackRel U (generatorTokenRel U relation) := by
  let programRel :=
    stackProgramRel (generatorTokenRel U relation)
  letI : IsWellOrder
      (List (StackToken (Option (ZFCarrier U)))) programRel :=
    stackProgramRel_isWellOrder (generatorTokenRel U relation)
  funext x y
  apply propext
  change
    (exists program : List (StackToken (Option (ZFCarrier U))),
      runStackProgram (rudimentaryGenerator U) program [] = some [x.1] /\
        forall other : List (StackToken (Option (ZFCarrier U))),
          runStackProgram (rudimentaryGenerator U) other [] = some [y.1] ->
            programRel program other) <->
      programRel
        (leastStackProgram U x.1 x.2 (generatorTokenRel U relation))
        (leastStackProgram U y.1 y.2 (generatorTokenRel U relation))
  constructor
  · rintro ⟨program, hprogram, hbelow⟩
    have hprogramBelowY :
        programRel program
          (leastStackProgram U y.1 y.2
            (generatorTokenRel U relation)) :=
      hbelow _
        (run_leastStackProgram U y.1 y.2
          (generatorTokenRel U relation))
    rcases trichotomous_of programRel
        (leastStackProgram U x.1 x.2
          (generatorTokenRel U relation)) program with
      hleast | heq | hprogramBelowX
    · exact IsTrans.trans _ _ _ hleast hprogramBelowY
    · simpa only [heq] using hprogramBelowY
    · exact False.elim
        (leastStackProgram_minimal U x.1 x.2
          (generatorTokenRel U relation) hprogram hprogramBelowX)
  · intro hleast
    refine
      ⟨leastStackProgram U x.1 x.2 (generatorTokenRel U relation),
        run_leastStackProgram U x.1 x.2
          (generatorTokenRel U relation), ?_⟩
    intro other hother
    rcases trichotomous_of programRel other
        (leastStackProgram U y.1 y.2
          (generatorTokenRel U relation)) with
      hotherBelow | heq | hleastYBelow
    · exact False.elim
        (leastStackProgram_minimal U y.1 y.2
          (generatorTokenRel U relation) hother hotherBelow)
    · simpa only [heq] using hleast
    · exact IsTrans.trans _ _ _ hleast hleastYBelow

/--
Specialization of the equality to a constructible relation graph which
internally well-orders the generator set.
-/
theorem successfulProgramValueRel_eq_defCarrierStackRel_of_internal
    (U relation : Model.LCarrier.{u})
    (hwell : Model.InternallyWellOrders relation U) :
    successfulProgramValueRel U.1 relation.1 =
      @defCarrierStackRel U.1
        (generatorTokenRel U.1 relation.1)
        (generatorTokenRel_isWellOrder_of_internal U relation hwell) := by
  letI : IsWellOrder (Option (ZFCarrier U.1))
      (generatorTokenRel U.1 relation.1) :=
    generatorTokenRel_isWellOrder_of_internal U relation hwell
  exact successfulProgramValueRel_eq_defCarrierStackRel U.1 relation.1

/--
An internally represented well-order of `U` therefore makes the
successful-program relation a well-order of `DefCarrier U.1`.
-/
theorem successfulProgramValueRel_isWellOrder_of_internal
    (U relation : Model.LCarrier.{u})
    (hwell : Model.InternallyWellOrders relation U) :
    IsWellOrder (DefCarrier U.1)
      (successfulProgramValueRel U.1 relation.1) := by
  let generatorWellOrder :=
    generatorTokenRel_isWellOrder_of_internal U relation hwell
  letI : IsWellOrder (Option (ZFCarrier U.1))
      (generatorTokenRel U.1 relation.1) := generatorWellOrder
  rw [successfulProgramValueRel_eq_defCarrierStackRel]
  exact defCarrierStackRel_isWellOrder U.1
    (generatorTokenRel U.1 relation.1)

end

end RudimentaryTerm

end Constructible.Godel
