/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackStepFormula

/-!
# Decoding arbitrary satisfying stack-step codes

The basic semantic theorem for `stackStepFormula` was first stated on genuine
token and stack codes.  Whole-program soundness also needs the converse shape:
starting from a genuine input stack code, every arbitrary raw token/output pair
accepted by the formula must decode to a real instruction and a real output
stack.  This file proves exactly that fact.
-/

@[expose] public section

universe u

namespace Constructible.Godel.RudimentaryTerm

open FiniteSequenceZF

/--
With a genuine input stack code, one-step satisfaction is equivalent to the
existence of a genuine token and output stack producing the supplied raw codes.
-/
theorem satisfies_stackStepFormula_iff_exists_decoding
    (U tokenCode outputCode : ZFSet.{u}) (input : List ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
        (stackStepAssignment U tokenCode (listCode input) outputCode) ↔
      ∃ token : StackToken (Option (Constructible.ZFCarrier U)),
        ∃ output : List ZFSet.{u},
          tokenCode = stackTokenZFCode U token ∧
            outputCode = listCode output ∧
            runStackToken (rudimentaryGenerator U) token input = some output := by
  constructor
  · intro hsatisfies
    rw [satisfies_stackStepFormula] at hsatisfies
    rcases hsatisfies with hvariable | hoperation
    · rcases hvariable with
        ⟨generator, htoken, hgenerator, houtput⟩
      rcases hgenerator with hgeneratorEq | hgeneratorMem
      · subst generator
        refine ⟨.inl none, U :: input, ?_, ?_, rfl⟩
        · simpa only [stackTokenZFCode_variable,
            rudimentaryGenerator] using htoken
        · simpa only [listCode_cons] using houtput
      · let generatorCarrier : Constructible.ZFCarrier U :=
          ⟨generator, hgeneratorMem⟩
        refine ⟨.inl (some generatorCarrier), generator :: input,
          ?_, ?_, rfl⟩
        · simpa only [stackTokenZFCode_variable,
            rudimentaryGenerator, generatorCarrier] using htoken
        · simpa only [listCode_cons] using houtput
    · rcases hoperation with
        ⟨operation, right, left, rest, result,
          htoken, hinput, houtput, hresult⟩
      cases input with
      | nil =>
          exact False.elim (empty_ne_zfPair right (ZFSet.pair left rest) hinput)
      | cons first tail =>
          have hfirst := (ZFSet.pair_inj.mp hinput).1
          have htail := (ZFSet.pair_inj.mp hinput).2
          subst first
          cases tail with
          | nil =>
              exact False.elim (empty_ne_zfPair left rest htail)
          | cons second remaining =>
              have hsecond := (ZFSet.pair_inj.mp htail).1
              have hremaining := (ZFSet.pair_inj.mp htail).2
              subst second
              rw [← hremaining] at houtput
              subst result
              refine ⟨.inr operation,
                op operation left right :: remaining, ?_, ?_, rfl⟩
              · simpa only [stackTokenZFCode_operation] using htoken
              · simpa only [listCode_cons] using houtput
  · rintro ⟨token, output, rfl, rfl, hrun⟩
    exact (satisfies_stackStepFormula_iff_run U token input output).mpr hrun

/-- The forward decoding direction as a convenient standalone lemma. -/
theorem exists_decoding_of_satisfies_stackStepFormula
    (U tokenCode outputCode : ZFSet.{u}) (input : List ZFSet.{u})
    (hsatisfies :
      FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
        (stackStepAssignment U tokenCode (listCode input) outputCode)) :
    ∃ token : StackToken (Option (Constructible.ZFCarrier U)),
      ∃ output : List ZFSet.{u},
        tokenCode = stackTokenZFCode U token ∧
          outputCode = listCode output ∧
          runStackToken (rudimentaryGenerator U) token input = some output :=
  (satisfies_stackStepFormula_iff_exists_decoding
    U tokenCode outputCode input).mp hsatisfies

end Constructible.Godel.RudimentaryTerm
