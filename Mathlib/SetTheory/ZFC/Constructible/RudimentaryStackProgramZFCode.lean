/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.IndexedSequenceZF
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryPrefixZFCode
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgram
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryTermZFCode

/-!
# Internal codes for rudimentary stack programs

Postfix program tokens and whole instruction lists are encoded by genuine
`ZFSet`s.  Variable tokens carry their generator value; operation tokens carry
the finite ordinal operation index.  Whole programs use the indexed sequence
encoding, which is tailored to a first-order execution-trace predicate.
-/

@[expose] public section

universe u

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section

/-- Internal code of one postfix stack instruction. -/
def stackTokenZFCode (U : ZFSet.{u}) :
    StackToken (Option (Constructible.ZFCarrier U)) → ZFSet.{u}
  | .inl generator =>
      triple varTag (rudimentaryGenerator U generator) ∅
  | .inr operation =>
      triple appTag (operationCode operation) ∅

@[simp]
theorem stackTokenZFCode_variable (U : ZFSet.{u})
    (generator : Option (Constructible.ZFCarrier U)) :
    stackTokenZFCode U (.inl generator) =
      triple varTag (rudimentaryGenerator U generator) ∅ :=
  rfl

@[simp]
theorem stackTokenZFCode_operation (U : ZFSet.{u})
    (operation : Fin 9) :
    stackTokenZFCode U (.inr operation) =
      triple appTag (operationCode operation) ∅ :=
  rfl

/-- Internal stack-token codes retain the complete instruction. -/
theorem stackTokenZFCode_injective (U : ZFSet.{u}) :
    Function.Injective (stackTokenZFCode U) := by
  intro first second hcode
  cases first with
  | inl firstGenerator =>
      cases second with
      | inl secondGenerator =>
          rcases ZFSet.pair_inj.mp hcode with ⟨_htag, htail⟩
          rcases ZFSet.pair_inj.mp htail with ⟨hgenerator, _hempty⟩
          exact congrArg Sum.inl
            (rudimentaryGenerator_injective U hgenerator)
      | inr secondOperation =>
          rcases ZFSet.pair_inj.mp hcode with ⟨htag, _htail⟩
          exact False.elim (varTag_ne_appTag htag)
  | inr firstOperation =>
      cases second with
      | inl secondGenerator =>
          rcases ZFSet.pair_inj.mp hcode with ⟨htag, _htail⟩
          exact False.elim (varTag_ne_appTag htag.symm)
      | inr secondOperation =>
          rcases ZFSet.pair_inj.mp hcode with ⟨_htag, htail⟩
          rcases ZFSet.pair_inj.mp htail with
            ⟨hoperation, _hempty⟩
          exact congrArg Sum.inr
            (operationCode_injective hoperation)

/-- A whole postfix program, represented as an indexed finite sequence. -/
def stackProgramZFCode (U : ZFSet.{u})
    (program : List (StackToken
      (Option (Constructible.ZFCarrier U)))) : ZFSet.{u} :=
  IndexedSequenceZF.sequenceCode (program.map (stackTokenZFCode U))

/-- Equality of internal program codes recovers equality of token lists. -/
theorem stackProgramZFCode_injective (U : ZFSet.{u}) :
    Function.Injective (stackProgramZFCode U) := by
  intro first second hcode
  apply (stackTokenZFCode_injective U).list_map
  apply IndexedSequenceZF.sequenceCode_injective
  exact hcode

/-- Every stack token code is constructible when its seed is. -/
theorem stackTokenZFCode_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U))) :
    stackTokenZFCode U token ∈ L := by
  cases token with
  | inl generator =>
      exact triple_mem_L varTag_mem_L
        (RudimentaryTerm.rudimentaryGenerator_mem_L hU generator)
        empty_mem_L
  | inr operation =>
      exact triple_mem_L appTag_mem_L
        (operationCode_mem_L operation) empty_mem_L

/-- Every finite postfix program has a constructible internal code. -/
theorem stackProgramZFCode_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (program : List (StackToken
      (Option (Constructible.ZFCarrier U)))) :
    stackProgramZFCode U program ∈ L := by
  apply IndexedSequenceZF.sequenceCode_mem_L
  intro encodedToken hEncodedToken
  rcases List.mem_map.mp hEncodedToken with ⟨token, _htoken, rfl⟩
  exact stackTokenZFCode_mem_L hU token

end

end RudimentaryTerm

end Constructible.Godel
