/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.FiniteSequenceZF
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryCode
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryTermZFCode

/-!
# Internal ZF codes for rudimentary prefix syntax

`RudimentaryTerm.code` is an external Lean list of prefix tokens.  This file
turns each token into a genuine `ZFSet`, then applies
`FiniteSequenceZF.sequenceCode` to internalize the whole finite prefix list.

Variable tokens carry the actual value of `rudimentaryGenerator`: `none` is
coded by `U`, while `some x` is coded by `x`.  These values are distinct by
foundation because every such `x` belongs to `U`.  Operation tokens carry the
operation index and the two subterm-code lengths.

This file only establishes faithful internal coding and constructibility.  It
does not internalize the shortlex comparison or term evaluation relation.
-/

@[expose] public section

universe u

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section

/-- The generator interpretation distinguishes all closure variables. -/
theorem rudimentaryGenerator_injective (U : ZFSet.{u}) :
    Function.Injective (rudimentaryGenerator U) := by
  intro first second h
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some x =>
          exfalso
          have hUx : U = x.1 := by
            simpa only [rudimentaryGenerator] using h
          have hself : x.1 ∈ x.1 := by
            exact hUx ▸ x.2
          exact ZFSet.mem_irrefl x.1 hself
  | some x =>
      cases second with
      | none =>
          exfalso
          have hxU : x.1 = U := by
            simpa only [rudimentaryGenerator] using h
          have hself : x.1 ∈ x.1 := by
            exact hxU.symm ▸ x.2
          exact ZFSet.mem_irrefl x.1 hself
      | some y =>
          have hxy : x.1 = y.1 := by
            simpa only [rudimentaryGenerator] using h
          exact congrArg Option.some (Subtype.ext hxy)

/--
Encode one external prefix token as a genuine ZF set.  Constructor tags are
the same tags used by the direct structural term encoding.
-/
def tokenZFCode (U : ZFSet.{u}) :
    CodeToken (Option (Constructible.ZFCarrier U)) -> ZFSet.{u}
  | .inl generator =>
      triple varTag (rudimentaryGenerator U generator) ∅
  | .inr operation =>
      triple appTag (operationCode operation.1)
        (ZFSet.pair
          (FiniteSequenceZF.natCode operation.2.1)
          (FiniteSequenceZF.natCode operation.2.2))

@[simp]
theorem tokenZFCode_variable (U : ZFSet.{u})
    (generator : Option (Constructible.ZFCarrier U)) :
    tokenZFCode U (.inl generator) =
      triple varTag (rudimentaryGenerator U generator) ∅ :=
  rfl

@[simp]
theorem tokenZFCode_operation (U : ZFSet.{u})
    (i : Fin 9) (leftLength rightLength : Nat) :
    tokenZFCode U (.inr (i, leftLength, rightLength)) =
      triple appTag (operationCode i)
        (ZFSet.pair
          (FiniteSequenceZF.natCode leftLength)
          (FiniteSequenceZF.natCode rightLength)) :=
  rfl

/-- The internal token code distinguishes every external prefix token. -/
theorem tokenZFCode_injective (U : ZFSet.{u}) :
    Function.Injective (tokenZFCode U) := by
  intro first second hcode
  cases first with
  | inl firstVariable =>
      cases second with
      | inl secondVariable =>
          rcases ZFSet.pair_inj.mp hcode with ⟨_htag, htail⟩
          rcases ZFSet.pair_inj.mp htail with
            ⟨hvariable, _hempty⟩
          exact congrArg Sum.inl
            (rudimentaryGenerator_injective U hvariable)
      | inr secondOperation =>
          rcases ZFSet.pair_inj.mp hcode with ⟨htag, _htail⟩
          exact False.elim (varTag_ne_appTag htag)
  | inr firstOperation =>
      cases second with
      | inl secondVariable =>
          rcases ZFSet.pair_inj.mp hcode with ⟨htag, _htail⟩
          exact False.elim (varTag_ne_appTag htag.symm)
      | inr secondOperation =>
          rcases ZFSet.pair_inj.mp hcode with ⟨_htag, htail⟩
          rcases ZFSet.pair_inj.mp htail with
            ⟨hoperation, hlengths⟩
          rcases ZFSet.pair_inj.mp hlengths with
            ⟨hleftLength, hrightLength⟩
          have hi : firstOperation.1 = secondOperation.1 :=
            operationCode_injective hoperation
          have hleft : firstOperation.2.1 = secondOperation.2.1 :=
            FiniteSequenceZF.natCode_injective hleftLength
          have hright : firstOperation.2.2 = secondOperation.2.2 :=
            FiniteSequenceZF.natCode_injective hrightLength
          cases firstOperation with
          | mk firstIndex firstLengths =>
              cases firstLengths with
              | mk firstLeft firstRight =>
                  cases secondOperation with
                  | mk secondIndex secondLengths =>
                      cases secondLengths with
                      | mk secondLeft secondRight =>
                          simp only at hi hleft hright
                          subst secondIndex
                          subst secondLeft
                          subst secondRight
                          rfl

/-- The whole external prefix list, represented by an internal finite sequence. -/
def prefixZFCode (U : ZFSet.{u}) (term : RudimentaryClosureTerm U) :
    ZFSet.{u} :=
  FiniteSequenceZF.sequenceCode ((code term).map (tokenZFCode U))

/-- Equality of internal prefix codes recovers equality of terms. -/
theorem prefixZFCode_injective (U : ZFSet.{u}) :
    Function.Injective (prefixZFCode U) := by
  intro first second hcode
  apply code_injective
  apply (tokenZFCode_injective U).list_map
  apply FiniteSequenceZF.sequenceCode_injective
  exact hcode

/-- Every generator value is constructible when `U` is constructible. -/
theorem rudimentaryGenerator_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (generator : Option (Constructible.ZFCarrier U)) :
    rudimentaryGenerator U generator ∈ L := by
  cases generator with
  | none => exact hU
  | some x => exact mem_L_of_mem x.2 hU

/-- Every encoded prefix token is constructible when `U` is constructible. -/
theorem tokenZFCode_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (token : CodeToken (Option (Constructible.ZFCarrier U))) :
    tokenZFCode U token ∈ L := by
  cases token with
  | inl generator =>
      exact triple_mem_L varTag_mem_L
        (rudimentaryGenerator_mem_L hU generator) empty_mem_L
  | inr operation =>
      exact triple_mem_L appTag_mem_L
        (operationCode_mem_L operation.1)
        (orderedPair_mem_L
          (FiniteSequenceZF.natCode_mem_L operation.2.1)
          (FiniteSequenceZF.natCode_mem_L operation.2.2))

/-- Every internal prefix code is constructible when its seed `U` is. -/
theorem prefixZFCode_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (term : RudimentaryClosureTerm U) :
    prefixZFCode U term ∈ L := by
  apply FiniteSequenceZF.sequenceCode_mem_L
  intro encodedToken hEncodedToken
  rcases List.mem_map.mp hEncodedToken with
    ⟨token, _htoken, rfl⟩
  exact tokenZFCode_mem_L hU token

end


end RudimentaryTerm

end Constructible.Godel
