/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.CanonicalStageOrder
public import Mathlib.SetTheory.ZFC.Constructible.InternalWellOrder
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgram
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryTokenOrderFormula

/-!
# Generator orders from internally represented well-orders

An internal relation graph on a constructible set `U` orders
`Model.InternalCarrier U`, while rudimentary programs use
`ZFCarrier U.1` as their ordinary generator type.  These two carriers are
canonically equivalent.  This file transports the represented well-order
across that equivalence, adds the distinguished `none` generator at the
front, and finally lifts the order to postfix stack programs by Shortlex.
-/

@[expose] public section

universe u

namespace Constructible

namespace Godel

namespace RudimentaryTerm

noncomputable section

/--
The elements of the underlying `ZFSet` of a constructible set are the same
as its internal carrier; the latter additionally records that each element
is constructible.
-/
def zfCarrierInternalEquiv (U : Model.LCarrier.{u}) :
    ZFCarrier U.1 ≃ Model.InternalCarrier U where
  toFun x :=
    ⟨⟨x.1, mem_L_of_mem x.2 U.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp]
theorem zfCarrierInternalEquiv_apply_val
    (U : Model.LCarrier.{u}) (x : ZFCarrier U.1) :
    ((zfCarrierInternalEquiv U x).1).1 = x.1 :=
  rfl

@[simp]
theorem zfCarrierInternalEquiv_symm_apply_val
    (U : Model.LCarrier.{u}) (x : Model.InternalCarrier U) :
    ((zfCarrierInternalEquiv U).symm x).1 = x.1.1 :=
  rfl

/--
The ordinary-generator relation is exactly the pullback of the internally
represented graph relation along `zfCarrierInternalEquiv`.
-/
theorem generatorPairRel_eq_invImage_graphRelOn
    (U relation : Model.LCarrier.{u}) :
    generatorPairRel relation.1 =
      InvImage (Model.graphRelOn relation U) (zfCarrierInternalEquiv U) := by
  funext x y
  rfl

/-- Transport an internally represented well-order to the plain `ZFCarrier`. -/
theorem generatorPairRel_isWellOrder_of_internal
    (U relation : Model.LCarrier.{u})
    (hwell : Model.InternallyWellOrders relation U) :
    IsWellOrder (ZFCarrier U.1) (generatorPairRel relation.1) := by
  rw [generatorPairRel_eq_invImage_graphRelOn]
  letI : IsWellOrder (Model.InternalCarrier U)
      (Model.graphRelOn relation U) := hwell
  exact
    { wf := InvImage.wf (zfCarrierInternalEquiv U)
        (IsWellFounded.wf :
          WellFounded (Model.graphRelOn relation U))
      trichotomous :=
        (InvImage.trichotomous
          (r := Model.graphRelOn relation U)
          (zfCarrierInternalEquiv U).injective).trichotomous }

/--
`generatorTokenRel` is the existing generic construction which puts one
distinguished point before a relation on the ordinary generators.
-/
theorem generatorTokenRel_eq_optionPrependRel
    (U relation : ZFSet.{u}) :
    generatorTokenRel U relation =
      optionPrependRel (generatorPairRel relation) := by
  funext left right
  cases left <;> cases right <;>
    simp [generatorTokenRel, optionPrependRel, optionSumEquiv, InvImage]

/--
An actual constructible graph which internally well-orders `U` induces the
well-order on generator tokens used by rudimentary programs.
-/
theorem generatorTokenRel_isWellOrder_of_internal
    (U relation : Model.LCarrier.{u})
    (hwell : Model.InternallyWellOrders relation U) :
    IsWellOrder (Option (ZFCarrier U.1))
      (generatorTokenRel U.1 relation.1) := by
  letI : IsWellOrder (ZFCarrier U.1) (generatorPairRel relation.1) :=
    generatorPairRel_isWellOrder_of_internal U relation hwell
  rw [generatorTokenRel_eq_optionPrependRel]
  exact optionPrependRel_isWellOrder (generatorPairRel relation.1)

/--
The corresponding Shortlex relation well-orders all postfix stack programs.
-/
theorem stackProgramRel_isWellOrder_of_internal
    (U relation : Model.LCarrier.{u})
    (hwell : Model.InternallyWellOrders relation U) :
    IsWellOrder
      (List (StackToken (Option (ZFCarrier U.1))))
      (stackProgramRel (generatorTokenRel U.1 relation.1)) := by
  letI : IsWellOrder (Option (ZFCarrier U.1))
      (generatorTokenRel U.1 relation.1) :=
    generatorTokenRel_isWellOrder_of_internal U relation hwell
  exact stackProgramRel_isWellOrder (generatorTokenRel U.1 relation.1)

end

end RudimentaryTerm

end Godel

end Constructible
