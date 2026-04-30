/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-! # Closure operators and shifts

In this file, we collect facts relating being stable under shifts with
closure properties of object properties.

-/

public section

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] (P : ObjectProperty C)

instance {A : Type*} [AddMonoid A] [HasShift C A] [P.IsStableUnderShift A] :
    P.retractClosure.IsStableUnderShift A where
  isStableUnderShiftBy a := IsStableUnderShiftBy.mk <| by
    intro X ⟨Y, hY, i, r, w⟩
    exact ⟨Y⟦a⟧, IsStableUnderShiftBy.le_shift Y hY, i⟦a⟧', r⟦a⟧', by grind⟩

instance {A : Type*} [AddGroup A] [HasShift C A] {α : Type*} {J : α → Type*}
    [∀ (i : α), Category (J i)] [P.IsStableUnderShift A] :
    (P.limitsClosure J).IsStableUnderShift A where
  isStableUnderShiftBy a := IsStableUnderShiftBy.mk <| by
    intro X hX
    induction hX with
    | of_mem X hX => exact limitsClosure.of_mem _ (IsStableUnderShiftBy.le_shift X hX)
    | of_isoClosure e hX hX' => exact limitsClosure.of_isoClosure ((shiftFunctor C a).mapIso e) hX'
    | of_limitPresentation pres h h' =>
      exact limitsClosure.of_limitPresentation (pres.map (shiftFunctor C a)) h'

end CategoryTheory.ObjectProperty
