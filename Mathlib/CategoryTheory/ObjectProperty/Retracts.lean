/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# Properties of objects that are stable under retracts

-/

namespace CategoryTheory

variable {C : Type*} [Category C]

namespace ObjectProperty

variable (P : ObjectProperty C)

class IsClosedUnderRetracts where
  of_retract {X Y : C} (e : Retract X Y) (hY : P Y) : P X

lemma prop_of_retract [P.IsClosedUnderRetracts]
    {X Y : C} (e : Retract X Y) (hY : P Y) : P X :=
  IsClosedUnderRetracts.of_retract e hY

instance [P.IsClosedUnderRetracts] :
    P.IsClosedUnderIsomorphisms where
  of_iso e h := P.prop_of_retract (Retract.ofIso e.symm) h

instance [IsIdempotentComplete C] [P.IsClosedUnderRetracts] :
    IsIdempotentComplete P.FullSubcategory where
  idempotents_split := by
    rintro X p hp
    obtain ⟨Y, e, he⟩ := retract_of_isIdempotentComplete X.1 p hp
    exact ⟨⟨Y, P.prop_of_retract e X.2⟩, e.i, e.r, e.retract, he⟩

end ObjectProperty

end CategoryTheory
