/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Properties of objects that are closed under finite limits

In this file, we introduce a typeclass `IsClosedUnderFiniteLimits`
saying that a property of objects `P : ObjectProperty C` of a category `C`
is closed under finite limits. The dual definition `IsClosedUnderFiniteLimits`
is also introduced.

-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] (P : ObjectProperty C)

/-- A typeclass expressing that a property of objects is closed under finite limits. -/
class IsClosedUnderFiniteLimits : Prop where
  isClosedUnderLimitsOfShape (J : Type) [SmallCategory J] [FinCategory J] :
    P.IsClosedUnderLimitsOfShape J := by intros; infer_instance

namespace IsClosedUnderFiniteLimits

attribute [instance] isClosedUnderLimitsOfShape

variable [HasFiniteLimits C] [P.IsClosedUnderFiniteLimits]

instance : HasFiniteLimits P.FullSubcategory where
  out _ _ _ := inferInstance

instance : PreservesFiniteLimits P.ι where
  preservesFiniteLimits _ _ _ := inferInstance

end IsClosedUnderFiniteLimits

/-- A typeclass expressing that a property of objects is closed under finite colimits. -/
class IsClosedUnderFiniteColimits : Prop where
  isClosedUnderColimitsOfShape (J : Type) [SmallCategory J] [FinCategory J] :
    P.IsClosedUnderColimitsOfShape J := by intros; infer_instance

namespace IsClosedUnderFiniteColimits

attribute [instance] isClosedUnderColimitsOfShape

variable [HasFiniteColimits C] [P.IsClosedUnderFiniteColimits]

instance : HasFiniteColimits P.FullSubcategory where
  out _ _ _ := inferInstance

instance : PreservesFiniteColimits P.ι where
  preservesFiniteColimits _ _ _ := inferInstance

end IsClosedUnderFiniteColimits

end CategoryTheory.ObjectProperty
