/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer

! This file was ported from Lean 3 source module category_theory.limits.preserves.filtered
! leanprover-community/mathlib commit c43486ecf2a5a17479a32ce09e4818924145e90e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.Filtered

/-!
# Preservation of filtered colimits and cofiltered limits.
Typically forgetful functors from algebraic categories preserve filtered colimits
(although not general colimits). See e.g. `algebra/category/Mon/filtered_colimits`.

## Future work
This could be generalised to allow diagrams in lower universes.
-/


open CategoryTheory

open CategoryTheory.Functor

namespace CategoryTheory.Limits

universe v u₁ u₂ u₃

-- declare the `v`'s first; see `category_theory.category` for an explanation
variable {C : Type u₁} [Category.{v} C]

variable {D : Type u₂} [Category.{v} D]

variable {E : Type u₃} [Category.{v} E]

variable {J : Type v} [SmallCategory J] {K : J ⥤ C}

/--
A functor is said to preserve filtered colimits, if it preserves all colimits of shape `J`, where
`J` is a filtered category.
-/
class PreservesFilteredColimits (F : C ⥤ D) : Type max u₁ u₂ (v + 1) where
  PreservesFilteredColimits :
    ∀ (J : Type v) [SmallCategory J] [IsFiltered J], PreservesColimitsOfShape J F
#align category_theory.limits.preserves_filtered_colimits CategoryTheory.Limits.PreservesFilteredColimits

attribute [instance] preserves_filtered_colimits.preserves_filtered_colimits

instance (priority := 100) PreservesColimits.preservesFilteredColimits (F : C ⥤ D)
    [PreservesColimits F] : PreservesFilteredColimits F
    where PreservesFilteredColimits := inferInstance
#align category_theory.limits.preserves_colimits.preserves_filtered_colimits CategoryTheory.Limits.PreservesColimits.preservesFilteredColimits

instance compPreservesFilteredColimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFilteredColimits F]
    [PreservesFilteredColimits G] : PreservesFilteredColimits (F ⋙ G)
    where PreservesFilteredColimits J _ _ := inferInstance
#align category_theory.limits.comp_preserves_filtered_colimits CategoryTheory.Limits.compPreservesFilteredColimits

/-- A functor is said to preserve cofiltered limits, if it preserves all limits of shape `J`, where
`J` is a cofiltered category.
-/
class PreservesCofilteredLimits (F : C ⥤ D) : Type max u₁ u₂ (v + 1) where
  PreservesCofilteredLimits :
    ∀ (J : Type v) [SmallCategory J] [IsCofiltered J], PreservesLimitsOfShape J F
#align category_theory.limits.preserves_cofiltered_limits CategoryTheory.Limits.PreservesCofilteredLimits

attribute [instance] preserves_cofiltered_limits.preserves_cofiltered_limits

instance (priority := 100) PreservesLimits.preservesCofilteredLimits (F : C ⥤ D)
    [PreservesLimits F] : PreservesCofilteredLimits F
    where PreservesCofilteredLimits := inferInstance
#align category_theory.limits.preserves_limits.preserves_cofiltered_limits CategoryTheory.Limits.PreservesLimits.preservesCofilteredLimits

instance compPreservesCofilteredLimits (F : C ⥤ D) (G : D ⥤ E) [PreservesCofilteredLimits F]
    [PreservesCofilteredLimits G] : PreservesCofilteredLimits (F ⋙ G)
    where PreservesCofilteredLimits J _ _ := inferInstance
#align category_theory.limits.comp_preserves_cofiltered_limits CategoryTheory.Limits.compPreservesCofilteredLimits

end CategoryTheory.Limits

