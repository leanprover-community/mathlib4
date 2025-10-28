/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Justus Springer
-/
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Preservation of filtered colimits and cofiltered limits.
Typically forgetful functors from algebraic categories preserve filtered colimits
(although not general colimits). See e.g. `Algebra/Category/MonCat/FilteredColimits`.

-/


open CategoryTheory

open CategoryTheory.Functor

namespace CategoryTheory.Limits

universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

section FilteredColimits

section Preserves

-- This should be used with explicit universe variables.
/-- `PreservesFilteredColimitsOfSize.{w', w} F` means that `F` sends all colimit cocones over any
filtered diagram `J ⥤ C` to colimit cocones, where `J : Type w` with `[Category.{w'} J]`. -/
@[nolint checkUnivs, pp_with_univ]
class PreservesFilteredColimitsOfSize (F : C ⥤ D) : Prop where
  preserves_filtered_colimits :
    ∀ (J : Type w) [Category.{w'} J] [IsFiltered J], PreservesColimitsOfShape J F

/--
A functor is said to preserve filtered colimits, if it preserves all colimits of shape `J`, where
`J` is a filtered category which is small relative to the universe in which morphisms of the source
live.
-/
abbrev PreservesFilteredColimits (F : C ⥤ D) : Prop :=
  PreservesFilteredColimitsOfSize.{v₂, v₂} F

attribute [instance 100] PreservesFilteredColimitsOfSize.preserves_filtered_colimits

instance (priority := 100) PreservesColimits.preservesFilteredColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w'} F] : PreservesFilteredColimitsOfSize.{w, w'} F where
  preserves_filtered_colimits _ := inferInstance

instance comp_preservesFilteredColimits (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFilteredColimitsOfSize.{w, w'} F] [PreservesFilteredColimitsOfSize.{w, w'} G] :
      PreservesFilteredColimitsOfSize.{w, w'} (F ⋙ G) where
  preserves_filtered_colimits _ := inferInstance

/-- A functor preserving larger filtered colimits also preserves smaller filtered colimits. -/
lemma preservesFilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [PreservesFilteredColimitsOfSize.{w', w₂'} F] :
      PreservesFilteredColimitsOfSize.{w, w₂} F where
  preserves_filtered_colimits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    haveI := IsFiltered.of_equivalence e.symm
    exact preservesColimitsOfShape_of_equiv e F

/--
`PreservesFilteredColimitsOfSize_shrink.{w, w'} F` tries to obtain
`PreservesFilteredColimitsOfSize.{w, w'} F` from some other `PreservesFilteredColimitsOfSize F`.
-/
lemma preservesFilteredColimitsOfSize_shrink (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{max w w₂, max w' w₂'} F] :
      PreservesFilteredColimitsOfSize.{w, w'} F :=
  preservesFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
Preserving filtered colimits at any universe implies preserving filtered colimits at universe `0`.
-/
lemma preservesSmallestFilteredColimits_of_preservesFilteredColimits (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w', w} F] : PreservesFilteredColimitsOfSize.{0, 0} F :=
  preservesFilteredColimitsOfSize_shrink F

end Preserves

section Reflects

-- This should be used with explicit universe variables.
/-- `ReflectsFilteredColimitsOfSize.{w', w} F` means that whenever the image of a filtered cocone
under `F` is a colimit cocone, the original cocone was already a colimit. -/
@[nolint checkUnivs, pp_with_univ]
class ReflectsFilteredColimitsOfSize (F : C ⥤ D) : Prop where
  reflects_filtered_colimits :
    ∀ (J : Type w) [Category.{w'} J] [IsFiltered J], ReflectsColimitsOfShape J F

/--
A functor is said to reflect filtered colimits, if it reflects all colimits of shape `J`, where
`J` is a filtered category which is small relative to the universe in which morphisms of the source
live.
-/
abbrev ReflectsFilteredColimits (F : C ⥤ D) : Prop :=
  ReflectsFilteredColimitsOfSize.{v₂, v₂} F

attribute [instance 100] ReflectsFilteredColimitsOfSize.reflects_filtered_colimits

instance (priority := 100) ReflectsColimits.reflectsFilteredColimits (F : C ⥤ D)
    [ReflectsColimitsOfSize.{w, w'} F] : ReflectsFilteredColimitsOfSize.{w, w'} F where
  reflects_filtered_colimits _ := inferInstance

instance comp_reflectsFilteredColimits (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFilteredColimitsOfSize.{w, w'} F] [ReflectsFilteredColimitsOfSize.{w, w'} G] :
      ReflectsFilteredColimitsOfSize.{w, w'} (F ⋙ G) where
  reflects_filtered_colimits _ := inferInstance

/-- A functor reflecting larger filtered colimits also reflects smaller filtered colimits. -/
lemma reflectsFilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [ReflectsFilteredColimitsOfSize.{w', w₂'} F] :
      ReflectsFilteredColimitsOfSize.{w, w₂} F where
  reflects_filtered_colimits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    haveI := IsFiltered.of_equivalence e.symm
    exact reflectsColimitsOfShape_of_equiv e F

/--
`ReflectsFilteredColimitsOfSize_shrink.{w, w'} F` tries to obtain
`ReflectsFilteredColimitsOfSize.{w, w'} F` from some other `ReflectsFilteredColimitsOfSize F`.
-/
lemma reflectsFilteredColimitsOfSize_shrink (F : C ⥤ D)
    [ReflectsFilteredColimitsOfSize.{max w w₂, max w' w₂'} F] :
      ReflectsFilteredColimitsOfSize.{w, w'} F :=
  reflectsFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
Reflecting filtered colimits at any universe implies reflecting filtered colimits at universe `0`.
-/
lemma reflectsSmallestFilteredColimits_of_reflectsFilteredColimits (F : C ⥤ D)
    [ReflectsFilteredColimitsOfSize.{w', w} F] : ReflectsFilteredColimitsOfSize.{0, 0} F :=
  reflectsFilteredColimitsOfSize_shrink F

end Reflects

end FilteredColimits

section CofilteredLimits

section Preserves

-- This should be used with explicit universe variables.
/-- `PreservesCofilteredLimitsOfSize.{w', w} F` means that `F` sends all limit cones over any
cofiltered diagram `J ⥤ C` to limit cones, where `J : Type w` with `[Category.{w'} J]`. -/
@[nolint checkUnivs, pp_with_univ]
class PreservesCofilteredLimitsOfSize (F : C ⥤ D) : Prop where
  preserves_cofiltered_limits :
    ∀ (J : Type w) [Category.{w'} J] [IsCofiltered J], PreservesLimitsOfShape J F

/--
A functor is said to preserve cofiltered limits, if it preserves all limits of shape `J`, where
`J` is a cofiltered category which is small relative to the universe in which morphisms of the
source live.
-/
abbrev PreservesCofilteredLimits (F : C ⥤ D) : Prop :=
  PreservesCofilteredLimitsOfSize.{v₂, v₂} F

attribute [instance 100] PreservesCofilteredLimitsOfSize.preserves_cofiltered_limits

instance (priority := 100) PreservesLimits.preservesCofilteredLimits (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w'} F] : PreservesCofilteredLimitsOfSize.{w, w'} F where
  preserves_cofiltered_limits _ := inferInstance

instance comp_preservesCofilteredLimits (F : C ⥤ D) (G : D ⥤ E)
    [PreservesCofilteredLimitsOfSize.{w, w'} F] [PreservesCofilteredLimitsOfSize.{w, w'} G] :
      PreservesCofilteredLimitsOfSize.{w, w'} (F ⋙ G) where
  preserves_cofiltered_limits _ := inferInstance

/-- A functor preserving larger cofiltered limits also preserves smaller cofiltered limits. -/
lemma preservesCofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [PreservesCofilteredLimitsOfSize.{w', w₂'} F] :
      PreservesCofilteredLimitsOfSize.{w, w₂} F where
  preserves_cofiltered_limits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    haveI := IsCofiltered.of_equivalence e.symm
    exact preservesLimitsOfShape_of_equiv e F

/--
`PreservesCofilteredLimitsOfSizeShrink.{w, w'} F` tries to obtain
`PreservesCofilteredLimitsOfSize.{w, w'} F` from some other `PreservesCofilteredLimitsOfSize F`.
-/
lemma preservesCofilteredLimitsOfSize_shrink (F : C ⥤ D)
    [PreservesCofilteredLimitsOfSize.{max w w₂, max w' w₂'} F] :
      PreservesCofilteredLimitsOfSize.{w, w'} F :=
  preservesCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
Preserving cofiltered limits at any universe implies preserving cofiltered limits at universe `0`.
-/
lemma preservesSmallestCofilteredLimits_of_preservesCofilteredLimits (F : C ⥤ D)
    [PreservesCofilteredLimitsOfSize.{w', w} F] : PreservesCofilteredLimitsOfSize.{0, 0} F :=
  preservesCofilteredLimitsOfSize_shrink F

end Preserves

section Reflects

-- This should be used with explicit universe variables.
/-- `ReflectsCofilteredLimitsOfSize.{w', w} F` means that whenever the image of a cofiltered cone
under `F` is a limit cone, the original cone was already a limit. -/
@[nolint checkUnivs, pp_with_univ]
class ReflectsCofilteredLimitsOfSize (F : C ⥤ D) : Prop where
  reflects_cofiltered_limits :
    ∀ (J : Type w) [Category.{w'} J] [IsCofiltered J], ReflectsLimitsOfShape J F

/--
A functor is said to reflect cofiltered limits, if it reflects all limits of shape `J`, where
`J` is a cofiltered category which is small relative to the universe in which morphisms of the
source live.
-/
abbrev ReflectsCofilteredLimits (F : C ⥤ D) : Prop :=
  ReflectsCofilteredLimitsOfSize.{v₂, v₂} F

attribute [instance 100] ReflectsCofilteredLimitsOfSize.reflects_cofiltered_limits

instance (priority := 100) ReflectsLimits.reflectsCofilteredLimits (F : C ⥤ D)
    [ReflectsLimitsOfSize.{w, w'} F] : ReflectsCofilteredLimitsOfSize.{w, w'} F where
  reflects_cofiltered_limits _ := inferInstance

instance comp_reflectsCofilteredLimits (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsCofilteredLimitsOfSize.{w, w'} F] [ReflectsCofilteredLimitsOfSize.{w, w'} G] :
      ReflectsCofilteredLimitsOfSize.{w, w'} (F ⋙ G) where
  reflects_cofiltered_limits _ := inferInstance

/-- A functor reflecting larger cofiltered limits also reflects smaller cofiltered limits. -/
lemma reflectsCofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [ReflectsCofilteredLimitsOfSize.{w', w₂'} F] :
      ReflectsCofilteredLimitsOfSize.{w, w₂} F where
  reflects_cofiltered_limits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    haveI := IsCofiltered.of_equivalence e.symm
    exact reflectsLimitsOfShape_of_equiv e F

/--
`ReflectsCofilteredLimitsOfSize_shrink.{w, w'} F` tries to obtain
`ReflectsCofilteredLimitsOfSize.{w, w'} F` from some other `ReflectsCofilteredLimitsOfSize F`.
-/
lemma reflectsCofilteredLimitsOfSize_shrink (F : C ⥤ D)
    [ReflectsCofilteredLimitsOfSize.{max w w₂, max w' w₂'} F] :
      ReflectsCofilteredLimitsOfSize.{w, w'} F :=
  reflectsCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
Reflecting cofiltered limits at any universe implies reflecting cofiltered limits at universe `0`.
-/
lemma reflectsSmallestCofilteredLimits_of_reflectsCofilteredLimits (F : C ⥤ D)
    [ReflectsCofilteredLimitsOfSize.{w', w} F] : ReflectsCofilteredLimitsOfSize.{0, 0} F :=
  reflectsCofilteredLimitsOfSize_shrink F

end Reflects

end CofilteredLimits

end CategoryTheory.Limits
