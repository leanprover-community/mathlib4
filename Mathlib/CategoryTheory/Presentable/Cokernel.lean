/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.IndYoneda
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Filtered-colimit preservation for homs out of cokernels
-/

@[expose] public section

universe u v

open CategoryTheory Limits

namespace CategoryTheory

/-- If ordinary homs out of `X` and `Y` preserve small filtered colimits, then ordinary homs out
of a cokernel of `X ⟶ Y` preserve small filtered colimits.

Ordinary hom out of a cokernel is an equalizer of ordinary hom functors, and filtered colimits
commute with finite limits in `Type`. -/
lemma preservesFilteredColimits_hom_cokernel_of_preserves_hom {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) [HasCokernel f]
    [PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (Opposite.op X))]
    [PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (Opposite.op Y))] :
    PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (Opposite.op (cokernel f))) := by
  refine ⟨fun J _ _ => ?_⟩
  let : PreservesFilteredColimitsOfSize.{0, 0}
      (lim : (WalkingParallelPairᵒᵖ ⥤ Type v) ⥤ Type v) :=
    lim_preservesFilteredColimitsOfSize_of_types WalkingParallelPairᵒᵖ
  let : PreservesColimitsOfShape J (lim : (WalkingParallelPairᵒᵖ ⥤ Type v) ⥤ Type v) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
  let H : WalkingParallelPairᵒᵖ ⥤ C ⥤ Type v := (parallelPair f 0).op ⋙ coyoneda
  have hH : PreservesColimitsOfShape J H.flip := by
    apply preservesColimitsOfShape_of_evaluation
    intro i
    have hi : PreservesColimitsOfShape J (H.obj i) := by
      cases i using Opposite.rec
      rename_i i
      cases i
      · exact inferInstanceAs (PreservesColimitsOfShape J (coyoneda.obj (Opposite.op X)))
      · exact inferInstanceAs (PreservesColimitsOfShape J (coyoneda.obj (Opposite.op Y)))
    exact preservesColimitsOfShape_of_natIso (flipCompEvaluation H i).symm
  let : PreservesColimitsOfShape J H.flip := hH
  have hlim : PreservesColimitsOfShape J (limit H) := by
    exact preservesColimitsOfShape_of_natIso (limitFlipIsoCompLim H.flip).symm
  let : PreservesColimitsOfShape J (limit H) := hlim
  exact preservesColimitsOfShape_of_natIso
    (coyonedaOpColimitIsoLimitCoyoneda (parallelPair f 0)).symm

end CategoryTheory
