/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits
import Mathlib.CategoryTheory.Limits.Indization.ParallelPair
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape

/-!
# Equalizers of ind-objects

We show that if a category `C` has equalizers, then ind-objects are closed under equalizers.

# References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 6.1
-/

universe v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

variable {I : Type v} [SmallCategory I] [IsFiltered I]

variable {J : Type} [SmallCategory J] [FinCategory J]

variable (F : J ⥤ I ⥤ C)

/--
Suppose `F : J ⥤ I ⥤ C` is a finite diagram in the functor category `I ⥤ C`, where `I` is small
and filtered. If `i : I`, we can apply the Yoneda embedding to `F(·, i)` to obtain a
diagram of presheaves `J ⥤ Cᵒᵖ ⥤ Type v`. Suppose that the limits of this diagram is always an
ind-object.

For `j : J` we can apply the Yoneda embedding to `F(j, ·)` and take colimits to obtain a finite
diagram `J ⥤ Cᵒᵖ ⥤ Type v` (which is actually a diagram `J ⥤ Ind C`). The theorem states that
the limit of this diagram is an ind-object.

This theorem will be used to construct equalizers in the category of ind-objects. It can be
interpreted as saying that ind-objects are closed under finite limits as long as the diagram
we are taking the limit of comes from a diagram in a functor category `I ⥤ C`. We will show (TODO)
that this is the case for any parallel pair of morphisms in `Ind C` and deduce that ind-objects
are closed under equalizers.

This is Proposition 6.1.16(i) in [Kashiwara2006].
-/
theorem isIndObject_limit_comp_yoneda_comp_colim
    (hF : ∀ i, IsIndObject (limit (F.flip.obj i ⋙ yoneda))) :
    IsIndObject (limit (F ⋙ (Functor.whiskeringRight _ _ _).obj yoneda ⋙ colim)) := by
  let G : J ⥤ I ⥤ (Cᵒᵖ ⥤ Type v) := F ⋙ (Functor.whiskeringRight _ _ _).obj yoneda
  apply IsIndObject.map (HasLimit.isoOfNatIso (colimitFlipIsoCompColim G)).hom
  apply IsIndObject.map (colimitLimitIso G).hom
  apply isIndObject_colimit
  exact fun i => IsIndObject.map (limitObjIsoLimitCompEvaluation _ _).inv (hF i)

end

/-- If `C` has equalizers. then ind-objects are closed under equalizers.

This is Proposition 6.1.17(i) in [Kashiwara2006].
-/
instance isClosedUnderLimitsOfShape_isIndObject_walkingParallelPair [HasEqualizers C] :
    ObjectProperty.IsClosedUnderLimitsOfShape (IsIndObject (C := C)) WalkingParallelPair :=
  .mk' (by
    rintro _ ⟨F, h⟩
    obtain ⟨P⟩ := nonempty_indParallelPairPresentation (h WalkingParallelPair.zero)
      (h WalkingParallelPair.one) (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right)
    exact IsIndObject.map
      (HasLimit.isoOfNatIso (P.parallelPairIsoParallelPairCompYoneda.symm ≪≫
        (diagramIsoParallelPair _).symm)).hom
      (isIndObject_limit_comp_yoneda_comp_colim (parallelPair P.φ P.ψ)
        (fun i => isIndObject_limit_comp_yoneda _)))

@[deprecated (since := "2025-09-22")]
alias closedUnderLimitsOfShape_walkingParallelPair_isIndObject :=
  isClosedUnderLimitsOfShape_isIndObject_walkingParallelPair

end CategoryTheory.Limits
