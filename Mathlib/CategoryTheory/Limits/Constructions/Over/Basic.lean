/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers

#align_import category_theory.limits.constructions.over.basic from "leanprover-community/mathlib"@"15db1b4f26ba89c6eb0c78b0a44c7e779a788e29"

/-!
# Limits in the over category

Declare instances for limits in the over category: If `C` has finite wide pullbacks, `Over B` has
finite limits, and if `C` has arbitrary wide pullbacks then `Over B` has limits.
-/


universe w v u v' u' w'

-- morphism levels before object levels. See note [category_theory universes].
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X : C}

namespace CategoryTheory.Over

/-- Make sure we can derive pullbacks in `Over B`. -/
instance hasPullbacks {B : C} [HasPullbacks C] : HasPullbacks (Over B) := by
  letI : HasLimitsOfShape (ULiftHom.{v} (ULift.{v} WalkingCospan)) C :=
    hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v} _)
  letI : Category (ULiftHom.{v} (ULift.{v} WalkingCospan)) := inferInstance
  exact hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v, v} _).symm

/-- Make sure we can derive equalizers in `Over B`. -/
instance hasEqualizers {B : C} [HasEqualizers C] : HasEqualizers (Over B) := by
  letI : HasLimitsOfShape (ULiftHom.{v} (ULift.{v} WalkingParallelPair)) C :=
    hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v} _)
  letI : Category (ULiftHom.{v} (ULift.{v} WalkingParallelPair)) := inferInstance
  exact hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v, v} _).symm

instance hasFiniteLimits {B : C} [HasFiniteWidePullbacks C] : HasFiniteLimits (Over B) := by
  apply @hasFiniteLimits_of_hasEqualizers_and_finite_products _ _ ?_ ?_
  · exact ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  · apply @hasEqualizers_of_hasPullbacks_and_binary_products _ _ ?_ _
    haveI : HasPullbacks C := ⟨inferInstance⟩
    exact ConstructProducts.over_binaryProduct_of_pullback
#align category_theory.over.has_finite_limits CategoryTheory.Over.hasFiniteLimits

instance hasLimits {B : C} [HasWidePullbacks.{w} C] : HasLimitsOfSize.{w} (Over B) := by
  apply @has_limits_of_hasEqualizers_and_products _ _ ?_ ?_
  · exact ConstructProducts.over_products_of_widePullbacks
  · apply @hasEqualizers_of_hasPullbacks_and_binary_products _ _ ?_ _
    haveI : HasPullbacks C := ⟨inferInstance⟩
    exact ConstructProducts.over_binaryProduct_of_pullback
#align category_theory.over.has_limits CategoryTheory.Over.hasLimits

section Preserves

section ToMove

variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

class PreservesFiniteWidePullbacks where
  preserves : ∀ J [Finite J], PreservesLimitsOfShape (WidePullbackShape J) F

instance [PreservesFiniteWidePullbacks F] (J : Type w) [Finite J] :
    PreservesLimitsOfShape (WidePullbackShape J) F := PreservesFiniteWidePullbacks.preserves J

instance [∀ J, PreservesLimitsOfShape (WidePullbackShape J) F] :
    PreservesFiniteWidePullbacks F :=
  ⟨fun _ _ => inferInstance⟩

end ToMove
section Products

open Over.ConstructProducts WidePullbackShape in
instance postPreservesProducts {J : Type w} {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) [PreservesLimitsOfShape (WidePullbackShape J) F] {B : C} :
  PreservesLimitsOfShape (Discrete J) (Over.post (X := B) F) where
    preservesLimit {K} := {
      preserves := fun {c} hc => by
        let h1 : IsLimit (F.mapCone <| (conesEquiv B _).inverse.obj c) :=
          PreservesLimit.preserves (IsLimit.ofRightAdjoint (conesEquiv B _).toAdjunction hc)
        let Fc : Cone (widePullbackDiagramOfDiagramOver (F.obj B) (K ⋙ Over.post F)) :=
          (Cones.postcomposeEquivalence (diagramIsoWideCospan _)).functor.obj
          (F.mapCone <| (conesEquiv B _).inverse.obj c)
        let hFc : IsLimit ((conesEquiv _ _).functor.obj Fc) := IsLimit.ofRightAdjoint
          (conesEquiv (F.obj B) _).symm.toAdjunction ((IsLimit.postcomposeHomEquiv _ _).symm h1)
        refine IsLimit.ofIsoLimit hFc <| Cones.ext (Over.isoMk (Iso.refl _) ?_)
          fun ⟨j⟩ => Over.OverMorphism.ext ?_
        <;> dsimp [Fc, diagramIsoWideCospan]
        <;> rw [Category.id_comp, Category.comp_id] }

instance postPreservesFiniteProducts {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    [PreservesFiniteWidePullbacks F] {B : C} :
  PreservesFiniteProducts (Over.post (X := B) F) where
    preserves _ _ := inferInstance

end Products
section
variable {J : Type} [SmallCategory J] [IsConnected J] [HasLimitsOfShape J C]
variable {D : Type u} [Category.{v} D] (F : C ⥤ D)

noncomputable instance (F : C ⥤ D) [PreservesLimitsOfShape J F] {B : C} :
    PreservesLimitsOfShape J (Over.post (X := B) F) := by
  letI : HasLimitsOfShape (ULiftHom.{v} (ULift.{v} J)) C :=
    hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v} _)
  letI : PreservesLimitsOfShape (ULiftHom.{v} (ULift.{v} J)) F :=
    preservesLimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv.{v, v} _) F
  exact preservesLimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv.{v, v} _).symm
    (Over.post (X := B) F)

noncomputable instance postPreservesPullbacks
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] {B : C} :
    PreservesLimitsOfShape WalkingCospan (Over.post (X := B) F) :=
  inferInstance

noncomputable instance postPreservesEqualizers
    [HasEqualizers C] [PreservesLimitsOfShape WalkingParallelPair F] {B : C} :
    PreservesLimitsOfShape WalkingParallelPair (Over.post (X := B) F) :=
  inferInstance

noncomputable instance postPreservesFiniteLimits [HasEqualizers C] [HasFiniteWidePullbacks C]
    [PreservesLimitsOfShape WalkingParallelPair F] [PreservesFiniteWidePullbacks F] {B : C} :
    PreservesFiniteLimits (Over.post (X := B) F) :=
  preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts _

noncomputable instance postPreservesLimits {B : C} [HasEqualizers C] [HasWidePullbacks.{w} C]
    [PreservesLimitsOfShape WalkingParallelPair F]
    [∀ (J : Type w), PreservesLimitsOfShape (WidePullbackShape J) F] :
    PreservesLimitsOfSize.{w, w} (Over.post (X := B) F) :=
  preservesLimitsOfPreservesEqualizersAndProducts _

end
end Preserves
end CategoryTheory.Over

namespace CategoryTheory.Under

/-- Make sure we can derive pushouts in `Under B`. -/
instance hasPushouts {B : C} [HasPushouts C] : HasPushouts (Under B) := by
  letI : HasColimitsOfShape (ULiftHom.{v} (ULift.{v} WalkingSpan)) C :=
    hasColimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v} _)
  letI : Category (ULiftHom.{v} (ULift.{v} WalkingSpan)) := inferInstance
  exact hasColimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v, v} _).symm

/-- Make sure we can derive equalizers in `Under B`. -/
instance hasCoequalizers {B : C} [HasCoequalizers C] : HasCoequalizers (Under B) := by
  letI : HasColimitsOfShape (ULiftHom.{v} (ULift.{v} WalkingParallelPair)) C :=
    hasColimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v} _)
  letI : Category (ULiftHom.{v} (ULift.{v} WalkingParallelPair)) := inferInstance
  exact hasColimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v, v} _).symm

instance hasFiniteColimits {B : C} [HasFiniteWidePushouts C] : HasFiniteColimits (Under B) := by
  apply @hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts _ _ ?_ ?_
  · exact ConstructCoproducts.under_finiteCoproducts_of_finiteWidePushouts
  · apply @hasCoequalizers_of_hasPushouts_and_binary_coproducts _ _ ?_ _
    haveI : HasPushouts C := ⟨inferInstance⟩
    exact ConstructCoproducts.under_binaryCoproduct_of_pushout

instance hasColimits {B : C} [HasWidePushouts.{w} C] : HasColimitsOfSize.{w} (Under B) := by
  apply @has_colimits_of_hasCoequalizers_and_coproducts _ _ ?_ ?_
  · exact ConstructCoproducts.under_coproducts_of_widePushouts
  · apply @hasCoequalizers_of_hasPushouts_and_binary_coproducts _ _ ?_ _
    haveI : HasPushouts C := ⟨inferInstance⟩
    exact ConstructCoproducts.under_binaryCoproduct_of_pushout

section Preserves

section ToMove

variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

class PreservesFiniteWidePushouts where
  preserves : ∀ J [Finite J], PreservesColimitsOfShape (WidePushoutShape J) F

instance [PreservesFiniteWidePushouts F] (J : Type w) [Finite J] :
    PreservesColimitsOfShape (WidePushoutShape J) F := PreservesFiniteWidePushouts.preserves J

instance [∀ J, PreservesColimitsOfShape (WidePushoutShape J) F] :
    PreservesFiniteWidePushouts F :=
  ⟨fun _ _ => inferInstance⟩

end ToMove
section Coproducts

open Under.ConstructCoproducts WidePushoutShape in
instance postPreservesCoproducts {J : Type w} {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) [PreservesColimitsOfShape (WidePushoutShape J) F] {B : C} :
  PreservesColimitsOfShape (Discrete J) (Under.post (X := B) F) where
    preservesColimit {K} := {
      preserves := fun {c} hc => by
        let h1 : IsColimit (F.mapCocone <| (coconesEquiv B _).inverse.obj c) :=
          PreservesColimit.preserves (IsColimit.ofLeftAdjoint
          (coconesEquiv B _).symm.toAdjunction hc)
        let Fc : Cocone (widePushoutDiagramOfDiagramUnder (F.obj B) (K ⋙ Under.post F)) :=
          (Cocones.precomposeEquivalence (diagramIsoWideSpan _)).inverse.obj
          (F.mapCocone <| (coconesEquiv B _).inverse.obj c)
        let hFc : IsColimit ((coconesEquiv _ _).functor.obj Fc) := IsColimit.ofLeftAdjoint
          (coconesEquiv (F.obj B) _).toAdjunction ((IsColimit.precomposeInvEquiv _ _).symm h1)
        refine IsColimit.ofIsoColimit hFc <| Cocones.ext (Under.isoMk (Iso.refl _) ?_)
          fun ⟨j⟩ => Under.UnderMorphism.ext ?_
        <;> dsimp [Fc, diagramIsoWideSpan]
        <;> rw [Category.id_comp, Category.comp_id] }

instance postPreservesFiniteCoproducts {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    [PreservesFiniteWidePushouts F] {B : C} :
  PreservesFiniteCoproducts (Under.post (X := B) F) where
    preserves _ _ := inferInstance

end Coproducts
section
variable {J : Type} [SmallCategory J] [IsConnected J] [HasColimitsOfShape J C]
variable {D : Type u} [Category.{v} D] (F : C ⥤ D)

noncomputable instance (F : C ⥤ D) [PreservesColimitsOfShape J F] {B : C} :
    PreservesColimitsOfShape J (Under.post (X := B) F) := by
  letI : HasColimitsOfShape (ULiftHom.{v} (ULift.{v} J)) C :=
    hasColimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv.{v} _)
  letI : PreservesColimitsOfShape (ULiftHom.{v} (ULift.{v} J)) F :=
    preservesColimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv.{v, v} _) F
  exact preservesColimitsOfShapeOfEquiv (ULiftHomULiftCategory.equiv.{v, v} _).symm
    (Under.post (X := B) F)

noncomputable instance postPreservesPushouts
    [HasPushouts C] [PreservesColimitsOfShape WalkingSpan F] {B : C} :
    PreservesColimitsOfShape WalkingSpan (Under.post (X := B) F) :=
  inferInstance

noncomputable instance postPreservesCoequalizers
    [HasCoequalizers C] [PreservesColimitsOfShape WalkingParallelPair F] {B : C} :
    PreservesColimitsOfShape WalkingParallelPair (Under.post (X := B) F) :=
  inferInstance

noncomputable instance postPreservesFiniteColimits [HasCoequalizers C] [HasFiniteWidePushouts C]
    [PreservesColimitsOfShape WalkingParallelPair F] [PreservesFiniteWidePushouts F] {B : C} :
    PreservesFiniteColimits (Under.post (X := B) F) :=
  preservesFiniteColimitsOfPreservesCoequalizersAndFiniteCoproducts _

noncomputable instance postPreservesColimits {B : C} [HasCoequalizers C] [HasWidePushouts.{w} C]
    [PreservesColimitsOfShape WalkingParallelPair F]
    [∀ (J : Type w), PreservesColimitsOfShape (WidePushoutShape J) F] :
    PreservesColimitsOfSize.{w, w} (Under.post (X := B) F) :=
  preservesColimitsOfPreservesCoequalizersAndCoproducts _

end
end Preserves
end CategoryTheory.Under
