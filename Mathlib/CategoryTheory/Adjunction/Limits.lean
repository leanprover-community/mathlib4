/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin

! This file was ported from Lean 3 source module category_theory.adjunction.limits
! leanprover-community/mathlib commit 9e7c80f638149bfb3504ba8ff48dfdbfc949fb1a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Limits.Creates

/-!
# Adjunctions and limits

A left adjoint preserves colimits (`category_theory.adjunction.left_adjoint_preserves_colimits`),
and a right adjoint preserves limits (`category_theory.adjunction.right_adjoint_preserves_limits`).

Equivalences create and reflect (co)limits.
(`category_theory.adjunction.is_equivalence_creates_limits`,
`category_theory.adjunction.is_equivalence_creates_colimits`,
`category_theory.adjunction.is_equivalence_reflects_limits`,
`category_theory.adjunction.is_equivalence_reflects_colimits`,)

In `category_theory.adjunction.cocones_iso` we show that
when `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/


open Opposite

namespace CategoryTheory.Adjunction

open CategoryTheory

open CategoryTheory.Functor

open CategoryTheory.Limits

universe v u v₁ v₂ v₀ u₁ u₂

section ArbitraryUniverse

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj

section PreservationColimits

variable {J : Type u} [Category.{v} J] (K : J ⥤ C)

/-- The right adjoint of `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
def functorialityRightAdjoint : Cocone (K ⋙ F) ⥤ Cocone K :=
  Cocones.functoriality _ G ⋙
    Cocones.precompose (K.rightUnitor.inv ≫ whiskerLeft K adj.Unit ≫ (associator _ _ _).inv)
#align category_theory.adjunction.functoriality_right_adjoint CategoryTheory.Adjunction.functorialityRightAdjoint

attribute [local reducible] functoriality_right_adjoint

/-- The unit for the adjunction for `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
@[simps]
def functorialityUnit : 𝟭 (Cocone K) ⟶ Cocones.functoriality _ F ⋙ functorialityRightAdjoint adj K
    where app c := { Hom := adj.Unit.app c.pt }
#align category_theory.adjunction.functoriality_unit CategoryTheory.Adjunction.functorialityUnit

/-- The counit for the adjunction for `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
@[simps]
def functorialityCounit :
    functorialityRightAdjoint adj K ⋙ Cocones.functoriality _ F ⟶ 𝟭 (Cocone (K ⋙ F))
    where app c := { Hom := adj.counit.app c.pt }
#align category_theory.adjunction.functoriality_counit CategoryTheory.Adjunction.functorialityCounit

/-- The functor `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)` is a left adjoint. -/
def functorialityIsLeftAdjoint : IsLeftAdjoint (Cocones.functoriality K F)
    where
  right := functorialityRightAdjoint adj K
  adj :=
    mkOfUnitCounit
      { Unit := functorialityUnit adj K
        counit := functorialityCounit adj K }
#align category_theory.adjunction.functoriality_is_left_adjoint CategoryTheory.Adjunction.functorialityIsLeftAdjoint

/-- A left adjoint preserves colimits.

See <https://stacks.math.columbia.edu/tag/0038>.
-/
def leftAdjointPreservesColimits : PreservesColimitsOfSize.{v, u} F
    where PreservesColimitsOfShape J 𝒥 :=
    {
      PreservesColimit := fun F =>
        {
          preserves := fun c hc =>
            is_colimit.iso_unique_cocone_morphism.inv fun s =>
              @Equiv.unique _ _ (is_colimit.iso_unique_cocone_morphism.hom hc _)
                ((adj.functoriality_is_left_adjoint _).adj.homEquiv _ _) } }
#align category_theory.adjunction.left_adjoint_preserves_colimits CategoryTheory.Adjunction.leftAdjointPreservesColimits

omit adj

-- see Note [lower instance priority]
instance (priority := 100) isEquivalencePreservesColimits (E : C ⥤ D) [IsEquivalence E] :
    PreservesColimitsOfSize.{v, u} E :=
  leftAdjointPreservesColimits E.Adjunction
#align category_theory.adjunction.is_equivalence_preserves_colimits CategoryTheory.Adjunction.isEquivalencePreservesColimits

-- see Note [lower instance priority]
instance (priority := 100) isEquivalenceReflectsColimits (E : D ⥤ C) [IsEquivalence E] :
    ReflectsColimitsOfSize.{v, u} E
    where ReflectsColimitsOfShape J 𝒥 :=
    {
      ReflectsColimit := fun K =>
        {
          reflects := fun c t =>
            by
            have l :=
              (is_colimit_of_preserves E.inv t).mapCoconeEquiv E.as_equivalence.unit_iso.symm
            refine' ((is_colimit.precompose_inv_equiv K.right_unitor _).symm l).ofIsoColimit _
            tidy } }
#align category_theory.adjunction.is_equivalence_reflects_colimits CategoryTheory.Adjunction.isEquivalenceReflectsColimits

-- see Note [lower instance priority]
instance (priority := 100) isEquivalenceCreatesColimits (H : D ⥤ C) [IsEquivalence H] :
    CreatesColimitsOfSize.{v, u} H
    where CreatesColimitsOfShape J 𝒥 :=
    {
      CreatesColimit := fun F =>
        {
          lifts := fun c t =>
            { liftedCocone := H.map_cocone_inv c
              validLift := H.map_cocone_map_cocone_inv c } } }
#align category_theory.adjunction.is_equivalence_creates_colimits CategoryTheory.Adjunction.isEquivalenceCreatesColimits

-- verify the preserve_colimits instance works as expected:
example (E : C ⥤ D) [IsEquivalence E] (c : Cocone K) (h : IsColimit c) :
    IsColimit (E.mapCocone c) :=
  PreservesColimit.preserves h

theorem hasColimit_comp_equivalence (E : C ⥤ D) [IsEquivalence E] [HasColimit K] :
    HasColimit (K ⋙ E) :=
  HasColimit.mk
    { Cocone := E.mapCocone (colimit.cocone K)
      IsColimit := PreservesColimit.preserves (colimit.isColimit K) }
#align category_theory.adjunction.has_colimit_comp_equivalence CategoryTheory.Adjunction.hasColimit_comp_equivalence

theorem hasColimit_of_comp_equivalence (E : C ⥤ D) [IsEquivalence E] [HasColimit (K ⋙ E)] :
    HasColimit K :=
  @hasColimitOfIso _ _ _ _ (K ⋙ E ⋙ inv E) K
    (@hasColimit_comp_equivalence _ _ _ _ _ _ (K ⋙ E) (inv E) _ _)
    ((Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft K E.asEquivalence.unitIso)
#align category_theory.adjunction.has_colimit_of_comp_equivalence CategoryTheory.Adjunction.hasColimit_of_comp_equivalence

/-- Transport a `has_colimits_of_shape` instance across an equivalence. -/
theorem hasColimitsOfShape_of_equivalence (E : C ⥤ D) [IsEquivalence E] [HasColimitsOfShape J D] :
    HasColimitsOfShape J C :=
  ⟨fun F => has_colimit_of_comp_equivalence F E⟩
#align category_theory.adjunction.has_colimits_of_shape_of_equivalence CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence

/-- Transport a `has_colimits` instance across an equivalence. -/
theorem has_colimits_of_equivalence (E : C ⥤ D) [IsEquivalence E] [HasColimitsOfSize.{v, u} D] :
    HasColimitsOfSize.{v, u} C :=
  ⟨fun J hJ => has_colimits_of_shape_of_equivalence E⟩
#align category_theory.adjunction.has_colimits_of_equivalence CategoryTheory.Adjunction.has_colimits_of_equivalence

end PreservationColimits

section PreservationLimits

variable {J : Type u} [Category.{v} J] (K : J ⥤ D)

/-- The left adjoint of `cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
def functorialityLeftAdjoint : Cone (K ⋙ G) ⥤ Cone K :=
  Cones.functoriality _ F ⋙
    Cones.postcompose ((associator _ _ _).Hom ≫ whiskerLeft K adj.counit ≫ K.rightUnitor.Hom)
#align category_theory.adjunction.functoriality_left_adjoint CategoryTheory.Adjunction.functorialityLeftAdjoint

attribute [local reducible] functoriality_left_adjoint

/-- The unit for the adjunction for`cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
@[simps]
def functorialityUnit' : 𝟭 (Cone (K ⋙ G)) ⟶ functorialityLeftAdjoint adj K ⋙ Cones.functoriality _ G
    where app c := { Hom := adj.Unit.app c.pt }
#align category_theory.adjunction.functoriality_unit' CategoryTheory.Adjunction.functorialityUnit'

/-- The counit for the adjunction for`cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
@[simps]
def functorialityCounit' : Cones.functoriality _ G ⋙ functorialityLeftAdjoint adj K ⟶ 𝟭 (Cone K)
    where app c := { Hom := adj.counit.app c.pt }
#align category_theory.adjunction.functoriality_counit' CategoryTheory.Adjunction.functorialityCounit'

/-- The functor `cones.functoriality K G : cone K ⥤ cone (K ⋙ G)` is a right adjoint. -/
def functorialityIsRightAdjoint : IsRightAdjoint (Cones.functoriality K G)
    where
  left := functorialityLeftAdjoint adj K
  adj :=
    mkOfUnitCounit
      { Unit := functorialityUnit' adj K
        counit := functorialityCounit' adj K }
#align category_theory.adjunction.functoriality_is_right_adjoint CategoryTheory.Adjunction.functorialityIsRightAdjoint

/-- A right adjoint preserves limits.

See <https://stacks.math.columbia.edu/tag/0038>.
-/
def rightAdjointPreservesLimits : PreservesLimitsOfSize.{v, u} G
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun K =>
        {
          preserves := fun c hc =>
            is_limit.iso_unique_cone_morphism.inv fun s =>
              @Equiv.unique _ _ (is_limit.iso_unique_cone_morphism.hom hc _)
                ((adj.functoriality_is_right_adjoint _).adj.homEquiv _ _).symm } }
#align category_theory.adjunction.right_adjoint_preserves_limits CategoryTheory.Adjunction.rightAdjointPreservesLimits

omit adj

-- see Note [lower instance priority]
instance (priority := 100) isEquivalencePreservesLimits (E : D ⥤ C) [IsEquivalence E] :
    PreservesLimitsOfSize.{v, u} E :=
  rightAdjointPreservesLimits E.inv.Adjunction
#align category_theory.adjunction.is_equivalence_preserves_limits CategoryTheory.Adjunction.isEquivalencePreservesLimits

-- see Note [lower instance priority]
instance (priority := 100) isEquivalenceReflectsLimits (E : D ⥤ C) [IsEquivalence E] :
    ReflectsLimitsOfSize.{v, u} E
    where ReflectsLimitsOfShape J 𝒥 :=
    {
      ReflectsLimit := fun K =>
        {
          reflects := fun c t =>
            by
            have := (is_limit_of_preserves E.inv t).mapConeEquiv E.as_equivalence.unit_iso.symm
            refine' ((is_limit.postcompose_hom_equiv K.left_unitor _).symm this).ofIsoLimit _
            tidy } }
#align category_theory.adjunction.is_equivalence_reflects_limits CategoryTheory.Adjunction.isEquivalenceReflectsLimits

-- see Note [lower instance priority]
instance (priority := 100) isEquivalenceCreatesLimits (H : D ⥤ C) [IsEquivalence H] :
    CreatesLimitsOfSize.{v, u} H
    where CreatesLimitsOfShape J 𝒥 :=
    {
      CreatesLimit := fun F =>
        {
          lifts := fun c t =>
            { liftedCone := H.map_cone_inv c
              validLift := H.map_cone_map_cone_inv c } } }
#align category_theory.adjunction.is_equivalence_creates_limits CategoryTheory.Adjunction.isEquivalenceCreatesLimits

-- verify the preserve_limits instance works as expected:
example (E : D ⥤ C) [IsEquivalence E] (c : Cone K) [h : IsLimit c] : IsLimit (E.mapCone c) :=
  PreservesLimit.preserves h

theorem hasLimit_comp_equivalence (E : D ⥤ C) [IsEquivalence E] [HasLimit K] : HasLimit (K ⋙ E) :=
  HasLimit.mk
    { Cone := E.mapCone (limit.cone K)
      IsLimit := PreservesLimit.preserves (limit.isLimit K) }
#align category_theory.adjunction.has_limit_comp_equivalence CategoryTheory.Adjunction.hasLimit_comp_equivalence

theorem hasLimit_of_comp_equivalence (E : D ⥤ C) [IsEquivalence E] [HasLimit (K ⋙ E)] :
    HasLimit K :=
  @hasLimitOfIso _ _ _ _ (K ⋙ E ⋙ inv E) K
    (@hasLimit_comp_equivalence _ _ _ _ _ _ (K ⋙ E) (inv E) _ _)
    (isoWhiskerLeft K E.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _)
#align category_theory.adjunction.has_limit_of_comp_equivalence CategoryTheory.Adjunction.hasLimit_of_comp_equivalence

/-- Transport a `has_limits_of_shape` instance across an equivalence. -/
theorem hasLimitsOfShape_of_equivalence (E : D ⥤ C) [IsEquivalence E] [HasLimitsOfShape J C] :
    HasLimitsOfShape J D :=
  ⟨fun F => has_limit_of_comp_equivalence F E⟩
#align category_theory.adjunction.has_limits_of_shape_of_equivalence CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence

/-- Transport a `has_limits` instance across an equivalence. -/
theorem has_limits_of_equivalence (E : D ⥤ C) [IsEquivalence E] [HasLimitsOfSize.{v, u} C] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun J hJ => has_limits_of_shape_of_equivalence E⟩
#align category_theory.adjunction.has_limits_of_equivalence CategoryTheory.Adjunction.has_limits_of_equivalence

end PreservationLimits

/-- auxiliary construction for `cocones_iso` -/
@[simps]
def coconesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
    (t : ((cocones J D).obj (op (K ⋙ F))).obj Y) : (G ⋙ (cocones J C).obj (op K)).obj Y
    where
  app j := (adj.homEquiv (K.obj j) Y) (t.app j)
  naturality' j j' f := by
    erw [← adj.hom_equiv_naturality_left, t.naturality]
    dsimp
    simp
#align category_theory.adjunction.cocones_iso_component_hom CategoryTheory.Adjunction.coconesIsoComponentHom

/-- auxiliary construction for `cocones_iso` -/
@[simps]
def coconesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
    (t : (G ⋙ (cocones J C).obj (op K)).obj Y) : ((cocones J D).obj (op (K ⋙ F))).obj Y
    where
  app j := (adj.homEquiv (K.obj j) Y).symm (t.app j)
  naturality' j j' f :=
    by
    erw [← adj.hom_equiv_naturality_left_symm, ← adj.hom_equiv_naturality_right_symm, t.naturality]
    dsimp; simp
#align category_theory.adjunction.cocones_iso_component_inv CategoryTheory.Adjunction.coconesIsoComponentInv

/-- auxiliary construction for `cones_iso` -/
@[simps]
def conesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : (Functor.op F ⋙ (cones J D).obj K).obj X) : ((cones J C).obj (K ⋙ G)).obj X
    where
  app j := (adj.homEquiv (unop X) (K.obj j)) (t.app j)
  naturality' j j' f :=
    by
    erw [← adj.hom_equiv_naturality_right, ← t.naturality, category.id_comp, category.id_comp]
    rfl
#align category_theory.adjunction.cones_iso_component_hom CategoryTheory.Adjunction.conesIsoComponentHom

/-- auxiliary construction for `cones_iso` -/
@[simps]
def conesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : ((cones J C).obj (K ⋙ G)).obj X) : (Functor.op F ⋙ (cones J D).obj K).obj X
    where
  app j := (adj.homEquiv (unop X) (K.obj j)).symm (t.app j)
  naturality' j j' f := by
    erw [← adj.hom_equiv_naturality_right_symm, ← t.naturality, category.id_comp, category.id_comp]
#align category_theory.adjunction.cones_iso_component_inv CategoryTheory.Adjunction.conesIsoComponentInv

end ArbitraryUniverse

variable {C : Type u₁} [Category.{v₀} C] {D : Type u₂} [Category.{v₀} D] {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G)

-- Note: this is natural in K, but we do not yet have the tools to formulate that.
/-- When `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/
def coconesIso {J : Type u} [Category.{v} J] {K : J ⥤ C} :
    (cocones J D).obj (op (K ⋙ F)) ≅ G ⋙ (cocones J C).obj (op K) :=
  NatIso.ofComponents
    (fun Y =>
      { Hom := coconesIsoComponentHom adj Y
        inv := coconesIsoComponentInv adj Y })
    (by tidy)
#align category_theory.adjunction.cocones_iso CategoryTheory.Adjunction.coconesIso

-- Note: this is natural in K, but we do not yet have the tools to formulate that.
/-- When `F ⊣ G`,
the functor associating to each `X` the cones over `K` with cone point `F.op.obj X`
is naturally isomorphic to
the functor associating to each `X` the cones over `K ⋙ G` with cone point `X`.
-/
def conesIso {J : Type u} [Category.{v} J] {K : J ⥤ D} :
    F.op ⋙ (cones J D).obj K ≅ (cones J C).obj (K ⋙ G) :=
  NatIso.ofComponents
    (fun X =>
      { Hom := conesIsoComponentHom adj X
        inv := conesIsoComponentInv adj X })
    (by tidy)
#align category_theory.adjunction.cones_iso CategoryTheory.Adjunction.conesIso

end CategoryTheory.Adjunction

