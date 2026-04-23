/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.StacksAttribute
import Mathlib.Util.CompileInductive

/-!
# Adjunctions and limits

A left adjoint preserves colimits (`CategoryTheory.Adjunction.leftAdjoint_preservesColimits`),
and a right adjoint preserves limits (`CategoryTheory.Adjunction.rightAdjoint_preservesLimits`).

Equivalences create and reflect (co)limits.
(`CategoryTheory.Functor.createsLimitsOfIsEquivalence`,
`CategoryTheory.Functor.createsColimitsOfIsEquivalence`,
`CategoryTheory.Functor.reflectsLimits_of_isEquivalence`,
`CategoryTheory.Functor.reflectsColimits_of_isEquivalence`.)

In `CategoryTheory.Adjunction.coconesIso` we show that
when `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/

@[expose] public section


open Opposite

namespace CategoryTheory

open Functor Limits

universe v u v₁ v₂ v₀ u₁ u₂

namespace Adjunction

section ArbitraryUniverse

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

section PreservationColimits

variable {J : Type u} [Category.{v} J] (K : J ⥤ C)

/-- The right adjoint of `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)`.

Auxiliary definition for `functorialityAdjunction`.
-/
def functorialityRightAdjoint : Cocone (K ⋙ F) ⥤ Cocone K :=
  Cocone.functoriality _ G ⋙
    Cocone.precompose (K.rightUnitor.inv ≫ whiskerLeft K adj.unit ≫ (associator _ _ _).inv)

attribute [local simp] functorialityRightAdjoint

/-- The unit for the adjunction for `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)`.

Auxiliary definition for `functorialityAdjunction`.
-/
@[simps]
def functorialityUnit :
    𝟭 (Cocone K) ⟶ Cocone.functoriality _ F ⋙ functorialityRightAdjoint adj K where
  app c := { hom := adj.unit.app c.pt }

/-- The counit for the adjunction for `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)`.

Auxiliary definition for `functorialityAdjunction`.
-/
@[simps]
def functorialityCounit :
    functorialityRightAdjoint adj K ⋙ Cocone.functoriality _ F ⟶ 𝟭 (Cocone (K ⋙ F)) where
  app c := { hom := adj.counit.app c.pt }

/-- The functor `Cocone.functoriality K F : Cocone K ⥤ Cocone (K ⋙ F)` is a left adjoint. -/
def functorialityAdjunction : Cocone.functoriality K F ⊣ functorialityRightAdjoint adj K where
  unit := functorialityUnit adj K
  counit := functorialityCounit adj K

include adj in
/-- A left adjoint preserves colimits. -/
@[stacks 0038]
lemma leftAdjoint_preservesColimits : PreservesColimitsOfSize.{v, u} F where
  preservesColimitsOfShape :=
    { preservesColimit :=
        { preserves := fun hc =>
            ⟨IsColimit.isoUniqueCoconeMorphism.inv fun _ =>
              @Equiv.unique _ _ (IsColimit.isoUniqueCoconeMorphism.hom hc _)
                ((adj.functorialityAdjunction _).homEquiv _ _)⟩ } }

noncomputable
instance colim_preservesColimits [HasColimitsOfShape J C] :
    PreservesColimits (colim (J := J) (C := C)) :=
  colimConstAdj.leftAdjoint_preservesColimits

-- see Note [lower instance priority]
noncomputable instance (priority := 100) isEquivalence_preservesColimits
    (E : C ⥤ D) [E.IsEquivalence] :
    PreservesColimitsOfSize.{v, u} E :=
  leftAdjoint_preservesColimits E.adjunction

-- see Note [lower instance priority]
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.reflectsColimits_of_isEquivalence
    (E : D ⥤ C) [E.IsEquivalence] :
    ReflectsColimitsOfSize.{v, u} E where
  reflectsColimitsOfShape :=
    { reflectsColimit :=
        { reflects := fun t =>
          ⟨(isColimitOfPreserves E.inv t).mapCoconeEquiv E.asEquivalence.unitIso.symm⟩ } }

-- see Note [lower instance priority]
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.createsColimitsOfIsEquivalence (H : D ⥤ C)
    [H.IsEquivalence] :
    CreatesColimitsOfSize.{v, u} H where
  CreatesColimitsOfShape :=
    { CreatesColimit :=
        { lifts := fun c _ =>
            { liftedCocone := mapCoconeInv H c
              validLift := mapCoconeMapCoconeInv H c } } }


-- verify the preserve_colimits instance works as expected:
noncomputable example (E : C ⥤ D) [E.IsEquivalence] (c : Cocone K) (h : IsColimit c) :
    IsColimit (E.mapCocone c) :=
  isColimitOfPreserves E h

theorem hasColimit_comp_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimit K] :
    HasColimit (K ⋙ E) :=
  HasColimit.mk
    { cocone := E.mapCocone (colimit.cocone K)
      isColimit := isColimitOfPreserves _ (colimit.isColimit K) }

theorem hasColimit_of_comp_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimit (K ⋙ E)] :
    HasColimit K := by
  rw [hasColimit_iff_of_iso
    ((Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft K E.asEquivalence.unitIso)]
  exact hasColimit_comp_equivalence (K ⋙ E) E.inv

/-- Transport a `HasColimitsOfShape` instance across an equivalence. -/
theorem hasColimitsOfShape_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfShape J D] :
    HasColimitsOfShape J C :=
  ⟨fun F => hasColimit_of_comp_equivalence F E⟩

/-- Transport a `HasColimitsOfSize` instance across an equivalence. -/
theorem has_colimits_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfSize.{v, u} D] :
    HasColimitsOfSize.{v, u} C :=
  ⟨fun _ _ => hasColimitsOfShape_of_equivalence E⟩

end PreservationColimits

section PreservationLimits

variable {J : Type u} [Category.{v} J] (K : J ⥤ D)

/-- The left adjoint of `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)`.

Auxiliary definition for `functorialityAdjunction'`.
-/
def functorialityLeftAdjoint : Cone (K ⋙ G) ⥤ Cone K :=
  Cone.functoriality _ F ⋙
    Cone.postcompose ((associator _ _ _).hom ≫ whiskerLeft K adj.counit ≫ K.rightUnitor.hom)

attribute [local simp] functorialityLeftAdjoint

/-- The unit for the adjunction for `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)`.

Auxiliary definition for `functorialityAdjunction'`.
-/
@[simps]
def functorialityUnit' :
    𝟭 (Cone (K ⋙ G)) ⟶ functorialityLeftAdjoint adj K ⋙ Cone.functoriality _ G where
  app c := { hom := adj.unit.app c.pt }

/-- The counit for the adjunction for `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)`.

Auxiliary definition for `functorialityAdjunction'`.
-/
@[simps]
def functorialityCounit' :
    Cone.functoriality _ G ⋙ functorialityLeftAdjoint adj K ⟶ 𝟭 (Cone K) where
  app c := { hom := adj.counit.app c.pt }

/-- The functor `Cone.functoriality K G : Cone K ⥤ Cone (K ⋙ G)` is a right adjoint. -/
def functorialityAdjunction' : functorialityLeftAdjoint adj K ⊣ Cone.functoriality K G where
  unit := functorialityUnit' adj K
  counit := functorialityCounit' adj K

include adj in
/-- A right adjoint preserves limits. -/
@[stacks 0038]
lemma rightAdjoint_preservesLimits : PreservesLimitsOfSize.{v, u} G where
  preservesLimitsOfShape :=
    { preservesLimit :=
        { preserves := fun hc =>
            ⟨IsLimit.isoUniqueConeMorphism.inv fun _ =>
              @Equiv.unique _ _ (IsLimit.isoUniqueConeMorphism.hom hc _)
                ((adj.functorialityAdjunction' _).homEquiv _ _).symm⟩ } }

instance lim_preservesLimits [HasLimitsOfShape J C] :
    PreservesLimits (lim (J := J) (C := C)) :=
  constLimAdj.rightAdjoint_preservesLimits

-- see Note [lower instance priority]
instance (priority := 100) isEquivalencePreservesLimits
    (E : D ⥤ C) [E.IsEquivalence] :
    PreservesLimitsOfSize.{v, u} E :=
  rightAdjoint_preservesLimits E.asEquivalence.symm.toAdjunction

-- see Note [lower instance priority]
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.reflectsLimits_of_isEquivalence
    (E : D ⥤ C) [E.IsEquivalence] :
    ReflectsLimitsOfSize.{v, u} E where
  reflectsLimitsOfShape :=
    { reflectsLimit :=
        { reflects := fun t =>
            ⟨(isLimitOfPreserves E.inv t).mapConeEquiv E.asEquivalence.unitIso.symm⟩ } }

-- see Note [lower instance priority]
noncomputable instance (priority := 100)
    _root_.CategoryTheory.Functor.createsLimitsOfIsEquivalence (H : D ⥤ C) [H.IsEquivalence] :
    CreatesLimitsOfSize.{v, u} H where
  CreatesLimitsOfShape :=
    { CreatesLimit :=
        { lifts := fun c _ =>
            { liftedCone := mapConeInv H c
              validLift := mapConeMapConeInv H c } } }


-- verify the preserve_limits instance works as expected:
noncomputable example (E : D ⥤ C) [E.IsEquivalence] (c : Cone K) (h : IsLimit c) :
    IsLimit (E.mapCone c) :=
  isLimitOfPreserves E h

theorem hasLimit_comp_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimit K] : HasLimit (K ⋙ E) :=
  HasLimit.mk
    { cone := E.mapCone (limit.cone K)
      isLimit := isLimitOfPreserves _ (limit.isLimit K) }

theorem hasLimit_of_comp_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimit (K ⋙ E)] :
    HasLimit K := by
  rw [← hasLimit_iff_of_iso
    (isoWhiskerLeft K E.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _)]
  exact hasLimit_comp_equivalence (K ⋙ E) E.inv

/-- Transport a `HasLimitsOfShape` instance across an equivalence. -/
theorem hasLimitsOfShape_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfShape J C] :
    HasLimitsOfShape J D :=
  ⟨fun F => hasLimit_of_comp_equivalence F E⟩

/-- Transport a `HasLimitsOfSize` instance across an equivalence. -/
theorem has_limits_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfSize.{v, u} C] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun _ _ => hasLimitsOfShape_of_equivalence E⟩

end PreservationLimits

set_option backward.isDefEq.respectTransparency false in
/-- auxiliary construction for `coconesIso` -/
@[simp]
def coconesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
    (t : ((cocones J D).obj (op (K ⋙ F))).obj Y) : (G ⋙ (cocones J C).obj (op K)).obj Y where
  app j := (adj.homEquiv (K.obj j) Y) (t.app j)
  naturality j j' f := by
    rw [← adj.homEquiv_naturality_left, ← Functor.comp_map, t.naturality]
    simp

/-- auxiliary construction for `coconesIso` -/
@[simp]
def coconesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
    (t : (G ⋙ (cocones J C).obj (op K)).obj Y) : ((cocones J D).obj (op (K ⋙ F))).obj Y where
  app j := (adj.homEquiv (K.obj j) Y).symm (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm, t.naturality]
    simp

/-- auxiliary construction for `conesIso` -/
@[simp]
def conesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : (Functor.op F ⋙ (cones J D).obj K).obj X) : ((cones J C).obj (K ⋙ G)).obj X where
  app j := (adj.homEquiv (unop X) (K.obj j)) (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_right, ← t.naturality, Category.id_comp, Category.id_comp]
    rfl

/-- auxiliary construction for `conesIso` -/
@[simp]
def conesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : ((cones J C).obj (K ⋙ G)).obj X) : (Functor.op F ⋙ (cones J D).obj K).obj X where
  app j := (adj.homEquiv (unop X) (K.obj j)).symm (t.app j)
  naturality j j' f := by
    erw [← adj.homEquiv_naturality_right_symm, ← t.naturality, Category.id_comp, Category.id_comp]

end ArbitraryUniverse

variable {C : Type u₁} [Category.{v₀} C] {D : Type u₂} [Category.{v₀} D] {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G)

attribute [local simp] homEquiv_unit homEquiv_counit

-- Note: this is natural in K, but we do not yet have the tools to formulate that.
/-- When `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/
def coconesIso {J : Type u} [Category.{v} J] {K : J ⥤ C} :
    (cocones J D).obj (op (K ⋙ F)) ≅ G ⋙ (cocones J C).obj (op K) :=
  NatIso.ofComponents fun Y =>
    { hom := TypeCat.ofHom (coconesIsoComponentHom adj Y)
      inv := TypeCat.ofHom (coconesIsoComponentInv adj Y) }

-- Note: this is natural in K, but we do not yet have the tools to formulate that.
/-- When `F ⊣ G`,
the functor associating to each `X` the cones over `K` with cone point `F.op.obj X`
is naturally isomorphic to
the functor associating to each `X` the cones over `K ⋙ G` with cone point `X`.
-/
def conesIso {J : Type u} [Category.{v} J] {K : J ⥤ D} :
    F.op ⋙ (cones J D).obj K ≅ (cones J C).obj (K ⋙ G) :=
  NatIso.ofComponents fun X =>
    { hom := TypeCat.ofHom (conesIsoComponentHom adj X)
      inv := TypeCat.ofHom (conesIsoComponentInv adj X) }

end Adjunction

namespace Functor

variable {J C D : Type*} [Category* J] [Category* C] [Category* D]
  (F : C ⥤ D)

noncomputable instance [IsLeftAdjoint F] : PreservesColimitsOfShape J F :=
  (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits.preservesColimitsOfShape

noncomputable instance [IsLeftAdjoint F] : PreservesColimitsOfSize.{v, u} F where

noncomputable instance [IsRightAdjoint F] : PreservesLimitsOfShape J F :=
  (Adjunction.ofIsRightAdjoint F).rightAdjoint_preservesLimits.preservesLimitsOfShape

noncomputable instance [IsRightAdjoint F] : PreservesLimitsOfSize.{v, u} F where

end Functor

end CategoryTheory
