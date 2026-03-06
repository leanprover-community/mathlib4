/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.MonCat.Shrink
public import Mathlib.Algebra.Category.Grp.Shrink
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

/-!
# The Yoneda embedding for monoid objects for locally small categories

Let `C` be a locally `w`-small category. We define the Yoneda
embedding `shrinkYonedaMon : Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w} w` and its `Grp` analogue.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

instance (F : C ⥤ MonCat.{w'}) [∀ X, Small.{w} (F.obj X)] :
    FunctorToTypes.Small.{w} (F ⋙ forget _) :=
  fun X ↦ inferInstanceAs <| Small.{w} (F.obj X)

instance (F : C ⥤ GrpCat.{w'}) [∀ X, Small.{w} (F.obj X)] :
    FunctorToTypes.Small.{w} (F ⋙ forget _) :=
  fun X ↦ inferInstanceAs <| Small.{w} (F.obj X)

/-- A functor `F : C ⥤ MonCat.{w'}` factors through `MonCat.{w}` if all the
monoids are `w`-small. -/
@[simps, pp_with_univ]
noncomputable def MonCat.shrinkFunctor (F : C ⥤ MonCat.{w'}) [∀ X, Small.{w} (F.obj X)] :
    C ⥤ MonCat.{w} where
  obj X := MonCat.of (Shrink.{w} (F.obj X))
  map {X Y} f := MonCat.ofHom <|
    (Shrink.mulEquiv.symm.toMonoidHom.comp (F.map f).hom).comp Shrink.mulEquiv.toMonoidHom

/-- The natural transformation `MonCat.shrinkFunctor.{w} F ⟶ MonCat.shrinkFunctor.{w} G`
induces by a natural transformation `τ : F ⟶ G` between `w`-small functors to monoids. -/
@[simps]
noncomputable def MonCat.shrinkFunctorMap {F G : C ⥤ MonCat.{w'}} (τ : F ⟶ G)
    [∀ X, Small.{w} (F.obj X)] [∀ X, Small.{w} (G.obj X)] :
    MonCat.shrinkFunctor.{w} F ⟶ MonCat.shrinkFunctor.{w} G where
  app X := MonCat.ofHom <|
    (Shrink.mulEquiv.symm.toMonoidHom.comp (τ.app X).hom).comp Shrink.mulEquiv.toMonoidHom
  naturality X Y f := by
    ext x
    exact
      congr($((FunctorToTypes.shrinkMap.{w} (Functor.whiskerRight τ (forget _))).naturality f) x)

/-- A functor `F : C ⥤ GrpCat.{w'}` factors through `GrGrpt.{w}` if all the
groups are `w`-small. -/
@[simps, pp_with_univ]
noncomputable def GrpCat.shrinkFunctor (F : C ⥤ GrpCat.{w'}) [∀ X, Small.{w} (F.obj X)] :
    C ⥤ GrpCat.{w} where
  obj X := GrpCat.of (Shrink.{w} (F.obj X))
  map {X Y} f := GrpCat.ofHom <|
    (Shrink.mulEquiv.symm.toMonoidHom.comp (F.map f).hom).comp Shrink.mulEquiv.toMonoidHom

/-- The natural transformation `GrpCat.shrinkFunctor.{w} F ⟶ GrpCat.shrinkFunctor.{w} G`
induces by a natural transformation `τ : F ⟶ G` between `w`-small functors to groups. -/
@[simps]
noncomputable def GrpCat.shrinkFunctorMap {F G : C ⥤ GrpCat.{w'}} (τ : F ⟶ G)
    [∀ X, Small.{w} (F.obj X)] [∀ X, Small.{w} (G.obj X)] :
    GrpCat.shrinkFunctor.{w} F ⟶ GrpCat.shrinkFunctor.{w} G where
  app X := GrpCat.ofHom <|
    (Shrink.mulEquiv.symm.toMonoidHom.comp (τ.app X).hom).comp Shrink.mulEquiv.toMonoidHom
  naturality X Y f := by
    ext x
    exact
      congr($((FunctorToTypes.shrinkMap.{w} (Functor.whiskerRight τ (forget _))).naturality f) x)

variable [LocallySmall.{w} C] [CartesianMonoidalCategory C]

instance (M : Mon C) (X : Cᵒᵖ) : Small.{w} ((yonedaMon.obj M).obj X) := by
  dsimp
  infer_instance

instance (M : Grp C) (X : Cᵒᵖ) : Small.{w} ((yonedaGrp.obj M).obj X) := by
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda embedding `Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w}` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
noncomputable def shrinkYonedaMon :
    Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w} where
  obj X := MonCat.shrinkFunctor (yonedaMon.obj X)
  map f := MonCat.shrinkFunctorMap (yonedaMon.map f)

open MonObj

/-- The type `(shrinkYonedaMon.obj M).obj Y` is equivalent to `Y.unop ⟶ M.X`. -/
noncomputable def shrinkYonedaMonObjObjEquiv {M : Mon C} {Y : Cᵒᵖ} :
    (shrinkYonedaMon.{w}.obj M).obj Y ≃* (Y.unop ⟶ M.X) :=
  Shrink.mulEquiv

set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm
    {M : Mon C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) :
    (shrinkYonedaMon.{w}.obj _).map g (shrinkYonedaMonObjObjEquiv.symm f) =
      shrinkYonedaMonObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

lemma shrinkYonedaMonObjObjEquiv_symm_comp {M : Mon C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X) :
    shrinkYonedaMonObjObjEquiv.symm (g ≫ f) =
    (shrinkYonedaMon.obj _).map g.op (shrinkYonedaMonObjObjEquiv.symm f) :=
  (shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm g.op f).symm

set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaMon_map_app_shrinkYonedaObjObjEquiv_symm
    {M M' : Mon C} {Y : Cᵒᵖ} (f : Y.unop ⟶ M.X) (g : M ⟶ M') :
    (shrinkYonedaMon.map g).app _ (shrinkYonedaMonObjObjEquiv.symm f) =
      shrinkYonedaMonObjObjEquiv.symm (f ≫ g.hom) := by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda embedding `Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{w}` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
noncomputable def shrinkYonedaGrp :
    Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{w} where
  obj X := GrpCat.shrinkFunctor (yonedaGrp.obj X)
  map f := GrpCat.shrinkFunctorMap (yonedaGrp.map f)

/-- The type `(shrinkYonedaGrp.obj M).obj Y` is equivalent to `Y.unop ⟶ M.X`. -/
noncomputable def shrinkYonedaGrpObjObjEquiv {M : Grp C} {Y : Cᵒᵖ} :
    (shrinkYonedaGrp.{w}.obj M).obj Y ≃* (Y.unop ⟶ M.X) :=
  Shrink.mulEquiv

set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm
    {M : Grp C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) :
    (shrinkYonedaGrp.{w}.obj _).map g (shrinkYonedaGrpObjObjEquiv.symm f) =
      shrinkYonedaGrpObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]

lemma shrinkYonedaGrpObjObjEquiv_symm_comp {M : Grp C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X) :
    shrinkYonedaGrpObjObjEquiv.symm (g ≫ f) =
    (shrinkYonedaGrp.obj _).map g.op (shrinkYonedaGrpObjObjEquiv.symm f) :=
  (shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm g.op f).symm

set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaGrp_map_app_shrinkYonedaObjObjEquiv_symm
    {M M' : Grp C} {Y : Cᵒᵖ} (f : Y.unop ⟶ M.X) (g : M ⟶ M') :
    (shrinkYonedaGrp.map g).app _ (shrinkYonedaGrpObjObjEquiv.symm f) =
      shrinkYonedaGrpObjObjEquiv.symm (f ≫ g.hom.hom) := by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]

end CategoryTheory
