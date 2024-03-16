/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.GradedObject.Bifunctor

/-!
# The action of a bifunctor on homological complexes

Given a bifunctor `F : C₁ ⥤ C₂ ⥤ D` and complexes shapes `c₁ : ComplexShape I₁` and
`c₂ : ComplexShape I₂`, we define a bifunctor `mapBifunctorHomologicalComplex F c₁ c₂`
of type `HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤ HomologicalComplex₂ D c₁ c₂`.

Then, when `K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂` and
`c : ComplexShape J` are such that we have `TotalComplexShape c₁ c₂ c`, we introduce
a typeclass `HasMapBifunctor K₁ K₂ F c` which allows to define
`mapBifunctor K₁ K₂ F c : HomologicalComplex D c` as the total complex of the
bicomplex `(((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂)`.

-/


open CategoryTheory Limits

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

namespace CategoryTheory

namespace Functor

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms D]
  (F : C₁ ⥤ C₂ ⥤ D) {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]

variable {c₁} in
/-- Auxiliary definition for `mapBifunctorHomologicalComplex`. -/
@[simps!]
def mapBifunctorHomologicalComplexObj (K₁ : HomologicalComplex C₁ c₁) :
    HomologicalComplex C₂ c₂ ⥤ HomologicalComplex₂ D c₁ c₂ where
  obj K₂ := HomologicalComplex₂.ofGradedObject c₁ c₂
      (((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).obj K₂.X)
      (fun i₁ i₁' i₂ => (F.map (K₁.d i₁ i₁')).app (K₂.X i₂))
      (fun i₁ i₂ i₂' => (F.obj (K₁.X i₁)).map (K₂.d i₂ i₂'))
      (fun i₁ i₁' h₁ i₂ => by
        dsimp
        rw [K₁.shape _ _ h₁, Functor.map_zero, zero_app])
      (fun i₁ i₂ i₂' h₂ => by
        dsimp
        rw [K₂.shape _ _ h₂, Functor.map_zero])
      (fun i₁ i₁' i₁'' i₂ => by
        dsimp
        rw [← NatTrans.comp_app, ← Functor.map_comp, HomologicalComplex.d_comp_d,
          Functor.map_zero, zero_app])
      (fun i₁ i₂ i₂' i₂'' => by
        dsimp
        rw [← Functor.map_comp, HomologicalComplex.d_comp_d, Functor.map_zero])
      (fun i₁ i₁' i₂ i₂' => by
        dsimp
        rw [NatTrans.naturality])
  map {K₂ K₂' φ} := HomologicalComplex₂.homMk
      (((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).map φ.f)
        (by dsimp; intros; rw [NatTrans.naturality]) (by
          dsimp
          intros
          simp only [← Functor.map_comp, φ.comm])
  map_id K₂ := by dsimp; ext; dsimp; rw [Functor.map_id]
  map_comp f g := by dsimp; ext; dsimp; rw [Functor.map_comp]

/-- Given a functor `F : C₁ ⥤ C₂ ⥤ D`, this is the bifunctor which sends
`K₁ : HomologicalComplex C₁ c₁` and `K₂ : HomologicalComplex C₂ c₂` to the bicomplex
which is degree `(i₁, i₂)` consists of `(F.obj (K₁.X i₁)).obj (K₂.X i₂)`. -/
@[simps! obj_obj_X_X obj_obj_X_d obj_obj_d_f obj_map_f_f map_app_f_f]
def mapBifunctorHomologicalComplex :
    HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤ HomologicalComplex₂ D c₁ c₂ where
  obj := mapBifunctorHomologicalComplexObj F c₂
  map {K₁ K₁'} f :=
    { app := fun K₂ => HomologicalComplex₂.homMk
        (((GradedObject.mapBifunctor F I₁ I₂).map f.f).app K₂.X) (by
          intros
          dsimp
          simp only [← NatTrans.comp_app, ← F.map_comp, f.comm]) (by simp) }

variable {c₁ c₂}

@[simp]
lemma mapBifunctorHomologicalComplex_obj_obj_toGradedObject
    (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂) :
    (((mapBifunctorHomologicalComplex F c₁ c₂).obj K₁).obj K₂).toGradedObject =
      ((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).obj K₂.X := rfl

end Functor

end CategoryTheory

namespace HomologicalComplex

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

/-- The condition that `((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂` has
a total complex. -/
abbrev HasMapBifunctor := (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).HasTotal c

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

/-- Given `K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂`,
a bifunctor `F : C₁ ⥤ C₂ ⥤ D` and a complex shape `ComplexShape J` such that we have
`[TotalComplexShape c₁ c₂ c]`, this `mapBifunctor K₁ K₂ F c : HomologicalComplex D c`
is the total complex of the bicomplex obtained by applying `F` to `K₁` and `K₂`. -/
noncomputable abbrev mapBifunctor : HomologicalComplex D c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).total c

/-- The inclusion of a summand of `(mapBifunctor K₁ K₂ F c).X j`. -/
noncomputable abbrev ιMapBifunctor
    (i₁ : I₁) (i₂ : I₂) (j : J) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).ιTotal c i₁ i₂ j h

/-- The inclusion of a summand of `(mapBifunctor K₁ K₂ F c).X j`, or zero. -/
noncomputable abbrev ιMapBifunctorOrZero (i₁ : I₁) (i₂ : I₂) (j : J) :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).ιTotalOrZero c i₁ i₂ j

lemma ιMapBifunctorOrZero_eq (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂ j = ιMapBifunctor K₁ K₂ F c i₁ i₂ j h := dif_pos h

lemma ιMapBifunctorOrZero_eq_zero (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) ≠ j) :
    ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂ j = 0 := dif_neg h

section

variable {K₁ K₂ L₁ L₂}

/-- The morphism `mapBifunctor K₁ K₂ F c ⟶ mapBifunctor L₁ L₂ F c` induced by
morphisms of complexes `K₁ ⟶ L₁` and `K₂ ⟶ L₂`. -/
noncomputable def mapBifunctorMap : mapBifunctor K₁ K₂ F c ⟶ mapBifunctor L₁ L₂ F c :=
  HomologicalComplex₂.total.map (((F.mapBifunctorHomologicalComplex c₁ c₂).map f₁).app K₂ ≫
    ((F.mapBifunctorHomologicalComplex c₁ c₂).obj L₁).map f₂) c

@[reassoc (attr := simp)]
lemma ι_mapBifunctorMap (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ (mapBifunctorMap f₁ f₂ F c).f j =
      (F.map (f₁.f i₁)).app (K₂.X i₂) ≫ (F.obj (L₁.X i₁)).map (f₂.f i₂) ≫
        ιMapBifunctor L₁ L₂ F c i₁ i₂ j h := by
  simp [mapBifunctorMap]

end

end HomologicalComplex
