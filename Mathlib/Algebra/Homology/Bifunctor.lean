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

assert_not_exists TwoSidedIdeal

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

variable {K₁ K₂ F c}
variable {A : D} {j : J}
  (f : ∀ (i₁ : I₁) (i₂ : I₂) (_ : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j),
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ A)

/-- Constructor for morphisms from `(mapBifunctor K₁ K₂ F c).X j`. -/
noncomputable def mapBifunctorDesc : (mapBifunctor K₁ K₂ F c).X j ⟶ A :=
  HomologicalComplex₂.totalDesc _ f

@[reassoc (attr := simp)]
lemma ι_mapBifunctorDesc (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ mapBifunctorDesc f = f i₁ i₂ h := by
  apply HomologicalComplex₂.ι_totalDesc

end

namespace mapBifunctor

variable {K₁ K₂ F c} in
@[ext]
lemma hom_ext {Y : D} {j : J} {f g : (mapBifunctor K₁ K₂ F c).X j ⟶ Y}
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j),
      ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ f = ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ g) :
    f = g :=
  HomologicalComplex₂.total.hom_ext _ h

section

variable (j j' : J)

/-- The first differential on `mapBifunctor K₁ K₂ F c` -/
noncomputable def D₁ :
    (mapBifunctor K₁ K₂ F c).X j ⟶ (mapBifunctor K₁ K₂ F c).X j' :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).D₁ c j j'

/-- The second differential on `mapBifunctor K₁ K₂ F c` -/
noncomputable def D₂ :
    (mapBifunctor K₁ K₂ F c).X j ⟶ (mapBifunctor K₁ K₂ F c).X j' :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).D₂ c j j'

lemma d_eq :
    (mapBifunctor K₁ K₂ F c).d j j' = D₁ K₁ K₂ F c j j' + D₂ K₁ K₂ F c j j' := rfl

end

section

variable (i₁ : I₁) (i₂ : I₂) (j : J)

/-- The first differential on a summand of `mapBifunctor K₁ K₂ F c` -/
noncomputable def d₁ :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₁ c i₁ i₂ j

/-- The second differential on a summand of `mapBifunctor K₁ K₂ F c` -/
noncomputable def d₂ :
    (F.obj (K₁.X i₁)).obj (K₂.X i₂) ⟶ (mapBifunctor K₁ K₂ F c).X j :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₂ c i₁ i₂ j

lemma d₁_eq_zero (h : ¬ c₁.Rel i₁ (c₁.next i₁)):
    d₁ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h

lemma d₂_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)):
    d₂ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h

lemma d₁_eq_zero' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁', i₂⟩ ≠ j) :
    d₁ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₁_eq_zero' _ _ h _ _ h'

lemma d₂_eq_zero' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁, i₂'⟩ ≠ j) :
    d₂ K₁ K₂ F c i₁ i₂ j = 0 :=
  HomologicalComplex₂.d₂_eq_zero' _ _ _ h _ h'

lemma d₁_eq' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J) :
    d₁ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₁ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.map (K₁.d i₁ i₁')).app (K₂.X i₂) ≫ ιMapBifunctorOrZero K₁ K₂ F c i₁' i₂ j) :=
  HomologicalComplex₂.d₁_eq' _ _ h _ _

lemma d₂_eq' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J) :
    d₂ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₂ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.obj (K₁.X i₁)).map (K₂.d i₂ i₂') ≫ ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂' j) :=
  HomologicalComplex₂.d₂_eq' _ _ _ h _

lemma d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁', i₂⟩ = j) :
    d₁ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₁ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.map (K₁.d i₁ i₁')).app (K₂.X i₂) ≫ ιMapBifunctor K₁ K₂ F c i₁' i₂ j h') :=
  HomologicalComplex₂.d₁_eq _ _ h _ _ h'

lemma d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (j : J)
    (h' : ComplexShape.π c₁ c₂ c ⟨i₁, i₂'⟩ = j) :
    d₂ K₁ K₂ F c i₁ i₂ j = ComplexShape.ε₂ c₁ c₂ c ⟨i₁, i₂⟩ •
      ((F.obj (K₁.X i₁)).map (K₂.d i₂ i₂') ≫ ιMapBifunctor K₁ K₂ F c i₁ i₂' j h') :=
  HomologicalComplex₂.d₂_eq _ _ _ h _ h'

end

section

variable (j j' : J) (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j)

@[reassoc (attr := simp)]
lemma ι_D₁ :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ D₁ K₁ K₂ F c j j' = d₁ K₁ K₂ F c i₁ i₂ j' := by
  apply HomologicalComplex₂.ι_D₁

@[reassoc (attr := simp)]
lemma ι_D₂ :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ D₂ K₁ K₂ F c j j' = d₂ K₁ K₂ F c i₁ i₂ j' := by
  apply HomologicalComplex₂.ι_D₂

end

end mapBifunctor

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

@[simp]
lemma mapBifunctorMap_map_add₁ {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    [Preadditive C₁] [HasZeroMorphisms C₂]
    {I₁ I₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
    {K₁ L₁ : HomologicalComplex C₁ c₁} (f g : K₁ ⟶ L₁) {K₂ L₂ : HomologicalComplex C₂ c₂}
    (h : K₂ ⟶ L₂) (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
    [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
    {J : Type*} [DecidableEq J] (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]
    [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] :
    mapBifunctorMap (f + g) h F c = mapBifunctorMap f h F c + mapBifunctorMap g h F c := by
  aesop_cat

@[simp]
lemma mapBifunctorMap_map_add₂ {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    [HasZeroMorphisms C₁] [Preadditive C₂]
    {I₁ I₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
    {K₁ L₁ : HomologicalComplex C₁ c₁} (f : K₁ ⟶ L₁) {K₂ L₂ : HomologicalComplex C₂ c₂}
    (g h : K₂ ⟶ L₂) (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X₁, (F.obj X₁).Additive]
    {J : Type*} [DecidableEq J] (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]
    [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] :
    mapBifunctorMap f (g + h) F c = mapBifunctorMap f g F c + mapBifunctorMap f h F c := by
  aesop_cat

end HomologicalComplex

namespace CategoryTheory.Functor

open HomologicalComplex

section

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂), HasMapBifunctor K₁ K₂ F c]

@[simps]
noncomputable def bifunctorMapHomologicalComplex :
    HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤ HomologicalComplex D c where
  obj K₁ :=
    { obj K₂ := mapBifunctor K₁ K₂ F c
      map f₂ := mapBifunctorMap (𝟙 K₁) f₂ F c
      map_id _ := by ext; dsimp; simp
      map_comp _ _ := by ext; dsimp; simp }
  map f₁ :=
    { app K₂ := mapBifunctorMap f₁ (𝟙 K₂) F c
      naturality _ _ _ := by ext; dsimp; simp }
  map_id _ := by ext; dsimp; simp
  map_comp _ _ := by ext; dsimp; simp

end

section

variable [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂), HasMapBifunctor K₁ K₂ F c]

instance : (bifunctorMapHomologicalComplex F c₁ c₂ c).Additive where

instance (K₂ : HomologicalComplex C₂ c₂) :
    ((bifunctorMapHomologicalComplex F c₁ c₂ c).flip.obj K₂).Additive where

end

section

variable [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).Additive]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂), HasMapBifunctor K₁ K₂ F c]

instance : (bifunctorMapHomologicalComplex F c₁ c₂ c).flip.Additive where

instance (K₁ : HomologicalComplex C₁ c₁) :
    ((bifunctorMapHomologicalComplex F c₁ c₂ c).obj K₁).Additive where

end

end CategoryTheory.Functor
