/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Action.Basic

/-!
# Categorical properties of `Action V G`

We show:

* When `V` has (co)limits so does `Action V G`.
* When `V` is preadditive, linear, or abelian so is `Action V G`.
-/

universe u v w₁ w₂ t₁ t₂

open CategoryTheory Limits

variable {V : Type*} [Category V] {G : Type*} [Monoid G]

namespace Action

section Limits

instance [HasFiniteProducts V] : HasFiniteProducts (Action V G) where
  out _ :=
    Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

instance [HasFiniteLimits V] : HasFiniteLimits (Action V G) where
  out _ _ _ :=
    Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

instance [HasLimits V] : HasLimits (Action V G) :=
  Adjunction.has_limits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

/-- If `V` has limits of shape `J`, so does `Action V G`. -/
instance hasLimitsOfShape {J : Type*} [Category J] [HasLimitsOfShape J V] :
    HasLimitsOfShape J (Action V G) :=
  Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

instance [HasFiniteCoproducts V] : HasFiniteCoproducts (Action V G) where
  out _ :=
    Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

instance [HasFiniteColimits V] : HasFiniteColimits (Action V G) where
  out _ _ _ :=
    Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

instance [HasColimits V] : HasColimits (Action V G) :=
  Adjunction.has_colimits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

/-- If `V` has colimits of shape `J`, so does `Action V G`. -/
instance hasColimitsOfShape {J : Type*} [Category J]
    [HasColimitsOfShape J V] : HasColimitsOfShape J (Action V G) :=
  Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

end Limits

section Preservation

variable {C : Type*} [Category C]

/-- `F : C ⥤ SingleObj G ⥤ V` preserves the limit of some `K : J ⥤ C` if it does
evaluated at `SingleObj.star G`. -/
private lemma SingleObj.preservesLimit (F : C ⥤ SingleObj G ⥤ V)
    {J : Type*} [Category J] (K : J ⥤ C)
    (h : PreservesLimit K (F ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G))) :
    PreservesLimit K F := by
  apply preservesLimit_of_evaluation
  intro _
  exact h

/-- `F : C ⥤ Action V G` preserves the limit of some `K : J ⥤ C` if
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
lemma preservesLimit_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category J] (K : J ⥤ C)
    (h : PreservesLimit K (F ⋙ Action.forget V G)) : PreservesLimit K F := by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesLimit K F' := SingleObj.preservesLimit _ _ h
  apply preservesLimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

/-- `F : C ⥤ Action V G` preserves limits of some shape `J`
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
lemma preservesLimitsOfShape_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category J] (h : PreservesLimitsOfShape J (F ⋙ Action.forget V G)) :
    PreservesLimitsOfShape J F := by
  constructor
  intro K
  apply Action.preservesLimit_of_preserves
  exact PreservesLimitsOfShape.preservesLimit

/-- `F : C ⥤ Action V G` preserves limits of some size
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
lemma preservesLimitsOfSize_of_preserves (F : C ⥤ Action V G)
    (h : PreservesLimitsOfSize.{w₂, w₁} (F ⋙ Action.forget V G)) :
    PreservesLimitsOfSize.{w₂, w₁} F := by
  constructor
  intro J _
  apply Action.preservesLimitsOfShape_of_preserves
  exact PreservesLimitsOfSize.preservesLimitsOfShape

/-- `F : C ⥤ SingleObj G ⥤ V` preserves the colimit of some `K : J ⥤ C` if it does
evaluated at `SingleObj.star G`. -/
private lemma SingleObj.preservesColimit (F : C ⥤ SingleObj G ⥤ V)
    {J : Type*} [Category J] (K : J ⥤ C)
    (h : PreservesColimit K (F ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G))) :
    PreservesColimit K F := by
  apply preservesColimit_of_evaluation
  intro _
  exact h

/-- `F : C ⥤ Action V G` preserves the colimit of some `K : J ⥤ C` if
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
lemma preservesColimit_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category J] (K : J ⥤ C)
    (h : PreservesColimit K (F ⋙ Action.forget V G)) : PreservesColimit K F := by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesColimit K F' := SingleObj.preservesColimit _ _ h
  apply preservesColimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

/-- `F : C ⥤ Action V G` preserves colimits of some shape `J`
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
lemma preservesColimitsOfShape_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category J] (h : PreservesColimitsOfShape J (F ⋙ Action.forget V G)) :
    PreservesColimitsOfShape J F := by
  constructor
  intro K
  apply Action.preservesColimit_of_preserves
  exact PreservesColimitsOfShape.preservesColimit

/-- `F : C ⥤ Action V G` preserves colimits of some size
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
lemma preservesColimitsOfSize_of_preserves (F : C ⥤ Action V G)
    (h : PreservesColimitsOfSize.{w₂, w₁} (F ⋙ Action.forget V G)) :
    PreservesColimitsOfSize.{w₂, w₁} F := by
  constructor
  intro J _
  apply Action.preservesColimitsOfShape_of_preserves
  exact PreservesColimitsOfSize.preservesColimitsOfShape

end Preservation

section Forget

noncomputable instance {J : Type*} [Category J] [HasLimitsOfShape J V] :
    PreservesLimitsOfShape J (Action.forget V G) := by
  show PreservesLimitsOfShape J ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  infer_instance

noncomputable instance {J : Type*} [Category J] [HasColimitsOfShape J V] :
    PreservesColimitsOfShape J (Action.forget V G) := by
  show PreservesColimitsOfShape J ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  infer_instance

noncomputable instance [HasFiniteLimits V] : PreservesFiniteLimits (Action.forget V G) := by
  show PreservesFiniteLimits ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteLimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro _ _ _
    infer_instance
  apply comp_preservesFiniteLimits

noncomputable instance [HasFiniteColimits V] : PreservesFiniteColimits (Action.forget V G) := by
  show PreservesFiniteColimits ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteColimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro _ _ _
    infer_instance
  apply comp_preservesFiniteColimits

instance {J : Type*} [Category J] (F : J ⥤ Action V G) :
    ReflectsLimit F (Action.forget V G) where
  reflects h := ⟨by
    apply isLimitOfReflects ((Action.functorCategoryEquivalence V G).functor)
    exact evaluationJointlyReflectsLimits _ (fun _ => h)⟩

instance {J : Type*} [Category J] :
    ReflectsLimitsOfShape J (Action.forget V G) where

instance : ReflectsLimits (Action.forget V G) where

instance {J : Type*} [Category J] (F : J ⥤ Action V G) :
    ReflectsColimit F (Action.forget V G) where
  reflects h := ⟨by
    apply isColimitOfReflects ((Action.functorCategoryEquivalence V G).functor)
    exact evaluationJointlyReflectsColimits _ (fun _ => h)⟩

noncomputable instance {J : Type*} [Category J] :
    ReflectsColimitsOfShape J (Action.forget V G) where

noncomputable instance : ReflectsColimits (Action.forget V G) where

end Forget

section HasZeroMorphisms

variable [HasZeroMorphisms V]

instance {X Y : Action V G} : Zero (X ⟶ Y) := ⟨0, by simp⟩

@[simp]
theorem zero_hom {X Y : Action V G} : (0 : X ⟶ Y).hom = 0 :=
  rfl

instance : HasZeroMorphisms (Action V G) where

instance forget_preservesZeroMorphisms : Functor.PreservesZeroMorphisms (forget V G) where

instance forget₂_preservesZeroMorphisms [HasForget V] :
    Functor.PreservesZeroMorphisms (forget₂ (Action V G) V) where

instance functorCategoryEquivalence_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (functorCategoryEquivalence V G).functor where

end HasZeroMorphisms

section Preadditive

variable [Preadditive V]

instance {X Y : Action V G} : Add (X ⟶ Y) where
  add f g := ⟨f.hom + g.hom, by simp [f.comm, g.comm]⟩

instance {X Y : Action V G} : Neg (X ⟶ Y) where
  neg f := ⟨-f.hom, by simp [f.comm]⟩

instance : Preadditive (Action V G) where
  homGroup X Y :=
    { nsmul := nsmulRec
      zsmul := zsmulRec
      zero_add := by intros; ext; exact zero_add _
      add_zero := by intros; ext; exact add_zero _
      add_assoc := by intros; ext; exact add_assoc _ _ _
      neg_add_cancel := by intros; ext; exact neg_add_cancel _
      add_comm := by intros; ext; exact add_comm _ _ }
  add_comp := by intros; ext; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := by intros; ext; exact Preadditive.comp_add _ _ _ _ _ _

instance forget_additive : Functor.Additive (forget V G) where

instance forget₂_additive [HasForget V] : Functor.Additive (forget₂ (Action V G) V) where

instance functorCategoryEquivalence_additive :
    Functor.Additive (functorCategoryEquivalence V G).functor where

@[simp]
theorem neg_hom {X Y : Action V G} (f : X ⟶ Y) : (-f).hom = -f.hom :=
  rfl

@[simp]
theorem add_hom {X Y : Action V G} (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom :=
  rfl

@[simp]
theorem sum_hom {X Y : Action V G} {ι : Type*} (f : ι → (X ⟶ Y)) (s : Finset ι) :
    (s.sum f).hom = s.sum fun i => (f i).hom :=
  (forget V G).map_sum f s

end Preadditive

section Linear

variable [Preadditive V] {R : Type*} [Semiring R] [Linear R V]

instance : Linear R (Action V G) where
  homModule X Y :=
    { smul := fun r f => ⟨r • f.hom, by simp [f.comm]⟩
      one_smul := by intros; ext; exact one_smul _ _
      smul_zero := by intros; ext; exact smul_zero _
      zero_smul := by intros; ext; exact zero_smul _ _
      add_smul := by intros; ext; exact add_smul _ _ _
      smul_add := by intros; ext; exact smul_add _ _ _
      mul_smul := by intros; ext; exact mul_smul _ _ _ }
  smul_comp := by intros; ext; exact Linear.smul_comp _ _ _ _ _ _
  comp_smul := by intros; ext; exact Linear.comp_smul _ _ _ _ _ _

instance forget_linear : Functor.Linear R (forget V G) where

instance forget₂_linear [HasForget V] : Functor.Linear R (forget₂ (Action V G) V) where

instance functorCategoryEquivalence_linear :
    Functor.Linear R (functorCategoryEquivalence V G).functor where

@[simp]
theorem smul_hom {X Y : Action V G} (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom :=
  rfl

variable {H : Type*} [Monoid H] (f : G →* H)

instance res_additive : (res V f).Additive where

instance res_linear : (res V f).Linear R where

end Linear

section Abelian

/-- Auxiliary construction for the `Abelian (Action V G)` instance. -/
def abelianAux : Action V G ≌ (SingleObj G) ⥤ V :=
  functorCategoryEquivalence V G

noncomputable instance [Abelian V] : Abelian (Action V G) :=
  abelianOfEquivalence abelianAux.functor

end Abelian

end Action

namespace CategoryTheory.Functor

variable {W : Type*} [Category W] (F : V ⥤ W) (G : Type*) [Monoid G] [Preadditive V]
  [Preadditive W]

instance mapAction_preadditive [F.Additive] : (F.mapAction G).Additive where

variable {R : Type*} [Semiring R] [CategoryTheory.Linear R V] [CategoryTheory.Linear R W]

instance mapAction_linear [F.Linear R] : (F.mapAction G).Linear R where

end CategoryTheory.Functor
