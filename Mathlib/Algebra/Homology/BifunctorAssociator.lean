/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GradedObject.Associator
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.Bifunctor

/-!
# The associator for actions of bifunctors on homological complexes

In this file, we adapt the results of the file
`CategoryTheory.GradedObject.Associator` to the case of homological complexes.
Given functors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂`, `G : C₁₂ ⥤ C₃ ⥤ C₄`,
`F : C₁ ⥤ C₂₃ ⥤ C₄`, `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃` equipped with an isomorphism
`associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃` (which informally means
that we have natural isomorphisms `G(F₁₂(X₁, X₂), X₃) ≅ F(X₁, G₂₃(X₂, X₃))`),
we define an isomorphism `mapBifunctorAssociator` from
`mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄` to
`mapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄` when
we have three homological complexes `K₁ : HomologicalComplex C₁ c₁`,
`K₂ : HomologicalComplex C₂ c₂` and `K₃ : HomologicalComplex C₃ c₃`,
assumptions `TotalComplexShape c₁ c₂ c₁₂`, `TotalComplexShape c₁₂ c₃ c₄`,
`TotalComplexShape c₂ c₃ c₂₃`, `TotalComplexShape c₁ c₂₃ c₄`,
and `ComplexShape.Associator c₁ c₂ c₃ c₁₂ c₂₃ c₄` about the complex
shapes, and technical assumptions
`[HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄]` and
`[HasGoodTrifunctor₂₃Obj F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄]` about the
commutation of certain functors to certain coproducts.

The main application of these results shall be the construction of
the associator for the monoidal category structure on homological complexes (TODO).

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C₁ C₂ C₁₂ C₂₃ C₃ C₄ : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category C₁₂] [Category C₂₃]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C₃]
  [Preadditive C₁₂] [Preadditive C₂₃] [Preadditive C₄]
  {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C₄}
  {F : C₁ ⥤ C₂₃ ⥤ C₄} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
  [F₁₂.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F₁₂.obj X₁).PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] [∀ (X₁₂ : C₁₂), (G.obj X₁₂).PreservesZeroMorphisms]
  [G₂₃.PreservesZeroMorphisms] [∀ (X₂ : C₂), (G₂₃.obj X₂).PreservesZeroMorphisms]
  [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]
  (associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  {ι₁ ι₂ ι₃ ι₁₂ ι₂₃ ι₄ : Type*}
  [DecidableEq ι₁₂] [DecidableEq ι₂₃] [DecidableEq ι₄]
  {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂} {c₃ : ComplexShape ι₃}
  (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  (K₃ : HomologicalComplex C₃ c₃)
  (c₁₂ : ComplexShape ι₁₂) (c₂₃ : ComplexShape ι₂₃) (c₄ : ComplexShape ι₄)
  [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c₄]
  [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c₄]
  [HasMapBifunctor K₁ K₂ F₁₂ c₁₂] [HasMapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄]
  [HasMapBifunctor K₂ K₃ G₂₃ c₂₃] [HasMapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄]
  [ComplexShape.Associator c₁ c₂ c₃ c₁₂ c₂₃ c₄]

variable (F₁₂ G) in
/-- Given bifunctors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂`, `G : C₁₂ ⥤ C₃ ⥤ C₄`, homological complexes
`K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂` and
`K₃ : HomologicalComplex C₃ c₃`, and complexes shapes `c₁₂`, `c₄`, this asserts
that for all `i₁₂ : ι₁₂` and `i₃ : ι₃`, the functor `G(-, K₃.X i₃)` commutes wich
the coproducts of the `F₁₂(X₁ i₁, X₂ i₂)` such that `π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂`. -/
abbrev HasGoodTrifunctor₁₂Obj :=
  GradedObject.HasGoodTrifunctor₁₂Obj F₁₂ G
    (ComplexShape.ρ₁₂ c₁ c₂ c₃ c₁₂ c₄) K₁.X K₂.X K₃.X

variable (F G₂₃) in
/-- Given bifunctors `F : C₁ ⥤ C₂₃ ⥤ C₄`, `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃`, homological complexes
`K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂` and
`K₃ : HomologicalComplex C₃ c₃`, and complexes shapes `c₁₂`, `c₂₃`, `c₄`
with `ComplexShape.Associator c₁ c₂ c₃ c₁₂ c₂₃ c₄`, this asserts that for
all `i₁ : ι₁` and `i₂₃ : ι₂₃`, the functor `F(K₁.X i₁, _)` commutes wich
the coproducts of the `G₂₃(K₂.X i₂, K₃.X i₃)`
such that `π c₂ c₃ c₂₃ ⟨i₂, i₃⟩ = i₂₃`. -/
abbrev HasGoodTrifunctor₂₃Obj :=
  GradedObject.HasGoodTrifunctor₂₃Obj F G₂₃
    (ComplexShape.ρ₂₃ c₁ c₂ c₃ c₁₂ c₂₃ c₄) K₁.X K₂.X K₃.X

instance :
    (((GradedObject.mapBifunctor F₁₂ ι₁ ι₂).obj K₁.X).obj K₂.X).HasMap
      (ComplexShape.π c₁ c₂ c₁₂) :=
  inferInstanceAs (HasMapBifunctor K₁ K₂ F₁₂ c₁₂)

instance :
    (((GradedObject.mapBifunctor G ι₁₂ ι₃).obj (GradedObject.mapBifunctorMapObj F₁₂
        (ComplexShape.π c₁ c₂ c₁₂) K₁.X K₂.X)).obj K₃.X).HasMap
          (ComplexShape.π c₁₂ c₃ c₄) :=
  inferInstanceAs (HasMapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄)

instance :
    (((GradedObject.mapBifunctor F ι₁ ι₂₃).obj K₁.X).obj
      (GradedObject.mapBifunctorMapObj G₂₃
        (ComplexShape.π c₂ c₃ c₂₃) K₂.X K₃.X)).HasMap (ComplexShape.π c₁ c₂₃ c₄) :=
  inferInstanceAs (HasMapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄)

variable [H₁₂ : HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄]
  [H₂₃ : HasGoodTrifunctor₂₃Obj F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄]

/-- The associator isomorphism for the action of bifunctors
on homological complexes. -/
noncomputable def mapBifunctorAssociator :
    mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄ ≅
      mapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄ :=
  isoOfGradedObjectIso
    (GradedObject.mapBifunctorAssociator (associator := associator)
      (H₁₂ := H₁₂) (H₂₃ := H₂₃)) (by
        sorry)

end HomologicalComplex
