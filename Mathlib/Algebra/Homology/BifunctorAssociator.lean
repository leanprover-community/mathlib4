/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GradedObject.Associator
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Homology.Bifunctor

/-!
# The associator for actions of bifunctors on homological complexes

In this file, we shall adapt (TODO) the results of the file
`CategoryTheory.GradedObject.Associator` to the case of homological complexes.
Given functors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂`, `G : C₁₂ ⥤ C₃ ⥤ C₄`,
`F : C₁ ⥤ C₂₃ ⥤ C₄`, `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃` equipped with an isomorphism
`associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃` (which informally means
that we have natural isomorphisms `G(F₁₂(X₁, X₂), X₃) ≅ F(X₁, G₂₃(X₂, X₃))`),
we shall define an isomorphism `mapBifunctorAssociator` from
`mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄` to
`mapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄` when
we have three homological complexes `K₁ : HomologicalComplex C₁ c₁`,
`K₂ : HomologicalComplex C₂ c₂` and `K₃ : HomologicalComplex C₃ c₃`,
assumptions `TotalComplexShape c₁ c₂ c₁₂`, `TotalComplexShape c₁₂ c₃ c₄`,
`TotalComplexShape c₂ c₃ c₂₃`, `TotalComplexShape c₁ c₂₃ c₄`,
and `ComplexShape.Associative c₁ c₂ c₃ c₁₂ c₂₃ c₄` about the complex
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
  [G.Additive] [∀ (X₁₂ : C₁₂), (G.obj X₁₂).PreservesZeroMorphisms]
  [G₂₃.PreservesZeroMorphisms] [∀ (X₂ : C₂), (G₂₃.obj X₂).PreservesZeroMorphisms]
  [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive]
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
  [ComplexShape.Associative c₁ c₂ c₃ c₁₂ c₂₃ c₄]

variable (F₁₂ G) in
/-- Given bifunctors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂`, `G : C₁₂ ⥤ C₃ ⥤ C₄`, homological complexes
`K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂` and
`K₃ : HomologicalComplex C₃ c₃`, and complexes shapes `c₁₂`, `c₄`, this asserts
that for all `i₁₂ : ι₁₂` and `i₃ : ι₃`, the functor `G(-, K₃.X i₃)` commutes with
the coproducts of the `F₁₂(X₁ i₁, X₂ i₂)` such that `π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂`. -/
abbrev HasGoodTrifunctor₁₂Obj :=
  GradedObject.HasGoodTrifunctor₁₂Obj F₁₂ G
    (ComplexShape.ρ₁₂ c₁ c₂ c₃ c₁₂ c₄) K₁.X K₂.X K₃.X

variable (F G₂₃) in
/-- Given bifunctors `F : C₁ ⥤ C₂₃ ⥤ C₄`, `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃`, homological complexes
`K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂` and
`K₃ : HomologicalComplex C₃ c₃`, and complexes shapes `c₁₂`, `c₂₃`, `c₄`
with `ComplexShape.Associative c₁ c₂ c₃ c₁₂ c₂₃ c₄`, this asserts that for
all `i₁ : ι₁` and `i₂₃ : ι₂₃`, the functor `F(K₁.X i₁, _)` commutes with
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

/-- The associator isomorphism for the action of bifunctors
on homological complexes, in each degree. -/
noncomputable def mapBifunctorAssociatorX
    [H₁₂ : HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄]
    [H₂₃ : HasGoodTrifunctor₂₃Obj F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄](j : ι₄) :
    (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j ≅
      (mapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄).X j :=
  (GradedObject.eval j).mapIso
    (GradedObject.mapBifunctorAssociator (associator := associator)
      (H₁₂ := H₁₂) (H₂₃ := H₂₃))

namespace mapBifunctor₁₂

section

variable (F₁₂ G)

/-- The inclusion of a summand in `mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄`. -/
noncomputable def ι (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j) :
    (G.obj ((F₁₂.obj (K₁.X i₁)).obj (K₂.X i₂))).obj (K₃.X i₃) ⟶
      (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j :=
  GradedObject.ιMapBifunctor₁₂BifunctorMapObj _ _ (ComplexShape.ρ₁₂ c₁ c₂ c₃ c₁₂ c₄) _ _ _ _ _ _ _ h

lemma ι_eq (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (i₁₂ : ι₁₂) (j : ι₄)
    (h₁₂ : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂)
    (h : ComplexShape.π c₁₂ c₃ c₄ (i₁₂, i₃) = j) :
    ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j (by rw [← h, ← h₁₂]; rfl) =
      (G.map (ιMapBifunctor K₁ K₂ F₁₂ c₁₂ i₁ i₂ i₁₂ h₁₂)).app (K₃.X i₃) ≫
        ιMapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄ i₁₂ i₃ j h := by
  subst h₁₂
  rfl

/-- The inclusion of a summand in `mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄`,
or zero. -/
noncomputable def ιOrZero (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄) :
    (G.obj ((F₁₂.obj (K₁.X i₁)).obj (K₂.X i₂))).obj (K₃.X i₃) ⟶
      (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j :=
  if h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j then
    ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h
  else 0

lemma ιOrZero_eq (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j) :
    ιOrZero F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j =
      ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h := dif_pos h

lemma ιOrZero_eq_zero (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) ≠ j) :
    ιOrZero F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j = 0 := dif_neg h

variable {F₁₂ G K₁ K₂ K₃ c₁₂ c₄} in
@[ext]
lemma hom_ext
    [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄] {j : ι₄} {A : C₄}
    {f g : (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j ⟶ A}
    (hfg : ∀ (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃)
      (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j),
      ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h ≫ f =
        ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h ≫ g) :
    f = g :=
  GradedObject.mapBifunctor₁₂BifunctorMapObj_ext hfg

end

section

variable {K₁ K₂ K₃ c₁₂ c₄}
variable [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄] {j : ι₄} {A : C₄}
  (f : ∀ (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (_ : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j),
        (G.obj ((F₁₂.obj (K₁.X i₁)).obj (K₂.X i₂))).obj (K₃.X i₃) ⟶ A)

/-- Constructor for morphisms from
`(mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j`. -/
noncomputable def mapBifunctor₁₂Desc :
    (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j ⟶ A :=
  GradedObject.mapBifunctor₁₂BifunctorDesc (ρ₁₂ := ComplexShape.ρ₁₂ c₁ c₂ c₃ c₁₂ c₄) f

@[reassoc (attr := simp)]
lemma ι_mapBifunctor₁₂Desc (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j) :
    ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h ≫ mapBifunctor₁₂Desc f =
      f i₁ i₂ i₃ h := by
  apply GradedObject.ι_mapBifunctor₁₂BifunctorDesc

end

variable (F₁₂ G)

/-- The first differential on a summand
of `mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄`. -/
noncomputable def d₁ (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄) :
    (G.obj ((F₁₂.obj (K₁.X i₁)).obj (K₂.X i₂))).obj (K₃.X i₃) ⟶
      (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j :=
  (ComplexShape.ε₁ c₁₂ c₃ c₄ (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃) *
    ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂)) •
  (G.map ((F₁₂.map (K₁.d i₁ (c₁.next i₁))).app (K₂.X i₂))).app (K₃.X i₃) ≫
    ιOrZero F₁₂ G K₁ K₂ K₃ c₁₂ c₄ _ i₂ i₃ j

lemma d₁_eq_zero (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄) (h : ¬ c₁.Rel i₁ (c₁.next i₁)) :
    d₁ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j = 0 := by
  dsimp [d₁]
  rw [shape _ _ _ h, Functor.map_zero, zero_app, Functor.map_zero, zero_app, zero_comp, smul_zero]

lemma d₁_eq {i₁ i₁' : ι₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : ι₂) (i₃ : ι₃) (j : ι₄) :
    d₁ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j =
    (ComplexShape.ε₁ c₁₂ c₃ c₄ (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃) *
      ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂) ) •
    (G.map ((F₁₂.map (K₁.d i₁ i₁')).app (K₂.X i₂))).app (K₃.X i₃) ≫
      ιOrZero F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁' i₂ i₃ j := by
  obtain rfl := c₁.next_eq' h₁
  rfl

/-- The second differential on a summand
of `mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄`. -/
noncomputable def d₂ (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄) :
    (G.obj ((F₁₂.obj (K₁.X i₁)).obj (K₂.X i₂))).obj (K₃.X i₃) ⟶
      (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j :=
  (c₁₂.ε₁ c₃ c₄ (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃) * c₁.ε₂ c₂ c₁₂ (i₁, i₂)) •
  (G.map ((F₁₂.obj (K₁.X i₁)).map (K₂.d i₂ (c₂.next i₂)))).app (K₃.X i₃) ≫
    ιOrZero F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ _ i₃ j

lemma d₂_eq_zero (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄) (h : ¬ c₂.Rel i₂ (c₂.next i₂)) :
    d₂ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j = 0 := by
  dsimp [d₂]
  rw [shape _ _ _ h, Functor.map_zero, Functor.map_zero, zero_app, zero_comp, smul_zero]

lemma d₂_eq (i₁ : ι₁) {i₂ i₂' : ι₂} (h₂ : c₂.Rel i₂ i₂') (i₃ : ι₃) (j : ι₄) :
    d₂ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j =
  (c₁₂.ε₁ c₃ c₄ (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃) * c₁.ε₂ c₂ c₁₂ (i₁, i₂)) •
    (G.map ((F₁₂.obj (K₁.X i₁)).map (K₂.d i₂ i₂'))).app (K₃.X i₃) ≫
      ιOrZero F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ _ i₃ j := by
  obtain rfl := c₂.next_eq' h₂
  rfl

/-- The third differential on a summand
of `mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄`. -/
noncomputable def d₃ (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄) :
    (G.obj ((F₁₂.obj (K₁.X i₁)).obj (K₂.X i₂))).obj (K₃.X i₃) ⟶
      (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j :=
  (ComplexShape.ε₂ c₁₂ c₃ c₄ (c₁.π c₂ c₁₂ (i₁, i₂), i₃)) •
    (G.obj ((F₁₂.obj (K₁.X i₁)).obj (K₂.X i₂))).map (K₃.d i₃ (c₃.next i₃)) ≫
      ιOrZero F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ _ j

lemma d₃_eq_zero (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄) (h : ¬ c₃.Rel i₃ (c₃.next i₃)) :
    d₃ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j = 0 := by
  dsimp [d₃]
  rw [shape _ _ _ h, Functor.map_zero, zero_comp, smul_zero]

lemma d₃_eq (i₁ : ι₁) (i₂ : ι₂) {i₃ i₃' : ι₃} (h₃ : c₃.Rel i₃ i₃') (j : ι₄) :
    d₃ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j =
  (ComplexShape.ε₂ c₁₂ c₃ c₄ (c₁.π c₂ c₁₂ (i₁, i₂), i₃)) •
    (G.obj ((F₁₂.obj (K₁.X i₁)).obj (K₂.X i₂))).map (K₃.d i₃ i₃') ≫
      ιOrZero F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ _ j := by
  obtain rfl := c₃.next_eq' h₃
  rfl


section

variable [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄]
variable (j j' : ι₄)

/-- The first differential on `mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄`. -/
noncomputable def D₁ :
    (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j ⟶
      (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j' :=
  mapBifunctor₁₂Desc (fun i₁ i₂ i₃ _ ↦ d₁ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j')

/-- The second differential on `mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄`. -/
noncomputable def D₂ :
    (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j ⟶
      (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j' :=
  mapBifunctor₁₂Desc (fun i₁ i₂ i₃ _ ↦ d₂ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j')

/-- The third differential on `mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄`. -/
noncomputable def D₃ :
    (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j ⟶
      (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j' :=
  mapBifunctor.D₂ _ _ _ _ _ _

end

section

variable (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j j' : ι₄)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j)

@[reassoc (attr := simp)]
lemma ι_D₁ [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄] :
    ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h ≫ D₁ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' =
      d₁ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j' := by
  simp [D₁]

@[reassoc (attr := simp)]
lemma ι_D₂ [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄] :
    ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h ≫ D₂ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' =
      d₂ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j' := by
  simp [D₂]

@[reassoc (attr := simp)]
lemma ι_D₃  :
    ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h ≫ D₃ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' =
      d₃ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j' := by
  simp only [ι_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl h, D₃, assoc, mapBifunctor.ι_D₂]
  by_cases h₁ : c₃.Rel i₃ (c₃.next i₃)
  · rw [d₃_eq _ _ _ _ _ _ _ _ _ h₁]
    by_cases h₂ : ComplexShape.π c₁₂ c₃ c₄ (c₁.π c₂ c₁₂ (i₁, i₂), c₃.next i₃) = j'
    · rw [mapBifunctor.d₂_eq _ _ _ _ _ h₁ _ h₂,
        ιOrZero_eq _ _ _ _ _ _ _ _ _ _ _ h₂,
        Linear.comp_units_smul, smul_left_cancel_iff,
        ι_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl h₂,
        NatTrans.naturality_assoc]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂, comp_zero,
        ιOrZero_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₂, comp_zero, smul_zero]
  · rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₁, comp_zero,
      d₃_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₁]

end

lemma d_eq (j j' : ι₄) [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄] :
    (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).d j j' =
      D₁ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' + D₂ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' +
        D₃ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' := by
  rw [mapBifunctor.d_eq]
  congr 1
  ext i₁ i₂ i₃ h
  simp only [Preadditive.comp_add, ι_D₁, ι_D₂]
  rw [ι_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl h, assoc, mapBifunctor.ι_D₁]
  set i₁₂ := ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  by_cases h₁ : c₁₂.Rel i₁₂ (c₁₂.next i₁₂)
  · by_cases h₂ : ComplexShape.π c₁₂ c₃ c₄ (c₁₂.next i₁₂, i₃) = j'
    · rw [mapBifunctor.d₁_eq _ _ _ _ h₁ _ _ h₂]
      simp only [mapBifunctor.d_eq, Functor.map_add, NatTrans.app_add, Preadditive.add_comp,
        smul_add, Preadditive.comp_add, Linear.comp_units_smul]
      congr 1
      · rw [← NatTrans.comp_app_assoc, ← Functor.map_comp,
          mapBifunctor.ι_D₁]
        by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
        · have h₄ := (ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂).symm
          rw [mapBifunctor.d₁_eq _ _ _ _ h₃ _ _ h₄,
            d₁_eq _ _ _ _ _ _ _ h₃,
            ιOrZero_eq _ _ _ _ _ _ _ _ _ _ _ (by rw [← h₂, ← h₄]; rfl),
            ι_eq _ _ _ _ _ _ _ _ _ _ (c₁₂.next i₁₂) _ h₄ h₂,
            Functor.map_units_smul, Functor.map_comp, NatTrans.app_units_zsmul,
            NatTrans.comp_app, Linear.units_smul_comp, assoc, smul_smul]
        · rw [d₁_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₃,
            mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₃,
            Functor.map_zero, zero_app, zero_comp, smul_zero]
      · rw [← NatTrans.comp_app_assoc, ← Functor.map_comp,
          mapBifunctor.ι_D₂]
        by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
        · have h₄ := (ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃).symm
          rw [mapBifunctor.d₂_eq _ _ _ _ _ h₃ _ h₄,
            d₂_eq _ _ _ _ _ _ _ _ h₃,
            ιOrZero_eq _ _ _ _ _ _ _ _ _ _ _ (by rw [← h₂, ← h₄]; rfl),
            ι_eq _ _ _ _ _ _ _ _ _ _ (c₁₂.next i₁₂) _ h₄ h₂,
            Functor.map_units_smul, Functor.map_comp, NatTrans.app_units_zsmul,
            NatTrans.comp_app, Linear.units_smul_comp, assoc, smul_smul]
        · rw [d₂_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₃,
            mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₃,
            Functor.map_zero, zero_app, zero_comp, smul_zero]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂, comp_zero]
      trans 0 + 0
      · simp
      · congr 1
        · by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
          · rw [d₁_eq _ _ _ _ _ _ _ h₃, ιOrZero_eq_zero, comp_zero, smul_zero]
            dsimp [ComplexShape.r]
            intro h₄
            apply h₂
            rw [← h₄, ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂]
          · rw [d₁_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₃]
        · by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
          · rw [d₂_eq _ _ _ _ _ _ _ _ h₃, ιOrZero_eq_zero, comp_zero, smul_zero]
            dsimp [ComplexShape.r]
            intro h₄
            apply h₂
            rw [← h₄, ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃]
          · rw [d₂_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₃]
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁, comp_zero,
      d₁_eq_zero, d₂_eq_zero, zero_add]
    · intro h₂
      apply h₁
      have := ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₂
      rw [c₁₂.next_eq' this]
      exact this
    · intro h₂
      apply h₁
      have := ComplexShape.rel_π₁ c₂ c₁₂ h₂ i₂
      rw [c₁₂.next_eq' this]
      exact this

end mapBifunctor₁₂

end HomologicalComplex
