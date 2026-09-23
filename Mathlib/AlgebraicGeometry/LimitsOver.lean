/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# (Co)limits in over categories

We show that if `P` is a morphism property in `Scheme` that is local at the source, then
colimits in `P.Over ⊤ X` for `X : Scheme` of locally directed diagrams of open immersions
exist and agree with the colimit in `Scheme`.
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u})

variable (P : MorphismProperty Scheme.{u})

section Over

variable {S : Scheme.{u}} {J : Type*} [Category* J] (F : J ⥤ Over S)
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f).left]
  [(F ⋙ Over.forget S ⋙ Scheme.forget).IsLocallyDirected]
  [Quiver.IsThin J] [Small.{u} J]

noncomputable instance : HasColimit F :=
  have {i j} (f : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget S).map f) :=
    inferInstanceAs <| IsOpenImmersion (F.map f).left
  have : ((F ⋙ Over.forget S) ⋙ Scheme.forget).IsLocallyDirected := ‹_›
  hasColimit_of_created _ (Over.forget S)

end Over

section OverProp

instance {S : Scheme.{u}} {U X Y : P.Over ⊤ S} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] (i : WalkingPair) :
    Mono ((span f g ⋙ MorphismProperty.Over.forget P ⊤ S ⋙ Over.forget S ⋙ Scheme.forget).map
      (WidePushoutShape.Hom.init i)) := by
  rw [mono_iff_injective]
  cases i
  · simpa using f.left.isOpenEmbedding.injective
  · simpa using g.left.isOpenEmbedding.injective

instance {S : Scheme.{u}} {U X Y : P.Over ⊤ S} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left]
    {i j : WalkingSpan} (t : i ⟶ j) :
      IsOpenImmersion ((span f g).map t).left := by
  obtain (a | (a | a)) := t
  · simp only [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id]
    infer_instance
  · simpa
  · simpa

variable [IsZariskiLocalAtSource P] {S : Scheme.{u}} {J : Type*} [Category* J] (F : J ⥤ P.Over ⊤ S)
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f).left]
  [(F ⋙ MorphismProperty.Over.forget P ⊤ S ⋙ Over.forget S ⋙ Scheme.forget).IsLocallyDirected]
  [Quiver.IsThin J] [Small.{u} J]

local instance :
    (((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S) ⋙
      Scheme.forget).IsLocallyDirected :=
  ‹_›

local instance {i j} (f : i ⟶ j) :
    IsOpenImmersion <|
      ((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S).map f :=
  inferInstanceAs <| IsOpenImmersion (F.map f).left

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : CreatesColimit F (MorphismProperty.Over.forget P ⊤ S) := by
  have : HasColimit (F ⋙ MorphismProperty.Over.forget P ⊤ S) :=
    hasColimit_of_created _ (Over.forget S)
  refine createsColimitOfFullyFaithfulOfIso
      { toComma := colimit (F ⋙ MorphismProperty.Over.forget P ⊤ S)
        prop := ?_ } (Iso.refl _)
  let e : (colimit (F ⋙ MorphismProperty.Over.forget P ⊤ S)).left ≅
      colimit ((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S) :=
    preservesColimitIso (Over.forget S) _
  let 𝒰 : (colimit (F ⋙ MorphismProperty.Over.forget P ⊤ S)).left.OpenCover :=
    (Scheme.IsLocallyDirected.openCover _).pushforwardIso e.inv
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) 𝒰]
  intro i
  simpa [𝒰, e] using (F.obj i).prop

instance : HasColimit F := hasColimit_of_created _ (MorphismProperty.Over.forget P ⊤ S)

instance : PreservesColimit F (MorphismProperty.Over.forget P ⊤ S) :=
  -- this is only `inferInstance` with the local instances above
  inferInstance

set_option backward.isDefEq.respectTransparency false in
instance (j : J) : IsOpenImmersion (colimit.ι F j).left := by
  rw [← MorphismProperty.Over.forget_comp_forget_map]
  let e : (colimit F).left ≅ colimit (F ⋙ _) :=
    preservesColimitIso (MorphismProperty.Over.forget P ⊤ S ⋙ Over.forget S) F
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion) _ e.hom]
  simp only [e, CategoryTheory.ι_preservesColimitIso_hom]
  exact inferInstanceAs <| IsOpenImmersion
    (colimit.ι ((F ⋙ MorphismProperty.Over.forget P ⊤ S) ⋙ Over.forget S) j)

instance {ι : Type*} [Small.{u} ι] : HasCoproductsOfShape ι (P.Over ⊤ S) where

instance : HasFiniteCoproducts (P.Over ⊤ S) where
  out := inferInstance

noncomputable instance (J : Type*) [Small.{u} J] :
    CreatesColimitsOfShape (Discrete J) (MorphismProperty.Over.forget P ⊤ S) where

end OverProp

end AlgebraicGeometry
