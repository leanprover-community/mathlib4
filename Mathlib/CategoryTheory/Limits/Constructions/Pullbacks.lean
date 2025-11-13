/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Constructing pullbacks from binary products and equalizers

If a category as binary products and equalizers, then it has pullbacks.
Also, if a category has binary coproducts and coequalizers, then it has pushouts
-/


universe v u

open CategoryTheory

namespace CategoryTheory.Limits

/-- If the product `X ⨯ Y` and the equalizer of `π₁ ≫ f` and `π₂ ≫ g` exist, then the
pullback of `f` and `g` exists: It is given by composing the equalizer with the projections. -/
theorem hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair {C : Type u} [𝒞 : Category.{v} C]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (pair X Y)]
    [HasLimit (parallelPair (prod.fst ≫ f) (prod.snd ≫ g))] : HasLimit (cospan f g) :=
  let π₁ : X ⨯ Y ⟶ X := prod.fst
  let π₂ : X ⨯ Y ⟶ Y := prod.snd
  let e := equalizer.ι (π₁ ≫ f) (π₂ ≫ g)
  HasLimit.mk
    { cone :=
        PullbackCone.mk (e ≫ π₁) (e ≫ π₂) <| by
          rw [Category.assoc, equalizer.condition]
          simp [e]
      isLimit :=
        PullbackCone.IsLimit.mk _ (fun s => equalizer.lift
          (prod.lift (s.π.app WalkingCospan.left) (s.π.app WalkingCospan.right)) <| by
            rw [← Category.assoc, limit.lift_π, ← Category.assoc, limit.lift_π]
            exact PullbackCone.condition _)
          (by simp [π₁, e]) (by simp [π₂, e]) fun s m h₁ h₂ => by
          ext
          · dsimp; simpa using h₁
          · simpa using h₂ }

section

attribute [local instance] hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair

/-- If a category has all binary products and all equalizers, then it also has all pullbacks.
As usual, this is not an instance, since there may be a more direct way to construct
pullbacks. -/
theorem hasPullbacks_of_hasBinaryProducts_of_hasEqualizers (C : Type u) [Category.{v} C]
    [HasBinaryProducts C] [HasEqualizers C] : HasPullbacks C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoCospan F).symm }

end

/-- If the coproduct `Y ⨿ Z` and the coequalizer of `f ≫ ι₁` and `g ≫ ι₂` exist, then the
pushout of `f` and `g` exists: It is given by composing the inclusions with the coequalizer. -/
theorem hasColimit_span_of_hasColimit_pair_of_hasColimit_parallelPair {C : Type u}
    [𝒞 : Category.{v} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasColimit (pair Y Z)]
    [HasColimit (parallelPair (f ≫ coprod.inl) (g ≫ coprod.inr))] : HasColimit (span f g) :=
  let ι₁ : Y ⟶ Y ⨿ Z := coprod.inl
  let ι₂ : Z ⟶ Y ⨿ Z := coprod.inr
  let c := coequalizer.π (f ≫ ι₁) (g ≫ ι₂)
  HasColimit.mk
    { cocone :=
        PushoutCocone.mk (ι₁ ≫ c) (ι₂ ≫ c) <| by
          rw [← Category.assoc, ← Category.assoc, coequalizer.condition]
      isColimit :=
        PushoutCocone.IsColimit.mk _
          (fun s => coequalizer.desc
              (coprod.desc (s.ι.app WalkingSpan.left) (s.ι.app WalkingSpan.right)) <| by
            rw [Category.assoc, colimit.ι_desc, Category.assoc, colimit.ι_desc]
            exact PushoutCocone.condition _)
          (by simp [ι₁, c]) (by simp [ι₂, c]) fun s m h₁ h₂ => by
          ext
          · simpa using h₁
          · simpa using h₂ }

section

attribute [local instance] hasColimit_span_of_hasColimit_pair_of_hasColimit_parallelPair

/-- If a category has all binary coproducts and all coequalizers, then it also has all pushouts.
As usual, this is not an instance, since there may be a more direct way to construct pushouts. -/
theorem hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers (C : Type u) [Category.{v} C]
    [HasBinaryCoproducts C] [HasCoequalizers C] : HasPushouts C :=
  hasPushouts_of_hasColimit_span C

end

end CategoryTheory.Limits
