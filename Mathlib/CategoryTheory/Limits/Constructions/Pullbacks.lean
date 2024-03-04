/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks

#align_import category_theory.limits.constructions.pullbacks from "leanprover-community/mathlib"@"cd7a8a184d7c5635e30083eabc4baf5589c30b7a"

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
        PullbackCone.mk (e ≫ π₁) (e ≫ π₂) <| by rw [Category.assoc, equalizer.condition]; simp
      isLimit :=
        PullbackCone.IsLimit.mk _ (fun s => equalizer.lift
          (prod.lift (s.π.app WalkingCospan.left) (s.π.app WalkingCospan.right)) <| by
              rw [← Category.assoc, limit.lift_π, ← Category.assoc, limit.lift_π];
                exact PullbackCone.condition _)
          (by simp [π₁, e]) (by simp [π₂, e]) fun s m h₁ h₂ => by
          ext
          · dsimp; simpa using h₁
          · simpa using h₂ }
#align category_theory.limits.has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair CategoryTheory.Limits.hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair

section

attribute [local instance] hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair

/-- If a category has all binary products and all equalizers, then it also has all pullbacks.
    As usual, this is not an instance, since there may be a more direct way to construct
    pullbacks. -/
theorem hasPullbacks_of_hasBinaryProducts_of_hasEqualizers (C : Type u) [Category.{v} C]
    [HasBinaryProducts C] [HasEqualizers C] : HasPullbacks C :=
  { has_limit := fun F => hasLimitOfIso (diagramIsoCospan F).symm }
#align category_theory.limits.has_pullbacks_of_has_binary_products_of_has_equalizers CategoryTheory.Limits.hasPullbacks_of_hasBinaryProducts_of_hasEqualizers

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
#align category_theory.limits.has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair CategoryTheory.Limits.hasColimit_span_of_hasColimit_pair_of_hasColimit_parallelPair

section

attribute [local instance] hasColimit_span_of_hasColimit_pair_of_hasColimit_parallelPair

/-- If a category has all binary coproducts and all coequalizers, then it also has all pushouts.
    As usual, this is not an instance, since there may be a more direct way to construct
    pushouts. -/
theorem hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers (C : Type u) [Category.{v} C]
    [HasBinaryCoproducts C] [HasCoequalizers C] : HasPushouts C :=
  hasPushouts_of_hasColimit_span C
#align category_theory.limits.has_pushouts_of_has_binary_coproducts_of_has_coequalizers CategoryTheory.Limits.hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers

end

end CategoryTheory.Limits
