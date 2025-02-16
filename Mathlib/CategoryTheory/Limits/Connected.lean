/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Connected limits

A connected limit is a limit whose shape is a connected category.

We show that constant functors from a connected category have a limit
and a colimit, give examples of connected categories, and prove
that the functor given by `(X × -)` preserves any connected limit.
That is, any limit of shape `J` where `J` is a connected category is
preserved by the functor `(X × -)`.
-/


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

section Const

namespace Limits

variable (J : Type u₁) [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C] (X : C)

/-- The obvious cone of a constant functor. -/
@[simps]
def constCone : Cone ((Functor.const J).obj X) where
  pt := X
  π := 𝟙 _

/-- The obvious cocone of a constant functor. -/
@[simps]
def constCocone : Cocone ((Functor.const J).obj X) where
  pt := X
  ι := 𝟙 _

variable [IsConnected J]

/-- When `J` is a connected category, the limit of a
constant functor `J ⥤ C` with value `X : C` identifies to `X`. -/
def isLimitConstCone : IsLimit (constCone J X) where
  lift s := s.π.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [comp_id]
    exact constant_of_preserves_morphisms _
      (fun _ _ f ↦ by simpa using s.w f) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)

/-- When `J` is a connected category, the colimit of a
constant functor `J ⥤ C` with value `X : C` identifies to `X`. -/
def isColimitConstCocone : IsColimit (constCocone J X) where
  desc s := s.ι.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [id_comp]
    exact constant_of_preserves_morphisms _
      (fun _ _ f ↦ by simpa using (s.w f).symm) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)

end Limits

end Const

section Examples

instance widePullbackShape_connected (J : Type v₁) : IsConnected (WidePullbackShape J) := by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [t (WidePullbackShape.Hom.term _)]

instance widePushoutShape_connected (J : Type v₁) : IsConnected (WidePushoutShape J) := by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [← t (WidePushoutShape.Hom.init _)]

instance parallelPairInhabited : Inhabited WalkingParallelPair :=
  ⟨WalkingParallelPair.one⟩

instance parallel_pair_connected : IsConnected WalkingParallelPair := by
  apply IsConnected.of_induct
  · introv _ t
    cases j
    · rwa [t WalkingParallelPairHom.left]
    · assumption

end Examples

variable {C : Type u₂} [Category.{v₂} C]
variable [HasBinaryProducts C]
variable {J : Type v₂} [SmallCategory J]

namespace ProdPreservesConnectedLimits

/-- (Impl). The obvious natural transformation from (X × K -) to K. -/
@[simps]
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ K where app _ := Limits.prod.snd

/-- (Impl). The obvious natural transformation from (X × K -) to X -/
@[simps]
def γ₁ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ (Functor.const J).obj X where
  app _ := Limits.prod.fst

/-- (Impl).
Given a cone for (X × K -), produce a cone for K using the natural transformation `γ₂` -/
@[simps]
def forgetCone {X : C} {K : J ⥤ C} (s : Cone (K ⋙ prod.functor.obj X)) : Cone K where
  pt := s.pt
  π := s.π ≫ γ₂ X

end ProdPreservesConnectedLimits

open ProdPreservesConnectedLimits

/-- The functor `(X × -)` preserves any connected limit.
Note that this functor does not preserve the two most obvious disconnected limits - that is,
`(X × -)` does not preserve products or terminal object, eg `(X ⨯ A) ⨯ (X ⨯ B)` is not isomorphic to
`X ⨯ (A ⨯ B)` and `X ⨯ 1` is not isomorphic to `1`.
-/
lemma prod_preservesConnectedLimits [IsConnected J] (X : C) :
    PreservesLimitsOfShape J (prod.functor.obj X) where
  preservesLimit {K} :=
    { preserves := fun {c} l => ⟨{
          lift := fun s =>
            prod.lift (s.π.app (Classical.arbitrary _) ≫ Limits.prod.fst) (l.lift (forgetCone s))
          fac := fun s j => by
            apply Limits.prod.hom_ext
            · erw [assoc, limMap_π, comp_id, limit.lift_π]
              exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (Classical.arbitrary _)).symm
            · simp [← l.fac (forgetCone s) j]
          uniq := fun s m L => by
            apply Limits.prod.hom_ext
            · erw [limit.lift_π, ← L (Classical.arbitrary J), assoc, limMap_π, comp_id]
              rfl
            · rw [limit.lift_π]
              apply l.uniq (forgetCone s)
              intro j
              simp [← L j] }⟩ }

end CategoryTheory
