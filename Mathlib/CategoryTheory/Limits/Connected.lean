/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.connected
! leanprover-community/mathlib commit d6814c584384ddf2825ff038e868451a7c956f31
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathbin.CategoryTheory.IsConnected
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Connected limits

A connected limit is a limit whose shape is a connected category.

We give examples of connected categories, and prove that the functor given
by `(X × -)` preserves any connected limit. That is, any limit of shape `J`
where `J` is a connected category is preserved by the functor `(X × -)`.
-/


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

section Examples

instance widePullbackShape_connected (J : Type v₁) : IsConnected (WidePullbackShape J) :=
  by
  apply is_connected.of_induct
  introv hp t
  cases j
  · exact hp
  · rwa [t (wide_pullback_shape.hom.term j)]
#align category_theory.wide_pullback_shape_connected CategoryTheory.widePullbackShape_connected

instance widePushoutShape_connected (J : Type v₁) : IsConnected (WidePushoutShape J) :=
  by
  apply is_connected.of_induct
  introv hp t
  cases j
  · exact hp
  · rwa [← t (wide_pushout_shape.hom.init j)]
#align category_theory.wide_pushout_shape_connected CategoryTheory.widePushoutShape_connected

instance parallelPairInhabited : Inhabited WalkingParallelPair :=
  ⟨WalkingParallelPair.one⟩
#align category_theory.parallel_pair_inhabited CategoryTheory.parallelPairInhabited

instance parallel_pair_connected : IsConnected WalkingParallelPair :=
  by
  apply is_connected.of_induct
  introv _ t
  cases j
  · rwa [t walking_parallel_pair_hom.left]
  · assumption
#align category_theory.parallel_pair_connected CategoryTheory.parallel_pair_connected

end Examples

attribute [local tidy] tactic.case_bash

variable {C : Type u₂} [Category.{v₂} C]

variable [HasBinaryProducts C]

variable {J : Type v₂} [SmallCategory J]

namespace ProdPreservesConnectedLimits

/-- (Impl). The obvious natural transformation from (X × K -) to K. -/
@[simps]
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ K where app Y := Limits.prod.snd
#align category_theory.prod_preserves_connected_limits.γ₂ CategoryTheory.ProdPreservesConnectedLimits.γ₂

/-- (Impl). The obvious natural transformation from (X × K -) to X -/
@[simps]
def γ₁ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ (Functor.const J).obj X
    where app Y := Limits.prod.fst
#align category_theory.prod_preserves_connected_limits.γ₁ CategoryTheory.ProdPreservesConnectedLimits.γ₁

/-- (Impl).
Given a cone for (X × K -), produce a cone for K using the natural transformation `γ₂` -/
@[simps]
def forgetCone {X : C} {K : J ⥤ C} (s : Cone (K ⋙ prod.functor.obj X)) : Cone K
    where
  pt := s.pt
  π := s.π ≫ γ₂ X
#align category_theory.prod_preserves_connected_limits.forget_cone CategoryTheory.ProdPreservesConnectedLimits.forgetCone

end ProdPreservesConnectedLimits

open ProdPreservesConnectedLimits

/-- The functor `(X × -)` preserves any connected limit.
Note that this functor does not preserve the two most obvious disconnected limits - that is,
`(X × -)` does not preserve products or terminal object, eg `(X ⨯ A) ⨯ (X ⨯ B)` is not isomorphic to
`X ⨯ (A ⨯ B)` and `X ⨯ 1` is not isomorphic to `1`.
-/
noncomputable def prodPreservesConnectedLimits [IsConnected J] (X : C) :
    PreservesLimitsOfShape J (prod.functor.obj X)
    where PreservesLimit K :=
    {
      preserves := fun c l =>
        { lift := fun s =>
            prod.lift (s.π.app (Classical.arbitrary _) ≫ Limits.prod.fst) (l.lift (forgetCone s))
          fac := fun s j => by
            apply prod.hom_ext
            · erw [assoc, lim_map_π, comp_id, limit.lift_π]
              exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (Classical.arbitrary _)).symm
            · simp [← l.fac (forget_cone s) j]
          uniq := fun s m L => by
            apply prod.hom_ext
            · erw [limit.lift_π, ← L (Classical.arbitrary J), assoc, lim_map_π, comp_id]
              rfl
            · rw [limit.lift_π]
              apply l.uniq (forget_cone s)
              intro j
              simp [← L j] } }
#align category_theory.prod_preserves_connected_limits CategoryTheory.prodPreservesConnectedLimits

end CategoryTheory

