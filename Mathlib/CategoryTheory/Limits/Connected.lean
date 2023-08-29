/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.limits.connected from "leanprover-community/mathlib"@"d6814c584384ddf2825ff038e868451a7c956f31"

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

instance widePullbackShape_connected (J : Type v₁) : IsConnected (WidePullbackShape J) := by
  apply IsConnected.of_induct
  -- ⊢ ∀ (p : Set (WidePullbackShape J)), ?j₀ ∈ p → (∀ {j₁ j₂ : WidePullbackShape J …
  introv hp t
  -- ⊢ j ∈ p
  cases j
  · exact hp
    -- 🎉 no goals
  · rwa [t (WidePullbackShape.Hom.term _)]
    -- 🎉 no goals
#align category_theory.wide_pullback_shape_connected CategoryTheory.widePullbackShape_connected

instance widePushoutShape_connected (J : Type v₁) : IsConnected (WidePushoutShape J) := by
  apply IsConnected.of_induct
  -- ⊢ ∀ (p : Set (WidePushoutShape J)), ?j₀ ∈ p → (∀ {j₁ j₂ : WidePushoutShape J}, …
  introv hp t
  -- ⊢ j ∈ p
  cases j
  · exact hp
    -- 🎉 no goals
  · rwa [← t (WidePushoutShape.Hom.init _)]
    -- 🎉 no goals
#align category_theory.wide_pushout_shape_connected CategoryTheory.widePushoutShape_connected

instance parallelPairInhabited : Inhabited WalkingParallelPair :=
  ⟨WalkingParallelPair.one⟩
#align category_theory.parallel_pair_inhabited CategoryTheory.parallelPairInhabited

instance parallel_pair_connected : IsConnected WalkingParallelPair := by
  apply IsConnected.of_induct
  -- ⊢ ∀ (p : Set WalkingParallelPair), ?j₀ ∈ p → (∀ {j₁ j₂ : WalkingParallelPair}, …
  introv _ t
  -- ⊢ j ∈ p
  cases j
  · rwa [t WalkingParallelPairHom.left]
    -- 🎉 no goals
  · assumption
    -- 🎉 no goals
#align category_theory.parallel_pair_connected CategoryTheory.parallel_pair_connected

end Examples

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
    PreservesLimitsOfShape J (prod.functor.obj X) where
  preservesLimit {K} :=
    {
      preserves := fun {c} l =>
        { lift := fun s =>
            prod.lift (s.π.app (Classical.arbitrary _) ≫ Limits.prod.fst) (l.lift (forgetCone s))
          fac := fun s j => by
            apply prod.hom_ext
            -- ⊢ ((fun s => prod.lift (NatTrans.app s.π (Classical.arbitrary J) ≫ prod.fst) ( …
            · erw [assoc, limMap_π, comp_id, limit.lift_π]
              -- ⊢ NatTrans.app (BinaryFan.mk (NatTrans.app s.π (Classical.arbitrary J) ≫ prod. …
              exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (Classical.arbitrary _)).symm
              -- 🎉 no goals
            · simp [← l.fac (forgetCone s) j]
              -- 🎉 no goals
          uniq := fun s m L => by
            apply prod.hom_ext
            -- ⊢ m ≫ prod.fst = (fun s => prod.lift (NatTrans.app s.π (Classical.arbitrary J) …
            · erw [limit.lift_π, ← L (Classical.arbitrary J), assoc, limMap_π, comp_id]
              -- ⊢ m ≫ prod.fst = NatTrans.app (BinaryFan.mk (m ≫ limit.π (pair X c.pt) { as := …
              rfl
              -- 🎉 no goals
            · rw [limit.lift_π]
              -- ⊢ m ≫ prod.snd = NatTrans.app (BinaryFan.mk (NatTrans.app s.π (Classical.arbit …
              apply l.uniq (forgetCone s)
              -- ⊢ ∀ (j : J), (m ≫ prod.snd) ≫ NatTrans.app c.π j = NatTrans.app (forgetCone s) …
              intro j
              -- ⊢ (m ≫ prod.snd) ≫ NatTrans.app c.π j = NatTrans.app (forgetCone s).π j
              simp [← L j] } }
              -- 🎉 no goals
#align category_theory.prod_preserves_connected_limits CategoryTheory.prodPreservesConnectedLimits

end CategoryTheory
