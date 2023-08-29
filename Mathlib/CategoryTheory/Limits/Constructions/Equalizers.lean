/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

#align_import category_theory.limits.constructions.equalizers from "leanprover-community/mathlib"@"3424a5932a77dcec2c177ce7d805acace6149299"

/-!
# Constructing equalizers from pullbacks and binary products.

If a category has pullbacks and binary products, then it has equalizers.

TODO: generalize universe
-/


noncomputable section

universe v v' u u'

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {D : Type u'} [Category.{v'} D] (G : C ⥤ D)

-- We hide the "implementation details" inside a namespace
namespace HasEqualizersOfHasPullbacksAndBinaryProducts

variable [HasBinaryProducts C] [HasPullbacks C]

/-- Define the equalizing object -/
@[reducible]
def constructEqualizer (F : WalkingParallelPair ⥤ C) : C :=
  pullback (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.left))
    (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.right))
#align category_theory.limits.has_equalizers_of_has_pullbacks_and_binary_products.construct_equalizer CategoryTheory.Limits.HasEqualizersOfHasPullbacksAndBinaryProducts.constructEqualizer

/-- Define the equalizing morphism -/
abbrev pullbackFst (F : WalkingParallelPair ⥤ C) :
    constructEqualizer F ⟶ F.obj WalkingParallelPair.zero :=
  pullback.fst
#align category_theory.limits.has_equalizers_of_has_pullbacks_and_binary_products.pullback_fst CategoryTheory.Limits.HasEqualizersOfHasPullbacksAndBinaryProducts.pullbackFst

theorem pullbackFst_eq_pullback_snd (F : WalkingParallelPair ⥤ C) : pullbackFst F = pullback.snd :=
  by convert (eq_whisker pullback.condition Limits.prod.fst :
      (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.zero) = _) <;> simp
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
#align category_theory.limits.has_equalizers_of_has_pullbacks_and_binary_products.pullback_fst_eq_pullback_snd CategoryTheory.Limits.HasEqualizersOfHasPullbacksAndBinaryProducts.pullbackFst_eq_pullback_snd

/-- Define the equalizing cone -/
@[reducible]
def equalizerCone (F : WalkingParallelPair ⥤ C) : Cone F :=
  Cone.ofFork
    (Fork.ofι (pullbackFst F)
      (by
        conv_rhs => rw [pullbackFst_eq_pullback_snd]
        -- ⊢ pullbackFst F ≫ F.map WalkingParallelPairHom.left = pullback.snd ≫ F.map Wal …
        convert (eq_whisker pullback.condition Limits.prod.snd :
          (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.one) = _) using 1 <;> simp))
                                                                                      -- 🎉 no goals
                                                                                      -- 🎉 no goals
#align category_theory.limits.has_equalizers_of_has_pullbacks_and_binary_products.equalizer_cone CategoryTheory.Limits.HasEqualizersOfHasPullbacksAndBinaryProducts.equalizerCone

/-- Show the equalizing cone is a limit -/
def equalizerConeIsLimit (F : WalkingParallelPair ⥤ C) : IsLimit (equalizerCone F) where
  lift := by
    intro c; apply pullback.lift (c.π.app _) (c.π.app _)
    -- ⊢ c.pt ⟶ (equalizerCone F).pt
             -- ⊢ NatTrans.app c.π WalkingParallelPair.zero ≫ prod.lift (𝟙 (F.obj WalkingParal …
    ext <;> simp
    -- ⊢ (NatTrans.app c.π WalkingParallelPair.zero ≫ prod.lift (𝟙 (F.obj WalkingPara …
            -- 🎉 no goals
            -- 🎉 no goals
  fac := by rintro c (_ | _) <;> simp
            -- ⊢ pullback.lift (NatTrans.app c.π WalkingParallelPair.zero) (NatTrans.app c.π  …
                                 -- 🎉 no goals
                                 -- 🎉 no goals
  uniq := by
    intro c _ J
    -- ⊢ m✝ = pullback.lift (NatTrans.app c.π WalkingParallelPair.zero) (NatTrans.app …
    have J0 := J WalkingParallelPair.zero; simp at J0
    -- ⊢ m✝ = pullback.lift (NatTrans.app c.π WalkingParallelPair.zero) (NatTrans.app …
                                           -- ⊢ m✝ = pullback.lift (NatTrans.app c.π WalkingParallelPair.zero) (NatTrans.app …
    apply pullback.hom_ext
    -- ⊢ m✝ ≫ pullback.fst = pullback.lift (NatTrans.app c.π WalkingParallelPair.zero …
    · rwa [limit.lift_π]
      -- 🎉 no goals
    · erw [limit.lift_π, ← J0, pullbackFst_eq_pullback_snd]
      -- 🎉 no goals
#align category_theory.limits.has_equalizers_of_has_pullbacks_and_binary_products.equalizer_cone_is_limit CategoryTheory.Limits.HasEqualizersOfHasPullbacksAndBinaryProducts.equalizerConeIsLimit

end HasEqualizersOfHasPullbacksAndBinaryProducts

open HasEqualizersOfHasPullbacksAndBinaryProducts

-- This is not an instance, as it is not always how one wants to construct equalizers!
/-- Any category with pullbacks and binary products, has equalizers. -/
theorem hasEqualizers_of_hasPullbacks_and_binary_products [HasBinaryProducts C] [HasPullbacks C] :
    HasEqualizers C :=
  { has_limit := fun F =>
      HasLimit.mk
        { cone := equalizerCone F
          isLimit := equalizerConeIsLimit F } }
#align category_theory.limits.has_equalizers_of_has_pullbacks_and_binary_products CategoryTheory.Limits.hasEqualizers_of_hasPullbacks_and_binary_products

attribute [local instance] hasPullback_of_preservesPullback

/-- A functor that preserves pullbacks and binary products also presrves equalizers. -/
def preservesEqualizersOfPreservesPullbacksAndBinaryProducts [HasBinaryProducts C] [HasPullbacks C]
    [PreservesLimitsOfShape (Discrete WalkingPair) G] [PreservesLimitsOfShape WalkingCospan G] :
    PreservesLimitsOfShape WalkingParallelPair G :=
  ⟨fun {K} =>
    preservesLimitOfPreservesLimitCone (equalizerConeIsLimit K) <|
      { lift := fun c => by
          refine' pullback.lift ?_ ?_ ?_ ≫ (PreservesPullback.iso _ _ _ ).inv
          · exact c.π.app WalkingParallelPair.zero
            -- 🎉 no goals
          · exact c.π.app WalkingParallelPair.zero
            -- 🎉 no goals
          apply (mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd _ _)).hom_ext
          -- ⊢ ∀ (j : Discrete WalkingPair), (NatTrans.app c.π WalkingParallelPair.zero ≫ G …
          rintro (_ | _)
          -- ⊢ (NatTrans.app c.π WalkingParallelPair.zero ≫ G.map (prod.lift (𝟙 (K.obj Walk …
          · simp only [Category.assoc, ← G.map_comp, prod.lift_fst, BinaryFan.π_app_left,
              BinaryFan.mk_fst]
          · simp only [BinaryFan.π_app_right, BinaryFan.mk_snd, Category.assoc, ← G.map_comp,
              prod.lift_snd]
            exact
              (c.π.naturality WalkingParallelPairHom.left).symm.trans
                (c.π.naturality WalkingParallelPairHom.right)
        fac := fun c j => by
          rcases j with (_ | _) <;>
          -- ⊢ (fun c => pullback.lift (NatTrans.app c.π WalkingParallelPair.zero) (NatTran …
            simp only [Category.comp_id, PreservesPullback.iso_inv_fst, Cone.ofFork_π, G.map_comp,
              PreservesPullback.iso_inv_fst_assoc, Functor.mapCone_π_app, eqToHom_refl,
              Category.assoc, Fork.ofι_π_app, pullback.lift_fst, pullback.lift_fst_assoc]
          exact (c.π.naturality WalkingParallelPairHom.left).symm.trans (Category.id_comp _)
          -- 🎉 no goals
        uniq := fun s m h => by
          rw [Iso.eq_comp_inv]
          -- ⊢ m ≫ (PreservesPullback.iso G (prod.lift (𝟙 (K.obj WalkingParallelPair.zero)) …
          have := h WalkingParallelPair.zero
          -- ⊢ m ≫ (PreservesPullback.iso G (prod.lift (𝟙 (K.obj WalkingParallelPair.zero)) …
          dsimp [equalizerCone] at this
          -- ⊢ m ≫ (PreservesPullback.iso G (prod.lift (𝟙 (K.obj WalkingParallelPair.zero)) …
          ext <;>
          -- ⊢ (m ≫ (PreservesPullback.iso G (prod.lift (𝟙 (K.obj WalkingParallelPair.zero) …
            simp only [PreservesPullback.iso_hom_snd, Category.assoc,
              PreservesPullback.iso_hom_fst, pullback.lift_fst, pullback.lift_snd,
              Category.comp_id, ← pullbackFst_eq_pullback_snd, ← this] }⟩
#align category_theory.limits.preserves_equalizers_of_preserves_pullbacks_and_binary_products CategoryTheory.Limits.preservesEqualizersOfPreservesPullbacksAndBinaryProducts

-- We hide the "implementation details" inside a namespace
namespace HasCoequalizersOfHasPushoutsAndBinaryCoproducts

variable [HasBinaryCoproducts C] [HasPushouts C]

/-- Define the equalizing object -/
@[reducible]
def constructCoequalizer (F : WalkingParallelPair ⥤ C) : C :=
  pushout (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.left))
    (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.right))
#align category_theory.limits.has_coequalizers_of_has_pushouts_and_binary_coproducts.construct_coequalizer CategoryTheory.Limits.HasCoequalizersOfHasPushoutsAndBinaryCoproducts.constructCoequalizer

/-- Define the equalizing morphism -/
abbrev pushoutInl (F : WalkingParallelPair ⥤ C) :
    F.obj WalkingParallelPair.one ⟶ constructCoequalizer F :=
  pushout.inl
#align category_theory.limits.has_coequalizers_of_has_pushouts_and_binary_coproducts.pushout_inl CategoryTheory.Limits.HasCoequalizersOfHasPushoutsAndBinaryCoproducts.pushoutInl

theorem pushoutInl_eq_pushout_inr (F : WalkingParallelPair ⥤ C) : pushoutInl F = pushout.inr := by
  convert (whisker_eq Limits.coprod.inl pushout.condition :
    (_ : F.obj _ ⟶ constructCoequalizer _) = _) <;> simp
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align category_theory.limits.has_coequalizers_of_has_pushouts_and_binary_coproducts.pushout_inl_eq_pushout_inr CategoryTheory.Limits.HasCoequalizersOfHasPushoutsAndBinaryCoproducts.pushoutInl_eq_pushout_inr

/-- Define the equalizing cocone -/
@[reducible]
def coequalizerCocone (F : WalkingParallelPair ⥤ C) : Cocone F :=
  Cocone.ofCofork
    (Cofork.ofπ (pushoutInl F) (by
        conv_rhs => rw [pushoutInl_eq_pushout_inr]
        -- ⊢ F.map WalkingParallelPairHom.left ≫ pushoutInl F = F.map WalkingParallelPair …
        convert (whisker_eq Limits.coprod.inr pushout.condition
          : (_ : F.obj _ ⟶ constructCoequalizer _) = _) using 1 <;> simp))
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
#align category_theory.limits.has_coequalizers_of_has_pushouts_and_binary_coproducts.coequalizer_cocone CategoryTheory.Limits.HasCoequalizersOfHasPushoutsAndBinaryCoproducts.coequalizerCocone

/-- Show the equalizing cocone is a colimit -/
def coequalizerCoconeIsColimit (F : WalkingParallelPair ⥤ C) : IsColimit (coequalizerCocone F) where
  desc := by
    intro c; apply pushout.desc (c.ι.app _) (c.ι.app _)
    -- ⊢ (coequalizerCocone F).pt ⟶ c.pt
             -- ⊢ coprod.desc (𝟙 (F.obj WalkingParallelPair.one)) (F.map WalkingParallelPairHo …
    ext <;> simp
    -- ⊢ coprod.inl ≫ coprod.desc (𝟙 (F.obj WalkingParallelPair.one)) (F.map WalkingP …
            -- 🎉 no goals
            -- 🎉 no goals
  fac := by rintro c (_ | _) <;> simp
            -- ⊢ NatTrans.app (coequalizerCocone F).ι WalkingParallelPair.zero ≫ pushout.desc …
                                 -- 🎉 no goals
                                 -- 🎉 no goals
  uniq := by
    intro c m J
    -- ⊢ m = pushout.desc (NatTrans.app c.ι WalkingParallelPair.one) (NatTrans.app c. …
    have J1 : pushoutInl F ≫ m = c.ι.app WalkingParallelPair.one := by
      simpa using J WalkingParallelPair.one
    apply pushout.hom_ext
    -- ⊢ pushout.inl ≫ m = pushout.inl ≫ pushout.desc (NatTrans.app c.ι WalkingParall …
    · rw [colimit.ι_desc]
      -- ⊢ pushout.inl ≫ m = NatTrans.app (PushoutCocone.mk (NatTrans.app c.ι WalkingPa …
      exact J1
      -- 🎉 no goals
    · rw [colimit.ι_desc, ← pushoutInl_eq_pushout_inr]
      -- ⊢ pushoutInl F ≫ m = NatTrans.app (PushoutCocone.mk (NatTrans.app c.ι WalkingP …
      exact J1
      -- 🎉 no goals
#align category_theory.limits.has_coequalizers_of_has_pushouts_and_binary_coproducts.coequalizer_cocone_is_colimit CategoryTheory.Limits.HasCoequalizersOfHasPushoutsAndBinaryCoproducts.coequalizerCoconeIsColimit

end HasCoequalizersOfHasPushoutsAndBinaryCoproducts

open HasCoequalizersOfHasPushoutsAndBinaryCoproducts

-- This is not an instance, as it is not always how one wants to construct equalizers!
/-- Any category with pullbacks and binary products, has equalizers. -/
theorem hasCoequalizers_of_hasPushouts_and_binary_coproducts [HasBinaryCoproducts C]
    [HasPushouts C] : HasCoequalizers C :=
  {
    has_colimit := fun F =>
      HasColimit.mk
        { cocone := coequalizerCocone F
          isColimit := coequalizerCoconeIsColimit F } }
#align category_theory.limits.has_coequalizers_of_has_pushouts_and_binary_coproducts CategoryTheory.Limits.hasCoequalizers_of_hasPushouts_and_binary_coproducts

attribute [local instance] hasPushout_of_preservesPushout

/-- A functor that preserves pushouts and binary coproducts also presrves coequalizers. -/
def preservesCoequalizersOfPreservesPushoutsAndBinaryCoproducts [HasBinaryCoproducts C]
    [HasPushouts C] [PreservesColimitsOfShape (Discrete WalkingPair) G]
    [PreservesColimitsOfShape WalkingSpan G] : PreservesColimitsOfShape WalkingParallelPair G :=
  ⟨fun {K} =>
    preservesColimitOfPreservesColimitCocone (coequalizerCoconeIsColimit K) <|
      { desc := fun c => by
          refine' (PreservesPushout.iso _ _ _).inv ≫ pushout.desc _ _ _
          · exact c.ι.app WalkingParallelPair.one
            -- 🎉 no goals
          · exact c.ι.app WalkingParallelPair.one
            -- 🎉 no goals
          apply (mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod _ _)).hom_ext
          -- ⊢ ∀ (j : Discrete WalkingPair), NatTrans.app (BinaryCofan.mk (G.map coprod.inl …
          rintro (_ | _)
          -- ⊢ NatTrans.app (BinaryCofan.mk (G.map coprod.inl) (G.map coprod.inr)).ι { as : …
          · simp only [BinaryCofan.ι_app_left, BinaryCofan.mk_inl, Category.assoc, ←
              G.map_comp_assoc, coprod.inl_desc]
          · simp only [BinaryCofan.ι_app_right, BinaryCofan.mk_inr, Category.assoc, ←
              G.map_comp_assoc, coprod.inr_desc]
            exact
              (c.ι.naturality WalkingParallelPairHom.left).trans
                (c.ι.naturality WalkingParallelPairHom.right).symm
        fac := fun c j => by
          rcases j with (_ | _) <;>
          -- ⊢ NatTrans.app (G.mapCocone (coequalizerCocone K)).ι WalkingParallelPair.zero  …
            simp only [Functor.mapCocone_ι_app, Cocone.ofCofork_ι, Category.id_comp,
              eqToHom_refl, Category.assoc, Functor.map_comp, Cofork.ofπ_ι_app, pushout.inl_desc,
              PreservesPushout.inl_iso_inv_assoc]
          exact (c.ι.naturality WalkingParallelPairHom.left).trans (Category.comp_id _)
          -- 🎉 no goals
        uniq := fun s m h => by
          rw [Iso.eq_inv_comp]
          -- ⊢ (PreservesPushout.iso G (coprod.desc (𝟙 (K.obj WalkingParallelPair.one)) (K. …
          have := h WalkingParallelPair.one
          -- ⊢ (PreservesPushout.iso G (coprod.desc (𝟙 (K.obj WalkingParallelPair.one)) (K. …
          dsimp [coequalizerCocone] at this
          -- ⊢ (PreservesPushout.iso G (coprod.desc (𝟙 (K.obj WalkingParallelPair.one)) (K. …
          ext <;>
          -- ⊢ pushout.inl ≫ (PreservesPushout.iso G (coprod.desc (𝟙 (K.obj WalkingParallel …
            simp only [PreservesPushout.inl_iso_hom_assoc, Category.id_comp, pushout.inl_desc,
              pushout.inr_desc, PreservesPushout.inr_iso_hom_assoc, ← pushoutInl_eq_pushout_inr, ←
              this] }⟩
#align category_theory.limits.preserves_coequalizers_of_preserves_pushouts_and_binary_coproducts CategoryTheory.Limits.preservesCoequalizersOfPreservesPushoutsAndBinaryCoproducts

end CategoryTheory.Limits
