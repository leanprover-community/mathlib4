/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.limits.preserves.shapes.equalizers from "leanprover-community/mathlib"@"4698e35ca56a0d4fa53aa5639c3364e0a77f4eba"

/-!
# Preserving (co)equalizers

Constructions to relate the notions of preserving (co)equalizers and reflecting (co)equalizers
to concrete (co)forks.

In particular, we show that `equalizerComparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,g`, as well as the dual result.
-/


noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section Equalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g)

/-- The map of a fork is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `Fork.ofι` with `Functor.mapCone`.
-/
def isLimitMapConeForkEquiv :
    IsLimit (G.mapCone (Fork.ofι h w)) ≃
      IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g)) :=
                                      -- 🎉 no goals
  (IsLimit.postcomposeHomEquiv (diagramIsoParallelPair _) _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) (by simp [Fork.ι])))
                                                      -- 🎉 no goals
#align category_theory.limits.is_limit_map_cone_fork_equiv CategoryTheory.Limits.isLimitMapConeForkEquiv

/-- The property of preserving equalizers expressed in terms of forks. -/
def isLimitForkMapOfIsLimit [PreservesLimit (parallelPair f g) G] (l : IsLimit (Fork.ofι h w)) :
    IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g)) :=
                                    -- 🎉 no goals
  isLimitMapConeForkEquiv G w (PreservesLimit.preserves l)
#align category_theory.limits.is_limit_fork_map_of_is_limit CategoryTheory.Limits.isLimitForkMapOfIsLimit

/-- The property of reflecting equalizers expressed in terms of forks. -/
def isLimitOfIsLimitForkMap [ReflectsLimit (parallelPair f g) G]
    (l : IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g))) :
                                         -- 🎉 no goals
    IsLimit (Fork.ofι h w) :=
  ReflectsLimit.reflects ((isLimitMapConeForkEquiv G w).symm l)
#align category_theory.limits.is_limit_of_is_limit_fork_map CategoryTheory.Limits.isLimitOfIsLimitForkMap

variable (f g) [HasEqualizer f g]

/--
If `G` preserves equalizers and `C` has them, then the fork constructed of the mapped morphisms of
a fork is a limit.
-/
def isLimitOfHasEqualizerOfPreservesLimit [PreservesLimit (parallelPair f g) G] :
    IsLimit (Fork.ofι
      (G.map (equalizer.ι f g)) (by simp only [← G.map_comp]; rw [equalizer.condition]) :
                                    -- ⊢ G.map (equalizer.ι f g ≫ f) = G.map (equalizer.ι f g ≫ g)
                                                              -- 🎉 no goals
      Fork (G.map f) (G.map g)) :=
  isLimitForkMapOfIsLimit G _ (equalizerIsEqualizer f g)
#align category_theory.limits.is_limit_of_has_equalizer_of_preserves_limit CategoryTheory.Limits.isLimitOfHasEqualizerOfPreservesLimit

variable [HasEqualizer (G.map f) (G.map g)]

/-- If the equalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
equalizer of `(f,g)`.
-/
def PreservesEqualizer.ofIsoComparison [i : IsIso (equalizerComparison f g G)] :
    PreservesLimit (parallelPair f g) G := by
  apply preservesLimitOfPreservesLimitCone (equalizerIsEqualizer f g)
  -- ⊢ IsLimit (G.mapCone (Fork.ofι (equalizer.ι f g) (_ : equalizer.ι f g ≫ f = eq …
  apply (isLimitMapConeForkEquiv _ _).symm _
  -- ⊢ IsLimit (Fork.ofι (G.map (equalizer.ι f g)) (_ : G.map (equalizer.ι f g) ≫ G …
  refine @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (parallelPair (G.map f) (G.map g))) ?_
  -- ⊢ IsIso (IsLimit.lift (limit.isLimit (parallelPair (G.map f) (G.map g))) (Fork …
  apply i
  -- 🎉 no goals
#align category_theory.limits.preserves_equalizer.of_iso_comparison CategoryTheory.Limits.PreservesEqualizer.ofIsoComparison

variable [PreservesLimit (parallelPair f g) G]

/--
If `G` preserves the equalizer of `(f,g)`, then the equalizer comparison map for `G` at `(f,g)` is
an isomorphism.
-/
def PreservesEqualizer.iso : G.obj (equalizer f g) ≅ equalizer (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasEqualizerOfPreservesLimit G f g) (limit.isLimit _)
#align category_theory.limits.preserves_equalizer.iso CategoryTheory.Limits.PreservesEqualizer.iso

@[simp]
theorem PreservesEqualizer.iso_hom :
    (PreservesEqualizer.iso G f g).hom = equalizerComparison f g G :=
  rfl
#align category_theory.limits.preserves_equalizer.iso_hom CategoryTheory.Limits.PreservesEqualizer.iso_hom

instance : IsIso (equalizerComparison f g G) := by
  rw [← PreservesEqualizer.iso_hom]
  -- ⊢ IsIso (PreservesEqualizer.iso G f g).hom
  infer_instance
  -- 🎉 no goals

end Equalizers

section Coequalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h)

/-- The map of a cofork is a colimit iff the cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `Cofork.ofπ` with `Functor.mapCocone`.
-/
def isColimitMapCoconeCoforkEquiv :
    IsColimit (G.mapCocone (Cofork.ofπ h w)) ≃
      IsColimit
        (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g)) :=
                                  -- 🎉 no goals
  (IsColimit.precomposeInvEquiv (diagramIsoParallelPair _) _).symm.trans <|
    IsColimit.equivIsoColimit <|
      Cofork.ext (Iso.refl _) <| by
        dsimp only [Cofork.π, Cofork.ofπ_ι_app]
        -- ⊢ NatTrans.app ((Cocones.precompose (diagramIsoParallelPair (parallelPair f g  …
        dsimp; rw [Category.comp_id, Category.id_comp]
        -- ⊢ (𝟙 (G.obj Y) ≫ G.map h) ≫ 𝟙 (G.obj Z) = G.map h
               -- 🎉 no goals
#align category_theory.limits.is_colimit_map_cocone_cofork_equiv CategoryTheory.Limits.isColimitMapCoconeCoforkEquiv

/-- The property of preserving coequalizers expressed in terms of coforks. -/
def isColimitCoforkMapOfIsColimit [PreservesColimit (parallelPair f g) G]
    (l : IsColimit (Cofork.ofπ h w)) :
    IsColimit
      (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g)) :=
                                -- 🎉 no goals
  isColimitMapCoconeCoforkEquiv G w (PreservesColimit.preserves l)
#align category_theory.limits.is_colimit_cofork_map_of_is_colimit CategoryTheory.Limits.isColimitCoforkMapOfIsColimit

/-- The property of reflecting coequalizers expressed in terms of coforks. -/
def isColimitOfIsColimitCoforkMap [ReflectsColimit (parallelPair f g) G]
    (l :
      IsColimit
        (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g))) :
                                  -- 🎉 no goals
    IsColimit (Cofork.ofπ h w) :=
  ReflectsColimit.reflects ((isColimitMapCoconeCoforkEquiv G w).symm l)
#align category_theory.limits.is_colimit_of_is_colimit_cofork_map CategoryTheory.Limits.isColimitOfIsColimitCoforkMap

variable (f g) [HasCoequalizer f g]

/--
If `G` preserves coequalizers and `C` has them, then the cofork constructed of the mapped morphisms
of a cofork is a colimit.
-/
def isColimitOfHasCoequalizerOfPreservesColimit [PreservesColimit (parallelPair f g) G] :
    IsColimit (Cofork.ofπ (G.map (coequalizer.π f g)) (by
      simp only [← G.map_comp]; rw [coequalizer.condition]) : Cofork (G.map f) (G.map g)) :=
      -- ⊢ G.map (f ≫ coequalizer.π f g) = G.map (g ≫ coequalizer.π f g)
                                -- 🎉 no goals
  isColimitCoforkMapOfIsColimit G _ (coequalizerIsCoequalizer f g)
#align category_theory.limits.is_colimit_of_has_coequalizer_of_preserves_colimit CategoryTheory.Limits.isColimitOfHasCoequalizerOfPreservesColimit

variable [HasCoequalizer (G.map f) (G.map g)]

/-- If the coequalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
coequalizer of `(f,g)`.
-/
def ofIsoComparison [i : IsIso (coequalizerComparison f g G)] :
    PreservesColimit (parallelPair f g) G := by
  apply preservesColimitOfPreservesColimitCocone (coequalizerIsCoequalizer f g)
  -- ⊢ IsColimit (G.mapCocone (Cofork.ofπ (coequalizer.π f g) (_ : f ≫ coequalizer. …
  apply (isColimitMapCoconeCoforkEquiv _ _).symm _
  -- ⊢ IsColimit (Cofork.ofπ (G.map (coequalizer.π f g)) (_ : G.map f ≫ G.map (coeq …
  refine
    @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (parallelPair (G.map f) (G.map g))) ?_
  apply i
  -- 🎉 no goals
#align category_theory.limits.of_iso_comparison CategoryTheory.Limits.ofIsoComparison

variable [PreservesColimit (parallelPair f g) G]

/--
If `G` preserves the coequalizer of `(f,g)`, then the coequalizer comparison map for `G` at `(f,g)`
is an isomorphism.
-/
def PreservesCoequalizer.iso : coequalizer (G.map f) (G.map g) ≅ G.obj (coequalizer f g) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasCoequalizerOfPreservesColimit G f g)
#align category_theory.limits.preserves_coequalizer.iso CategoryTheory.Limits.PreservesCoequalizer.iso

@[simp]
theorem PreservesCoequalizer.iso_hom :
    (PreservesCoequalizer.iso G f g).hom = coequalizerComparison f g G :=
  rfl
#align category_theory.limits.preserves_coequalizer.iso_hom CategoryTheory.Limits.PreservesCoequalizer.iso_hom

instance : IsIso (coequalizerComparison f g G) := by
  rw [← PreservesCoequalizer.iso_hom]
  -- ⊢ IsIso (PreservesCoequalizer.iso G f g).hom
  infer_instance
  -- 🎉 no goals

instance map_π_epi : Epi (G.map (coequalizer.π f g)) :=
  ⟨fun {W} h k => by
    rw [← ι_comp_coequalizerComparison]
    -- ⊢ (coequalizer.π (G.map f) (G.map g) ≫ coequalizerComparison f g G) ≫ h = (coe …
    haveI : Epi (coequalizer.π (G.map f) (G.map g) ≫ coequalizerComparison f g G) := by
      apply epi_comp
    apply (cancel_epi _).1⟩
    -- 🎉 no goals
#align category_theory.limits.map_π_epi CategoryTheory.Limits.map_π_epi

@[reassoc]
theorem map_π_preserves_coequalizer_inv :
    G.map (coequalizer.π f g) ≫ (PreservesCoequalizer.iso G f g).inv =
      coequalizer.π (G.map f) (G.map g) := by
  rw [← ι_comp_coequalizerComparison_assoc, ← PreservesCoequalizer.iso_hom, Iso.hom_inv_id,
    comp_id]
#align category_theory.limits.map_π_preserves_coequalizer_inv CategoryTheory.Limits.map_π_preserves_coequalizer_inv

@[reassoc]
theorem map_π_preserves_coequalizer_inv_desc {W : D} (k : G.obj Y ⟶ W)
    (wk : G.map f ≫ k = G.map g ≫ k) :
    G.map (coequalizer.π f g) ≫ (PreservesCoequalizer.iso G f g).inv ≫ coequalizer.desc k wk = k :=
  by rw [← Category.assoc, map_π_preserves_coequalizer_inv, coequalizer.π_desc]
     -- 🎉 no goals
#align category_theory.limits.map_π_preserves_coequalizer_inv_desc CategoryTheory.Limits.map_π_preserves_coequalizer_inv_desc

@[reassoc]
theorem map_π_preserves_coequalizer_inv_colimMap {X' Y' : D} (f' g' : X' ⟶ Y')
    [HasCoequalizer f' g'] (p : G.obj X ⟶ X') (q : G.obj Y ⟶ Y') (wf : G.map f ≫ q = p ≫ f')
    (wg : G.map g ≫ q = p ≫ g') :
    G.map (coequalizer.π f g) ≫
        (PreservesCoequalizer.iso G f g).inv ≫
          colimMap (parallelPairHom (G.map f) (G.map g) f' g' p q wf wg) =
      q ≫ coequalizer.π f' g' :=
  by rw [← Category.assoc, map_π_preserves_coequalizer_inv, ι_colimMap, parallelPairHom_app_one]
     -- 🎉 no goals
#align category_theory.limits.map_π_preserves_coequalizer_inv_colim_map CategoryTheory.Limits.map_π_preserves_coequalizer_inv_colimMap

@[reassoc]
theorem map_π_preserves_coequalizer_inv_colimMap_desc {X' Y' : D} (f' g' : X' ⟶ Y')
    [HasCoequalizer f' g'] (p : G.obj X ⟶ X') (q : G.obj Y ⟶ Y') (wf : G.map f ≫ q = p ≫ f')
    (wg : G.map g ≫ q = p ≫ g') {Z' : D} (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    G.map (coequalizer.π f g) ≫
        (PreservesCoequalizer.iso G f g).inv ≫
          colimMap (parallelPairHom (G.map f) (G.map g) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h := by
  slice_lhs 1 3 => rw [map_π_preserves_coequalizer_inv_colimMap]
  -- ⊢ (q ≫ coequalizer.π f' g') ≫ coequalizer.desc h wh = q ≫ h
  slice_lhs 2 3 => rw [coequalizer.π_desc]
  -- 🎉 no goals
#align category_theory.limits.map_π_preserves_coequalizer_inv_colim_map_desc CategoryTheory.Limits.map_π_preserves_coequalizer_inv_colimMap_desc

/-- Any functor preserves coequalizers of split pairs. -/
instance (priority := 1) preservesSplitCoequalizers (f g : X ⟶ Y) [HasSplitCoequalizer f g] :
    PreservesColimit (parallelPair f g) G := by
  apply
    preservesColimitOfPreservesColimitCocone
      (HasSplitCoequalizer.isSplitCoequalizer f g).isCoequalizer
  apply
    (isColimitMapCoconeCoforkEquiv G _).symm
      ((HasSplitCoequalizer.isSplitCoequalizer f g).map G).isCoequalizer
#align category_theory.limits.preserves_split_coequalizers CategoryTheory.Limits.preservesSplitCoequalizers

end Coequalizers

end CategoryTheory.Limits
