/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Adjunction.Reflective

#align_import category_theory.abelian.transfer from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Transferring "abelian-ness" across a functor

If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

See <https://stacks.math.columbia.edu/tag/03A3>

## Notes
The hypotheses, following the statement from the Stacks project,
may appear surprising: we don't ask that the counit of the adjunction is an isomorphism,
but just that we have some potentially unrelated isomorphism `i : F ⋙ G ≅ 𝟭 C`.

However Lemma A1.1.1 from [Elephant] shows that in this situation the counit itself
must be an isomorphism, and thus that `C` is a reflective subcategory of `D`.

Someone may like to formalize that lemma, and restate this theorem in terms of `Reflective`.
(That lemma has a nice string diagrammatic proof that holds in any bicategory.)
-/


noncomputable section

namespace CategoryTheory

open Limits

universe v u₁ u₂

namespace AbelianOfAdjunction

variable {C : Type u₁} [Category.{v} C] [Preadditive C]
variable {D : Type u₂} [Category.{v} D] [Abelian D]
variable (F : C ⥤ D)
variable (G : D ⥤ C) [Functor.PreservesZeroMorphisms G]
variable (adj : G ⊣ F) [Reflective F]

/-- No point making this an instance, as it requires `i`. -/
theorem hasKernels : HasKernels C :=
  { has_limit := fun _ ↦ hasLimit_of_reflective _ F }
#align category_theory.abelian_of_adjunction.has_kernels CategoryTheory.AbelianOfAdjunction.hasKernels

/-- No point making this an instance, as it requires `i` and `adj`. -/
theorem hasCokernels : HasCokernels C :=
  { has_colimit := fun _ ↦ hasColimit_of_reflective _ F }
#align category_theory.abelian_of_adjunction.has_cokernels CategoryTheory.AbelianOfAdjunction.hasCokernels

-- variable [Limits.HasCokernels C]

-- /-- Auxiliary construction for `coimageIsoImage` -/
-- def cokernelIso {X Y : C} (f : X ⟶ Y) : G.obj (cokernel (F.map f)) ≅ cokernel f := by
--   -- We have to write an explicit `PreservesColimits` type here,
--   -- as `leftAdjointPreservesColimits` has universe variables.
--   have : PreservesColimits G := adj.leftAdjointPreservesColimits
--   calc
--     G.obj (cokernel (F.map f)) ≅ cokernel (G.map (F.map f)) :=
--       (asIso (cokernelComparison _ G)).symm
--     _ ≅ cokernel (adj.counit.app X ≫ f ≫ (inv adj.counit).app Y) :=
--       cokernelIsoOfEq (NatIso.naturality_2 (asIso adj.counit) f).symm
--     _ ≅ cokernel (f ≫ (inv adj.counit).app Y) :=
--       cokernelEpiComp (adj.counit.app X) (f ≫ (inv adj.counit).app Y)
--     _ ≅ cokernel f := cokernelCompIsIso f ((inv adj.counit).app Y)
-- #align category_theory.abelian_of_adjunction.cokernel_iso CategoryTheory.AbelianOfAdjunction.cokernelIso

-- variable [Limits.HasKernels C] [PreservesFiniteLimits G]

-- /-- Auxiliary construction for `coimageIsoImage` -/
-- def coimageIsoImageAux {X Y : C} (f : X ⟶ Y) :
--     kernel (G.map (cokernel.π (F.map f))) ≅ kernel (cokernel.π f) := by
--   have : PreservesColimits G := adj.leftAdjointPreservesColimits
--   calc
--     kernel (G.map (cokernel.π (F.map f))) ≅
--         kernel (cokernel.π (G.map (F.map f)) ≫ cokernelComparison (F.map f) G) :=
--       kernelIsoOfEq (π_comp_cokernelComparison _ _).symm
--     _ ≅ kernel (cokernel.π (G.map (F.map f))) := kernelCompMono _ _
--     _ ≅ kernel (cokernel.π (_ ≫ f ≫ _) ≫ (cokernelIsoOfEq _).hom) :=
--       (kernelIsoOfEq (π_comp_cokernelIsoOfEq_hom (NatIso.naturality_2 (asIso adj.counit) f)).symm)
--     _ ≅ kernel (cokernel.π (_ ≫ f ≫ (inv adj.counit).app Y)) := kernelCompMono _ _
--     _ ≅ kernel (cokernel.π (f ≫ (inv adj.counit).app Y) ≫
--         (cokernelEpiComp (adj.counit.app X) _).inv) :=
--       sorry-- (kernelIsoOfEq (by simp only [cokernel.π_desc, cokernelEpiComp_inv]))
--     _ ≅ kernel (cokernel.π (f ≫ _)) := kernelCompMono _ _
--     _ ≅ kernel (inv (i.inv.app Y) ≫ cokernel.π f ≫ (cokernelCompIsIso f (i.inv.app Y)).inv) :=
--       (kernelIsoOfEq
--         (by simp only [cokernel.π_desc, cokernelCompIsIso_inv, Iso.hom_inv_id_app_assoc,
--           NatIso.inv_inv_app]))
--     _ ≅ kernel (cokernel.π f ≫ _) := kernelIsIsoComp _ _
--     _ ≅ kernel (cokernel.π f) := kernelCompMono _ _
-- #align category_theory.abelian_of_adjunction.coimage_iso_image_aux CategoryTheory.AbelianOfAdjunction.coimageIsoImageAux

-- variable [Functor.PreservesZeroMorphisms F]

-- /-- Auxiliary definition: the abelian coimage and abelian image agree.
-- We still need to check that this agrees with the canonical morphism.
-- -/
-- def coimageIsoImage {X Y : C} (f : X ⟶ Y) : Abelian.coimage f ≅ Abelian.image f := by
--   have : PreservesLimits F := adj.rightAdjointPreservesLimits
--   calc
--     Abelian.coimage f ≅ cokernel (kernel.ι f) := Iso.refl _
--     _ ≅ G.obj (cokernel (F.map (kernel.ι f))) := (cokernelIso _ _ i adj _).symm
--     _ ≅ G.obj (cokernel (kernelComparison f F ≫ kernel.ι (F.map f))) :=
--       (G.mapIso (cokernelIsoOfEq (by simp)))
--     _ ≅ G.obj (cokernel (kernel.ι (F.map f))) := G.mapIso (cokernelEpiComp _ _)
--     _ ≅ G.obj (Abelian.coimage (F.map f)) := Iso.refl _
--     _ ≅ G.obj (Abelian.image (F.map f)) := G.mapIso (Abelian.coimageIsoImage _)
--     _ ≅ G.obj (kernel (cokernel.π (F.map f))) := Iso.refl _
--     _ ≅ kernel (G.map (cokernel.π (F.map f))) := PreservesKernel.iso _ _
--     _ ≅ kernel (cokernel.π f) := coimageIsoImageAux F G i adj f
--     _ ≅ Abelian.image f := Iso.refl _
-- #align category_theory.abelian_of_adjunction.coimage_iso_image CategoryTheory.AbelianOfAdjunction.coimageIsoImage

-- -- The account of this proof in the Stacks project omits this calculation.
-- theorem coimageIsoImage_hom {X Y : C} (f : X ⟶ Y) :
--     (coimageIsoImage F G i adj f).hom = Abelian.coimageImageComparison f := by
--   dsimp [coimageIsoImage, cokernelIso, cokernelEpiComp, cokernelCompIsIso_inv,
--     coimageIsoImageAux, kernelCompMono]
--   simpa only [← cancel_mono (Abelian.image.ι f), ← cancel_epi (Abelian.coimage.π f),
--     Category.assoc, Category.id_comp, cokernel.π_desc_assoc,
--     π_comp_cokernelIsoOfEq_inv_assoc, PreservesKernel.iso_hom,
--     π_comp_cokernelComparison_assoc, ← G.map_comp_assoc, kernel.lift_ι,
--     Abelian.coimage_image_factorisation, lift_comp_kernelIsoOfEq_hom_assoc,
--     kernelIsIsoComp_hom, kernel.lift_ι_assoc, kernelIsoOfEq_hom_comp_ι_assoc,
--     kernelComparison_comp_ι_assoc, π_comp_cokernelIsoOfEq_hom_assoc,
--     asIso_hom, NatIso.inv_inv_app] using NatIso.naturality_1 i f
-- #align category_theory.abelian_of_adjunction.coimage_iso_image_hom CategoryTheory.AbelianOfAdjunction.coimageIsoImage_hom

def coimageIso {X Y : C} (f : X ⟶ Y) [PreservesFiniteLimits G] :
    haveI := hasKernels F
    haveI := hasCokernels F
    F.obj (Abelian.coimage f) ≅ Abelian.coimage (F.map f) :=
  haveI := hasKernels F
  haveI := hasCokernels F
  calc  _ ≅ F.obj (cokernel ((kernel.ι f))) := Iso.refl _
        _ ≅ cokernel (F.map (kernel.ι f)) := sorry
        _ ≅ cokernel (kernel.ι (F.map f)) :=
          cokernel.mapIso (F.map (kernel.ι f)) (kernel.ι (F.map f))
            (PreservesKernel.iso _ _) (Iso.refl _) (by aesop)
        _ ≅ Abelian.coimage (F.map f) := Iso.refl _

def imageIso {X Y : C} (f : X ⟶ Y) [PreservesFiniteLimits G] :
    haveI := hasKernels F
    haveI := hasCokernels F
    F.obj (Abelian.image f) ≅ Abelian.image (F.map f) :=
  haveI := hasKernels F
  haveI := hasCokernels F
  calc  _ ≅ F.obj (kernel (cokernel.π f)) := Iso.refl _
        _ ≅ kernel (F.map (cokernel.π f)) := PreservesKernel.iso _ _
        _ ≅ _ := sorry

lemma map_coimageImageComparison {X Y : C} (f : X ⟶ Y) [PreservesFiniteLimits G] :
    haveI := hasKernels F
    haveI := hasCokernels F
    F.map (Abelian.coimageImageComparison f) = (coimageIso F G f).hom ≫
      Abelian.coimageImageComparison (F.map f) ≫ (imageIso F G f).inv := sorry

end AbelianOfAdjunction

open AbelianOfAdjunction

/-- If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

See <https://stacks.math.columbia.edu/tag/03A3>
-/
def abelianOfAdjunction {C : Type u₁} [Category.{v} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v} D] [Abelian D] (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]
    (G : D ⥤ C) [Functor.PreservesZeroMorphisms G] [PreservesFiniteLimits G]
    (adj : G ⊣ F) [Reflective F] : Abelian C := by
  haveI := hasKernels F
  haveI := hasCokernels F
  have : ∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    rw [← isIso_iff_of_reflects_iso _ F, map_coimageImageComparison F G]
    infer_instance
  apply Abelian.ofCoimageImageComparisonIsIso

/-- If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

See <https://stacks.math.columbia.edu/tag/03A3>
-/
def abelianOfAdjunction' {C : Type u₁} [Category.{v} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v} D] [Abelian D] (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]
    (G : D ⥤ C) [Functor.PreservesZeroMorphisms G] [PreservesFiniteLimits G]
    (adj : G ⊣ F) [Reflective F] : Abelian C where
  normalMonoOfMono f _ := by
    suffices NormalMono (F.map f) by sorry
    have : Mono (F.map f) := inferInstance
    exact normalMonoOfMono (F.map f)
  normalEpiOfEpi f _ := by
    suffices NormalEpi (F.map f) by sorry
    refine ⟨kernel (F.map f), kernel.ι _, by simp, ?_⟩
    apply Cofork.IsColimit.mk'
    intro s
    simp only [Cofork.ofπ_pt, parallelPair_obj_one, Functor.const_obj_obj, Cofork.π_ofπ]
    sorry
    -- have : (F ⋙ G).PreservesEpimorphisms :=
    --   Functor.preservesEpimorphisms.of_iso (asIso adj.counit).symm
    -- have : G.ReflectsEpimorphisms := sorry
    -- have : F.PreservesEpimorphisms := F.preservesEpimorphisms_of_preserves_of_reflects G
    -- have : HasZeroObject C := hasZeroObject_of_hasTerminal_object
    -- have : HasCokernels C := hasCokernels F
    -- have : Epi (F.map f) := by
    --   apply Abelian.epi_of_cokernel_π_eq_zero
    --   have := cokernel.π_of_epi f
    --   replace this := congrArg F.map this
    --   simp only [Functor.map_zero] at this
    --   have h : F.map (cokernel.π f) = cokernel.π (F.map f) ≫ cokernelComparison _ _ := by simp
    --   have : Mono (cokernelComparison f F) := by
    --     sorry
    --   apply Mono.right_cancellation (f := cokernelComparison f F) _ _
    --   simpa
    -- exact normalEpiOfEpi (F.map f)
  has_kernels := { has_limit := fun f ↦ hasLimit_of_reflective _ F }
  has_cokernels := { has_colimit := fun f ↦ hasColimit_of_reflective _ F }

/-- If `C` is an additive category equivalent to an abelian category `D`
via a functor that preserves zero morphisms,
then `C` is also abelian.
-/
def abelianOfEquivalence {C : Type u₁} [Category.{v} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v} D] [Abelian D] (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]
    [F.IsEquivalence] : Abelian C :=
  have : Reflective F := sorry
  abelianOfAdjunction F F.inv F.asEquivalence.symm.toAdjunction
#align category_theory.abelian_of_equivalence CategoryTheory.abelianOfEquivalence

end CategoryTheory
