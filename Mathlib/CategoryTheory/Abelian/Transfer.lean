/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Adjunction.Limits

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
variable (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F)

/-- No point making this an instance, as it requires `i`. -/
theorem hasKernels [PreservesFiniteLimits G] : HasKernels C :=
  { has_limit := fun f => by
      have := NatIso.naturality_1 i f
      simp? at this says
        simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map, Functor.id_map] at this
      rw [← this]
      haveI : HasKernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasKernel_comp_mono _ _
      apply Limits.hasKernel_iso_comp }
#align category_theory.abelian_of_adjunction.has_kernels CategoryTheory.AbelianOfAdjunction.hasKernels

/-- No point making this an instance, as it requires `i` and `adj`. -/
theorem hasCokernels : HasCokernels C :=
  { has_colimit := fun f => by
      have : PreservesColimits G := adj.leftAdjointPreservesColimits
      have := NatIso.naturality_1 i f
      simp? at this says
        simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map, Functor.id_map] at this
      rw [← this]
      haveI : HasCokernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasCokernel_comp_iso _ _
      apply Limits.hasCokernel_epi_comp }
#align category_theory.abelian_of_adjunction.has_cokernels CategoryTheory.AbelianOfAdjunction.hasCokernels

variable [Limits.HasCokernels C]

/-- Auxiliary construction for `coimageIsoImage` -/
def cokernelIso {X Y : C} (f : X ⟶ Y) : G.obj (cokernel (F.map f)) ≅ cokernel f := by
  -- We have to write an explicit `PreservesColimits` type here,
  -- as `leftAdjointPreservesColimits` has universe variables.
  have : PreservesColimits G := adj.leftAdjointPreservesColimits
  calc
    G.obj (cokernel (F.map f)) ≅ cokernel (G.map (F.map f)) :=
      (asIso (cokernelComparison _ G)).symm
    _ ≅ cokernel (i.hom.app X ≫ f ≫ i.inv.app Y) := cokernelIsoOfEq (NatIso.naturality_2 i f).symm
    _ ≅ cokernel (f ≫ i.inv.app Y) := cokernelEpiComp (i.hom.app X) (f ≫ i.inv.app Y)
    _ ≅ cokernel f := cokernelCompIsIso f (i.inv.app Y)
#align category_theory.abelian_of_adjunction.cokernel_iso CategoryTheory.AbelianOfAdjunction.cokernelIso

variable [Limits.HasKernels C] [PreservesFiniteLimits G]

/-- Auxiliary construction for `coimageIsoImage` -/
def coimageIsoImageAux {X Y : C} (f : X ⟶ Y) :
    kernel (G.map (cokernel.π (F.map f))) ≅ kernel (cokernel.π f) := by
  have : PreservesColimits G := adj.leftAdjointPreservesColimits
  calc
    kernel (G.map (cokernel.π (F.map f))) ≅
        kernel (cokernel.π (G.map (F.map f)) ≫ cokernelComparison (F.map f) G) :=
      kernelIsoOfEq (π_comp_cokernelComparison _ _).symm
    _ ≅ kernel (cokernel.π (G.map (F.map f))) := kernelCompMono _ _
    _ ≅ kernel (cokernel.π (_ ≫ f ≫ _) ≫ (cokernelIsoOfEq _).hom) :=
      (kernelIsoOfEq (π_comp_cokernelIsoOfEq_hom (NatIso.naturality_2 i f)).symm)
    _ ≅ kernel (cokernel.π (_ ≫ f ≫ _)) := kernelCompMono _ _
    _ ≅ kernel (cokernel.π (f ≫ i.inv.app Y) ≫ (cokernelEpiComp (i.hom.app X) _).inv) :=
      (kernelIsoOfEq (by simp only [cokernel.π_desc, cokernelEpiComp_inv]))
    _ ≅ kernel (cokernel.π (f ≫ _)) := kernelCompMono _ _
    _ ≅ kernel (inv (i.inv.app Y) ≫ cokernel.π f ≫ (cokernelCompIsIso f (i.inv.app Y)).inv) :=
      (kernelIsoOfEq
        (by simp only [cokernel.π_desc, cokernelCompIsIso_inv, Iso.hom_inv_id_app_assoc,
          NatIso.inv_inv_app]))
    _ ≅ kernel (cokernel.π f ≫ _) := kernelIsIsoComp _ _
    _ ≅ kernel (cokernel.π f) := kernelCompMono _ _
#align category_theory.abelian_of_adjunction.coimage_iso_image_aux CategoryTheory.AbelianOfAdjunction.coimageIsoImageAux

variable [Functor.PreservesZeroMorphisms F]

/-- Auxiliary definition: the abelian coimage and abelian image agree.
We still need to check that this agrees with the canonical morphism.
-/
def coimageIsoImage {X Y : C} (f : X ⟶ Y) : Abelian.coimage f ≅ Abelian.image f := by
  have : PreservesLimits F := adj.rightAdjointPreservesLimits
  calc
    Abelian.coimage f ≅ cokernel (kernel.ι f) := Iso.refl _
    _ ≅ G.obj (cokernel (F.map (kernel.ι f))) := (cokernelIso _ _ i adj _).symm
    _ ≅ G.obj (cokernel (kernelComparison f F ≫ kernel.ι (F.map f))) :=
      (G.mapIso (cokernelIsoOfEq (by simp)))
    _ ≅ G.obj (cokernel (kernel.ι (F.map f))) := G.mapIso (cokernelEpiComp _ _)
    _ ≅ G.obj (Abelian.coimage (F.map f)) := Iso.refl _
    _ ≅ G.obj (Abelian.image (F.map f)) := G.mapIso (Abelian.coimageIsoImage _)
    _ ≅ G.obj (kernel (cokernel.π (F.map f))) := Iso.refl _
    _ ≅ kernel (G.map (cokernel.π (F.map f))) := PreservesKernel.iso _ _
    _ ≅ kernel (cokernel.π f) := coimageIsoImageAux F G i adj f
    _ ≅ Abelian.image f := Iso.refl _
#align category_theory.abelian_of_adjunction.coimage_iso_image CategoryTheory.AbelianOfAdjunction.coimageIsoImage

-- The account of this proof in the Stacks project omits this calculation.
theorem coimageIsoImage_hom {X Y : C} (f : X ⟶ Y) :
    (coimageIsoImage F G i adj f).hom = Abelian.coimageImageComparison f := by
  dsimp [coimageIsoImage, cokernelIso, cokernelEpiComp, cokernelCompIsIso_inv,
    coimageIsoImageAux, kernelCompMono]
  simpa only [← cancel_mono (Abelian.image.ι f), ← cancel_epi (Abelian.coimage.π f),
    Category.assoc, Category.id_comp, cokernel.π_desc_assoc,
    π_comp_cokernelIsoOfEq_inv_assoc, PreservesKernel.iso_hom,
    π_comp_cokernelComparison_assoc, ← G.map_comp_assoc, kernel.lift_ι,
    Abelian.coimage_image_factorisation, lift_comp_kernelIsoOfEq_hom_assoc,
    kernelIsIsoComp_hom, kernel.lift_ι_assoc, kernelIsoOfEq_hom_comp_ι_assoc,
    kernelComparison_comp_ι_assoc, π_comp_cokernelIsoOfEq_hom_assoc,
    asIso_hom, NatIso.inv_inv_app] using NatIso.naturality_1 i f
#align category_theory.abelian_of_adjunction.coimage_iso_image_hom CategoryTheory.AbelianOfAdjunction.coimageIsoImage_hom

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
    (G : D ⥤ C) [Functor.PreservesZeroMorphisms G] [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C)
    (adj : G ⊣ F) : Abelian C := by
  haveI := hasKernels F G i
  haveI := hasCokernels F G i adj
  have : ∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    rw [← coimageIsoImage_hom F G i adj f]
    infer_instance
  apply Abelian.ofCoimageImageComparisonIsIso
#align category_theory.abelian_of_adjunction CategoryTheory.abelianOfAdjunction

/-- If `C` is an additive category equivalent to an abelian category `D`
via a functor that preserves zero morphisms,
then `C` is also abelian.
-/
def abelianOfEquivalence {C : Type u₁} [Category.{v} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v} D] [Abelian D] (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]
    [F.IsEquivalence] : Abelian C :=
  abelianOfAdjunction F F.inv F.asEquivalence.unitIso.symm F.asEquivalence.symm.toAdjunction
#align category_theory.abelian_of_equivalence CategoryTheory.abelianOfEquivalence

end CategoryTheory
