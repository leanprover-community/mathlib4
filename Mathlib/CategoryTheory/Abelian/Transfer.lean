/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.abelian.transfer
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.Basic
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathbin.CategoryTheory.Adjunction.Limits

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
may appear suprising: we don't ask that the counit of the adjunction is an isomorphism,
but just that we have some potentially unrelated isomorphism `i : F ⋙ G ≅ 𝟭 C`.

However Lemma A1.1.1 from [Elephant] shows that in this situation the counit itself
must be an isomorphism, and thus that `C` is a reflective subcategory of `D`.

Someone may like to formalize that lemma, and restate this theorem in terms of `reflective`.
(That lemma has a nice string diagrammatic proof that holds in any bicategory.)
-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v u₁ u₂

namespace AbelianOfAdjunction

variable {C : Type u₁} [Category.{v} C] [Preadditive C]

variable {D : Type u₂} [Category.{v} D] [Abelian D]

variable (F : C ⥤ D)

variable (G : D ⥤ C) [Functor.PreservesZeroMorphisms G]

variable (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F)

include i

/-- No point making this an instance, as it requires `i`. -/
theorem hasKernels [PreservesFiniteLimits G] : HasKernels C :=
  {
    HasLimit := fun X Y f => by
      have := nat_iso.naturality_1 i f
      simp at this
      rw [← this]
      haveI : has_kernel (G.map (F.map f) ≫ i.hom.app _) := limits.has_kernel_comp_mono _ _
      apply limits.has_kernel_iso_comp }
#align category_theory.abelian_of_adjunction.has_kernels CategoryTheory.AbelianOfAdjunction.hasKernels

include adj

/-- No point making this an instance, as it requires `i` and `adj`. -/
theorem hasCokernels : HasCokernels C :=
  {
    HasColimit := fun X Y f =>
      by
      haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits
      have := nat_iso.naturality_1 i f
      simp at this
      rw [← this]
      haveI : has_cokernel (G.map (F.map f) ≫ i.hom.app _) := limits.has_cokernel_comp_iso _ _
      apply limits.has_cokernel_epi_comp }
#align category_theory.abelian_of_adjunction.has_cokernels CategoryTheory.AbelianOfAdjunction.hasCokernels

variable [Limits.HasCokernels C]

/-- Auxiliary construction for `coimage_iso_image` -/
def cokernelIso {X Y : C} (f : X ⟶ Y) : G.obj (cokernel (F.map f)) ≅ cokernel f :=
  by
  -- We have to write an explicit `preserves_colimits` type here,
  -- as `left_adjoint_preserves_colimits` has universe variables.
  haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits
  calc
    G.obj (cokernel (F.map f)) ≅ cokernel (G.map (F.map f)) :=
      (as_iso (cokernel_comparison _ G)).symm
    _ ≅ cokernel (_ ≫ f ≫ _) := (cokernel_iso_of_eq (nat_iso.naturality_2 i f).symm)
    _ ≅ cokernel (f ≫ _) := (cokernel_epi_comp _ _)
    _ ≅ cokernel f := cokernel_comp_is_iso _ _
    
#align category_theory.abelian_of_adjunction.cokernel_iso CategoryTheory.AbelianOfAdjunction.cokernelIso

variable [Limits.HasKernels C] [PreservesFiniteLimits G]

/-- Auxiliary construction for `coimage_iso_image` -/
def coimageIsoImageAux {X Y : C} (f : X ⟶ Y) :
    kernel (G.map (cokernel.π (F.map f))) ≅ kernel (cokernel.π f) :=
  by
  haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits
  calc
    kernel (G.map (cokernel.π (F.map f))) ≅
        kernel (cokernel.π (G.map (F.map f)) ≫ cokernel_comparison (F.map f) G) :=
      kernel_iso_of_eq (π_comp_cokernel_comparison _ _).symm
    _ ≅ kernel (cokernel.π (G.map (F.map f))) := (kernel_comp_mono _ _)
    _ ≅ kernel (cokernel.π (_ ≫ f ≫ _) ≫ (cokernel_iso_of_eq _).Hom) :=
      (kernel_iso_of_eq (π_comp_cokernel_iso_of_eq_hom (nat_iso.naturality_2 i f)).symm)
    _ ≅ kernel (cokernel.π (_ ≫ f ≫ _)) := (kernel_comp_mono _ _)
    _ ≅ kernel (cokernel.π (f ≫ i.inv.app Y) ≫ (cokernel_epi_comp (i.hom.app X) _).inv) :=
      (kernel_iso_of_eq (by simp only [cokernel.π_desc, cokernel_epi_comp_inv]))
    _ ≅ kernel (cokernel.π (f ≫ _)) := (kernel_comp_mono _ _)
    _ ≅ kernel (inv (i.inv.app Y) ≫ cokernel.π f ≫ (cokernel_comp_is_iso f (i.inv.app Y)).inv) :=
      (kernel_iso_of_eq
        (by
          simp only [cokernel.π_desc, cokernel_comp_is_iso_inv, iso.hom_inv_id_app_assoc,
            nat_iso.inv_inv_app]))
    _ ≅ kernel (cokernel.π f ≫ _) := (kernel_is_iso_comp _ _)
    _ ≅ kernel (cokernel.π f) := kernel_comp_mono _ _
    
#align category_theory.abelian_of_adjunction.coimage_iso_image_aux CategoryTheory.AbelianOfAdjunction.coimageIsoImageAux

variable [Functor.PreservesZeroMorphisms F]

/-- Auxiliary definition: the abelian coimage and abelian image agree.
We still need to check that this agrees with the canonical morphism.
-/
def coimageIsoImage {X Y : C} (f : X ⟶ Y) : Abelian.coimage f ≅ Abelian.image f :=
  by
  haveI : preserves_limits F := adj.right_adjoint_preserves_limits
  haveI : preserves_colimits G := adj.left_adjoint_preserves_colimits
  calc
    abelian.coimage f ≅ cokernel (kernel.ι f) := iso.refl _
    _ ≅ G.obj (cokernel (F.map (kernel.ι f))) := (cokernel_iso _ _ i adj _).symm
    _ ≅ G.obj (cokernel (kernel_comparison f F ≫ kernel.ι (F.map f))) :=
      (G.map_iso (cokernel_iso_of_eq (by simp)))
    _ ≅ G.obj (cokernel (kernel.ι (F.map f))) := (G.map_iso (cokernel_epi_comp _ _))
    _ ≅ G.obj (abelian.coimage (F.map f)) := (iso.refl _)
    _ ≅ G.obj (abelian.image (F.map f)) := (G.map_iso (abelian.coimage_iso_image _))
    _ ≅ G.obj (kernel (cokernel.π (F.map f))) := (iso.refl _)
    _ ≅ kernel (G.map (cokernel.π (F.map f))) := (preserves_kernel.iso _ _)
    _ ≅ kernel (cokernel.π f) := (coimage_iso_image_aux F G i adj f)
    _ ≅ abelian.image f := iso.refl _
    
#align category_theory.abelian_of_adjunction.coimage_iso_image CategoryTheory.AbelianOfAdjunction.coimageIsoImage

attribute [local simp] cokernel_iso coimage_iso_image coimage_iso_image_aux

-- The account of this proof in the Stacks project omits this calculation.
theorem coimageIsoImage_hom {X Y : C} (f : X ⟶ Y) :
    (coimageIsoImage F G i adj f).Hom = Abelian.coimageImageComparison f :=
  by
  ext
  simpa only [← G.map_comp_assoc, coimage_iso_image, nat_iso.inv_inv_app, cokernel_iso,
    coimage_iso_image_aux, iso.trans_symm, iso.symm_symm_eq, iso.refl_trans, iso.trans_refl,
    iso.trans_hom, iso.symm_hom, cokernel_comp_is_iso_inv, cokernel_epi_comp_inv, as_iso_hom,
    functor.map_iso_hom, cokernel_epi_comp_hom, preserves_kernel.iso_hom, kernel_comp_mono_hom,
    kernel_is_iso_comp_hom, cokernel_iso_of_eq_hom_comp_desc_assoc, cokernel.π_desc_assoc,
    category.assoc, π_comp_cokernel_iso_of_eq_inv_assoc, π_comp_cokernel_comparison_assoc,
    kernel.lift_ι, kernel.lift_ι_assoc, kernel_iso_of_eq_hom_comp_ι_assoc,
    kernel_comparison_comp_ι_assoc, abelian.coimage_image_factorisation] using
    nat_iso.naturality_1 i f
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
  haveI := has_kernels F G i
  haveI := has_cokernels F G i adj
  have : ∀ {X Y : C} (f : X ⟶ Y), is_iso (abelian.coimage_image_comparison f) :=
    by
    intro X Y f
    rw [← coimage_iso_image_hom F G i adj f]
    infer_instance
  apply abelian.of_coimage_image_comparison_is_iso
#align category_theory.abelian_of_adjunction CategoryTheory.abelianOfAdjunction

/-- If `C` is an additive category equivalent to an abelian category `D`
via a functor that preserves zero morphisms,
then `C` is also abelian.
-/
def abelianOfEquivalence {C : Type u₁} [Category.{v} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v} D] [Abelian D] (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]
    [IsEquivalence F] : Abelian C :=
  abelianOfAdjunction F F.inv F.asEquivalence.unitIso.symm F.asEquivalence.symm.toAdjunction
#align category_theory.abelian_of_equivalence CategoryTheory.abelianOfEquivalence

end CategoryTheory

