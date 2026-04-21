/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Subcategories of abelian categories

Let `C` be an abelian category. Given `P : ObjectProperty C` which contains
zero, is closed under kernels, cokernels and finite products, we show that the
full subcategory defined by `P` is abelian.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] (P : ObjectProperty C)

lemma preservesMonomorphisms_ι_of_isNormalEpiCategory [HasZeroMorphisms C] [HasFiniteCoproducts C]
    [HasKernels C] [HasCokernels C] [IsNormalEpiCategory C] [HasZeroObject C] [P.ContainsZero]
    [P.IsClosedUnderKernels] : P.ι.PreservesMonomorphisms :=
  have := P.preservesKernels_ι
  NormalEpiCategory.preservesMonomorphisms_of_preservesKernels P.ι

instance [Abelian C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] :
    IsNormalMonoCategory P.FullSubcategory where
  normalMonoOfMono {X Y} f :=
    have := P.preservesMonomorphisms_ι_of_isNormalEpiCategory
    ⟨{Z := .mk _ (P.prop_cokernel f.hom X.property Y.property)
      g := P.homMk (cokernel.π f.hom)
      w := by cat_disch
      isLimit := isLimitOfReflects P.ι ((KernelFork.isLimitMapConeEquiv _ _).symm
        (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (P.ι.map f)) :))}⟩

lemma preservesEpimorphisms_ι_of_isNormalMonoCategory [HasZeroMorphisms C] [HasFiniteProducts C]
    [HasKernels C] [HasCokernels C] [IsNormalMonoCategory C] [HasZeroObject C] [P.ContainsZero]
    [P.IsClosedUnderCokernels] : P.ι.PreservesEpimorphisms :=
  have := P.preservesCokernels_ι
  NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels P.ι

instance [Abelian C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] :
    IsNormalEpiCategory P.FullSubcategory where
  normalEpiOfEpi {X Y} f :=
    have := P.preservesEpimorphisms_ι_of_isNormalMonoCategory
    ⟨{W := .mk _ (P.prop_kernel f.hom X.property Y.property)
      g := P.homMk (kernel.ι f.hom)
      w := by cat_disch
      isColimit := isColimitOfReflects P.ι ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (P.ι.map f)) :))}⟩

instance [Abelian C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderFiniteProducts] : Abelian P.FullSubcategory where

end CategoryTheory.ObjectProperty
