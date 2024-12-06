/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# A balanced additive category with homology is abelian

-/

namespace CategoryTheory

open Limits ZeroObject Preadditive

variable (C : Type*) [Category C] [Preadditive C] [CategoryWithHomology C]

namespace AbelianOfCategoryWithHomologyOfBalanced

lemma hasKernels : HasKernels C where
  has_limit {X Y} f := ⟨_, (ShortComplex.mk (0 : X ⟶ X) f (by simp)).leftHomologyData.hi⟩

lemma hasCokernels : HasCokernels C where
  has_colimit {X Y} g := ⟨_, (ShortComplex.mk g (0 : Y ⟶ Y) (by simp)).rightHomologyData.hp⟩

end AbelianOfCategoryWithHomologyOfBalanced

attribute [local instance] AbelianOfCategoryWithHomologyOfBalanced.hasKernels
  AbelianOfCategoryWithHomologyOfBalanced.hasCokernels

variable [HasFiniteProducts C] [Balanced C]

noncomputable def abelianOfCategoryWithHomologyOfBalanced : Abelian C where
  normalMonoOfMono f _ := ⟨_, _, _,
    ((ShortComplex.mk _ _ (cokernel.condition f)).exact_of_g_is_cokernel
      (cokernelIsCokernel _)).fIsKernel⟩
  normalEpiOfEpi f _ := ⟨_, _, _,
    ((ShortComplex.mk _ _ (kernel.condition f)).exact_of_f_is_kernel
      (kernelIsKernel _)).gIsCokernel⟩

end CategoryTheory
