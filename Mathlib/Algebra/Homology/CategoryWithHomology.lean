import Mathlib.Algebra.Homology.ShortComplex.ShortExact

namespace CategoryTheory

open Limits ZeroObject Preadditive

variable (C : Type*) [Category C] [Preadditive C] [CategoryWithHomology C]
  [HasFiniteProducts C] [Balanced C]

namespace AbelianOfCategoryWithHomologyOfBalanced

lemma hasKernels : HasKernels C where
  has_limit {X Y} f := ⟨_, (ShortComplex.mk (0 : X ⟶ X) f (by simp)).leftHomologyData.hi⟩

lemma hasCokernels : HasCokernels C where
  has_colimit {X Y} g := ⟨_, (ShortComplex.mk g (0 : Y ⟶ Y) (by simp)).rightHomologyData.hp⟩

end AbelianOfCategoryWithHomologyOfBalanced

attribute [local instance] AbelianOfCategoryWithHomologyOfBalanced.hasKernels
  AbelianOfCategoryWithHomologyOfBalanced.hasCokernels

noncomputable def abelianOfCategoryWithHomologyOfBalanced : Abelian C where
  normalMonoOfMono f _ := ⟨_, _, _,
    ((ShortComplex.mk _ _ (cokernel.condition f)).exact_of_g_is_cokernel
      (cokernelIsCokernel _)).fIsKernel⟩
  normalEpiOfEpi f _ := ⟨_, _, _,
    ((ShortComplex.mk _ _ (kernel.condition f)).exact_of_f_is_kernel
      (kernelIsKernel _)).gIsCokernel⟩

end CategoryTheory
