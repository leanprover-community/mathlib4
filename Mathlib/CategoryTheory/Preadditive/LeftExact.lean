/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

#align_import category_theory.preadditive.left_exact from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Left exactness of functors between preadditive categories

We show that a functor is left exact in the sense that it preserves finite limits, if it
preserves kernels. The dual result holds for right exact functors and cokernels.
## Main results
* We first derive preservation of binary product in the lemma
  `preservesBinaryProductsOfPreservesKernels`,
* then show the preservation of equalizers in `preservesEqualizerOfPreservesKernels`,
* and then derive the preservation of all finite limits with the usual construction.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Preadditive

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive D] (F : C ⥤ D) [PreservesZeroMorphisms F]

section FiniteLimits

/-- A functor between preadditive categories which preserves kernels preserves that an
arbitrary binary fan is a limit.
-/
def isLimitMapConeBinaryFanOfPreservesKernels {X Y Z : C} (π₁ : Z ⟶ X) (π₂ : Z ⟶ Y)
    [PreservesLimit (parallelPair π₂ 0) F] (i : IsLimit (BinaryFan.mk π₁ π₂)) :
    IsLimit (F.mapCone (BinaryFan.mk π₁ π₂)) := by
  let bc := BinaryBicone.ofLimitCone i
  let presf : PreservesLimit (parallelPair bc.snd 0) F := by simpa
  let hf : IsLimit bc.sndKernelFork := BinaryBicone.isLimitSndKernelFork i
  exact (isLimitMapConeBinaryFanEquiv F π₁ π₂).invFun
    (BinaryBicone.isBilimitOfKernelInl (F.mapBinaryBicone bc)
    (isLimitMapConeForkEquiv' F bc.inl_snd (isLimitOfPreserves F hf))).isLimit
#align category_theory.functor.is_limit_map_cone_binary_fan_of_preserves_kernels CategoryTheory.Functor.isLimitMapConeBinaryFanOfPreservesKernels

/-- A kernel preserving functor between preadditive categories preserves any pair being a limit. -/
def preservesBinaryProductOfPreservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] {X Y : C} :
    PreservesLimit (pair X Y) F where
  preserves {c} hc :=
    IsLimit.ofIsoLimit
      (isLimitMapConeBinaryFanOfPreservesKernels F _ _ (IsLimit.ofIsoLimit hc (isoBinaryFanMk c)))
      ((Cones.functoriality _ F).mapIso (isoBinaryFanMk c).symm)
#align category_theory.functor.preserves_binary_product_of_preserves_kernels CategoryTheory.Functor.preservesBinaryProductOfPreservesKernels

attribute [local instance] preservesBinaryProductOfPreservesKernels

/-- A kernel preserving functor between preadditive categories preserves binary products. -/
def preservesBinaryProductsOfPreservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
  PreservesLimitsOfShape (Discrete WalkingPair) F where
    preservesLimit := preservesLimitOfIsoDiagram F (diagramIsoPair _).symm
#align category_theory.functor.preserves_binary_products_of_preserves_kernels CategoryTheory.Functor.preservesBinaryProductsOfPreservesKernels

attribute [local instance] preservesBinaryProductsOfPreservesKernels

variable [HasBinaryBiproducts C]

/-- A functor between preadditive categories preserves the equalizer of two
morphisms if it preserves all kernels. -/
def preservesEqualizerOfPreservesKernels [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F]
    {X Y : C} (f g : X ⟶ Y) : PreservesLimit (parallelPair f g) F := by
  letI := preservesBinaryBiproductsOfPreservesBinaryProducts F
  haveI := additive_of_preservesBinaryBiproducts F
  constructor; intro c i
  let c' := isLimitKernelForkOfFork (i.ofIsoLimit (Fork.isoForkOfι c))
  dsimp only [kernelForkOfFork_ofι] at c'
  let iFc := isLimitForkMapOfIsLimit' F _ c'
  apply IsLimit.ofIsoLimit _ ((Cones.functoriality _ F).mapIso (Fork.isoForkOfι c).symm)
  apply (isLimitMapConeForkEquiv F (Fork.condition c)).invFun
  let p : parallelPair (F.map (f - g)) 0 ≅ parallelPair (F.map f - F.map g) 0 :=
    parallelPair.eqOfHomEq F.map_sub rfl
  exact
    IsLimit.ofIsoLimit
      (isLimitForkOfKernelFork ((IsLimit.postcomposeHomEquiv p _).symm iFc))
      (Fork.ext (Iso.refl _) (by simp [p]))
#align category_theory.functor.preserves_equalizer_of_preserves_kernels CategoryTheory.Functor.preservesEqualizerOfPreservesKernels

/-- A functor between preadditive categories preserves all equalizers if it preserves all kernels.
-/
def preservesEqualizersOfPreservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesLimitsOfShape WalkingParallelPair F where
  preservesLimit {K} := by
    letI := preservesEqualizerOfPreservesKernels F (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)
    apply preservesLimitOfIsoDiagram F (diagramIsoParallelPair K).symm
#align category_theory.functor.preserves_equalizers_of_preserves_kernels CategoryTheory.Functor.preservesEqualizersOfPreservesKernels

/-- A functor between preadditive categories which preserves kernels preserves all finite limits.
-/
def preservesFiniteLimitsOfPreservesKernels [HasFiniteProducts C] [HasEqualizers C]
    [HasZeroObject C] [HasZeroObject D] [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesFiniteLimits F := by
  letI := preservesEqualizersOfPreservesKernels F
  letI := preservesTerminalObjectOfPreservesZeroMorphisms F
  letI := preservesLimitsOfShapePemptyOfPreservesTerminal F
  letI : PreservesFiniteProducts F := ⟨preservesFiniteProductsOfPreservesBinaryAndTerminal F⟩
  exact preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts F
#align category_theory.functor.preserves_finite_limits_of_preserves_kernels CategoryTheory.Functor.preservesFiniteLimitsOfPreservesKernels

end FiniteLimits

section FiniteColimits

/-- A functor between preadditive categories which preserves cokernels preserves finite coproducts.
-/
def isColimitMapCoconeBinaryCofanOfPreservesCokernels {X Y Z : C} (ι₁ : X ⟶ Z) (ι₂ : Y ⟶ Z)
    [PreservesColimit (parallelPair ι₂ 0) F] (i : IsColimit (BinaryCofan.mk ι₁ ι₂)) :
    IsColimit (F.mapCocone (BinaryCofan.mk ι₁ ι₂)) := by
  let bc := BinaryBicone.ofColimitCocone i
  let presf : PreservesColimit (parallelPair bc.inr 0) F := by simpa
  let hf : IsColimit bc.inrCokernelCofork := BinaryBicone.isColimitInrCokernelCofork i
  exact
    (isColimitMapCoconeBinaryCofanEquiv F ι₁ ι₂).invFun
      (BinaryBicone.isBilimitOfCokernelFst (F.mapBinaryBicone bc)
          (isColimitMapCoconeCoforkEquiv' F bc.inr_fst (isColimitOfPreserves F hf))).isColimit
#align category_theory.functor.is_colimit_map_cocone_binary_cofan_of_preserves_cokernels CategoryTheory.Functor.isColimitMapCoconeBinaryCofanOfPreservesCokernels

/-- A cokernel preserving functor between preadditive categories preserves any pair being
a colimit. -/
def preservesCoproductOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] {X Y : C} :
    PreservesColimit (pair X Y) F where
  preserves {c} hc :=
    IsColimit.ofIsoColimit
      (isColimitMapCoconeBinaryCofanOfPreservesCokernels F _ _
        (IsColimit.ofIsoColimit hc (isoBinaryCofanMk c)))
      ((Cocones.functoriality _ F).mapIso (isoBinaryCofanMk c).symm)
#align category_theory.functor.preserves_coproduct_of_preserves_cokernels CategoryTheory.Functor.preservesCoproductOfPreservesCokernels

attribute [local instance] preservesCoproductOfPreservesCokernels

/-- A cokernel preserving functor between preadditive categories preserves binary coproducts. -/
def preservesBinaryCoproductsOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    PreservesColimitsOfShape (Discrete WalkingPair) F where
  preservesColimit := preservesColimitOfIsoDiagram F (diagramIsoPair _).symm
#align category_theory.functor.preserves_binary_coproducts_of_preserves_cokernels CategoryTheory.Functor.preservesBinaryCoproductsOfPreservesCokernels

attribute [local instance] preservesBinaryCoproductsOfPreservesCokernels

variable [HasBinaryBiproducts C]

/-- A functor between preadditive categories preserves the coequalizer of two
morphisms if it preserves all cokernels. -/
def preservesCoequalizerOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] {X Y : C} (f g : X ⟶ Y) :
    PreservesColimit (parallelPair f g) F := by
  letI := preservesBinaryBiproductsOfPreservesBinaryCoproducts F
  haveI := additive_of_preservesBinaryBiproducts F
  constructor
  intro c i
  let c' := isColimitCokernelCoforkOfCofork (i.ofIsoColimit (Cofork.isoCoforkOfπ c))
  dsimp only [cokernelCoforkOfCofork_ofπ] at c'
  let iFc := isColimitCoforkMapOfIsColimit' F _ c'
  apply
    IsColimit.ofIsoColimit _ ((Cocones.functoriality _ F).mapIso (Cofork.isoCoforkOfπ c).symm)
  apply (isColimitMapCoconeCoforkEquiv F (Cofork.condition c)).invFun
  let p : parallelPair (F.map (f - g)) 0 ≅ parallelPair (F.map f - F.map g) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  exact
    IsColimit.ofIsoColimit
      (isColimitCoforkOfCokernelCofork ((IsColimit.precomposeHomEquiv p.symm _).symm iFc))
      (Cofork.ext (Iso.refl _) (by simp [p]))
#align category_theory.functor.preserves_coequalizer_of_preserves_cokernels CategoryTheory.Functor.preservesCoequalizerOfPreservesCokernels

/-- A functor between preadditive categories preserves all coequalizers if it preserves all kernels.
-/
def preservesCoequalizersOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    PreservesColimitsOfShape WalkingParallelPair F where
  preservesColimit {K} := by
    letI := preservesCoequalizerOfPreservesCokernels F (K.map Limits.WalkingParallelPairHom.left)
        (K.map Limits.WalkingParallelPairHom.right)
    apply preservesColimitOfIsoDiagram F (diagramIsoParallelPair K).symm
#align category_theory.functor.preserves_coequalizers_of_preserves_cokernels CategoryTheory.Functor.preservesCoequalizersOfPreservesCokernels

/-- A functor between preadditive categories which preserves kernels preserves all finite limits.
-/
def preservesFiniteColimitsOfPreservesCokernels [HasFiniteCoproducts C] [HasCoequalizers C]
    [HasZeroObject C] [HasZeroObject D]
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] : PreservesFiniteColimits F := by
  letI := preservesCoequalizersOfPreservesCokernels F
  letI := preservesInitialObjectOfPreservesZeroMorphisms F
  letI := preservesColimitsOfShapePemptyOfPreservesInitial F
  letI : PreservesFiniteCoproducts F := ⟨preservesFiniteCoproductsOfPreservesBinaryAndInitial F⟩
  exact preservesFiniteColimitsOfPreservesCoequalizersAndFiniteCoproducts F
#align category_theory.functor.preserves_finite_colimits_of_preserves_cokernels CategoryTheory.Functor.preservesFiniteColimitsOfPreservesCokernels

end FiniteColimits

end Functor

end CategoryTheory
