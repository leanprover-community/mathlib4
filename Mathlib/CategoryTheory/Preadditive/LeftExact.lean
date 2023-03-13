/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.preadditive.left_exact
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Left exactness of functors between preadditive categories

We show that a functor is left exact in the sense that it preserves finite limits, if it
preserves kernels. The dual result holds for right exact functors and cokernels.
## Main results
* We first derive preservation of binary product in the lemma
  `preserves_binary_products_of_preserves_kernels`,
* then show the preservation of equalizers in `preserves_equalizer_of_preserves_kernels`,
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
    IsLimit (F.mapCone (BinaryFan.mk π₁ π₂)) :=
  by
  let bc := binary_bicone.of_limit_cone i
  let presf : preserves_limit (parallel_pair bc.snd 0) F := by simpa
  let hf : is_limit bc.snd_kernel_fork := binary_bicone.is_limit_snd_kernel_fork i
  exact
    (is_limit_map_cone_binary_fan_equiv F π₁ π₂).invFun
      (binary_bicone.is_bilimit_of_kernel_inl (F.map_binary_bicone bc)
          (is_limit_map_cone_fork_equiv' F _ (is_limit_of_preserves F hf))).IsLimit
#align category_theory.functor.is_limit_map_cone_binary_fan_of_preserves_kernels CategoryTheory.Functor.isLimitMapConeBinaryFanOfPreservesKernels

/-- A kernel preserving functor between preadditive categories preserves any pair being a limit. -/
def preservesBinaryProductOfPreservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] {X Y : C} :
    PreservesLimit (pair X Y) F
    where preserves c hc :=
    IsLimit.ofIsoLimit
      (isLimitMapConeBinaryFanOfPreservesKernels F _ _ (IsLimit.ofIsoLimit hc (isoBinaryFanMk c)))
      ((Cones.functoriality _ F).mapIso (isoBinaryFanMk c).symm)
#align category_theory.functor.preserves_binary_product_of_preserves_kernels CategoryTheory.Functor.preservesBinaryProductOfPreservesKernels

attribute [local instance] preserves_binary_product_of_preserves_kernels

/-- A kernel preserving functor between preadditive categories preserves binary products. -/
def preservesBinaryProductsOfPreservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesLimitsOfShape (Discrete WalkingPair) F
    where PreservesLimit p := preservesLimitOfIsoDiagram F (diagramIsoPair p).symm
#align category_theory.functor.preserves_binary_products_of_preserves_kernels CategoryTheory.Functor.preservesBinaryProductsOfPreservesKernels

attribute [local instance] preserves_binary_products_of_preserves_kernels

variable [HasBinaryBiproducts C]

/-- A functor between preadditive categories preserves the equalizer of two
morphisms if it preserves all kernels. -/
def preservesEqualizerOfPreservesKernels [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F]
    {X Y : C} (f g : X ⟶ Y) : PreservesLimit (parallelPair f g) F :=
  by
  letI := preserves_binary_biproducts_of_preserves_binary_products F
  haveI := additive_of_preserves_binary_biproducts F
  constructor; intro c i
  let c' := is_limit_kernel_fork_of_fork (i.of_iso_limit (fork.iso_fork_of_ι c))
  dsimp only [kernel_fork_of_fork_of_ι] at c'
  let iFc := is_limit_fork_map_of_is_limit' F _ c'
  apply is_limit.of_iso_limit _ ((cones.functoriality _ F).mapIso (fork.iso_fork_of_ι c).symm)
  apply (is_limit_map_cone_fork_equiv F (fork.condition c)).invFun
  let p : parallel_pair (F.map (f - g)) 0 ≅ parallel_pair (F.map f - F.map g) 0 :=
    parallel_pair.eq_of_hom_eq F.map_sub rfl
  refine'
    is_limit.of_iso_limit
      (is_limit_fork_of_kernel_fork ((is_limit.postcompose_hom_equiv p _).symm iFc)) _
  convert fork.iso_fork_of_ι _
  rw [fork_of_kernel_fork_ι, fork.ι_postcompose, kernel_fork.ι_of_ι,
    parallel_pair.eq_of_hom_eq_hom_app]
  erw [category.comp_id]
#align category_theory.functor.preserves_equalizer_of_preserves_kernels CategoryTheory.Functor.preservesEqualizerOfPreservesKernels

/-- A functor between preadditive categories preserves all equalizers if it preserves all kernels.
-/
def preservesEqualizersOfPreservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesLimitsOfShape WalkingParallelPair F
    where PreservesLimit K :=
    by
    letI :=
      preserves_equalizer_of_preserves_kernels F (K.map walking_parallel_pair_hom.left)
        (K.map walking_parallel_pair_hom.right)
    apply preserves_limit_of_iso_diagram F (diagram_iso_parallel_pair K).symm
#align category_theory.functor.preserves_equalizers_of_preserves_kernels CategoryTheory.Functor.preservesEqualizersOfPreservesKernels

/-- A functor between preadditive categories which preserves kernels preserves all finite limits.
-/
def preservesFiniteLimitsOfPreservesKernels [HasFiniteProducts C] [HasEqualizers C]
    [HasZeroObject C] [HasZeroObject D] [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesFiniteLimits F :=
  by
  letI := preserves_equalizers_of_preserves_kernels F
  letI := preserves_terminal_object_of_preserves_zero_morphisms F
  letI := preserves_limits_of_shape_pempty_of_preserves_terminal F
  letI p_prod := preserves_finite_products_of_preserves_binary_and_terminal F
  apply @preserves_finite_limits_of_preserves_equalizers_and_finite_products _ _ _ _ _ _ _ _ @p_prod
#align category_theory.functor.preserves_finite_limits_of_preserves_kernels CategoryTheory.Functor.preservesFiniteLimitsOfPreservesKernels

end FiniteLimits

section FiniteColimits

/-- A functor between preadditive categories which preserves cokernels preserves finite coproducts.
-/
def isColimitMapCoconeBinaryCofanOfPreservesCokernels {X Y Z : C} (ι₁ : X ⟶ Z) (ι₂ : Y ⟶ Z)
    [PreservesColimit (parallelPair ι₂ 0) F] (i : IsColimit (BinaryCofan.mk ι₁ ι₂)) :
    IsColimit (F.mapCocone (BinaryCofan.mk ι₁ ι₂)) :=
  by
  let bc := binary_bicone.of_colimit_cocone i
  let presf : preserves_colimit (parallel_pair bc.inr 0) F := by simpa
  let hf : is_colimit bc.inr_cokernel_cofork := binary_bicone.is_colimit_inr_cokernel_cofork i
  exact
    (is_colimit_map_cocone_binary_cofan_equiv F ι₁ ι₂).invFun
      (binary_bicone.is_bilimit_of_cokernel_fst (F.map_binary_bicone bc)
          (is_colimit_map_cocone_cofork_equiv' F _ (is_colimit_of_preserves F hf))).IsColimit
#align category_theory.functor.is_colimit_map_cocone_binary_cofan_of_preserves_cokernels CategoryTheory.Functor.isColimitMapCoconeBinaryCofanOfPreservesCokernels

/-- A cokernel preserving functor between preadditive categories preserves any pair being
a colimit. -/
def preservesCoproductOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] {X Y : C} :
    PreservesColimit (pair X Y) F
    where preserves c hc :=
    IsColimit.ofIsoColimit
      (isColimitMapCoconeBinaryCofanOfPreservesCokernels F _ _
        (IsColimit.ofIsoColimit hc (isoBinaryCofanMk c)))
      ((Cocones.functoriality _ F).mapIso (isoBinaryCofanMk c).symm)
#align category_theory.functor.preserves_coproduct_of_preserves_cokernels CategoryTheory.Functor.preservesCoproductOfPreservesCokernels

attribute [local instance] preserves_coproduct_of_preserves_cokernels

/-- A cokernel preserving functor between preadditive categories preserves binary coproducts. -/
def preservesBinaryCoproductsOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    PreservesColimitsOfShape (Discrete WalkingPair) F
    where PreservesColimit p := preservesColimitOfIsoDiagram F (diagramIsoPair p).symm
#align category_theory.functor.preserves_binary_coproducts_of_preserves_cokernels CategoryTheory.Functor.preservesBinaryCoproductsOfPreservesCokernels

attribute [local instance] preserves_binary_coproducts_of_preserves_cokernels

variable [HasBinaryBiproducts C]

/-- A functor between preadditive categoris preserves the coequalizer of two
morphisms if it preserves all cokernels. -/
def preservesCoequalizerOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] {X Y : C} (f g : X ⟶ Y) :
    PreservesColimit (parallelPair f g) F :=
  by
  letI := preserves_binary_biproducts_of_preserves_binary_coproducts F
  haveI := additive_of_preserves_binary_biproducts F
  constructor
  intro c i
  let c' := is_colimit_cokernel_cofork_of_cofork (i.of_iso_colimit (cofork.iso_cofork_of_π c))
  dsimp only [cokernel_cofork_of_cofork_of_π] at c'
  let iFc := is_colimit_cofork_map_of_is_colimit' F _ c'
  apply
    is_colimit.of_iso_colimit _ ((cocones.functoriality _ F).mapIso (cofork.iso_cofork_of_π c).symm)
  apply (is_colimit_map_cocone_cofork_equiv F (cofork.condition c)).invFun
  let p : parallel_pair (F.map (f - g)) 0 ≅ parallel_pair (F.map f - F.map g) 0 :=
    parallel_pair.ext (iso.refl _) (iso.refl _) (by simp) (by simp)
  refine'
    is_colimit.of_iso_colimit
      (is_colimit_cofork_of_cokernel_cofork ((is_colimit.precompose_hom_equiv p.symm _).symm iFc)) _
  convert cofork.iso_cofork_of_π _
  rw [cofork_of_cokernel_cofork_π, cofork.π_precompose, cokernel_cofork.π_of_π, iso.symm_hom,
    parallel_pair.ext_inv_app, iso.refl_inv]
  erw [category.id_comp]
#align category_theory.functor.preserves_coequalizer_of_preserves_cokernels CategoryTheory.Functor.preservesCoequalizerOfPreservesCokernels

/-- A functor between preadditive categories preserves all coequalizers if it preserves all kernels.
-/
def preservesCoequalizersOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    PreservesColimitsOfShape WalkingParallelPair F
    where PreservesColimit K :=
    by
    letI :=
      preserves_coequalizer_of_preserves_cokernels F (K.map limits.walking_parallel_pair_hom.left)
        (K.map limits.walking_parallel_pair_hom.right)
    apply preserves_colimit_of_iso_diagram F (diagram_iso_parallel_pair K).symm
#align category_theory.functor.preserves_coequalizers_of_preserves_cokernels CategoryTheory.Functor.preservesCoequalizersOfPreservesCokernels

/-- A functor between preadditive categories which preserves kernels preserves all finite limits.
-/
def preservesFiniteColimitsOfPreservesCokernels [HasFiniteCoproducts C] [HasCoequalizers C]
    [HasZeroObject C] [HasZeroObject D]
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] : PreservesFiniteColimits F :=
  by
  letI := preserves_coequalizers_of_preserves_cokernels F
  letI := preserves_initial_object_of_preserves_zero_morphisms F
  letI := preserves_colimits_of_shape_pempty_of_preserves_initial F
  letI p_prod := preserves_finite_coproducts_of_preserves_binary_and_initial F
  apply
    @preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts C _ _ _ _ _ _ _
      @p_prod
#align category_theory.functor.preserves_finite_colimits_of_preserves_cokernels CategoryTheory.Functor.preservesFiniteColimitsOfPreservesCokernels

end FiniteColimits

end Functor

end CategoryTheory

