/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.Additive

open CategoryTheory Category Limits

noncomputable def _root_.CategoryTheory.Limits.isLimit_mapCone_of_kernelFork_ofι_cokernel_condition_of_mono
    {C D : Type*} [Category C] [Category D] [Abelian C] [HasZeroMorphisms D]
    {X Y : D} (i : X ⟶ Y) [HasCokernel i] (F : D ⥤ C)
    [F.PreservesZeroMorphisms] [Mono (F.map i)]
    [PreservesColimit (parallelPair i 0) F] :
    IsLimit (F.mapCone (KernelFork.ofι i (cokernel.condition i))) := by
  let e : parallelPair (cokernel.π (F.map i)) 0 ≅ parallelPair (cokernel.π i) 0 ⋙ F :=
    parallelPair.ext (Iso.refl _) (asIso (cokernelComparison i F)) (by simp) (by simp)
  refine' IsLimit.postcomposeInvEquiv e _ _
  let hi := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (F.map i))
  refine' IsLimit.ofIsoLimit hi (Fork.ext (Iso.refl _) _)
  change 𝟙 _ ≫ F.map i ≫ 𝟙 _ = F.map i
  rw [comp_id, id_comp]

noncomputable def _root_.CategoryTheory.Limits.isColimit_mapCocone_of_cokernelCofork_ofπ_kernel_condition_of_epi
    {C D : Type*} [Category C] [Category D] [Abelian C] [HasZeroMorphisms D]
    {X Y : D} (p : X ⟶ Y) [HasKernel p] (F : D ⥤ C)
    [F.PreservesZeroMorphisms] [Epi (F.map p)]
    [PreservesLimit (parallelPair p 0) F] :
    IsColimit (F.mapCocone (CokernelCofork.ofπ p (kernel.condition p))) := by
  let e : parallelPair (kernel.ι p) 0 ⋙ F ≅ parallelPair (kernel.ι (F.map p)) 0 := by
    refine' parallelPair.ext (asIso (kernelComparison p F)) (Iso.refl _) (by simp) (by simp)
  refine' IsColimit.precomposeInvEquiv e _ _
  let hp := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (F.map p))
  refine' IsColimit.ofIsoColimit hp (Cofork.ext (Iso.refl _) _)
  change F.map p ≫ 𝟙 _ = 𝟙 _ ≫ F.map p
  rw [comp_id, id_comp]

namespace HomologicalComplex

variable {C ι : Type*} {c : ComplexShape ι} [Category C] [Abelian C]

noncomputable instance : NormalEpiCategory (HomologicalComplex C c) := ⟨fun p _ =>
  NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfEval _ _ (fun _ =>
      isColimit_mapCocone_of_cokernelCofork_ofπ_kernel_condition_of_epi _ _))⟩

noncomputable instance : NormalMonoCategory (HomologicalComplex C c) := ⟨fun p _ =>
  NormalMono.mk _ (cokernel.π p) (cokernel.condition _)
    (isLimitOfEval _ _ (fun _ =>
      isLimit_mapCone_of_kernelFork_ofι_cokernel_condition_of_mono _ _))⟩

noncomputable instance : Abelian (HomologicalComplex C c) where

variable (S : ShortComplex (HomologicalComplex C c))

lemma exact_of_degreewise_exact (hS : ∀ (i : ι), (S.map (eval C c i)).Exact) :
    S.Exact := by
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [IsZero.iff_id_eq_zero]
  ext i
  apply (IsZero.of_iso (hS i) (S.mapHomologyIso (eval C c i)).symm).eq_of_src

lemma shortExact_of_degreewise_shortExact
    (hS : ∀ (i : ι), (S.map (eval C c i)).ShortExact) :
    S.ShortExact where
  mono_f := mono_of_mono_f _ (fun i => (hS i).mono_f)
  epi_g := epi_of_epi_f _ (fun i => (hS i).epi_g)
  exact := exact_of_degreewise_exact S (fun i => (hS i).exact)

end HomologicalComplex
