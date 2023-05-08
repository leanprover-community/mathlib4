import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Abelian.Basic

namespace CategoryTheory

open Category Limits

variable {C D : Type _} [Category C] [Abelian C] [Category D] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

namespace ShortComplex

noncomputable def abelianImageToKernel :
    Abelian.image S.f ⟶ kernel S.g :=
  kernel.lift S.g (Abelian.image.ι S.f)
    (by simp only [← cancel_epi (Abelian.factorThruImage S.f),
      kernel.lift_ι_assoc, zero, comp_zero])

@[reassoc (attr := simp)]
lemma abelianImageToKernel_comp_kernel_ι :
  S.abelianImageToKernel ≫ kernel.ι S.g = Abelian.image.ι S.f := kernel.lift_ι _ _ _

instance : Mono S.abelianImageToKernel :=
  mono_of_mono_fac S.abelianImageToKernel_comp_kernel_ι

@[reassoc (attr := simp 1100)]
lemma abelianImageToKernel_comp_kernel_ι_comp_cokernel_π :
  S.abelianImageToKernel ≫ kernel.ι S.g ≫ cokernel.π S.f = 0 := by simp

noncomputable def abelianImageToKernelIsKernel :
  IsLimit (KernelFork.ofι S.abelianImageToKernel
    S.abelianImageToKernel_comp_kernel_ι_comp_cokernel_π) :=
  KernelFork.IsLimit.ofι _ _
    (fun k hk => kernel.lift _ (k ≫ kernel.ι S.g) (by rw [assoc, hk]))
    (fun k hk => by simp only [← cancel_mono (kernel.ι S.g), assoc,
      abelianImageToKernel_comp_kernel_ι, kernel.lift_ι])
    (fun k hk b hb => by simp only [← cancel_mono S.abelianImageToKernel,
      ← cancel_mono (kernel.ι S.g), hb, assoc, abelianImageToKernel_comp_kernel_ι, kernel.lift_ι])

namespace LeftHomologyData

@[simps]
noncomputable def ofAbelian : S.LeftHomologyData := by
  let γ := kernel.ι S.g ≫ cokernel.π S.f
  let f' := kernel.lift S.g S.f S.zero
  have hf' : f' = kernel.lift γ f' (by simp) ≫ kernel.ι γ := by rw [kernel.lift_ι]
  have wπ : f' ≫ cokernel.π (kernel.ι γ) = 0 := by
    rw [hf']
    simp only [assoc, cokernel.condition, comp_zero]
  let e : Abelian.image S.f ≅ kernel γ :=
    IsLimit.conePointUniqueUpToIso S.abelianImageToKernelIsKernel (limit.isLimit _)
  have he : e.hom ≫ kernel.ι γ = S.abelianImageToKernel :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have fac : f' = Abelian.factorThruImage S.f ≫ e.hom ≫ kernel.ι γ := by
    rw [hf', he]
    simp only [kernel.lift_ι, abelianImageToKernel, ← cancel_mono (kernel.ι S.g), assoc]
  have hπ : IsColimit (CokernelCofork.ofπ _ wπ) :=
    CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => cokernel.desc _ x (by
      simpa only [← cancel_epi e.hom, ← cancel_epi (Abelian.factorThruImage S.f),
        comp_zero, fac, assoc] using hx))
    (fun x hx => cokernel.π_desc _ _ _)
    (fun x hx b hb => coequalizer.hom_ext (by simp only [hb, cokernel.π_desc]))
  exact
  { K := kernel S.g,
    H := Abelian.coimage (kernel.ι S.g ≫ cokernel.π S.f)
    i := kernel.ι _
    π := cokernel.π _
    wi := kernel.condition _
    hi := kernelIsKernel _
    wπ := wπ
    hπ := hπ }

end LeftHomologyData

noncomputable def cokernelToAbelianCoimage :
    cokernel S.f ⟶ Abelian.coimage S.g :=
  cokernel.desc S.f (Abelian.coimage.π S.g) (by
    simp only [← cancel_mono (Abelian.factorThruCoimage S.g), assoc,
      cokernel.π_desc, zero, zero_comp])

@[reassoc (attr := simp)]
lemma cokernel_π_comp_cokernelToAbelianCoimage :
  cokernel.π S.f ≫ S.cokernelToAbelianCoimage = Abelian.coimage.π S.g := cokernel.π_desc _ _ _

instance : Epi S.cokernelToAbelianCoimage :=
  epi_of_epi_fac S.cokernel_π_comp_cokernelToAbelianCoimage

lemma kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage :
  (kernel.ι S.g ≫ cokernel.π S.f) ≫ S.cokernelToAbelianCoimage = 0 := by simp

noncomputable def cokernelToAbelianCoimageIsCokernel :
  IsColimit (CokernelCofork.ofπ S.cokernelToAbelianCoimage
    S.kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun k hk => cokernel.desc _ (cokernel.π S.f ≫ k) (by simpa only [assoc] using hk))
    (fun k hk => by simp only [← cancel_epi (cokernel.π S.f),
        cokernel_π_comp_cokernelToAbelianCoimage_assoc, cokernel.π_desc])
    (fun k hk b hb => by
      simp only [← cancel_epi S.cokernelToAbelianCoimage, ← cancel_epi (cokernel.π S.f), hb,
        cokernel_π_comp_cokernelToAbelianCoimage_assoc, cokernel.π_desc])

namespace RightHomologyData

@[simps]
noncomputable def ofAbelian : S.RightHomologyData := by
  let γ := kernel.ι S.g ≫ cokernel.π S.f
  let g' := cokernel.desc S.f S.g S.zero
  have hg' : g' = cokernel.π γ ≫ cokernel.desc γ g' (by simp) := by rw [cokernel.π_desc]
  have wι : kernel.ι (cokernel.π γ) ≫ g' = 0 := by rw [hg', kernel.condition_assoc, zero_comp]
  let e : cokernel γ ≅ Abelian.coimage S.g :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) S.cokernelToAbelianCoimageIsCokernel
  have he : cokernel.π γ ≫ e.hom = S.cokernelToAbelianCoimage :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one
  have fac : g' = cokernel.π γ ≫ e.hom ≫ Abelian.factorThruCoimage S.g := by
    rw [hg', reassoc_of% he]
    simp only [cokernel.π_desc, ← cancel_epi (cokernel.π S.f),
      cokernel_π_comp_cokernelToAbelianCoimage_assoc]
  have hι : IsLimit (KernelFork.ofι _ wι) :=
    KernelFork.IsLimit.ofι _ _
      (fun x hx => kernel.lift _ x (by
        simpa only [← cancel_mono e.hom, ← cancel_mono (Abelian.factorThruCoimage S.g), assoc,
          zero_comp, fac] using hx))
      (fun x hx => kernel.lift_ι _ _ _)
      (fun x hx b hb => equalizer.hom_ext (by simp only [hb, kernel.lift_ι]))
  exact
  { Q := cokernel S.f,
    H := Abelian.image (kernel.ι S.g ≫ cokernel.π S.f)
    p := cokernel.π _
    ι := kernel.ι _
    wp := cokernel.condition _
    hp := cokernelIsCokernel _
    wι := wι
    hι := hι }

end RightHomologyData

noncomputable def HomologyData.ofAbelian : S.HomologyData where
  left := LeftHomologyData.ofAbelian S
  right := RightHomologyData.ofAbelian S
  iso := Abelian.coimageIsoImage (kernel.ι S.g ≫ cokernel.π S.f)

instance _root_.CategoryTheory.categoryWithHomology_of_abelian :
    CategoryWithHomology C where
  hasHomology S := HasHomology.mk' (HomologyData.ofAbelian S)

noncomputable def isLimit_mapCone_of_kernelFork_ofι_cokernel_condition_of_mono
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

noncomputable instance : NormalMonoCategory (ShortComplex C) := ⟨fun i _ => by
  refine' NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (isLimit_of_isLimitπ _ _ _ _ )
  all_goals apply isLimit_mapCone_of_kernelFork_ofι_cokernel_condition_of_mono⟩

noncomputable def isColimit_mapCocone_of_cokernelCofork_ofπ_kernel_condition_of_epi
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

noncomputable instance : NormalEpiCategory (ShortComplex C) := ⟨fun p _ => by
  refine' NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimit_of_isColimitπ _ _ _ _ )
  all_goals apply isColimit_mapCocone_of_cokernelCofork_ofπ_kernel_condition_of_epi⟩

noncomputable instance : Abelian (ShortComplex C) where

end ShortComplex

end CategoryTheory
