/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ImageToKernel
import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Abelian categories have homology

In this file, it is shown that all short complexes `S` in abelian
categories have terms of type `S.HomologyData`.

The strategy of the proof is to study the morphism
`kernel.ι S.g ≫ cokernel.π S.f`. We show that there is a
`LeftHomologyData` for `S` for which the `H` field consists
of the coimage of `kernel.ι S.g ≫ cokernel.π S.f`, while
there is a `RightHomologyData` for which the `H` is the
image of `kernel.ι S.g ≫ cokernel.π S.f`. The fact that
these left and right homology data are compatible (i.e.
provide a `HomologyData`) is obtained by using the
coimage-image isomorphism in abelian categories.

-/

universe v' u' v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

namespace ShortComplex

/-- The canonical morphism `Abelian.image S.f ⟶ kernel S.g` for a short complex `S`
in an abelian category. -/
noncomputable def abelianImageToKernel : Abelian.image S.f ⟶ kernel S.g :=
  kernel.lift S.g (Abelian.image.ι S.f)
    (by simp only [← cancel_epi (Abelian.factorThruImage S.f),
      kernel.lift_ι_assoc, zero, comp_zero])

@[reassoc (attr := simp)]
lemma abelianImageToKernel_comp_kernel_ι :
    S.abelianImageToKernel ≫ kernel.ι S.g = Abelian.image.ι S.f :=
  kernel.lift_ι _ _ _

instance : Mono S.abelianImageToKernel :=
  mono_of_mono_fac S.abelianImageToKernel_comp_kernel_ι

@[reassoc (attr := simp 1100)]
lemma abelianImageToKernel_comp_kernel_ι_comp_cokernel_π :
    S.abelianImageToKernel ≫ kernel.ι S.g ≫ cokernel.π S.f = 0 := by
  simp only [abelianImageToKernel_comp_kernel_ι_assoc, kernel.condition]

/-- `Abelian.image S.f` is the kernel of `kernel.ι S.g ≫ cokernel.π S.f` -/
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

/-- The canonical `LeftHomologyData` of a short complex `S` in an abelian category, for
which the `H` field is `Abelian.coimage (kernel.ι S.g ≫ cokernel.π S.f)`. -/
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
      i := kernel.ι _,
      π := cokernel.π _
      wi := kernel.condition _
      hi := kernelIsKernel _
      wπ := wπ
      hπ := hπ }

end LeftHomologyData

/-- The canonical morphism `cokernel S.f ⟶ Abelian.coimage S.g` for a short complex `S`
in an abelian category. -/
noncomputable def cokernelToAbelianCoimage : cokernel S.f ⟶ Abelian.coimage S.g :=
  cokernel.desc S.f (Abelian.coimage.π S.g) (by
    simp only [← cancel_mono (Abelian.factorThruCoimage S.g), assoc,
      cokernel.π_desc, zero, zero_comp])

@[reassoc (attr := simp)]
lemma cokernel_π_comp_cokernelToAbelianCoimage :
    cokernel.π S.f ≫ S.cokernelToAbelianCoimage = Abelian.coimage.π S.g :=
  cokernel.π_desc _ _ _

instance : Epi S.cokernelToAbelianCoimage :=
  epi_of_epi_fac S.cokernel_π_comp_cokernelToAbelianCoimage

lemma kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage :
    (kernel.ι S.g ≫ cokernel.π S.f) ≫ S.cokernelToAbelianCoimage = 0 := by simp

/-- `Abelian.coimage S.g` is the cokernel of `kernel.ι S.g ≫ cokernel.π S.f` -/
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

/-- The canonical `RightHomologyData` of a short complex `S` in an abelian category, for
which the `H` field is `Abelian.image (kernel.ι S.g ≫ cokernel.π S.f)`. -/
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

/-- The canonical `HomologyData` of a short complex `S` in an abelian category. -/
noncomputable def HomologyData.ofAbelian : S.HomologyData where
  left := LeftHomologyData.ofAbelian S
  right := RightHomologyData.ofAbelian S
  iso := Abelian.coimageIsoImage (kernel.ι S.g ≫ cokernel.π S.f)

instance _root_.CategoryTheory.categoryWithHomology_of_abelian :
    CategoryWithHomology C where
  hasHomology S := HasHomology.mk' (HomologyData.ofAbelian S)

noncomputable def _root_.CategoryTheory.Limits.isLimit_mapCone_of_kernelFork_ofι_cokernel_condition_of_mono
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
    (isLimitOfIsLimitπ _ _ _ _ )
  all_goals apply isLimit_mapCone_of_kernelFork_ofι_cokernel_condition_of_mono⟩

noncomputable def _root_.CategoryTheory.Limits.isColimit_mapCocone_of_cokernelCofork_ofπ_kernel_condition_of_epi
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
    (isColimitOfIsColimitπ _ _ _ _ )
  all_goals apply isColimit_mapCocone_of_cokernelCofork_ofπ_kernel_condition_of_epi⟩

noncomputable instance : Abelian (ShortComplex C) where

attribute [local instance] strongEpi_of_epi

noncomputable def homologyIsoImageICyclesCompPOpcycles :
    S.homology ≅ image (S.iCycles ≫ S.pOpcycles) :=
  image.isoStrongEpiMono _ _ S.homology_π_ι

@[reassoc (attr := simp)]
lemma homologyIsoImageICyclesCompPOpcycles_ι :
    S.homologyIsoImageICyclesCompPOpcycles.hom ≫ image.ι (S.iCycles ≫ S.pOpcycles) =
      S.homologyι :=
  image.isoStrongEpiMono_hom_comp_ι _ _ _

namespace HomologyData

namespace OfEpiMonoFactorisation

variable {kf : KernelFork S.g} {cc : CokernelCofork S.f}
  (hkf : IsLimit kf) (hcc : IsColimit cc)
  {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt}
  (fac : kf.ι ≫ cc.π = π ≫ ι)
  [Epi π] [Mono ι]

noncomputable def isoK : kf.pt ≅ S.cycles :=
  IsLimit.conePointUniqueUpToIso hkf S.cyclesIsKernel

@[reassoc (attr := simp)]
lemma isoK_inv_ι : (isoK S hkf).inv ≫ kf.ι = S.iCycles :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero

@[reassoc (attr := simp)]
lemma isoK_hom_iCycles : (isoK S hkf).hom ≫ S.iCycles = kf.ι := by
  rw [← isoK_inv_ι S hkf, Iso.hom_inv_id_assoc]

noncomputable def isoQ : cc.pt ≅ S.opcycles :=
  IsColimit.coconePointUniqueUpToIso hcc S.opcyclesIsCokernel

@[reassoc (attr := simp)]
lemma π_isoQ_hom : cc.π ≫ (isoQ S hcc).hom = S.pOpcycles :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one

@[reassoc (attr := simp)]
lemma pOpcycles_isoQ_inv : S.pOpcycles ≫ (isoQ S hcc).inv = cc.π := by
  rw [← π_isoQ_hom S hcc, assoc, Iso.hom_inv_id, comp_id]

lemma fac' : ((isoK S hkf).inv ≫ π) ≫ ι ≫ (isoQ S hcc).hom = S.iCycles ≫ S.pOpcycles := by
  simp only [assoc, ← reassoc_of% fac, π_isoQ_hom, isoK_inv_ι_assoc]

noncomputable def isoImage : H ≅ image (S.iCycles ≫ S.pOpcycles) := by
  have := epi_comp (isoK S hkf).inv π
  have := mono_comp ι (isoQ S hcc).hom
  exact image.isoStrongEpiMono _ _ (fac' S hkf hcc fac)

@[reassoc (attr := simp)]
lemma isoImage_ι :
    (isoImage S hkf hcc fac).hom ≫ image.ι (S.iCycles ≫ S.pOpcycles) =
      ι ≫ (isoQ S hcc).hom := by
  have := epi_comp (isoK S hkf).inv π
  have := mono_comp ι (isoQ S hcc).hom
  apply image.isoStrongEpiMono_hom_comp_ι
  simp only [assoc, ← reassoc_of% fac, π_isoQ_hom, isoK_inv_ι_assoc]

noncomputable def isoHomology : H ≅ S.homology :=
  isoImage S hkf hcc fac ≪≫ S.homologyIsoImageICyclesCompPOpcycles.symm

@[reassoc (attr := simp)]
lemma π_comp_isoHomology_hom :
    π ≫ (isoHomology S hkf hcc fac).hom = (isoK S hkf).hom ≫ S.homologyπ := by
  dsimp [isoHomology]
  simp only [← cancel_mono (S.homologyIsoImageICyclesCompPOpcycles.hom), assoc,
    Iso.inv_hom_id, comp_id, ← cancel_mono (image.ι (S.iCycles ≫ S.pOpcycles)),
    isoImage_ι, homologyIsoImageICyclesCompPOpcycles_ι, homology_π_ι, ← reassoc_of% fac,
    π_isoQ_hom, isoK_hom_iCycles_assoc]

@[reassoc (attr := simp)]
lemma isoHomology_hom_comp_ι :
    (isoHomology S hkf hcc fac).inv ≫ ι = S.homologyι ≫ (isoQ S hcc).inv := by
  rw [← cancel_epi S.homologyπ, ← cancel_epi (isoK S hkf).hom,
    homology_π_ι_assoc, ← π_comp_isoHomology_hom_assoc S hkf hcc fac, Iso.hom_inv_id_assoc,
    ← fac, isoK_hom_iCycles_assoc, pOpcycles_isoQ_inv]

lemma f'_eq : hkf.lift (KernelFork.ofι S.f S.zero) = S.toCycles ≫ (isoK S hkf).inv := by
  have : Mono kf.ι := ⟨fun _ _ h => Fork.IsLimit.hom_ext hkf h⟩
  rw [← cancel_mono kf.ι]
  simp only [Fork.ofι_pt, Fork.IsLimit.lift_ι, Fork.ι_ofι, assoc,
    isoK_inv_ι, toCycles_i]

lemma g'_eq : hcc.desc (CokernelCofork.ofπ S.g S.zero) =
    (isoQ S hcc).hom ≫ S.fromOpcycles := by
  have : Epi cc.π := ⟨fun _ _ h => Cofork.IsColimit.hom_ext hcc h⟩
  rw [← cancel_epi cc.π]
  simp only [Cofork.IsColimit.π_desc, Cofork.π_ofπ, π_isoQ_hom_assoc, p_fromOpcycles]

lemma homologyπ_isoHomology_inv :
    S.homologyπ ≫ (isoHomology S hkf hcc fac).inv = (isoK S hkf).inv ≫ π := by
  simp only [← cancel_mono (isoHomology S hkf hcc fac).hom, assoc, Iso.inv_hom_id, comp_id,
    π_comp_isoHomology_hom, Iso.inv_hom_id_assoc]

lemma isoHomology_inv_homologyι :
    (isoHomology S hkf hcc fac).hom ≫ S.homologyι = ι ≫ (isoQ S hcc).hom := by
  rw [← cancel_mono (isoQ S hcc).inv, assoc, assoc, Iso.hom_inv_id, comp_id,
    ← isoHomology_hom_comp_ι S hkf hcc fac, Iso.hom_inv_id_assoc]

@[simps]
noncomputable def leftHomologyData : S.LeftHomologyData where
  K := kf.pt
  H := H
  i := kf.ι
  π := π
  wi := KernelFork.condition kf
  hi := IsLimit.ofIsoLimit hkf (Fork.ext (Iso.refl _) (by simp))
  wπ := by
    dsimp
    rw [← cancel_mono (isoHomology S hkf hcc fac).hom, assoc, assoc, id_comp,
      π_comp_isoHomology_hom, zero_comp, f'_eq,
      assoc, Iso.inv_hom_id_assoc, toCycles_comp_homologyπ]
  hπ := by
    dsimp
    let e : parallelPair (hkf.lift (KernelFork.ofι S.f S.zero) ≫ 𝟙 _) 0 ≅
        parallelPair S.toCycles 0 := parallelPair.ext (Iso.refl _) (isoK S hkf)
          (by dsimp ; rw [f'_eq, assoc, assoc, id_comp, Iso.inv_hom_id, comp_id, id_comp])
          (by dsimp ; simp only [zero_comp, comp_zero])
    refine' IsColimit.precomposeInvEquiv e _ _
    exact IsColimit.ofIsoColimit S.homologyIsCokernel
      (Cofork.ext (isoHomology S hkf hcc fac).symm (homologyπ_isoHomology_inv S _ _ _))

@[simps]
noncomputable def rightHomologyData : S.RightHomologyData where
  Q := cc.pt
  H := H
  p := cc.π
  ι := ι
  wp := CokernelCofork.condition cc
  hp := IsColimit.ofIsoColimit hcc (Cofork.ext (Iso.refl _) (by simp))
  wι := by
    dsimp
    rw [id_comp, g'_eq, ← cancel_epi (isoHomology S hkf hcc fac).inv, comp_zero,
      isoHomology_hom_comp_ι_assoc, Iso.inv_hom_id_assoc, homologyι_comp_fromOpcycles]
  hι := by
    let e : parallelPair (𝟙 _ ≫ hcc.desc (CokernelCofork.ofπ S.g S.zero)) 0 ≅
        parallelPair S.fromOpcycles 0 := parallelPair.ext (isoQ S hcc) (Iso.refl _)
          (by dsimp; simp only [id_comp, comp_id, g'_eq])
          (by simp)
    refine' IsLimit.postcomposeHomEquiv e _ _
    exact IsLimit.ofIsoLimit S.homologyIsKernel
      (Iso.symm (Fork.ext (isoHomology S hkf hcc fac) (isoHomology_inv_homologyι S hkf hcc fac)))

end OfEpiMonoFactorisation

@[simps]
noncomputable def ofEpiMonoFactorisation {kf : KernelFork S.g} {cc : CokernelCofork S.f}
    (hkf : IsLimit kf) (hcc : IsColimit cc) {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt}
    (fac : kf.ι ≫ cc.π = π ≫ ι) [Epi π] [Mono ι] :
    S.HomologyData where
  left := OfEpiMonoFactorisation.leftHomologyData S hkf hcc fac
  right := OfEpiMonoFactorisation.rightHomologyData S hkf hcc fac
  iso := Iso.refl _

end HomologyData

end ShortComplex

end CategoryTheory
