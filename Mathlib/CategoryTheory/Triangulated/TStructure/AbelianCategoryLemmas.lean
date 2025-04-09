import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Tactic.Linarith

open CategoryTheory Category CategoryTheory.Limits ZeroObject

universe v u u' v'

def CategoryTheory.Limits.compNatIso' {C : Type u} [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {X : C} {Y : C} {f : X ⟶ Y} {D : Type u'}
    [CategoryTheory.Category.{v, u'} D] [CategoryTheory.Limits.HasZeroMorphisms D]
    (F : CategoryTheory.Functor C D) [F.PreservesZeroMorphisms] :
    (CategoryTheory.Limits.parallelPair f 0).comp F ≅
    CategoryTheory.Limits.parallelPair (F.map f) 0 := by
refine NatIso.ofComponents ?_ ?_
· intro j
  cases j with
  | zero => exact Iso.refl _
  | one => exact Iso.refl _
· intro i j f
  cases f with
  | left => simp only [Functor.comp_obj, parallelPair_obj_zero, parallelPair_obj_one,
    Functor.comp_map, parallelPair_map_left, Iso.refl_hom, Category.comp_id, Category.id_comp]
  | right => simp only [Functor.comp_obj, parallelPair_obj_zero, parallelPair_obj_one,
    Functor.comp_map, parallelPair_map_right, Functor.map_zero, Iso.refl_hom, Category.comp_id,
    comp_zero]
  | id => simp only [Functor.comp_obj, walkingParallelPairHom_id, Functor.comp_map, Functor.map_id,
    parallelPair_obj_zero, parallelPair_obj_one, Category.id_comp, Category.comp_id]

def CategoryTheory.Functor.mapKernelFork {C : Type u} [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {X : C} {Y : C} {f : X ⟶ Y} {D : Type u'}
    [CategoryTheory.Category.{v, u'} D] [CategoryTheory.Limits.HasZeroMorphisms D]
    (F : CategoryTheory.Functor C D) [F.PreservesZeroMorphisms] (c : KernelFork f) :
    KernelFork (F.map f) := (Cones.postcompose (compNatIso' F).hom).obj (F.mapCone c)


lemma CategoryTheory.Functor.mapKernelFork_pt {C : Type u} [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {X : C} {Y : C} {f : X ⟶ Y} {D : Type u'}
    [CategoryTheory.Category.{v, u'} D] [CategoryTheory.Limits.HasZeroMorphisms D]
    (F : CategoryTheory.Functor C D) [F.PreservesZeroMorphisms] (c : KernelFork f) :
    (F.mapKernelFork c).pt = F.obj c.pt :=
  by simp only [mapKernelFork, Cones.postcompose_obj_pt, mapCone_pt]

lemma CategoryTheory.Functor.mapKernelFork_ι {C : Type u} [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {X : C} {Y : C} {f : X ⟶ Y} {D : Type u'}
    [CategoryTheory.Category.{v, u'} D] [CategoryTheory.Limits.HasZeroMorphisms D]
    (F : CategoryTheory.Functor C D) [F.PreservesZeroMorphisms] (c : KernelFork f) :
    (F.mapKernelFork c).ι = F.map c.ι := by
  simp only [mapKernelFork, compNatIso', comp_obj, parallelPair_obj_zero, parallelPair_obj_one,
    Cones.postcompose_obj_pt, mapCone_pt, const_obj_obj]
  rw [Fork.ι, Cones.postcompose_obj_π]
  simp only [Cones.postcompose_obj_pt, mapCone_pt, NatTrans.comp_app, const_obj_obj, comp_obj,
    parallelPair_obj_zero, mapCone_π_app, Fork.app_zero_eq_ι, NatIso.ofComponents_hom_app,
    Iso.refl_hom, Category.comp_id]

def CategoryTheory.Functor.mapKernelForkIso {C : Type u} [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {X : C} {Y : C} {f : X ⟶ Y} {D : Type u'}
    [CategoryTheory.Category.{v, u'} D] [CategoryTheory.Limits.HasZeroMorphisms D]
    (F : CategoryTheory.Functor C D) [F.PreservesZeroMorphisms] (c : KernelFork f) :
    F.mapKernelFork c ≅ KernelFork.ofι (F.map c.ι) (by simp only [const_obj_obj,
      parallelPair_obj_zero, KernelFork.map_condition]) := by
  refine Cones.ext ?_ ?_
  · rw [F.mapKernelFork_pt]
    exact Iso.refl _
  · intro j
    cases j with
    | zero => simp only [const_obj_obj, parallelPair_obj_zero, Fork.app_zero_eq_ι, Fork.ofι_pt,
      eq_mpr_eq_cast, cast_eq, Iso.refl_hom, Fork.ofι_π_app]
              erw [Category.id_comp]
              rw [F.mapKernelFork_ι]
    | one => simp only [const_obj_obj, parallelPair_obj_one, Fork.app_one_eq_ι_comp_left,
      parallelPair_obj_zero, KernelFork.condition, Fork.ofι_pt, eq_mpr_eq_cast, cast_eq,
      Iso.refl_hom, Fork.ofι_π_app, KernelFork.map_condition, comp_zero]

def CategoryTheory.Limits.KernelFork.functoriality {C : Type u} [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {D : Type u'} [CategoryTheory.Category.{v, u'} D]
    [CategoryTheory.Limits.HasZeroMorphisms D] (F : CategoryTheory.Functor C D)
    [F.PreservesZeroMorphisms] {X Y : C} (f : X ⟶ Y) :
    CategoryTheory.Limits.KernelFork f ⥤ CategoryTheory.Limits.KernelFork (F.map f) where
obj c := F.mapKernelFork c
map α :=
  {hom := by simp only; rw [F.mapKernelFork_pt, F.mapKernelFork_pt]; exact F.map α.hom
   w := by
     intro j
     cases j with
     | zero => simp only [Functor.mapKernelFork, compNatIso', Functor.comp_obj,
       parallelPair_obj_zero, parallelPair_obj_one, Cones.postcompose_obj_pt, Functor.mapCone_pt,
       eq_mpr_eq_cast, cast_eq, id_eq, Cones.postcompose_obj_π, NatTrans.comp_app,
       Functor.const_obj_obj, Functor.mapCone_π_app, Fork.app_zero_eq_ι,
       NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id]
               rw [← Functor.map_comp]; simp only [Fork.hom_comp_ι]
     | one => simp only [parallelPair_obj_one, eq_mpr_eq_cast, cast_eq, id_eq,
       Fork.app_one_eq_ι_comp_left, Functor.const_obj_obj, parallelPair_obj_zero, condition,
       comp_zero]
  }

def CategoryTheory.Functor.mapCokernelCofork {C : Type u} [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {X : C} {Y : C} {f : X ⟶ Y} {D : Type u'}
    [CategoryTheory.Category.{v, u'} D] [CategoryTheory.Limits.HasZeroMorphisms D]
    (F : CategoryTheory.Functor C D) [F.PreservesZeroMorphisms] (c : CokernelCofork f) :
    CokernelCofork (F.map f) := (Cocones.precompose (compNatIso' F).inv).obj (F.mapCocone c)


lemma CategoryTheory.Functor.mapCokernelCofork_pt {C : Type u} [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {X : C} {Y : C} {f : X ⟶ Y} {D : Type u'}
    [CategoryTheory.Category.{v, u'} D] [CategoryTheory.Limits.HasZeroMorphisms D]
    (F : CategoryTheory.Functor C D) [F.PreservesZeroMorphisms] (c : CokernelCofork f) :
    (F.mapCokernelCofork c).pt = F.obj c.pt :=
  by simp only [mapCokernelCofork, Cocones.precompose_obj_pt, mapCocone_pt]

lemma CategoryTheory.Functor.mapCokernelCofork_π {C : Type u} [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {X : C} {Y : C} {f : X ⟶ Y} {D : Type u'}
    [CategoryTheory.Category.{v, u'} D] [CategoryTheory.Limits.HasZeroMorphisms D]
    (F : CategoryTheory.Functor C D) [F.PreservesZeroMorphisms] (c : CokernelCofork f) :
    (F.mapCokernelCofork c).π = F.map c.π := by
  simp only [parallelPair_obj_one, mapCokernelCofork, compNatIso', comp_obj, parallelPair_obj_zero,
    Cocones.precompose_obj_pt, mapCocone_pt, const_obj_obj]
  rw [Cofork.π, Cocones.precompose_obj_ι]
  simp only [Cocones.precompose_obj_pt, mapCocone_pt, NatTrans.comp_app, parallelPair_obj_one,
    comp_obj, const_obj_obj, NatIso.ofComponents_inv_app, Iso.refl_inv, mapCocone_ι_app,
    Cofork.app_one_eq_π, Category.id_comp]

def CategoryTheory.Functor.mapCokernelCoforkIso {C : Type u} [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {X : C} {Y : C} {f : X ⟶ Y} {D : Type u'}
    [CategoryTheory.Category.{v, u'} D] [CategoryTheory.Limits.HasZeroMorphisms D]
    (F : CategoryTheory.Functor C D) [F.PreservesZeroMorphisms] (c : CokernelCofork f) :
    F.mapCokernelCofork c ≅ CokernelCofork.ofπ (F.map c.π) (by simp only [const_obj_obj,
      CokernelCofork.map_condition]) := by
  refine Cocones.ext ?_ ?_
  · rw [F.mapCokernelCofork_pt]
    exact Iso.refl _
  · intro j
    cases j with
    | zero => simp only [parallelPair_obj_zero, const_obj_obj, Cofork.ofπ_pt,
      Cofork.app_zero_eq_comp_π_left, CokernelCofork.condition, eq_mpr_eq_cast, cast_eq,
      Iso.refl_hom, zero_comp, Cofork.ofπ_ι_app, CokernelCofork.map_condition]
    | one => simp only [parallelPair_obj_one, const_obj_obj, Cofork.ofπ_pt, Cofork.app_one_eq_π,
      eq_mpr_eq_cast, cast_eq, Iso.refl_hom, Cofork.ofπ_ι_app]
             erw [Category.comp_id]
             rw [F.mapCokernelCofork_π]

def CategoryTheory.Limits.CokernelCofork.functoriality {C : Type u}
    [CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroMorphisms C] {D : Type u'}
    [CategoryTheory.Category.{v, u'} D] [CategoryTheory.Limits.HasZeroMorphisms D]
    (F : CategoryTheory.Functor C D) [F.PreservesZeroMorphisms] {X Y : C} (f : X ⟶ Y) :
    CategoryTheory.Limits.CokernelCofork f ⥤ CategoryTheory.Limits.CokernelCofork (F.map f) where
obj c := F.mapCokernelCofork c
map α :=
  {hom := by simp only; rw [F.mapCokernelCofork_pt, F.mapCokernelCofork_pt]; exact F.map α.hom
   w := by
     intro j
     cases j with
     | zero => simp only [parallelPair_obj_zero, Functor.const_obj_obj,
       Cofork.app_zero_eq_comp_π_left, condition, eq_mpr_eq_cast, cast_eq, id_eq, zero_comp]
--               rw [← Functor.map_comp]; simp only [Fork.hom_comp_ι]
     | one => simp only [parallelPair_obj_one, Functor.const_obj_obj, Cofork.app_one_eq_π,
       eq_mpr_eq_cast, cast_eq, id_eq]
              rw [F.mapCokernelCofork_π, ← Functor.map_comp, F.mapCokernelCofork_π]
              simp only [parallelPair_obj_one, Functor.const_obj_obj, Fork.π_comp_hom]
  }

variable {A C : Type u} [Category.{v, u} A] [Category.{v,u} C] [HasZeroMorphisms C]
  [Abelian A] {B : Type u'} [Category.{v', u'} B] [Abelian B]
variable {X Y : A} {f : X ⟶ Y} (S : ShortComplex A)
variable (F : A ⥤ B) [Functor.Additive F]


lemma imageFactorisationOfEpi_aux {X Y : C} (f : X ⟶ Y) (F F' : MonoFactorisation f)
    (hF : NormalEpi F.e) : hF.g ≫ F'.e = 0 := by
  rw [← cancel_mono F'.m, zero_comp, assoc, F'.fac]
  conv_lhs => congr; rfl; rw [← F.fac]
  rw [← assoc, hF.w, zero_comp]

def imageFactorisationOfNormalEpi {X Y : C} (f : X ⟶ Y) (F : MonoFactorisation f)
    (hF : NormalEpi F.e) : ImageFactorisation f where
  F := F
  isImage :=
  {
   lift := fun F' ↦
     hF.isColimit.desc (CokernelCofork.ofπ F'.e (imageFactorisationOfEpi_aux f F F' hF))
   lift_fac := fun F' ↦ by
     rw [← cancel_epi F.e, ← assoc]
     have := hF.isColimit.fac (CokernelCofork.ofπ F'.e (imageFactorisationOfEpi_aux f F F' hF))
       WalkingParallelPair.one
     simp only [parallelPair_obj_one, Cofork.ofπ_pt, Functor.const_obj_obj, Cofork.ofπ_ι_app,
       comp_id] at this
     rw [this, F.fac, F'.fac]
  }

noncomputable def imageComparison (h : IsIso (cokernelComparison f F)) :
    F.obj (Abelian.image f) ⟶ Abelian.image (F.map f) := by
  refine kernel.lift (cokernel.π (F.map f)) (F.map (Abelian.image.ι f)) ?_
  refine Mono.right_cancellation (f := cokernelComparison f F) _ _ ?_
  simp only [equalizer_as_kernel, Category.assoc, π_comp_cokernelComparison, zero_comp]
  rw [← F.map_comp]
  convert F.map_zero _ _
  simp only [kernel.condition]

lemma kernelImageComparison_compat (hcoker : IsIso (cokernelComparison S.f F)) :
    F.map S.abelianImageToKernel ≫ kernelComparison S.g F =
    imageComparison F hcoker ≫ (F.mapShortComplex.obj S).abelianImageToKernel := by
  refine Mono.right_cancellation (f := kernel.ι (F.map S.g)) _ _ ?_
  simp only [Category.assoc, kernelComparison_comp_ι]
  rw [← F.map_comp, S.abelianImageToKernel_comp_kernel_ι]
  erw [(F.mapShortComplex.obj S).abelianImageToKernel_comp_kernel_ι]
  rw [imageComparison]
  simp only [equalizer_as_kernel, Functor.mapShortComplex_obj, ShortComplex.map_X₁,
    ShortComplex.map_X₂, ShortComplex.map_f, kernel.lift_ι]

lemma image_compat : (Abelian.imageIsoImage f).inv ≫ Abelian.image.ι f =
    Limits.image.ι f := by aesop_cat

namespace CategoryTheory.ShortComplex

noncomputable def LeftHomologyData.ofIsColimitCokernelCoforkAbelianImageToKernel
    (cc : CokernelCofork S.abelianImageToKernel) (hcc : IsColimit cc) :
    S.LeftHomologyData where
  K := kernel S.g
  H := cc.pt
  i := kernel.ι S.g
  π := cc.π
  wi := by simp
  hi := kernelIsKernel S.g
  wπ := by
    have h := Abelian.factorThruImage S.f ≫= cc.condition
    rw [comp_zero, ← assoc] at h
    convert h
    simp [← cancel_mono (kernel.ι _)]
  hπ := CokernelCofork.IsColimit.ofπ _ _
      (fun a ha ↦ hcc.desc (CokernelCofork.ofπ (π := a) (by
        rw [← cancel_epi (Abelian.factorThruImage S.f), comp_zero, ← assoc]
        convert ha
        simp [← cancel_mono (kernel.ι _)])))
      (fun a ha ↦ hcc.fac _ _)
      (fun a ha b hb ↦ Cofork.IsColimit.hom_ext hcc (by simpa using hb))

noncomputable def homologyIsoCokernelAbelianImageToKernel :
    S.homology ≅ cokernel S.abelianImageToKernel :=
  (LeftHomologyData.ofIsColimitCokernelCoforkAbelianImageToKernel S _
    (cokernelIsCokernel _)).homologyIso

noncomputable def RightHomologyData.ofIsLimitKernelForkCokernelToAbelianCoimage
    (kf : KernelFork S.cokernelToAbelianCoimage) (hkf : IsLimit kf) :
    S.RightHomologyData where
  Q := cokernel S.f
  H := kf.pt
  p := cokernel.π S.f
  ι := kf.ι
  wp := by simp
  hp := cokernelIsCokernel S.f
  wι := by
    have h := kf.condition =≫ Abelian.factorThruCoimage S.g
    rw [zero_comp, assoc] at h
    convert h
    simp [← cancel_epi (cokernel.π _)]
  hι := KernelFork.IsLimit.ofι _ _
          (fun a ha ↦ hkf.lift (KernelFork.ofι (ι := a) (by
            rw [← cancel_mono (Abelian.factorThruCoimage S.g), zero_comp, assoc]
            convert ha
            simp [← cancel_epi (cokernel.π _)])))
          (fun _ _ ↦ hkf.fac _ _)
          (fun _ _ _ hb ↦ Fork.IsLimit.hom_ext hkf (by simpa using hb))

noncomputable def homologyIsoKernelCokernelToAbelianCoimage :
    S.homology ≅ kernel S.cokernelToAbelianCoimage :=
  (RightHomologyData.ofIsLimitKernelForkCokernelToAbelianCoimage S _
    (kernelIsKernel _)).homologyIso

def imageToKernelIsIsoOfExact {S : ShortComplex A} (h : IsZero S.homology) :
    IsIso S.abelianImageToKernel := by
  have : Epi S.abelianImageToKernel := by
    refine NormalMonoCategory.epi_of_zero_cokernel _ (cokernel S.abelianImageToKernel) ?_
    have : cokernel.π S.abelianImageToKernel = 0 :=
      IsZero.eq_zero_of_tgt (IsZero.of_iso h S.homologyIsoCokernelAbelianImageToKernel.symm) _
    conv => congr; congr; rw [← this]
    exact cokernelIsCokernel _
  exact isIso_of_mono_of_epi S.abelianImageToKernel (C := A)

def cokernelToAbelianCoimageIsIsoOfExact {S : ShortComplex A} (h : IsZero S.homology) :
    IsIso S.cokernelToAbelianCoimage := by
  have : Mono S.cokernelToAbelianCoimage := by
    refine NormalEpiCategory.mono_of_zero_kernel _ (kernel S.cokernelToAbelianCoimage) ?_
    have : kernel.ι S.cokernelToAbelianCoimage = 0 :=
      IsZero.eq_zero_of_src (IsZero.of_iso h S.homologyIsoKernelCokernelToAbelianCoimage.symm) _
    conv => congr; congr; rw [← this]
    exact kernelIsKernel _
  exact isIso_of_mono_of_epi S.cokernelToAbelianCoimage (C := A)

end CategoryTheory.ShortComplex

variable {B : Type*} [Category B] [Abelian B]
variable {X Y : A} (f : X ⟶ Y)
variable (F : A ⥤ B) [Functor.Additive F]

noncomputable def imageComparisonOfCokernelComparisonMono (hc : Mono (cokernelComparison f F)) :
    F.obj (Abelian.image f) ⟶ Abelian.image (F.map f) := by
  refine kernel.lift (cokernel.π (F.map f)) (F.map (Abelian.image.ι f)) ?_
  rw [← cancel_mono (cokernelComparison f F)]
  simp only [equalizer_as_kernel, assoc, π_comp_cokernelComparison, zero_comp]
  rw [← F.map_comp, kernel.condition, F.map_zero]

@[simp]
lemma imageComparison_comp_ι (hc : Mono (cokernelComparison f F)) :
    imageComparisonOfCokernelComparisonMono f F hc ≫ Abelian.image.ι (F.map f) =
    F.map (Abelian.image.ι f) := by
  simp only [imageComparisonOfCokernelComparisonMono, equalizer_as_kernel, kernel.lift_ι]

@[simp]
lemma factorThruImage_comp_imageComparison (hc : Mono (cokernelComparison f F)) :
    F.map (Abelian.factorThruImage f) ≫ imageComparisonOfCokernelComparisonMono f F hc =
    Abelian.factorThruImage (F.map f) := by
  rw [← cancel_mono (Abelian.image.ι (F.map f)), assoc, imageComparison_comp_ι,
    Abelian.image.fac, ← F.map_comp, Abelian.image.fac]

lemma imageComparisonMonoOfMono (hc : Mono (cokernelComparison f F))
    (hm : Mono (F.map (Abelian.image.ι f))) :
    Mono (imageComparisonOfCokernelComparisonMono f F hc) := by
  refine @mono_of_mono _ _ _ _ _ _ (Abelian.image.ι (F.map f)) ?_
  rw [imageComparison_comp_ι]
  exact hm

lemma kernelComplexExact : (ShortComplex.mk (kernel.ι f) f (kernel.condition f)).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  sorry
-- Proof needs to be fixed, mathlib changed.
/-  refine IsZero.of_iso ?_ (ShortComplex.homology'IsoHomology _).symm
  refine IsZero.of_iso ?_ (homology'IsoCokernelLift _ _ _)
  simp only [equalizer_as_kernel, IsLimit.lift_self, Fork.ofι_pt]
  refine IsZero.of_iso (isZero_zero A) (Limits.cokernel.ofEpi _)
-/

lemma monoCokernelComplexShortExact (hm : Mono f) :
    (ShortComplex.mk f (cokernel.π f) (by simp)).ShortExact where
  exact := by
    have := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel f)
    refine ShortComplex.exact_of_iso (ShortComplex.isoMk ?_ ?_ ?_ ?_ ?_)
      (kernelComplexExact (cokernel.π f))
    · exact IsLimit.conePointUniqueUpToIso (kernelIsKernel (cokernel.π f)) this
    · exact Iso.refl _
    · exact Iso.refl _
    · simp only [Cofork.ofπ_pt, Functor.const_obj_obj, Cofork.π_ofπ, Iso.refl_hom, comp_id]
      have := IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel (cokernel.π f)) this
        WalkingParallelPair.zero
      simp only [Fork.ofι_pt, parallelPair_obj_zero, Cofork.ofπ_pt, Functor.const_obj_obj,
        Cofork.π_ofπ, Fork.ofι_π_app] at this
      exact this
    · simp only [Iso.refl_hom, id_comp, comp_id]

lemma epiKernelComplexShortExact (_ : Epi f) :
    (ShortComplex.mk (kernel.ι f) f (by simp)).ShortExact where
  exact := kernelComplexExact f

lemma kernelImageComplexShortExact : (ShortComplex.mk (kernel.ι f) (Abelian.factorThruImage f)
    (by rw [← cancel_mono (Abelian.image.ι f), assoc, Abelian.image.fac, zero_comp,
    kernel.condition f])).ShortExact where
  exact := by
    set φ := ShortComplex.homMk (S₁ := ShortComplex.mk (kernel.ι f) (Abelian.factorThruImage f)
      (by rw [← cancel_mono (Abelian.image.ι f), assoc, Abelian.image.fac, zero_comp,
      kernel.condition f])) (S₂ := ShortComplex.mk (kernel.ι f) f (kernel.condition f))
      (𝟙 _) (𝟙 _) (Abelian.image.ι f) (by rw [id_comp, comp_id])
      (by rw [id_comp]; simp only [equalizer_as_kernel, id_eq, eq_mpr_eq_cast, kernel.lift_ι])
    have : Epi φ.τ₁ := by simp only [equalizer_as_kernel, id_eq, eq_mpr_eq_cast,
      ShortComplex.homMk_τ₁, φ]; exact inferInstance
    have : IsIso φ.τ₂ := by simp only [equalizer_as_kernel, id_eq, eq_mpr_eq_cast,
      ShortComplex.homMk_τ₂, φ]; exact inferInstance
    have : Mono φ.τ₃ := by simp only [equalizer_as_kernel, id_eq, eq_mpr_eq_cast,
      ShortComplex.homMk_τ₃, φ]; exact inferInstance
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
    exact kernelComplexExact f

lemma imageComparisonEpiOfExact (hc : IsIso (cokernelComparison f F))
    (he : (ShortComplex.mk (F.map (Abelian.image.ι f))
    (F.map (cokernel.π f)) (by rw [← F.map_comp]; simp)).Exact) :
    Epi (imageComparisonOfCokernelComparisonMono f F inferInstance) := by
  set R₁ := (ShortComplex.mk (F.map (Abelian.image.ι f))
    (F.map (cokernel.π f)) (by rw [← F.map_comp]; simp)).toComposableArrows
  set R₂ := (ShortComplex.mk (Abelian.image.ι (F.map f)) (cokernel.π (F.map f))
    (by simp)).toComposableArrows
  set φ : R₁ ⟶ R₂ := by
    refine ComposableArrows.homMk
      (fun i ↦
        match i with
        | 0 => imageComparisonOfCokernelComparisonMono f F inferInstance
        | 1 => 𝟙 _
        | 2 => CategoryTheory.inv (cokernelComparison f F)) ?_
    intro i _
    match i with
    | 0 => erw [imageComparison_comp_ι, comp_id]; rfl
    | 1 => simp only
           rw [← cancel_mono (cokernelComparison f F), assoc, IsIso.inv_hom_id, comp_id]
           erw [id_comp]
           simp only [R₁, R₂]
           change F.map (cokernel.π f) = cokernel.π (F.map f) ≫ _
           rw [π_comp_cokernelComparison]
  have hR₁ : R₁.Exact := ShortComplex.Exact.exact_toComposableArrows he
  have hR₂ : R₂.Exact :=
    ShortComplex.Exact.exact_toComposableArrows (kernelComplexExact (cokernel.π (F.map f)))
  have hR₂' : Mono (R₂.map' 0 1) := by
    simp only [R₂, ShortComplex.toComposableArrows]
    simp only [Nat.reduceAdd, equalizer_as_kernel, ComposableArrows.mk₂, id_eq, Int.reduceNeg,
      Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.reduceSub, Int.reduceAdd, Fin.zero_eta,
      ComposableArrows.precomp_obj, ComposableArrows.Precomp.obj_zero, Fin.mk_one,
      ComposableArrows.Precomp.obj_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj,
      ComposableArrows.map', ComposableArrows.precomp_map, ComposableArrows.Precomp.map_zero_one]
    exact inferInstance
  have h₀ : Epi (ComposableArrows.app' φ 1) := by
    simp only [id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.reduceAdd,
      Int.reduceSub, ComposableArrows.obj', Nat.reduceAdd, Fin.mk_one, ComposableArrows.app',
      ComposableArrows.homMk_app, φ]
    exact inferInstance
  have h₁ : Mono (ComposableArrows.app' φ 2) := by
    simp only [ComposableArrows.obj', Nat.reduceAdd, Fin.reduceFinMk, ComposableArrows.app',
      ComposableArrows.homMk_app, φ]
    exact inferInstance
  exact Abelian.epi_of_mono_of_epi_of_mono φ hR₁ hR₂ hR₂' h₀ h₁

lemma imageComparisonIsoOfMonoAndExact (hc : IsIso (cokernelComparison f F))
    (hm : Mono (F.map (Abelian.image.ι f)))
    (he : (ShortComplex.mk (F.map (Abelian.image.ι f))
    (F.map (cokernel.π f)) (by rw [← F.map_comp]; simp)).Exact) :
    IsIso (imageComparisonOfCokernelComparisonMono f F inferInstance) := by
  have := imageComparisonMonoOfMono f F inferInstance hm
  have := imageComparisonEpiOfExact f F hc he
  exact isIso_of_mono_of_epi _

lemma imageComparisonVsKernelComparison (S : ShortComplex A)
    (hS : IsIso (cokernelComparison S.f F)) :
    (imageComparisonOfCokernelComparisonMono S.f F inferInstance) ≫
    (F.mapShortComplex.obj S).abelianImageToKernel =
    F.map (S.abelianImageToKernel) ≫ kernelComparison S.g F := by
  rw [← cancel_mono (kernel.ι (F.map S.g)), assoc]
  erw [ShortComplex.abelianImageToKernel_comp_kernel_ι, imageComparison_comp_ι]
  rw [assoc, kernelComparison_comp_ι, ← F.map_comp, S.abelianImageToKernel_comp_kernel_ι]

lemma kernelComparisonMonoOfMono (hm : Mono (F.map (kernel.ι f))) :
    Mono (kernelComparison f F) := by
  refine @mono_of_mono _ _ _ _ _ _ (kernel.ι (F.map f)) ?_
  rw [kernelComparison_comp_ι]
  exact hm

lemma kernelComparisonEpiOfImageComparisonMono (hc : Mono (cokernelComparison f F))
    (hm : Mono (imageComparisonOfCokernelComparisonMono f F hc))
    (he : (ShortComplex.mk (F.map (kernel.ι f))
    (F.map (Abelian.factorThruImage f))
    (by rw [← F.map_comp, ← F.map_zero]; congr 1; rw [← cancel_mono (Abelian.image.ι f), assoc,
    Abelian.image.fac, kernel.condition, zero_comp])).Exact) : Epi (kernelComparison f F) := by
  set R₁ := (ShortComplex.mk (F.map (kernel.ι f))
    (F.map (Abelian.factorThruImage f))
    (by rw [← F.map_comp, ← F.map_zero]; congr 1; rw [← cancel_mono (Abelian.image.ι f), assoc,
    Abelian.image.fac, kernel.condition, zero_comp])).toComposableArrows
  set R₂ := (ShortComplex.mk (kernel.ι (F.map f)) (Abelian.factorThruImage (F.map f))
    (by rw [← cancel_mono (Abelian.image.ι (F.map f)), assoc, Abelian.image.fac, zero_comp,
        kernel.condition])).toComposableArrows
  set φ : R₁ ⟶ R₂ := by
    refine ComposableArrows.homMk
      (fun i ↦
        match i with
        | 0 => kernelComparison f F
        | 1 => 𝟙 _
        | 2 => imageComparisonOfCokernelComparisonMono f F hc)
      ?_
    intro i _
    match i with
    | 0 => erw [kernelComparison_comp_ι, comp_id]; rfl
    | 1 => erw [factorThruImage_comp_imageComparison, id_comp]; rfl
  have hR₁ : R₁.Exact := ShortComplex.Exact.exact_toComposableArrows he
  have hR₂ : R₂.Exact := ShortComplex.Exact.exact_toComposableArrows
    (kernelImageComplexShortExact (F.map f)).exact
  have hR₂' : Mono (R₂.map' 0 1) := by
    simp only [Nat.reduceAdd, equalizer_as_kernel, id_eq, eq_mpr_eq_cast, Int.reduceNeg,
      Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.reduceSub, Int.reduceAdd, Fin.zero_eta,
      ShortComplex.toComposableArrows_obj, ComposableArrows.Precomp.obj_zero, Fin.mk_one,
      ComposableArrows.Precomp.obj_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj,
      ComposableArrows.map', ShortComplex.toComposableArrows_map,
      ComposableArrows.Precomp.map_zero_one, R₂]
    exact inferInstance
  have h₀ : Epi (ComposableArrows.app' φ 1) := by
    simp only [id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.reduceAdd,
      Int.reduceSub, ComposableArrows.obj', Nat.reduceAdd, Fin.mk_one, ComposableArrows.app',
      ComposableArrows.homMk_app, φ]
    exact inferInstance
  have h₁ : Mono (ComposableArrows.app' φ 2) := hm
  exact Abelian.epi_of_mono_of_epi_of_mono φ hR₁ hR₂ hR₂' h₀ h₁

namespace CategoryTheory.ShortComplex

variable {S}

lemma exact_iff_epi_abelianImageToKernel : S.Exact ↔ Epi S.abelianImageToKernel := by
  rw [S.exact_iff_epi_kernel_lift]
  have eq : kernel.lift S.g S.f S.zero = Abelian.factorThruImage S.f ≫ S.abelianImageToKernel := by
    rw [← cancel_mono (kernel.ι S.g), assoc, S.abelianImageToKernel_comp_kernel_ι,
      Abelian.image.fac, kernel.lift_ι]
  constructor
  · exact fun _ ↦ epi_of_epi_fac eq.symm
  · exact fun _ ↦ by rw [eq]; exact epi_comp _ _

lemma exact_iff_isIso_abelianImageToKernel : S.Exact ↔ IsIso S.abelianImageToKernel := by
  rw [exact_iff_epi_abelianImageToKernel]
  constructor
  · exact fun _ ↦ isIso_of_mono_of_epi _
  · exact fun _ ↦ inferInstance

noncomputable def isoAbelianImageToKernelOfExact (h : S.Exact) :
    Abelian.image S.f ≅ kernel S.g :=
  @asIso _ _ _  _ S.abelianImageToKernel (exact_iff_isIso_abelianImageToKernel.mp h)

variable (S)

/-- The 4 composable arrows associated to a short complex. -/
@[simps!]
noncomputable def toComposableArrows₄ (S : ShortComplex A) : ComposableArrows A 4 :=
  ComposableArrows.mk₄ (0 : (0 : A) ⟶ S.X₁) S.f S.g (0 : S.X₃ ⟶ (0 : A))

lemma isComplex_toComposableArrows₄ (S : ShortComplex A) :
    S.toComposableArrows₄.IsComplex where
  zero i _ := match i with
    | 0 => by simp
    | 1 => S.zero
    | 2 => by erw [comp_zero]

noncomputable def toComposableArrows₄_δ₀_δfinal_iso_toComposableArrows (S : ShortComplex A) :
    S.toComposableArrows ≅ S.toComposableArrows₄.δ₀.δlast := by
  refine ComposableArrows.isoMk ?_ ?_
  · intro i
    match i with
    | 0 => exact Iso.refl _
    | 1 => exact Iso.refl _
    | 2 => exact Iso.refl _
  · intro i _
    match i with
    | 0 => erw [id_comp, comp_id]; rfl
    | 1 => erw [comp_id, id_comp]; rfl

lemma ShortExact.exact_toComposableArrows₄ {S : ShortComplex A} (hS : S.ShortExact) :
    S.toComposableArrows₄.Exact := by
  rw [ComposableArrows.exact_iff_δ₀]
  constructor
  · refine ComposableArrows.exact₂_mk _ (by erw [zero_comp]) ?_
    change (ShortComplex.mk 0 S.f _).Exact
    exact (ShortComplex.exact_iff_mono _ (IsZero.eq_zero_of_src (isZero_zero A) _)).mpr hS.mono_f
  · rw [ComposableArrows.exact_iff_δlast]
    constructor
    · exact ComposableArrows.exact_of_iso (S.toComposableArrows₄_δ₀_δfinal_iso_toComposableArrows)
        hS.exact.exact_toComposableArrows
    · refine ComposableArrows.exact₂_mk _ (by erw [comp_zero]) ?_
      change (ShortComplex.mk S.g 0 _).Exact
      exact (ShortComplex.exact_iff_epi _ (IsZero.eq_zero_of_tgt (isZero_zero A) _)).mpr hS.epi_g

lemma exact_iff_exact_toComposableArrows₄ (S : ShortComplex A) :
    S.ShortExact ↔ S.toComposableArrows₄.Exact := by
  constructor
  · exact fun h ↦ h.exact_toComposableArrows₄
  · intro h; refine {exact := ?_, mono_f := ?_, epi_g := ?_}
    · rw [exact_iff_exact_toComposableArrows]
      refine ComposableArrows.exact_of_iso
        S.toComposableArrows₄_δ₀_δfinal_iso_toComposableArrows.symm ?_
      rw [ComposableArrows.exact_iff_δ₀] at h
      have := h.2
      rw [ComposableArrows.exact_iff_δlast] at this
      exact this.1
    · rw [ComposableArrows.exact_iff_δ₀, ComposableArrows.exact₂_iff] at h
      · change (ShortComplex.mk 0 S.f _).Exact ∧ _ at h
        exact (ShortComplex.exact_iff_mono _ (IsZero.eq_zero_of_src (isZero_zero A) _)).mp h.1
      · rw [ComposableArrows.isComplex₂_iff]; erw [zero_comp]
    · rw [ComposableArrows.exact_iff_δlast, ComposableArrows.exact₂_iff] at h
      · change _ ∧ (ShortComplex.mk S.g 0 _).Exact at h
        exact (ShortComplex.exact_iff_epi _ (IsZero.eq_zero_of_tgt (isZero_zero A) _)).mp h.2
      · rw [ComposableArrows.isComplex₂_iff]; erw [comp_zero]

noncomputable def LeftHomologyData_ker_f' {S : ShortComplex A} (h : LeftHomologyData S) :
    kernel h.f' ≅ kernel S.f := by
  refine (kernelCompMono h.f' h.i).symm.trans ?_
  simp only [LeftHomologyData.f'_i]
  exact Iso.refl _

/--
Doc string, why the prime?
-/
noncomputable def LeftHomologyData_image_f' {S : ShortComplex A}
    (h : LeftHomologyData S) : Abelian.image h.f' ≅ Abelian.image S.f := by
  set F' := Abelian.imageStrongEpiMonoFactorisation h.f'
  refine (image.isoStrongEpiMono F'.e (F'.m ≫ h.i) (f := S.f)
    (by simp only [MonoFactorisation.fac_assoc, LeftHomologyData.f'_i])).trans
    (Abelian.imageIsoImage _).symm

end ShortComplex

end CategoryTheory
