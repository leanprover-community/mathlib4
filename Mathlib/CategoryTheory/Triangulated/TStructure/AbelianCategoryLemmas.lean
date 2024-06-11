import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Tactic.Linarith

open CategoryTheory CategoryTheory.Limits ZeroObject

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

variable {A : Type u} [Category.{v, u} A] [Abelian A] {B : Type u'} [Category.{v', u'} B]
  [Abelian B]
variable {X Y : A} {f : X ⟶ Y} (S : ShortComplex A)
variable (F : A ⥤ B) [Functor.Additive F]

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

lemma image_compat : (Abelian.imageIsoImage S.f).hom ≫ (imageToKernel' S.f S.g S.zero) =
    S.abelianImageToKernel := by
  refine Mono.right_cancellation (f := kernel.ι S.g) _ _ ?_
  refine Epi.left_cancellation (f := (Abelian.imageIsoImage S.f).inv) _ _ ?_
  conv_lhs => rw [← Category.assoc, ← Category.assoc,  Iso.inv_hom_id, Category.id_comp]
  simp only [imageToKernel']
  simp only [kernel.lift_ι, IsImage.isoExt_inv, image.isImage_lift,
    ShortComplex.abelianImageToKernel_comp_kernel_ι, equalizer_as_kernel]
  refine Epi.left_cancellation (f := factorThruImage S.f) _ _ ?_
  simp only [image.fac, image.fac_lift_assoc, Abelian.imageStrongEpiMonoFactorisation_I,
    Abelian.imageStrongEpiMonoFactorisation_e, kernel.lift_ι]

noncomputable def ShortComplex.homologyIsoCokernelAbelianImageToKernel (S : ShortComplex A) :
    S.homology ≅ Limits.cokernel S.abelianImageToKernel := by
  refine (S.homology'IsoHomology.symm.trans (homology'IsoCokernelImageToKernel' S.f S.g
    S.zero)).trans ?_
  refine cokernel.mapIso (imageToKernel' S.f S.g S.zero) S.abelianImageToKernel
    (Abelian.imageIsoImage S.f).symm (Iso.refl _) ?_
  refine Epi.left_cancellation (f := (Abelian.imageIsoImage S.f).hom) _ _ ?_
  rw [Iso.refl, Category.comp_id, ← Category.assoc, Iso.symm_hom, Iso.hom_inv_id,
    Category.id_comp, image_compat]

def imageToKernelIsIsoOfExact {S : ShortComplex A} (h : IsZero S.homology) :
    IsIso S.abelianImageToKernel := by
  have : Epi S.abelianImageToKernel := by
    refine NormalMonoCategory.epi_of_zero_cokernel _ (cokernel S.abelianImageToKernel) ?_
    have : cokernel.π S.abelianImageToKernel = 0 :=
      IsZero.eq_zero_of_tgt (IsZero.of_iso h (ShortComplex.homologyIsoCokernelAbelianImageToKernel
      S).symm) _
    conv => congr; congr; rw [← this]
    exact cokernelIsCokernel _
  exact isIso_of_mono_of_epi S.abelianImageToKernel (C := A)

/-
variable {ι : Type*} {c : ComplexShape ι}

def HomologicalComplex.homologyIsoCokernelAbelianImageToKernel (S : HomologicalComplex A c)
    {i j k : ι} (hij : i = c.prev j) (hjk : k = c.next j) :
  S.homology j ≅ Limits.cokernel
  (ShortComplex.abelianImageToKernel (ShortComplex.mk (S.d i j) (S.d j k) sorry)) := sorry
-/

#exit

noncomputable def CochainComplexToShortComplex (S : CochainComplex A ℤ) (n : ℤ) : ShortComplex A :=
  ShortComplex.mk (Abelian.image.ι (S.d (n - 1) n)) (Abelian.coimage.π (S.d n (n + 1)))
  (by refine Epi.left_cancellation (f := Abelian.factorThruImage (S.d (n - 1) n)) _ _ ?_
      refine Mono.right_cancellation (f := Abelian.factorThruCoimage (S.d n (n + 1))) _ _ ?_
      simp only [equalizer_as_kernel, coequalizer_as_cokernel, kernel.lift_ι_assoc, Category.assoc,
        cokernel.π_desc, HomologicalComplex.d_comp_d, comp_zero, zero_comp])

noncomputable def CochainComplexToShortComplexHomology (S : CochainComplex A ℤ) (n : ℤ) :
    S.homology' n ≅ (CochainComplexToShortComplex S n).homology := by
  refine (S.homology'Iso (j := n) (i := n - 1) (k := n + 1) (by simp only [ComplexShape.up_Rel,
    sub_add_cancel]) (by simp only [ComplexShape.up_Rel])).trans
    (Iso.trans ?_ (CochainComplexToShortComplex S n).homology'IsoHomology)
  simp only [CochainComplexToShortComplex]
  have heq : S.d n (n + 1) = Abelian.coimage.π (S.d n (n + 1)) ≫ Abelian.factorThruCoimage
    (S.d n (n + 1)) := by simp only [coequalizer_as_cokernel, cokernel.π_desc]
  set e := kernelSubobject_comp_mono_isIso (Abelian.coimage.π (S.d n (n + 1)))
    (Abelian.factorThruCoimage (S.d n (n + 1)))
  have h1 := kernelSubobject_comp_mono (Abelian.coimage.π (S.d n (n + 1)))
    (Abelian.factorThruCoimage (S.d n (n + 1)))
  simp_rw [← heq] at h1
  set e' := Subobject.isoOfEq _ _ h1.symm with e'def
  set f := homology'.desc (Abelian.image.ι (S.d (n - 1) n)) (Abelian.coimage.π (S.d n (n + 1)))
    sorry (D := homology' (S.d (n - 1) n) (S.d n (n + 1)) (S.d_comp_d _ _ _))
    (e'.hom ≫ homology'.π _ _ _)
    (by simp only [equalizer_as_kernel, coequalizer_as_cokernel, e'def, Subobject.isoOfEq_hom])



  rw [homology', homology', imageToKernel]--; erw [imageToKernel]




#exit
  refine (homology'IsoCokernelImageToKernel' _ _ _).trans
    ((homology'IsoCokernelImageToKernel' _ _ _).trans ?_).symm
