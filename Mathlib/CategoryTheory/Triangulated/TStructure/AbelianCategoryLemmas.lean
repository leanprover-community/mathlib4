import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Tactic.Linarith

open CategoryTheory.Limits

open CategoryTheory

universe v u u'

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

#exit

variable {A : Type u} [Category.{v} A] [Abelian A]

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
