import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Tactic.Linarith

open CategoryTheory.Limits

open CategoryTheory

universe v u

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
