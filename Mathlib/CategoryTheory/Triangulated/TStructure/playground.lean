import Mathlib.Algebra.Homology.ShortComplex.Abelian

open CategoryTheory Limits

variable {A : Type*} [Category A] [Abelian A] (S : ShortComplex A)

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
