/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

#align_import category_theory.abelian.images from "leanprover-community/mathlib"@"9e7c80f638149bfb3504ba8ff48dfdbfc949fb1a"

/-!
# The abelian image and coimage.

In an abelian category we usually want the image of a morphism `f` to be defined as
`kernel (cokernel.π f)`, and the coimage to be defined as `cokernel (kernel.ι f)`.

We make these definitions here, as `Abelian.image f` and `Abelian.coimage f`
(without assuming the category is actually abelian),
and later relate these to the usual categorical notions when in an abelian category.

There is a canonical morphism `coimageImageComparison : Abelian.coimage f ⟶ Abelian.image f`.
Later we show that this is always an isomorphism in an abelian category,
and conversely a category with (co)kernels and finite products in which this morphism
is always an isomorphism is an abelian category.
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasKernels C] [HasCokernels C]

variable {P Q : C} (f : P ⟶ Q)

section Image

/-- The kernel of the cokernel of `f` is called the (abelian) image of `f`. -/
protected abbrev image : C :=
  kernel (cokernel.π f)
#align category_theory.abelian.image CategoryTheory.Abelian.image

/-- The inclusion of the image into the codomain. -/
protected abbrev image.ι : Abelian.image f ⟶ Q :=
  kernel.ι (cokernel.π f)
#align category_theory.abelian.image.ι CategoryTheory.Abelian.image.ι

/-- There is a canonical epimorphism `p : P ⟶ image f` for every `f`. -/
protected abbrev factorThruImage : P ⟶ Abelian.image f :=
  kernel.lift (cokernel.π f) f <| cokernel.condition f
#align category_theory.abelian.factor_thru_image CategoryTheory.Abelian.factorThruImage

-- Porting note: simp can prove this and reassoc version, removed tags
/-- `f` factors through its image via the canonical morphism `p`. -/
protected theorem image.fac : Abelian.factorThruImage f ≫ image.ι f = f :=
  kernel.lift_ι _ _ _
#align category_theory.abelian.image.fac CategoryTheory.Abelian.image.fac

instance mono_factorThruImage [Mono f] : Mono (Abelian.factorThruImage f) :=
  mono_of_mono_fac <| image.fac f
#align category_theory.abelian.mono_factor_thru_image CategoryTheory.Abelian.mono_factorThruImage

end Image

section Coimage

/-- The cokernel of the kernel of `f` is called the (abelian) coimage of `f`. -/
protected abbrev coimage : C :=
  cokernel (kernel.ι f)
#align category_theory.abelian.coimage CategoryTheory.Abelian.coimage

/-- The projection onto the coimage. -/
protected abbrev coimage.π : P ⟶ Abelian.coimage f :=
  cokernel.π (kernel.ι f)
#align category_theory.abelian.coimage.π CategoryTheory.Abelian.coimage.π

/-- There is a canonical monomorphism `i : coimage f ⟶ Q`. -/
protected abbrev factorThruCoimage : Abelian.coimage f ⟶ Q :=
  cokernel.desc (kernel.ι f) f <| kernel.condition f
#align category_theory.abelian.factor_thru_coimage CategoryTheory.Abelian.factorThruCoimage

/-- `f` factors through its coimage via the canonical morphism `p`. -/
protected theorem coimage.fac : coimage.π f ≫ Abelian.factorThruCoimage f = f :=
  cokernel.π_desc _ _ _
#align category_theory.abelian.coimage.fac CategoryTheory.Abelian.coimage.fac

instance epi_factorThruCoimage [Epi f] : Epi (Abelian.factorThruCoimage f) :=
  epi_of_epi_fac <| coimage.fac f
#align category_theory.abelian.epi_factor_thru_coimage CategoryTheory.Abelian.epi_factorThruCoimage

end Coimage

/-- The canonical map from the abelian coimage to the abelian image.
In any abelian category this is an isomorphism.

Conversely, any additive category with kernels and cokernels and
in which this is always an isomorphism, is abelian.

See <https://stacks.math.columbia.edu/tag/0107>
-/
def coimageImageComparison : Abelian.coimage f ⟶ Abelian.image f :=
  cokernel.desc (kernel.ι f) (kernel.lift (cokernel.π f) f (by simp)) (by ext; simp)
                                                               -- 🎉 no goals
                                                                          -- ⊢ (kernel.ι f ≫ kernel.lift (cokernel.π f) f (_ : f ≫ cokernel.π f = 0)) ≫ equ …
                                                                               -- 🎉 no goals
#align category_theory.abelian.coimage_image_comparison CategoryTheory.Abelian.coimageImageComparison

/-- An alternative formulation of the canonical map from the abelian coimage to the abelian image.
-/
def coimageImageComparison' : Abelian.coimage f ⟶ Abelian.image f :=
  kernel.lift (cokernel.π f) (cokernel.desc (kernel.ι f) f (by simp)) (by ext; simp)
                                                               -- 🎉 no goals
                                                                          -- ⊢ coequalizer.π (kernel.ι f) 0 ≫ cokernel.desc (kernel.ι f) f (_ : kernel.ι f  …
                                                                               -- 🎉 no goals
#align category_theory.abelian.coimage_image_comparison' CategoryTheory.Abelian.coimageImageComparison'

theorem coimageImageComparison_eq_coimageImageComparison' :
    coimageImageComparison f = coimageImageComparison' f := by
  ext
  -- ⊢ (coequalizer.π (kernel.ι f) 0 ≫ coimageImageComparison f) ≫ equalizer.ι (cok …
  simp [coimageImageComparison, coimageImageComparison']
  -- 🎉 no goals
#align category_theory.abelian.coimage_image_comparison_eq_coimage_image_comparison' CategoryTheory.Abelian.coimageImageComparison_eq_coimageImageComparison'

@[reassoc (attr := simp)]
theorem coimage_image_factorisation : coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f := by
  simp [coimageImageComparison]
  -- 🎉 no goals
#align category_theory.abelian.coimage_image_factorisation CategoryTheory.Abelian.coimage_image_factorisation

end CategoryTheory.Abelian
