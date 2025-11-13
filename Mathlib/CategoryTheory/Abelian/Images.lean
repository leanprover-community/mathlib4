/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

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

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {P Q : C} (f : P ⟶ Q)

section Image

variable [HasCokernel f] [HasKernel (cokernel.π f)]

/-- The kernel of the cokernel of `f` is called the (abelian) image of `f`. -/
protected abbrev image : C :=
  kernel (cokernel.π f)

/-- The inclusion of the image into the codomain. -/
protected abbrev image.ι : Abelian.image f ⟶ Q :=
  kernel.ι (cokernel.π f)

/-- There is a canonical epimorphism `p : P ⟶ image f` for every `f`. -/
protected abbrev factorThruImage : P ⟶ Abelian.image f :=
  kernel.lift (cokernel.π f) f <| cokernel.condition f

/-- `f` factors through its image via the canonical morphism `p`. -/
protected theorem image.fac : Abelian.factorThruImage f ≫ image.ι f = f :=
  kernel.lift_ι _ _ _

instance mono_factorThruImage [Mono f] : Mono (Abelian.factorThruImage f) :=
  mono_of_mono_fac <| image.fac f

end Image

section Coimage

variable [HasKernel f] [HasCokernel (kernel.ι f)]

/-- The cokernel of the kernel of `f` is called the (abelian) coimage of `f`. -/
protected abbrev coimage : C :=
  cokernel (kernel.ι f)

/-- The projection onto the coimage. -/
protected abbrev coimage.π : P ⟶ Abelian.coimage f :=
  cokernel.π (kernel.ι f)

/-- There is a canonical monomorphism `i : coimage f ⟶ Q`. -/
protected abbrev factorThruCoimage : Abelian.coimage f ⟶ Q :=
  cokernel.desc (kernel.ι f) f <| kernel.condition f

/-- `f` factors through its coimage via the canonical morphism `p`. -/
protected theorem coimage.fac : coimage.π f ≫ Abelian.factorThruCoimage f = f :=
  cokernel.π_desc _ _ _

instance epi_factorThruCoimage [Epi f] : Epi (Abelian.factorThruCoimage f) :=
  epi_of_epi_fac <| coimage.fac f

end Coimage

section Comparison

variable [HasCokernel f] [HasKernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]

/-- The canonical map from the abelian coimage to the abelian image.
In any abelian category this is an isomorphism.

Conversely, any additive category with kernels and cokernels and
in which this is always an isomorphism, is abelian. -/
@[stacks 0107]
def coimageImageComparison : Abelian.coimage f ⟶ Abelian.image f :=
  cokernel.desc (kernel.ι f) (kernel.lift (cokernel.π f) f (by simp)) (by ext; simp)

/-- An alternative formulation of the canonical map from the abelian coimage to the abelian image.
-/
def coimageImageComparison' : Abelian.coimage f ⟶ Abelian.image f :=
  kernel.lift (cokernel.π f) (cokernel.desc (kernel.ι f) f (by simp)) (by ext; simp)

theorem coimageImageComparison_eq_coimageImageComparison' :
    coimageImageComparison f = coimageImageComparison' f := by
  ext
  simp [coimageImageComparison, coimageImageComparison']

@[reassoc (attr := simp)]
theorem coimage_image_factorisation : coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f := by
  simp [coimageImageComparison]

end Comparison

variable [HasKernels C] [HasCokernels C]

/-- The coimage-image comparison morphism is functorial. -/
@[simps! obj map]
def coimageImageComparisonFunctor : Arrow C ⥤ Arrow C where
  obj f := Arrow.mk (coimageImageComparison f.hom)
  map {f g} η := Arrow.homMk
    (cokernel.map _ _ (kernel.map _ _ η.left η.right (by simp)) η.left (by simp))
    (kernel.map _ _ η.right (cokernel.map _ _ η.left η.right (by simp)) (by simp)) (by cat_disch)

end CategoryTheory.Abelian
