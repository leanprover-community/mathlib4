/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Image-to-kernel comparison maps

Whenever `f : A ⟶ B` and `g : B ⟶ C` satisfy `w : f ≫ g = 0`,
we have `image_le_kernel f g w : imageSubobject f ≤ kernelSubobject g`
(assuming the appropriate images and kernels exist).

`imageToKernel f g w` is the corresponding morphism between objects in `C`.

-/

universe v u w

open CategoryTheory CategoryTheory.Limits

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

noncomputable section

section

variable {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g]

theorem image_le_kernel (w : f ≫ g = 0) : imageSubobject f ≤ kernelSubobject g :=
  imageSubobject_le_mk _ _ (kernel.lift _ _ w) (by simp)

/-- The canonical morphism `imageSubobject f ⟶ kernelSubobject g` when `f ≫ g = 0`.
-/
def imageToKernel (w : f ≫ g = 0) : (imageSubobject f : V) ⟶ (kernelSubobject g : V) :=
  Subobject.ofLE _ _ (image_le_kernel _ _ w)

instance (w : f ≫ g = 0) : Mono (imageToKernel f g w) := by
  dsimp only [imageToKernel]
  infer_instance

/-- Prefer `imageToKernel`. -/
@[simp]
theorem subobject_ofLE_as_imageToKernel (w : f ≫ g = 0) (h) :
    Subobject.ofLE (imageSubobject f) (kernelSubobject g) h = imageToKernel f g w :=
  rfl

attribute [local instance] HasForget.instFunLike

-- Porting note: removed elementwise attribute which does not seem to be helpful here
-- a more suitable lemma is added below
@[reassoc (attr := simp)]
theorem imageToKernel_arrow (w : f ≫ g = 0) :
    imageToKernel f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow := by
  simp [imageToKernel]

@[simp]
lemma imageToKernel_arrow_apply {FV : V → V → Type*} {CV : V → Type*}
    [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] (w : f ≫ g = 0)
    (x : ToType (Subobject.underlying.obj (imageSubobject f))) :
    (kernelSubobject g).arrow (imageToKernel f g w x) =
      (imageSubobject f).arrow x := by
  rw [← ConcreteCategory.comp_apply, imageToKernel_arrow]

-- This is less useful as a `simp` lemma than it initially appears,
-- as it "loses" the information the morphism factors through the image.
theorem factorThruImageSubobject_comp_imageToKernel (w : f ≫ g = 0) :
    factorThruImageSubobject f ≫ imageToKernel f g w = factorThruKernelSubobject g f w := by
  ext
  simp

end

section

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

@[simp]
theorem imageToKernel_zero_left [HasKernels V] [HasZeroObject V] {w} :
    imageToKernel (0 : A ⟶ B) g w = 0 := by
  ext
  simp

theorem imageToKernel_zero_right [HasImages V] {w} :
    imageToKernel f (0 : B ⟶ C) w =
      (imageSubobject f).arrow ≫ inv (kernelSubobject (0 : B ⟶ C)).arrow := by
  ext
  simp

section

variable [HasKernels V] [HasImages V]

theorem imageToKernel_comp_right {D : V} (h : C ⟶ D) (w : f ≫ g = 0) :
    imageToKernel f (g ≫ h) (by simp [reassoc_of% w]) =
      imageToKernel f g w ≫ Subobject.ofLE _ _ (kernelSubobject_comp_le g h) := by
  ext
  simp

theorem imageToKernel_comp_left {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0) :
    imageToKernel (h ≫ f) g (by simp [w]) =
      Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫ imageToKernel f g w := by
  ext
  simp

@[simp]
theorem imageToKernel_comp_mono {D : V} (h : C ⟶ D) [Mono h] (w) :
    imageToKernel f (g ≫ h) w =
      imageToKernel f g ((cancel_mono h).mp (by simpa using w : (f ≫ g) ≫ h = 0 ≫ h)) ≫
        (Subobject.isoOfEq _ _ (kernelSubobject_comp_mono g h)).inv := by
  ext
  simp

@[simp]
theorem imageToKernel_epi_comp {Z : V} (h : Z ⟶ A) [Epi h] (w) :
    imageToKernel (h ≫ f) g w =
      Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫
        imageToKernel f g ((cancel_epi h).mp (by simpa using w : h ≫ f ≫ g = h ≫ 0)) := by
  ext
  simp

end

@[simp]
theorem imageToKernel_comp_hom_inv_comp [HasEqualizers V] [HasImages V] {Z : V} {i : B ≅ Z} (w) :
    imageToKernel (f ≫ i.hom) (i.inv ≫ g) w =
      (imageSubobjectCompIso _ _).hom ≫
        imageToKernel f g (by simpa using w) ≫ (kernelSubobjectIsoComp i.inv g).inv := by
  ext
  simp

open ZeroObject

/-- `imageToKernel` for `A --0--> B --g--> C`, where `g` is a mono is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance imageToKernel_epi_of_zero_of_mono [HasKernels V] [HasZeroObject V] [Mono g] :
    Epi (imageToKernel (0 : A ⟶ B) g (by simp)) :=
  epi_of_target_iso_zero _ (kernelSubobjectIso g ≪≫ kernel.ofMono g)

/-- `imageToKernel` for `A --f--> B --0--> C`, where `g` is an epi is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance imageToKernel_epi_of_epi_of_zero [HasImages V] [Epi f] :
    Epi (imageToKernel f (0 : B ⟶ C) (by simp)) := by
  simp only [imageToKernel_zero_right]
  haveI := epi_image_of_epi f
  rw [← imageSubobject_arrow]
  infer_instance

end

section imageToKernel'

/-!
We provide a variant `imageToKernel' : image f ⟶ kernel g`,
and use this to give alternative formulas for `homology f g w`.
-/

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) [HasKernels V] [HasImages V]

/-- While `imageToKernel f g w` provides a morphism
`imageSubobject f ⟶ kernelSubobject g`
in terms of the subobject API,
this variant provides a morphism
`image f ⟶ kernel g`,
which is sometimes more convenient.
-/
def imageToKernel' (w : f ≫ g = 0) : image f ⟶ kernel g :=
  kernel.lift g (image.ι f) <| by
    ext
    simpa using w

@[simp]
theorem imageSubobjectIso_imageToKernel' (w : f ≫ g = 0) :
    (imageSubobjectIso f).hom ≫ imageToKernel' f g w =
      imageToKernel f g w ≫ (kernelSubobjectIso g).hom := by
  ext
  simp [imageToKernel']

@[simp]
theorem imageToKernel'_kernelSubobjectIso (w : f ≫ g = 0) :
    imageToKernel' f g w ≫ (kernelSubobjectIso g).inv =
      (imageSubobjectIso f).inv ≫ imageToKernel f g w := by
  ext
  simp [imageToKernel']

end imageToKernel'

end
