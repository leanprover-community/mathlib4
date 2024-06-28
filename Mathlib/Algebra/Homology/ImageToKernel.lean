/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Subobject.Limits

#align_import algebra.homology.image_to_kernel from "leanprover-community/mathlib"@"618ea3d5c99240cd7000d8376924906a148bf9ff"

/-!
# Image-to-kernel comparison maps

Whenever `f : A ⟶ B` and `g : B ⟶ C` satisfy `w : f ≫ g = 0`,
we have `image_le_kernel f g w : imageSubobject f ≤ kernelSubobject g`
(assuming the appropriate images and kernels exist).

`imageToKernel f g w` is the corresponding morphism between objects in `C`.

We define `homology' f g w` of such a pair as the cokernel of `imageToKernel f g w`.

Note: As part of the transition to the new homology API, `homology` is temporarily
renamed `homology'`. It is planned that this definition shall be removed and replaced by
`ShortComplex.homology`.

-/

universe v u w

open CategoryTheory CategoryTheory.Limits

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

open scoped Classical

noncomputable section

section

variable {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g]

theorem image_le_kernel (w : f ≫ g = 0) : imageSubobject f ≤ kernelSubobject g :=
  imageSubobject_le_mk _ _ (kernel.lift _ _ w) (by simp)
#align image_le_kernel image_le_kernel

/-- The canonical morphism `imageSubobject f ⟶ kernelSubobject g` when `f ≫ g = 0`.
-/
def imageToKernel (w : f ≫ g = 0) : (imageSubobject f : V) ⟶ (kernelSubobject g : V) :=
  Subobject.ofLE _ _ (image_le_kernel _ _ w)
#align image_to_kernel imageToKernel

instance (w : f ≫ g = 0) : Mono (imageToKernel f g w) := by
  dsimp only [imageToKernel]
  infer_instance

/-- Prefer `imageToKernel`. -/
@[simp]
theorem subobject_ofLE_as_imageToKernel (w : f ≫ g = 0) (h) :
    Subobject.ofLE (imageSubobject f) (kernelSubobject g) h = imageToKernel f g w :=
  rfl
#align subobject_of_le_as_image_to_kernel subobject_ofLE_as_imageToKernel

attribute [local instance] ConcreteCategory.instFunLike

-- Porting note: removed elementwise attribute which does not seem to be helpful here
-- a more suitable lemma is added below
@[reassoc (attr := simp)]
theorem imageToKernel_arrow (w : f ≫ g = 0) :
    imageToKernel f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow := by
  simp [imageToKernel]
#align image_to_kernel_arrow imageToKernel_arrow

@[simp]
lemma imageToKernel_arrow_apply [ConcreteCategory V] (w : f ≫ g = 0)
    (x : (forget V).obj (Subobject.underlying.obj (imageSubobject f))) :
    (kernelSubobject g).arrow (imageToKernel f g w x) =
      (imageSubobject f).arrow x := by
  rw [← comp_apply, imageToKernel_arrow]

-- This is less useful as a `simp` lemma than it initially appears,
-- as it "loses" the information the morphism factors through the image.
theorem factorThruImageSubobject_comp_imageToKernel (w : f ≫ g = 0) :
    factorThruImageSubobject f ≫ imageToKernel f g w = factorThruKernelSubobject g f w := by
  ext
  simp
#align factor_thru_image_subobject_comp_image_to_kernel factorThruImageSubobject_comp_imageToKernel

end

section

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

@[simp]
theorem imageToKernel_zero_left [HasKernels V] [HasZeroObject V] {w} :
    imageToKernel (0 : A ⟶ B) g w = 0 := by
  ext
  simp
#align image_to_kernel_zero_left imageToKernel_zero_left

theorem imageToKernel_zero_right [HasImages V] {w} :
    imageToKernel f (0 : B ⟶ C) w =
      (imageSubobject f).arrow ≫ inv (kernelSubobject (0 : B ⟶ C)).arrow := by
  ext
  simp
#align image_to_kernel_zero_right imageToKernel_zero_right

section

variable [HasKernels V] [HasImages V]

theorem imageToKernel_comp_right {D : V} (h : C ⟶ D) (w : f ≫ g = 0) :
    imageToKernel f (g ≫ h) (by simp [reassoc_of% w]) =
      imageToKernel f g w ≫ Subobject.ofLE _ _ (kernelSubobject_comp_le g h) := by
  ext
  simp
#align image_to_kernel_comp_right imageToKernel_comp_right

theorem imageToKernel_comp_left {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0) :
    imageToKernel (h ≫ f) g (by simp [w]) =
      Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫ imageToKernel f g w := by
  ext
  simp
#align image_to_kernel_comp_left imageToKernel_comp_left

@[simp]
theorem imageToKernel_comp_mono {D : V} (h : C ⟶ D) [Mono h] (w) :
    imageToKernel f (g ≫ h) w =
      imageToKernel f g ((cancel_mono h).mp (by simpa using w : (f ≫ g) ≫ h = 0 ≫ h)) ≫
        (Subobject.isoOfEq _ _ (kernelSubobject_comp_mono g h)).inv := by
  ext
  simp
#align image_to_kernel_comp_mono imageToKernel_comp_mono

@[simp]
theorem imageToKernel_epi_comp {Z : V} (h : Z ⟶ A) [Epi h] (w) :
    imageToKernel (h ≫ f) g w =
      Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫
        imageToKernel f g ((cancel_epi h).mp (by simpa using w : h ≫ f ≫ g = h ≫ 0)) := by
  ext
  simp
#align image_to_kernel_epi_comp imageToKernel_epi_comp

end

@[simp]
theorem imageToKernel_comp_hom_inv_comp [HasEqualizers V] [HasImages V] {Z : V} {i : B ≅ Z} (w) :
    imageToKernel (f ≫ i.hom) (i.inv ≫ g) w =
      (imageSubobjectCompIso _ _).hom ≫
        imageToKernel f g (by simpa using w) ≫ (kernelSubobjectIsoComp i.inv g).inv := by
  ext
  simp
#align image_to_kernel_comp_hom_inv_comp imageToKernel_comp_hom_inv_comp

open ZeroObject

/-- `imageToKernel` for `A --0--> B --g--> C`, where `g` is a mono is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance imageToKernel_epi_of_zero_of_mono [HasKernels V] [HasZeroObject V] [Mono g] :
    Epi (imageToKernel (0 : A ⟶ B) g (by simp)) :=
  epi_of_target_iso_zero _ (kernelSubobjectIso g ≪≫ kernel.ofMono g)
#align image_to_kernel_epi_of_zero_of_mono imageToKernel_epi_of_zero_of_mono

/-- `imageToKernel` for `A --f--> B --0--> C`, where `g` is an epi is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance imageToKernel_epi_of_epi_of_zero [HasImages V] [Epi f] :
    Epi (imageToKernel f (0 : B ⟶ C) (by simp)) := by
  simp only [imageToKernel_zero_right]
  haveI := epi_image_of_epi f
  rw [← imageSubobject_arrow]
  exact @epi_comp _ _ _ _ _ _ (epi_comp _ _) _ _
#align image_to_kernel_epi_of_epi_of_zero imageToKernel_epi_of_epi_of_zero

end

section

variable {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g]

/-- The homology of a pair of morphisms `f : A ⟶ B` and `g : B ⟶ C` satisfying `f ≫ g = 0`
is the cokernel of the `imageToKernel` morphism for `f` and `g`.
-/
def homology' {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g] (w : f ≫ g = 0)
    [HasCokernel (imageToKernel f g w)] : V :=
  cokernel (imageToKernel f g w)
#align homology homology'

section

variable (w : f ≫ g = 0) [HasCokernel (imageToKernel f g w)]

/-- The morphism from cycles to homology. -/
def homology'.π : (kernelSubobject g : V) ⟶ homology' f g w :=
  cokernel.π _
#align homology.π homology'.π

@[simp]
theorem homology'.condition : imageToKernel f g w ≫ homology'.π f g w = 0 :=
  cokernel.condition _
#align homology.condition homology'.condition

/-- To construct a map out of homology, it suffices to construct a map out of the cycles
which vanishes on boundaries.
-/
def homology'.desc {D : V} (k : (kernelSubobject g : V) ⟶ D) (p : imageToKernel f g w ≫ k = 0) :
    homology' f g w ⟶ D :=
  cokernel.desc _ k p
#align homology.desc homology'.desc

-- Porting note: removed elementwise attribute which does not seem to be helpful here
@[reassoc (attr := simp)]
theorem homology'.π_desc {D : V} (k : (kernelSubobject g : V) ⟶ D)
    (p : imageToKernel f g w ≫ k = 0) : homology'.π f g w ≫ homology'.desc f g w k p = k := by
  simp [homology'.π, homology'.desc]
#align homology.π_desc homology'.π_desc

/-- To check two morphisms out of `homology' f g w` are equal, it suffices to check on cycles. -/
@[ext]
theorem homology'.ext {D : V} {k k' : homology' f g w ⟶ D}
    (p : homology'.π f g w ≫ k = homology'.π f g w ≫ k') : k = k' :=
  coequalizer.hom_ext p
#align homology.ext homology'.ext

/-- The cokernel of the map `Im f ⟶ Ker 0` is isomorphic to the cokernel of `f.` -/
def homology'OfZeroRight [HasCokernel (imageToKernel f (0 : B ⟶ C) comp_zero)] [HasCokernel f]
    [HasCokernel (image.ι f)] [Epi (factorThruImage f)] :
    homology' f (0 : B ⟶ C) comp_zero ≅ cokernel f :=
  (cokernel.mapIso _ _ (imageSubobjectIso _) ((kernelSubobjectIso 0).trans kernelZeroIsoSource)
        (by simp)).trans
    (cokernelImageι _)
#align homology_of_zero_right homology'OfZeroRight

/-- The kernel of the map `Im 0 ⟶ Ker f` is isomorphic to the kernel of `f.` -/
def homology'OfZeroLeft [HasZeroObject V] [HasKernels V] [HasImage (0 : A ⟶ B)]
    [HasCokernel (imageToKernel (0 : A ⟶ B) g zero_comp)] :
    homology' (0 : A ⟶ B) g zero_comp ≅ kernel g :=
  ((cokernelIsoOfEq <| imageToKernel_zero_left _).trans cokernelZeroIsoTarget).trans
    (kernelSubobjectIso _)
#align homology_of_zero_left homology'OfZeroLeft

/-- `homology 0 0 _` is just the middle object. -/
@[simps]
def homology'ZeroZero [HasZeroObject V] [HasImage (0 : A ⟶ B)]
    [HasCokernel (imageToKernel (0 : A ⟶ B) (0 : B ⟶ C) zero_comp)] :
    homology' (0 : A ⟶ B) (0 : B ⟶ C) zero_comp ≅ B where
  hom := homology'.desc (0 : A ⟶ B) (0 : B ⟶ C) zero_comp (kernelSubobject 0).arrow (by simp)
  inv := inv (kernelSubobject 0).arrow ≫ homology'.π _ _ _
#align homology_zero_zero homology'ZeroZero

end

section

variable {f g} (w : f ≫ g = 0) {A' B' C' : V} {f' : A' ⟶ B'} [HasImage f'] {g' : B' ⟶ C'}
  [HasKernel g'] (w' : f' ≫ g' = 0) (α : Arrow.mk f ⟶ Arrow.mk f') [HasImageMap α]
  (β : Arrow.mk g ⟶ Arrow.mk g') {A₁ B₁ C₁ : V} {f₁ : A₁ ⟶ B₁} [HasImage f₁] {g₁ : B₁ ⟶ C₁}
  [HasKernel g₁] (w₁ : f₁ ≫ g₁ = 0) {A₂ B₂ C₂ : V} {f₂ : A₂ ⟶ B₂} [HasImage f₂] {g₂ : B₂ ⟶ C₂}
  [HasKernel g₂] (w₂ : f₂ ≫ g₂ = 0) {A₃ B₃ C₃ : V} {f₃ : A₃ ⟶ B₃} [HasImage f₃] {g₃ : B₃ ⟶ C₃}
  [HasKernel g₃] (w₃ : f₃ ≫ g₃ = 0) (α₁ : Arrow.mk f₁ ⟶ Arrow.mk f₂) [HasImageMap α₁]
  (β₁ : Arrow.mk g₁ ⟶ Arrow.mk g₂) (α₂ : Arrow.mk f₂ ⟶ Arrow.mk f₃) [HasImageMap α₂]
  (β₂ : Arrow.mk g₂ ⟶ Arrow.mk g₃)

/-- Given compatible commutative squares between
a pair `f g` and a pair `f' g'` satisfying `f ≫ g = 0` and `f' ≫ g' = 0`,
the `imageToKernel` morphisms intertwine the induced map on kernels and the induced map on images.
-/
@[reassoc]
theorem imageSubobjectMap_comp_imageToKernel (p : α.right = β.left) :
    imageToKernel f g w ≫ kernelSubobjectMap β = imageSubobjectMap α ≫ imageToKernel f' g' w' := by
  ext
  simp [p]
#align image_subobject_map_comp_image_to_kernel imageSubobjectMap_comp_imageToKernel

variable [HasCokernel (imageToKernel f g w)] [HasCokernel (imageToKernel f' g' w')]
variable [HasCokernel (imageToKernel f₁ g₁ w₁)]
variable [HasCokernel (imageToKernel f₂ g₂ w₂)]
variable [HasCokernel (imageToKernel f₃ g₃ w₃)]

/-- Given compatible commutative squares between
a pair `f g` and a pair `f' g'` satisfying `f ≫ g = 0` and `f' ≫ g' = 0`,
we get a morphism on homology.
-/
def homology'.map (p : α.right = β.left) : homology' f g w ⟶ homology' f' g' w' :=
  cokernel.desc _ (kernelSubobjectMap β ≫ cokernel.π _) <| by
    rw [imageSubobjectMap_comp_imageToKernel_assoc w w' α β p]
    simp only [cokernel.condition, comp_zero]
#align homology.map homology'.map

-- Porting note: removed elementwise attribute which does not seem to be helpful here,
-- the correct lemma is stated below
@[reassoc (attr := simp)]
theorem homology'.π_map (p : α.right = β.left) :
    homology'.π f g w ≫ homology'.map w w' α β p =
      kernelSubobjectMap β ≫ homology'.π f' g' w' := by
  simp only [homology'.π, homology'.map, cokernel.π_desc]
#align homology.π_map homology'.π_map

section

attribute [local instance] ConcreteCategory.instFunLike

@[simp]
lemma homology'.π_map_apply [ConcreteCategory.{w} V] (p : α.right = β.left)
    (x : (forget V).obj (Subobject.underlying.obj (kernelSubobject g))) :
    homology'.map w w' α β p (homology'.π f g w x) =
      homology'.π f' g' w' (kernelSubobjectMap β x) := by
  simp only [← comp_apply, homology'.π_map w w' α β p]

end

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem homology'.map_desc (p : α.right = β.left) {D : V} (k : (kernelSubobject g' : V) ⟶ D)
    (z : imageToKernel f' g' w' ≫ k = 0) :
    homology'.map w w' α β p ≫ homology'.desc f' g' w' k z =
      homology'.desc f g w (kernelSubobjectMap β ≫ k)
        (by simp only [imageSubobjectMap_comp_imageToKernel_assoc w w' α β p, z, comp_zero]) := by
  ext
  simp only [homology'.π_desc, homology'.π_map_assoc]
#align homology.map_desc homology'.map_desc

@[simp]
theorem homology'.map_id : homology'.map w w (𝟙 _) (𝟙 _) rfl = 𝟙 _ := by
  ext
  simp only [homology'.π_map, kernelSubobjectMap_id, Category.id_comp, Category.comp_id]
#align homology.map_id homology'.map_id

/-- Auxiliary lemma for homology computations. -/
theorem homology'.comp_right_eq_comp_left {V : Type*} [Category V] {A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ : V}
    {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} {f₃ : A₃ ⟶ B₃} {g₃ : B₃ ⟶ C₃}
    {α₁ : Arrow.mk f₁ ⟶ Arrow.mk f₂} {β₁ : Arrow.mk g₁ ⟶ Arrow.mk g₂}
    {α₂ : Arrow.mk f₂ ⟶ Arrow.mk f₃} {β₂ : Arrow.mk g₂ ⟶ Arrow.mk g₃} (p₁ : α₁.right = β₁.left)
    (p₂ : α₂.right = β₂.left) : (α₁ ≫ α₂).right = (β₁ ≫ β₂).left := by
  simp only [Arrow.comp_left, Arrow.comp_right, p₁, p₂]
#align homology.comp_right_eq_comp_left homology'.comp_right_eq_comp_left

@[reassoc]
theorem homology'.map_comp (p₁ : α₁.right = β₁.left) (p₂ : α₂.right = β₂.left) :
    homology'.map w₁ w₂ α₁ β₁ p₁ ≫ homology'.map w₂ w₃ α₂ β₂ p₂ =
      homology'.map w₁ w₃ (α₁ ≫ α₂) (β₁ ≫ β₂) (homology'.comp_right_eq_comp_left p₁ p₂) := by
  ext
  simp only [kernelSubobjectMap_comp, homology'.π_map_assoc, homology'.π_map, Category.assoc]
#align homology.map_comp homology'.map_comp

/-- An isomorphism between two three-term complexes induces an isomorphism on homology. -/
def homology'.mapIso (α : Arrow.mk f₁ ≅ Arrow.mk f₂) (β : Arrow.mk g₁ ≅ Arrow.mk g₂)
    (p : α.hom.right = β.hom.left) : homology' f₁ g₁ w₁ ≅ homology' f₂ g₂ w₂ where
  hom := homology'.map w₁ w₂ α.hom β.hom p
  inv :=
    homology'.map w₂ w₁ α.inv β.inv
      (by
        rw [← cancel_mono α.hom.right, ← Comma.comp_right, α.inv_hom_id, Comma.id_right, p, ←
          Comma.comp_left, β.inv_hom_id, Comma.id_left]
        rfl)
  hom_inv_id := by
    rw [homology'.map_comp, ← homology'.map_id]
    congr <;> simp only [Iso.hom_inv_id]
  inv_hom_id := by
    rw [homology'.map_comp, ← homology'.map_id]
    congr <;> simp only [Iso.inv_hom_id]
#align homology.map_iso homology'.mapIso

end

end

section

variable {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0) {f' : A ⟶ B} {g' : B ⟶ C}
  (w' : f' ≫ g' = 0) [HasKernels V] [HasCokernels V] [HasImages V] [HasImageMaps V]

-- Porting note: removed the private auxiliary tactic which becomes unnecessary
--/-- Custom tactic to golf and speedup boring proofs in `homology.congr`. -/
--private unsafe def aux_tac : tactic Unit :=
--  sorry

/-- `homology f g w ≅ homology f' g' w'` if `f = f'` and `g = g'`.
(Note the objects are not changing here.)
-/
@[simps]
def homology'.congr (pf : f = f') (pg : g = g') : homology' f g w ≅ homology' f' g' w' where
  hom := homology'.map w w' ⟨𝟙 _, 𝟙 _, by aesop_cat⟩ ⟨𝟙 _, 𝟙 _, by aesop_cat⟩ rfl
  inv := homology'.map w' w ⟨𝟙 _, 𝟙 _, by aesop_cat⟩ ⟨𝟙 _, 𝟙 _, by aesop_cat⟩ rfl
  hom_inv_id := by
    obtain rfl := pf
    obtain rfl := pg
    rw [homology'.map_comp, ← homology'.map_id]
    congr <;> aesop_cat
  inv_hom_id := by
    obtain rfl := pf
    obtain rfl := pg
    rw [homology'.map_comp, ← homology'.map_id]
    congr <;> aesop_cat
#align homology.congr homology'.congr

end

/-!
We provide a variant `imageToKernel' : image f ⟶ kernel g`,
and use this to give alternative formulas for `homology f g w`.
-/


section imageToKernel'

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
#align image_to_kernel' imageToKernel'

@[simp]
theorem imageSubobjectIso_imageToKernel' (w : f ≫ g = 0) :
    (imageSubobjectIso f).hom ≫ imageToKernel' f g w =
      imageToKernel f g w ≫ (kernelSubobjectIso g).hom := by
  ext
  simp [imageToKernel']
#align image_subobject_iso_image_to_kernel' imageSubobjectIso_imageToKernel'

@[simp]
theorem imageToKernel'_kernelSubobjectIso (w : f ≫ g = 0) :
    imageToKernel' f g w ≫ (kernelSubobjectIso g).inv =
      (imageSubobjectIso f).inv ≫ imageToKernel f g w := by
  ext
  simp [imageToKernel']
#align image_to_kernel'_kernel_subobject_iso imageToKernel'_kernelSubobjectIso

variable [HasCokernels V]

/-- `homology' f g w` can be computed as the cokernel of `imageToKernel' f g w`.
-/
def homology'IsoCokernelImageToKernel' (w : f ≫ g = 0) :
    homology' f g w ≅ cokernel (imageToKernel' f g w) where
  hom := cokernel.map _ _ (imageSubobjectIso f).hom (kernelSubobjectIso g).hom
      (by simp only [imageSubobjectIso_imageToKernel'])
  inv := cokernel.map _ _ (imageSubobjectIso f).inv (kernelSubobjectIso g).inv
      (by simp only [imageToKernel'_kernelSubobjectIso])
  hom_inv_id := by
    -- Just calling `ext` here uses the higher priority `homology'.ext`,
    -- which precomposes with `homology'.π`.
    -- As we are trying to work in terms of `cokernel`, it is better to use `coequalizer.hom_ext`.
    apply coequalizer.hom_ext
    simp only [Iso.hom_inv_id_assoc, cokernel.π_desc, cokernel.π_desc_assoc, Category.assoc,
      coequalizer_as_cokernel]
    exact (Category.comp_id _).symm
  inv_hom_id := by
    ext
    simp only [Iso.inv_hom_id_assoc, cokernel.π_desc, Category.comp_id, cokernel.π_desc_assoc,
      Category.assoc]
#align homology_iso_cokernel_image_to_kernel' homology'IsoCokernelImageToKernel'

variable [HasEqualizers V]

/-- `homology f g w` can be computed as the cokernel of `kernel.lift g f w`.
-/
def homology'IsoCokernelLift (w : f ≫ g = 0) : homology' f g w ≅ cokernel (kernel.lift g f w) := by
  refine homology'IsoCokernelImageToKernel' f g w ≪≫ ?_
  have p : factorThruImage f ≫ imageToKernel' f g w = kernel.lift g f w := by
    ext
    simp [imageToKernel']
  exact (cokernelEpiComp _ _).symm ≪≫ cokernelIsoOfEq p
#align homology_iso_cokernel_lift homology'IsoCokernelLift

end imageToKernel'
