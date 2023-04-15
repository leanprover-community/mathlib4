/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison

! This file was ported from Lean 3 source module category_theory.subobject.limits
! leanprover-community/mathlib commit 956af7c76589f444f2e1313911bad16366ea476d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Subobject.Lattice

/-!
# Specific subobjects

We define `equalizer_subobject`, `kernel_subobject` and `image_subobject`, which are the subobjects
represented by the equalizer, kernel and image of (a pair of) morphism(s) and provide conditions
for `P.factors f`, where `P` is one of these special subobjects.

TODO: Add conditions for when `P` is a pullback subobject.
TODO: an iff characterisation of `(image_subobject f).factors h`

-/


universe v u

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Subobject Opposite

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace CategoryTheory

namespace Limits

section Equalizer

variable (f g : X ⟶ Y) [HasEqualizer f g]

/-- The equalizer of morphisms `f g : X ⟶ Y` as a `subobject X`. -/
abbrev equalizerSubobject : Subobject X :=
  Subobject.mk (equalizer.ι f g)
#align category_theory.limits.equalizer_subobject CategoryTheory.Limits.equalizerSubobject

/-- The underlying object of `equalizer_subobject f g` is (up to isomorphism!)
the same as the chosen object `equalizer f g`. -/
def equalizerSubobjectIso : (equalizerSubobject f g : C) ≅ equalizer f g :=
  Subobject.underlyingIso (equalizer.ι f g)
#align category_theory.limits.equalizer_subobject_iso CategoryTheory.Limits.equalizerSubobjectIso

@[simp, reassoc.1]
theorem equalizerSubobject_arrow :
    (equalizerSubobjectIso f g).Hom ≫ equalizer.ι f g = (equalizerSubobject f g).arrow := by
  simp [equalizer_subobject_iso]
#align category_theory.limits.equalizer_subobject_arrow CategoryTheory.Limits.equalizerSubobject_arrow

@[simp, reassoc.1]
theorem equalizerSubobject_arrow' :
    (equalizerSubobjectIso f g).inv ≫ (equalizerSubobject f g).arrow = equalizer.ι f g := by
  simp [equalizer_subobject_iso]
#align category_theory.limits.equalizer_subobject_arrow' CategoryTheory.Limits.equalizerSubobject_arrow'

@[reassoc.1]
theorem equalizerSubobject_arrow_comp :
    (equalizerSubobject f g).arrow ≫ f = (equalizerSubobject f g).arrow ≫ g := by
  rw [← equalizer_subobject_arrow, category.assoc, category.assoc, equalizer.condition]
#align category_theory.limits.equalizer_subobject_arrow_comp CategoryTheory.Limits.equalizerSubobject_arrow_comp

theorem equalizerSubobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) :
    (equalizerSubobject f g).Factors h :=
  ⟨equalizer.lift h w, by simp⟩
#align category_theory.limits.equalizer_subobject_factors CategoryTheory.Limits.equalizerSubobject_factors

theorem equalizerSubobject_factors_iff {W : C} (h : W ⟶ X) :
    (equalizerSubobject f g).Factors h ↔ h ≫ f = h ≫ g :=
  ⟨fun w => by
    rw [← subobject.factor_thru_arrow _ _ w, category.assoc, equalizer_subobject_arrow_comp,
      category.assoc],
    equalizerSubobject_factors f g h⟩
#align category_theory.limits.equalizer_subobject_factors_iff CategoryTheory.Limits.equalizerSubobject_factors_iff

end Equalizer

section Kernel

variable [HasZeroMorphisms C] (f : X ⟶ Y) [HasKernel f]

/-- The kernel of a morphism `f : X ⟶ Y` as a `subobject X`. -/
abbrev kernelSubobject : Subobject X :=
  Subobject.mk (kernel.ι f)
#align category_theory.limits.kernel_subobject CategoryTheory.Limits.kernelSubobject

/-- The underlying object of `kernel_subobject f` is (up to isomorphism!)
the same as the chosen object `kernel f`. -/
def kernelSubobjectIso : (kernelSubobject f : C) ≅ kernel f :=
  Subobject.underlyingIso (kernel.ι f)
#align category_theory.limits.kernel_subobject_iso CategoryTheory.Limits.kernelSubobjectIso

@[simp, reassoc.1, elementwise]
theorem kernelSubobject_arrow :
    (kernelSubobjectIso f).Hom ≫ kernel.ι f = (kernelSubobject f).arrow := by
  simp [kernel_subobject_iso]
#align category_theory.limits.kernel_subobject_arrow CategoryTheory.Limits.kernelSubobject_arrow

@[simp, reassoc.1, elementwise]
theorem kernelSubobject_arrow' :
    (kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f := by
  simp [kernel_subobject_iso]
#align category_theory.limits.kernel_subobject_arrow' CategoryTheory.Limits.kernelSubobject_arrow'

@[simp, reassoc.1, elementwise]
theorem kernelSubobject_arrow_comp : (kernelSubobject f).arrow ≫ f = 0 :=
  by
  rw [← kernel_subobject_arrow]
  simp only [category.assoc, kernel.condition, comp_zero]
#align category_theory.limits.kernel_subobject_arrow_comp CategoryTheory.Limits.kernelSubobject_arrow_comp

theorem kernelSubobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    (kernelSubobject f).Factors h :=
  ⟨kernel.lift _ h w, by simp⟩
#align category_theory.limits.kernel_subobject_factors CategoryTheory.Limits.kernelSubobject_factors

theorem kernelSubobject_factors_iff {W : C} (h : W ⟶ X) :
    (kernelSubobject f).Factors h ↔ h ≫ f = 0 :=
  ⟨fun w => by
    rw [← subobject.factor_thru_arrow _ _ w, category.assoc, kernel_subobject_arrow_comp,
      comp_zero],
    kernelSubobject_factors f h⟩
#align category_theory.limits.kernel_subobject_factors_iff CategoryTheory.Limits.kernelSubobject_factors_iff

/-- A factorisation of `h : W ⟶ X` through `kernel_subobject f`, assuming `h ≫ f = 0`. -/
def factorThruKernelSubobject {W : C} (h : W ⟶ X) (w : h ≫ f = 0) : W ⟶ kernelSubobject f :=
  (kernelSubobject f).factorThru h (kernelSubobject_factors f h w)
#align category_theory.limits.factor_thru_kernel_subobject CategoryTheory.Limits.factorThruKernelSubobject

@[simp]
theorem factorThruKernelSubobject_comp_arrow {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    factorThruKernelSubobject f h w ≫ (kernelSubobject f).arrow = h :=
  by
  dsimp [factor_thru_kernel_subobject]
  simp
#align category_theory.limits.factor_thru_kernel_subobject_comp_arrow CategoryTheory.Limits.factorThruKernelSubobject_comp_arrow

@[simp]
theorem factorThruKernelSubobject_comp_kernelSubobjectIso {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    factorThruKernelSubobject f h w ≫ (kernelSubobjectIso f).Hom = kernel.lift f h w :=
  (cancel_mono (kernel.ι f)).1 <| by simp
#align category_theory.limits.factor_thru_kernel_subobject_comp_kernel_subobject_iso CategoryTheory.Limits.factorThruKernelSubobject_comp_kernelSubobjectIso

section

variable {f} {X' Y' : C} {f' : X' ⟶ Y'} [HasKernel f']

/-- A commuting square induces a morphism between the kernel subobjects. -/
def kernelSubobjectMap (sq : Arrow.mk f ⟶ Arrow.mk f') :
    (kernelSubobject f : C) ⟶ (kernelSubobject f' : C) :=
  Subobject.factorThru _ ((kernelSubobject f).arrow ≫ sq.left)
    (kernelSubobject_factors _ _ (by simp [sq.w]))
#align category_theory.limits.kernel_subobject_map CategoryTheory.Limits.kernelSubobjectMap

@[simp, reassoc.1, elementwise]
theorem kernelSubobjectMap_arrow (sq : Arrow.mk f ⟶ Arrow.mk f') :
    kernelSubobjectMap sq ≫ (kernelSubobject f').arrow = (kernelSubobject f).arrow ≫ sq.left := by
  simp [kernel_subobject_map]
#align category_theory.limits.kernel_subobject_map_arrow CategoryTheory.Limits.kernelSubobjectMap_arrow

@[simp]
theorem kernelSubobjectMap_id : kernelSubobjectMap (𝟙 (Arrow.mk f)) = 𝟙 _ :=
  by
  ext
  simp
  dsimp
  simp
#align category_theory.limits.kernel_subobject_map_id CategoryTheory.Limits.kernelSubobjectMap_id

-- See library note [dsimp, simp].
@[simp]
theorem kernelSubobjectMap_comp {X'' Y'' : C} {f'' : X'' ⟶ Y''} [HasKernel f'']
    (sq : Arrow.mk f ⟶ Arrow.mk f') (sq' : Arrow.mk f' ⟶ Arrow.mk f'') :
    kernelSubobjectMap (sq ≫ sq') = kernelSubobjectMap sq ≫ kernelSubobjectMap sq' :=
  by
  ext
  simp
#align category_theory.limits.kernel_subobject_map_comp CategoryTheory.Limits.kernelSubobjectMap_comp

@[reassoc.1]
theorem kernel_map_comp_kernelSubobjectIso_inv (sq : Arrow.mk f ⟶ Arrow.mk f') :
    kernel.map f f' sq.1 sq.2 sq.3.symm ≫ (kernelSubobjectIso _).inv =
      (kernelSubobjectIso _).inv ≫ kernelSubobjectMap sq :=
  by ext <;> simp
#align category_theory.limits.kernel_map_comp_kernel_subobject_iso_inv CategoryTheory.Limits.kernel_map_comp_kernelSubobjectIso_inv

@[reassoc.1]
theorem kernelSubobjectIso_comp_kernel_map (sq : Arrow.mk f ⟶ Arrow.mk f') :
    (kernelSubobjectIso _).Hom ≫ kernel.map f f' sq.1 sq.2 sq.3.symm =
      kernelSubobjectMap sq ≫ (kernelSubobjectIso _).Hom :=
  by simp [← iso.comp_inv_eq, kernel_map_comp_kernel_subobject_iso_inv]
#align category_theory.limits.kernel_subobject_iso_comp_kernel_map CategoryTheory.Limits.kernelSubobjectIso_comp_kernel_map

end

@[simp]
theorem kernelSubobject_zero {A B : C} : kernelSubobject (0 : A ⟶ B) = ⊤ :=
  (isIso_iff_mk_eq_top _).mp (by infer_instance)
#align category_theory.limits.kernel_subobject_zero CategoryTheory.Limits.kernelSubobject_zero

instance isIso_kernelSubobject_zero_arrow : IsIso (kernelSubobject (0 : X ⟶ Y)).arrow :=
  (isIso_arrow_iff_eq_top _).mpr kernelSubobject_zero
#align category_theory.limits.is_iso_kernel_subobject_zero_arrow CategoryTheory.Limits.isIso_kernelSubobject_zero_arrow

theorem le_kernelSubobject (A : Subobject X) (h : A.arrow ≫ f = 0) : A ≤ kernelSubobject f :=
  Subobject.le_mk_of_comm (kernel.lift f A.arrow h) (by simp)
#align category_theory.limits.le_kernel_subobject CategoryTheory.Limits.le_kernelSubobject

/-- The isomorphism between the kernel of `f ≫ g` and the kernel of `g`,
when `f` is an isomorphism.
-/
def kernelSubobjectIsoComp {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobject (f ≫ g) : C) ≅ (kernelSubobject g : C) :=
  kernelSubobjectIso _ ≪≫ kernelIsIsoComp f g ≪≫ (kernelSubobjectIso _).symm
#align category_theory.limits.kernel_subobject_iso_comp CategoryTheory.Limits.kernelSubobjectIsoComp

@[simp]
theorem kernelSubobjectIsoComp_hom_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobjectIsoComp f g).Hom ≫ (kernelSubobject g).arrow =
      (kernelSubobject (f ≫ g)).arrow ≫ f :=
  by simp [kernel_subobject_iso_comp]
#align category_theory.limits.kernel_subobject_iso_comp_hom_arrow CategoryTheory.Limits.kernelSubobjectIsoComp_hom_arrow

@[simp]
theorem kernelSubobjectIsoComp_inv_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobjectIsoComp f g).inv ≫ (kernelSubobject (f ≫ g)).arrow =
      (kernelSubobject g).arrow ≫ inv f :=
  by simp [kernel_subobject_iso_comp]
#align category_theory.limits.kernel_subobject_iso_comp_inv_arrow CategoryTheory.Limits.kernelSubobjectIsoComp_inv_arrow

/-- The kernel of `f` is always a smaller subobject than the kernel of `f ≫ h`. -/
theorem kernelSubobject_comp_le (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [HasKernel (f ≫ h)] :
    kernelSubobject f ≤ kernelSubobject (f ≫ h) :=
  le_kernelSubobject _ _ (by simp)
#align category_theory.limits.kernel_subobject_comp_le CategoryTheory.Limits.kernelSubobject_comp_le

/-- Postcomposing by an monomorphism does not change the kernel subobject. -/
@[simp]
theorem kernelSubobject_comp_mono (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] :
    kernelSubobject (f ≫ h) = kernelSubobject f :=
  le_antisymm (le_kernelSubobject _ _ ((cancel_mono h).mp (by simp))) (kernelSubobject_comp_le f h)
#align category_theory.limits.kernel_subobject_comp_mono CategoryTheory.Limits.kernelSubobject_comp_mono

instance kernelSubobject_comp_mono_isIso (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] :
    IsIso (Subobject.ofLe _ _ (kernelSubobject_comp_le f h)) :=
  by
  rw [of_le_mk_le_mk_of_comm (kernel_comp_mono f h).inv]
  · infer_instance
  · simp
#align category_theory.limits.kernel_subobject_comp_mono_is_iso CategoryTheory.Limits.kernelSubobject_comp_mono_isIso

/-- Taking cokernels is an order-reversing map from the subobjects of `X` to the quotient objects
    of `X`. -/
@[simps]
def cokernelOrderHom [HasCokernels C] (X : C) : Subobject X →o (Subobject (op X))ᵒᵈ
    where
  toFun :=
    Subobject.lift (fun A f hf => Subobject.mk (cokernel.π f).op)
      (by
        rintro A B f g hf hg i rfl
        refine' subobject.mk_eq_mk_of_comm _ _ (iso.op _) (Quiver.Hom.unop_inj _)
        ·
          exact
            (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _)
                (is_cokernel_epi_comp (colimit.is_colimit _) i.hom rfl)).symm
        ·
          simp only [iso.comp_inv_eq, iso.op_hom, iso.symm_hom, unop_comp, Quiver.Hom.unop_op,
            colimit.comp_cocone_point_unique_up_to_iso_hom, cofork.of_π_ι_app,
            coequalizer.cofork_π])
  monotone' :=
    Subobject.ind₂ _ <| by
      intro A B f g hf hg h
      dsimp only [subobject.lift_mk]
      refine' subobject.mk_le_mk_of_comm (cokernel.desc f (cokernel.π g) _).op _
      · rw [← subobject.of_mk_le_mk_comp h, category.assoc, cokernel.condition, comp_zero]
      · exact Quiver.Hom.unop_inj (cokernel.π_desc _ _ _)
#align category_theory.limits.cokernel_order_hom CategoryTheory.Limits.cokernelOrderHom

/-- Taking kernels is an order-reversing map from the quotient objects of `X` to the subobjects of
    `X`. -/
@[simps]
def kernelOrderHom [HasKernels C] (X : C) : (Subobject (op X))ᵒᵈ →o Subobject X
    where
  toFun :=
    Subobject.lift (fun A f hf => Subobject.mk (kernel.ι f.unop))
      (by
        rintro A B f g hf hg i rfl
        refine' subobject.mk_eq_mk_of_comm _ _ _ _
        ·
          exact
            is_limit.cone_point_unique_up_to_iso (limit.is_limit _)
              (is_kernel_comp_mono (limit.is_limit (parallel_pair g.unop 0)) i.unop.hom rfl)
        · dsimp
          simp only [← iso.eq_inv_comp, limit.cone_point_unique_up_to_iso_inv_comp,
            fork.of_ι_π_app])
  monotone' :=
    Subobject.ind₂ _ <| by
      intro A B f g hf hg h
      dsimp only [subobject.lift_mk]
      refine' subobject.mk_le_mk_of_comm (kernel.lift g.unop (kernel.ι f.unop) _) _
      · rw [← subobject.of_mk_le_mk_comp h, unop_comp, kernel.condition_assoc, zero_comp]
      · exact Quiver.Hom.op_inj (by simp)
#align category_theory.limits.kernel_order_hom CategoryTheory.Limits.kernelOrderHom

end Kernel

section Image

variable (f : X ⟶ Y) [HasImage f]

/-- The image of a morphism `f g : X ⟶ Y` as a `subobject Y`. -/
abbrev imageSubobject : Subobject Y :=
  Subobject.mk (image.ι f)
#align category_theory.limits.image_subobject CategoryTheory.Limits.imageSubobject

/-- The underlying object of `image_subobject f` is (up to isomorphism!)
the same as the chosen object `image f`. -/
def imageSubobjectIso : (imageSubobject f : C) ≅ image f :=
  Subobject.underlyingIso (image.ι f)
#align category_theory.limits.image_subobject_iso CategoryTheory.Limits.imageSubobjectIso

@[simp, reassoc.1]
theorem imageSubobject_arrow : (imageSubobjectIso f).Hom ≫ image.ι f = (imageSubobject f).arrow :=
  by simp [image_subobject_iso]
#align category_theory.limits.image_subobject_arrow CategoryTheory.Limits.imageSubobject_arrow

@[simp, reassoc.1]
theorem imageSubobject_arrow' : (imageSubobjectIso f).inv ≫ (imageSubobject f).arrow = image.ι f :=
  by simp [image_subobject_iso]
#align category_theory.limits.image_subobject_arrow' CategoryTheory.Limits.imageSubobject_arrow'

/-- A factorisation of `f : X ⟶ Y` through `image_subobject f`. -/
def factorThruImageSubobject : X ⟶ imageSubobject f :=
  factorThruImage f ≫ (imageSubobjectIso f).inv
#align category_theory.limits.factor_thru_image_subobject CategoryTheory.Limits.factorThruImageSubobject

instance [HasEqualizers C] : Epi (factorThruImageSubobject f) :=
  by
  dsimp [factor_thru_image_subobject]
  apply epi_comp

@[simp, reassoc.1, elementwise]
theorem imageSubobject_arrow_comp : factorThruImageSubobject f ≫ (imageSubobject f).arrow = f := by
  simp [factor_thru_image_subobject, image_subobject_arrow]
#align category_theory.limits.image_subobject_arrow_comp CategoryTheory.Limits.imageSubobject_arrow_comp

theorem imageSubobject_arrow_comp_eq_zero [HasZeroMorphisms C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasImage f] [Epi (factorThruImageSubobject f)] (h : f ≫ g = 0) :
    (imageSubobject f).arrow ≫ g = 0 :=
  zero_of_epi_comp (factorThruImageSubobject f) <| by simp [h]
#align category_theory.limits.image_subobject_arrow_comp_eq_zero CategoryTheory.Limits.imageSubobject_arrow_comp_eq_zero

theorem imageSubobject_factors_comp_self {W : C} (k : W ⟶ X) : (imageSubobject f).Factors (k ≫ f) :=
  ⟨k ≫ factorThruImage f, by simp⟩
#align category_theory.limits.image_subobject_factors_comp_self CategoryTheory.Limits.imageSubobject_factors_comp_self

@[simp]
theorem factorThruImageSubobject_comp_self {W : C} (k : W ⟶ X) (h) :
    (imageSubobject f).factorThru (k ≫ f) h = k ≫ factorThruImageSubobject f :=
  by
  ext
  simp
#align category_theory.limits.factor_thru_image_subobject_comp_self CategoryTheory.Limits.factorThruImageSubobject_comp_self

@[simp]
theorem factorThruImageSubobject_comp_self_assoc {W W' : C} (k : W ⟶ W') (k' : W' ⟶ X) (h) :
    (imageSubobject f).factorThru (k ≫ k' ≫ f) h = k ≫ k' ≫ factorThruImageSubobject f :=
  by
  ext
  simp
#align category_theory.limits.factor_thru_image_subobject_comp_self_assoc CategoryTheory.Limits.factorThruImageSubobject_comp_self_assoc

/-- The image of `h ≫ f` is always a smaller subobject than the image of `f`. -/
theorem imageSubobject_comp_le {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)] :
    imageSubobject (h ≫ f) ≤ imageSubobject f :=
  Subobject.mk_le_mk_of_comm (image.preComp h f) (by simp)
#align category_theory.limits.image_subobject_comp_le CategoryTheory.Limits.imageSubobject_comp_le

section

open ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C]

@[simp]
theorem imageSubobject_zero_arrow : (imageSubobject (0 : X ⟶ Y)).arrow = 0 :=
  by
  rw [← image_subobject_arrow]
  simp
#align category_theory.limits.image_subobject_zero_arrow CategoryTheory.Limits.imageSubobject_zero_arrow

@[simp]
theorem imageSubobject_zero {A B : C} : imageSubobject (0 : A ⟶ B) = ⊥ :=
  Subobject.eq_of_comm (imageSubobjectIso _ ≪≫ imageZero ≪≫ Subobject.botCoeIsoZero.symm) (by simp)
#align category_theory.limits.image_subobject_zero CategoryTheory.Limits.imageSubobject_zero

end

section

variable [HasEqualizers C]

attribute [local instance] epi_comp

/-- The morphism `image_subobject (h ≫ f) ⟶ image_subobject f`
is an epimorphism when `h` is an epimorphism.
In general this does not imply that `image_subobject (h ≫ f) = image_subobject f`,
although it will when the ambient category is abelian.
 -/
instance imageSubobject_comp_le_epi_of_epi {X' : C} (h : X' ⟶ X) [Epi h] (f : X ⟶ Y) [HasImage f]
    [HasImage (h ≫ f)] : Epi (Subobject.ofLe _ _ (imageSubobject_comp_le h f)) :=
  by
  rw [of_le_mk_le_mk_of_comm (image.pre_comp h f)]
  · infer_instance
  · simp
#align category_theory.limits.image_subobject_comp_le_epi_of_epi CategoryTheory.Limits.imageSubobject_comp_le_epi_of_epi

end

section

variable [HasEqualizers C]

/-- Postcomposing by an isomorphism gives an isomorphism between image subobjects. -/
def imageSubobjectCompIso (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobject (f ≫ h) : C) ≅ (imageSubobject f : C) :=
  imageSubobjectIso _ ≪≫ (image.compIso _ _).symm ≪≫ (imageSubobjectIso _).symm
#align category_theory.limits.image_subobject_comp_iso CategoryTheory.Limits.imageSubobjectCompIso

@[simp, reassoc.1]
theorem imageSubobjectCompIso_hom_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobjectCompIso f h).Hom ≫ (imageSubobject f).arrow =
      (imageSubobject (f ≫ h)).arrow ≫ inv h :=
  by simp [image_subobject_comp_iso]
#align category_theory.limits.image_subobject_comp_iso_hom_arrow CategoryTheory.Limits.imageSubobjectCompIso_hom_arrow

@[simp, reassoc.1]
theorem imageSubobjectCompIso_inv_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobjectCompIso f h).inv ≫ (imageSubobject (f ≫ h)).arrow =
      (imageSubobject f).arrow ≫ h :=
  by simp [image_subobject_comp_iso]
#align category_theory.limits.image_subobject_comp_iso_inv_arrow CategoryTheory.Limits.imageSubobjectCompIso_inv_arrow

end

theorem imageSubobject_mono (f : X ⟶ Y) [Mono f] : imageSubobject f = mk f :=
  eq_of_comm (imageSubobjectIso f ≪≫ imageMonoIsoSource f ≪≫ (underlyingIso f).symm) (by simp)
#align category_theory.limits.image_subobject_mono CategoryTheory.Limits.imageSubobject_mono

/-- Precomposing by an isomorphism does not change the image subobject. -/
theorem imageSubobject_iso_comp [HasEqualizers C] {X' : C} (h : X' ⟶ X) [IsIso h] (f : X ⟶ Y)
    [HasImage f] : imageSubobject (h ≫ f) = imageSubobject f :=
  le_antisymm (imageSubobject_comp_le h f)
    (Subobject.mk_le_mk_of_comm (inv (image.preComp h f)) (by simp))
#align category_theory.limits.image_subobject_iso_comp CategoryTheory.Limits.imageSubobject_iso_comp

theorem imageSubobject_le {A B : C} {X : Subobject B} (f : A ⟶ B) [HasImage f] (h : A ⟶ X)
    (w : h ≫ X.arrow = f) : imageSubobject f ≤ X :=
  Subobject.le_of_comm
    ((imageSubobjectIso f).Hom ≫
      image.lift
        { i := (X : C)
          e := h
          m := X.arrow })
    (by simp)
#align category_theory.limits.image_subobject_le CategoryTheory.Limits.imageSubobject_le

theorem imageSubobject_le_mk {A B : C} {X : C} (g : X ⟶ B) [Mono g] (f : A ⟶ B) [HasImage f]
    (h : A ⟶ X) (w : h ≫ g = f) : imageSubobject f ≤ Subobject.mk g :=
  imageSubobject_le f (h ≫ (Subobject.underlyingIso g).inv) (by simp [w])
#align category_theory.limits.image_subobject_le_mk CategoryTheory.Limits.imageSubobject_le_mk

/-- Given a commutative square between morphisms `f` and `g`,
we have a morphism in the category from `image_subobject f` to `image_subobject g`. -/
def imageSubobjectMap {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
    (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    (imageSubobject f : C) ⟶ (imageSubobject g : C) :=
  (imageSubobjectIso f).Hom ≫ image.map sq ≫ (imageSubobjectIso g).inv
#align category_theory.limits.image_subobject_map CategoryTheory.Limits.imageSubobjectMap

@[simp, reassoc.1]
theorem imageSubobjectMap_arrow {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
    (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    imageSubobjectMap sq ≫ (imageSubobject g).arrow = (imageSubobject f).arrow ≫ sq.right :=
  by
  simp only [image_subobject_map, category.assoc, image_subobject_arrow']
  erw [image.map_ι, ← category.assoc, image_subobject_arrow]
#align category_theory.limits.image_subobject_map_arrow CategoryTheory.Limits.imageSubobjectMap_arrow

theorem image_map_comp_imageSubobjectIso_inv {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
    [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    image.map sq ≫ (imageSubobjectIso _).inv = (imageSubobjectIso _).inv ≫ imageSubobjectMap sq :=
  by ext <;> simp
#align category_theory.limits.image_map_comp_image_subobject_iso_inv CategoryTheory.Limits.image_map_comp_imageSubobjectIso_inv

theorem imageSubobjectIso_comp_image_map {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
    [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    (imageSubobjectIso _).Hom ≫ image.map sq = imageSubobjectMap sq ≫ (imageSubobjectIso _).Hom :=
  by
  rw [← iso.comp_inv_eq, category.assoc, ← (image_subobject_iso (arrow.mk f).Hom).eq_inv_comp, ←
      image_map_comp_image_subobject_iso_inv] <;>
    rfl
#align category_theory.limits.image_subobject_iso_comp_image_map CategoryTheory.Limits.imageSubobjectIso_comp_image_map

end Image

end Limits

end CategoryTheory

