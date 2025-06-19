/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Specific subobjects

We define `equalizerSubobject`, `kernelSubobject` and `imageSubobject`, which are the subobjects
represented by the equalizer, kernel and image of (a pair of) morphism(s) and provide conditions
for `P.factors f`, where `P` is one of these special subobjects.

TODO: Add conditions for when `P` is a pullback subobject.
TODO: an iff characterisation of `(imageSubobject f).Factors h`

-/

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Subobject Opposite

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace CategoryTheory

namespace Limits

section Equalizer

variable (f g : X ⟶ Y) [HasEqualizer f g]

/-- The equalizer of morphisms `f g : X ⟶ Y` as a `Subobject X`. -/
abbrev equalizerSubobject : Subobject X :=
  Subobject.mk (equalizer.ι f g)

/-- The underlying object of `equalizerSubobject f g` is (up to isomorphism!)
the same as the chosen object `equalizer f g`. -/
def equalizerSubobjectIso : (equalizerSubobject f g : C) ≅ equalizer f g :=
  Subobject.underlyingIso (equalizer.ι f g)

@[reassoc (attr := simp)]
theorem equalizerSubobject_arrow :
    (equalizerSubobjectIso f g).hom ≫ equalizer.ι f g = (equalizerSubobject f g).arrow := by
  simp [equalizerSubobjectIso]

@[reassoc (attr := simp)]
theorem equalizerSubobject_arrow' :
    (equalizerSubobjectIso f g).inv ≫ (equalizerSubobject f g).arrow = equalizer.ι f g := by
  simp [equalizerSubobjectIso]

@[reassoc]
theorem equalizerSubobject_arrow_comp :
    (equalizerSubobject f g).arrow ≫ f = (equalizerSubobject f g).arrow ≫ g := by
  rw [← equalizerSubobject_arrow, Category.assoc, Category.assoc, equalizer.condition]

theorem equalizerSubobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) :
    (equalizerSubobject f g).Factors h :=
  ⟨equalizer.lift h w, by simp⟩

theorem equalizerSubobject_factors_iff {W : C} (h : W ⟶ X) :
    (equalizerSubobject f g).Factors h ↔ h ≫ f = h ≫ g :=
  ⟨fun w => by
    rw [← Subobject.factorThru_arrow _ _ w, Category.assoc, equalizerSubobject_arrow_comp,
      Category.assoc],
    equalizerSubobject_factors f g h⟩

end Equalizer

section Kernel

variable [HasZeroMorphisms C] (f : X ⟶ Y) [HasKernel f]

/-- The kernel of a morphism `f : X ⟶ Y` as a `Subobject X`. -/
abbrev kernelSubobject : Subobject X :=
  Subobject.mk (kernel.ι f)

/-- The underlying object of `kernelSubobject f` is (up to isomorphism!)
the same as the chosen object `kernel f`. -/
def kernelSubobjectIso : (kernelSubobject f : C) ≅ kernel f :=
  Subobject.underlyingIso (kernel.ι f)

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem kernelSubobject_arrow :
    (kernelSubobjectIso f).hom ≫ kernel.ι f = (kernelSubobject f).arrow := by
  simp [kernelSubobjectIso]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem kernelSubobject_arrow' :
    (kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f := by
  simp [kernelSubobjectIso]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem kernelSubobject_arrow_comp : (kernelSubobject f).arrow ≫ f = 0 := by
  rw [← kernelSubobject_arrow]
  simp only [Category.assoc, kernel.condition, comp_zero]

theorem kernelSubobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    (kernelSubobject f).Factors h :=
  ⟨kernel.lift _ h w, by simp⟩

theorem kernelSubobject_factors_iff {W : C} (h : W ⟶ X) :
    (kernelSubobject f).Factors h ↔ h ≫ f = 0 :=
  ⟨fun w => by
    rw [← Subobject.factorThru_arrow _ _ w, Category.assoc, kernelSubobject_arrow_comp,
      comp_zero],
    kernelSubobject_factors f h⟩

/-- A factorisation of `h : W ⟶ X` through `kernelSubobject f`, assuming `h ≫ f = 0`. -/
def factorThruKernelSubobject {W : C} (h : W ⟶ X) (w : h ≫ f = 0) : W ⟶ kernelSubobject f :=
  (kernelSubobject f).factorThru h (kernelSubobject_factors f h w)

@[simp]
theorem factorThruKernelSubobject_comp_arrow {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    factorThruKernelSubobject f h w ≫ (kernelSubobject f).arrow = h := by
  dsimp [factorThruKernelSubobject]
  simp

@[simp]
theorem factorThruKernelSubobject_comp_kernelSubobjectIso {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    factorThruKernelSubobject f h w ≫ (kernelSubobjectIso f).hom = kernel.lift f h w :=
  (cancel_mono (kernel.ι f)).1 <| by simp

section

variable {f} {X' Y' : C} {f' : X' ⟶ Y'} [HasKernel f']

/-- A commuting square induces a morphism between the kernel subobjects. -/
def kernelSubobjectMap (sq : Arrow.mk f ⟶ Arrow.mk f') :
    (kernelSubobject f : C) ⟶ (kernelSubobject f' : C) :=
  Subobject.factorThru _ ((kernelSubobject f).arrow ≫ sq.left)
    (kernelSubobject_factors _ _ (by simp [sq.w]))

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem kernelSubobjectMap_arrow (sq : Arrow.mk f ⟶ Arrow.mk f') :
    kernelSubobjectMap sq ≫ (kernelSubobject f').arrow = (kernelSubobject f).arrow ≫ sq.left := by
  simp [kernelSubobjectMap]

@[simp]
theorem kernelSubobjectMap_id : kernelSubobjectMap (𝟙 (Arrow.mk f)) = 𝟙 _ := by aesop_cat

@[simp]
theorem kernelSubobjectMap_comp {X'' Y'' : C} {f'' : X'' ⟶ Y''} [HasKernel f'']
    (sq : Arrow.mk f ⟶ Arrow.mk f') (sq' : Arrow.mk f' ⟶ Arrow.mk f'') :
    kernelSubobjectMap (sq ≫ sq') = kernelSubobjectMap sq ≫ kernelSubobjectMap sq' := by
  aesop_cat

@[reassoc]
theorem kernel_map_comp_kernelSubobjectIso_inv (sq : Arrow.mk f ⟶ Arrow.mk f') :
    kernel.map f f' sq.1 sq.2 sq.3.symm ≫ (kernelSubobjectIso _).inv =
      (kernelSubobjectIso _).inv ≫ kernelSubobjectMap sq := by aesop_cat

@[reassoc]
theorem kernelSubobjectIso_comp_kernel_map (sq : Arrow.mk f ⟶ Arrow.mk f') :
    (kernelSubobjectIso _).hom ≫ kernel.map f f' sq.1 sq.2 sq.3.symm =
      kernelSubobjectMap sq ≫ (kernelSubobjectIso _).hom := by
  simp [← Iso.comp_inv_eq, kernel_map_comp_kernelSubobjectIso_inv]

end

@[simp]
theorem kernelSubobject_zero {A B : C} : kernelSubobject (0 : A ⟶ B) = ⊤ :=
  (isIso_iff_mk_eq_top _).mp (by infer_instance)

instance isIso_kernelSubobject_zero_arrow : IsIso (kernelSubobject (0 : X ⟶ Y)).arrow :=
  (isIso_arrow_iff_eq_top _).mpr kernelSubobject_zero

theorem le_kernelSubobject (A : Subobject X) (h : A.arrow ≫ f = 0) : A ≤ kernelSubobject f :=
  Subobject.le_mk_of_comm (kernel.lift f A.arrow h) (by simp)

/-- The isomorphism between the kernel of `f ≫ g` and the kernel of `g`,
when `f` is an isomorphism.
-/
def kernelSubobjectIsoComp {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobject (f ≫ g) : C) ≅ (kernelSubobject g : C) :=
  kernelSubobjectIso _ ≪≫ kernelIsIsoComp f g ≪≫ (kernelSubobjectIso _).symm

@[simp]
theorem kernelSubobjectIsoComp_hom_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobjectIsoComp f g).hom ≫ (kernelSubobject g).arrow =
      (kernelSubobject (f ≫ g)).arrow ≫ f := by
  simp [kernelSubobjectIsoComp]

@[simp]
theorem kernelSubobjectIsoComp_inv_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobjectIsoComp f g).inv ≫ (kernelSubobject (f ≫ g)).arrow =
      (kernelSubobject g).arrow ≫ inv f := by
  simp [kernelSubobjectIsoComp]

/-- The kernel of `f` is always a smaller subobject than the kernel of `f ≫ h`. -/
theorem kernelSubobject_comp_le (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [HasKernel (f ≫ h)] :
    kernelSubobject f ≤ kernelSubobject (f ≫ h) :=
  le_kernelSubobject _ _ (by simp)

/-- Postcomposing by a monomorphism does not change the kernel subobject. -/
@[simp]
theorem kernelSubobject_comp_mono (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] :
    kernelSubobject (f ≫ h) = kernelSubobject f :=
  le_antisymm (le_kernelSubobject _ _ ((cancel_mono h).mp (by simp))) (kernelSubobject_comp_le f h)

instance kernelSubobject_comp_mono_isIso (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] :
    IsIso (Subobject.ofLE _ _ (kernelSubobject_comp_le f h)) := by
  rw [ofLE_mk_le_mk_of_comm (kernelCompMono f h).inv]
  · infer_instance
  · simp

/-- Taking cokernels is an order-reversing map from the subobjects of `X` to the quotient objects
    of `X`. -/
@[simps]
def cokernelOrderHom [HasCokernels C] (X : C) : Subobject X →o (Subobject (op X))ᵒᵈ where
  toFun :=
    Subobject.lift (fun _ f _ => Subobject.mk (cokernel.π f).op)
      (by
        rintro A B f g hf hg i rfl
        refine Subobject.mk_eq_mk_of_comm _ _ (Iso.op ?_) (Quiver.Hom.unop_inj ?_)
        · exact (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
            (isCokernelEpiComp (colimit.isColimit _) i.hom rfl)).symm
        · simp only [Iso.comp_inv_eq, Iso.op_hom, Iso.symm_hom, unop_comp, Quiver.Hom.unop_op,
            colimit.comp_coconePointUniqueUpToIso_hom, Cofork.ofπ_ι_app,
            coequalizer.cofork_π])
  monotone' :=
    Subobject.ind₂ _ <| by
      intro A B f g hf hg h
      dsimp only [Subobject.lift_mk]
      refine Subobject.mk_le_mk_of_comm (cokernel.desc f (cokernel.π g) ?_).op ?_
      · rw [← Subobject.ofMkLEMk_comp h, Category.assoc, cokernel.condition, comp_zero]
      · exact Quiver.Hom.unop_inj (cokernel.π_desc _ _ _)

/-- Taking kernels is an order-reversing map from the quotient objects of `X` to the subobjects of
    `X`. -/
@[simps]
def kernelOrderHom [HasKernels C] (X : C) : (Subobject (op X))ᵒᵈ →o Subobject X where
  toFun :=
    Subobject.lift (fun _ f _ => Subobject.mk (kernel.ι f.unop))
      (by
        rintro A B f g hf hg i rfl
        refine Subobject.mk_eq_mk_of_comm _ _ ?_ ?_
        · exact
            IsLimit.conePointUniqueUpToIso (limit.isLimit _)
              (isKernelCompMono (limit.isLimit (parallelPair g.unop 0)) i.unop.hom rfl)
        · dsimp
          simp only [← Iso.eq_inv_comp, limit.conePointUniqueUpToIso_inv_comp,
            Fork.ofι_π_app])
  monotone' :=
    Subobject.ind₂ _ <| by
      intro A B f g hf hg h
      dsimp only [Subobject.lift_mk]
      refine Subobject.mk_le_mk_of_comm (kernel.lift g.unop (kernel.ι f.unop) ?_) ?_
      · rw [← Subobject.ofMkLEMk_comp h, unop_comp, kernel.condition_assoc, zero_comp]
      · exact Quiver.Hom.op_inj (by simp)

end Kernel

section Image

variable (f : X ⟶ Y) [HasImage f]

/-- The image of a morphism `f g : X ⟶ Y` as a `Subobject Y`. -/
abbrev imageSubobject : Subobject Y :=
  Subobject.mk (image.ι f)

/-- The underlying object of `imageSubobject f` is (up to isomorphism!)
the same as the chosen object `image f`. -/
def imageSubobjectIso : (imageSubobject f : C) ≅ image f :=
  Subobject.underlyingIso (image.ι f)

@[reassoc (attr := simp)]
theorem imageSubobject_arrow :
    (imageSubobjectIso f).hom ≫ image.ι f = (imageSubobject f).arrow := by simp [imageSubobjectIso]

@[reassoc (attr := simp)]
theorem imageSubobject_arrow' :
    (imageSubobjectIso f).inv ≫ (imageSubobject f).arrow = image.ι f := by simp [imageSubobjectIso]

/-- A factorisation of `f : X ⟶ Y` through `imageSubobject f`. -/
def factorThruImageSubobject : X ⟶ imageSubobject f :=
  factorThruImage f ≫ (imageSubobjectIso f).inv

instance [HasEqualizers C] : Epi (factorThruImageSubobject f) := by
  dsimp [factorThruImageSubobject]
  apply epi_comp

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem imageSubobject_arrow_comp : factorThruImageSubobject f ≫ (imageSubobject f).arrow = f := by
  simp [factorThruImageSubobject, imageSubobject_arrow]

theorem imageSubobject_arrow_comp_eq_zero [HasZeroMorphisms C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasImage f] [Epi (factorThruImageSubobject f)] (h : f ≫ g = 0) :
    (imageSubobject f).arrow ≫ g = 0 :=
  zero_of_epi_comp (factorThruImageSubobject f) <| by simp [h]

theorem imageSubobject_factors_comp_self {W : C} (k : W ⟶ X) : (imageSubobject f).Factors (k ≫ f) :=
  ⟨k ≫ factorThruImage f, by simp⟩

@[simp]
theorem factorThruImageSubobject_comp_self {W : C} (k : W ⟶ X) (h) :
    (imageSubobject f).factorThru (k ≫ f) h = k ≫ factorThruImageSubobject f := by
  ext
  simp

@[simp]
theorem factorThruImageSubobject_comp_self_assoc {W W' : C} (k : W ⟶ W') (k' : W' ⟶ X) (h) :
    (imageSubobject f).factorThru (k ≫ k' ≫ f) h = k ≫ k' ≫ factorThruImageSubobject f := by
  ext
  simp

/-- The image of `h ≫ f` is always a smaller subobject than the image of `f`. -/
theorem imageSubobject_comp_le {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)] :
    imageSubobject (h ≫ f) ≤ imageSubobject f :=
  Subobject.mk_le_mk_of_comm (image.preComp h f) (by simp)

section

open ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C]

@[simp]
theorem imageSubobject_zero_arrow : (imageSubobject (0 : X ⟶ Y)).arrow = 0 := by
  rw [← imageSubobject_arrow]
  simp

@[simp]
theorem imageSubobject_zero {A B : C} : imageSubobject (0 : A ⟶ B) = ⊥ :=
  Subobject.eq_of_comm (imageSubobjectIso _ ≪≫ imageZero ≪≫ Subobject.botCoeIsoZero.symm) (by simp)

end

section

variable [HasEqualizers C]

/-- The morphism `imageSubobject (h ≫ f) ⟶ imageSubobject f`
is an epimorphism when `h` is an epimorphism.
In general this does not imply that `imageSubobject (h ≫ f) = imageSubobject f`,
although it will when the ambient category is abelian.
-/
instance imageSubobject_comp_le_epi_of_epi {X' : C} (h : X' ⟶ X) [Epi h] (f : X ⟶ Y) [HasImage f]
    [HasImage (h ≫ f)] : Epi (Subobject.ofLE _ _ (imageSubobject_comp_le h f)) := by
  rw [ofLE_mk_le_mk_of_comm (image.preComp h f)]
  · infer_instance
  · simp

end

section

variable [HasEqualizers C]

/-- Postcomposing by an isomorphism gives an isomorphism between image subobjects. -/
def imageSubobjectCompIso (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobject (f ≫ h) : C) ≅ (imageSubobject f : C) :=
  imageSubobjectIso _ ≪≫ (image.compIso _ _).symm ≪≫ (imageSubobjectIso _).symm

@[reassoc (attr := simp)]
theorem imageSubobjectCompIso_hom_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobjectCompIso f h).hom ≫ (imageSubobject f).arrow =
      (imageSubobject (f ≫ h)).arrow ≫ inv h := by
  simp [imageSubobjectCompIso]

@[reassoc (attr := simp)]
theorem imageSubobjectCompIso_inv_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobjectCompIso f h).inv ≫ (imageSubobject (f ≫ h)).arrow =
      (imageSubobject f).arrow ≫ h := by
  simp [imageSubobjectCompIso]

end

theorem imageSubobject_mono (f : X ⟶ Y) [Mono f] : imageSubobject f = Subobject.mk f :=
  eq_of_comm (imageSubobjectIso f ≪≫ imageMonoIsoSource f ≪≫ (underlyingIso f).symm) (by simp)

/-- Precomposing by an isomorphism does not change the image subobject. -/
theorem imageSubobject_iso_comp [HasEqualizers C] {X' : C} (h : X' ⟶ X) [IsIso h] (f : X ⟶ Y)
    [HasImage f] : imageSubobject (h ≫ f) = imageSubobject f :=
  le_antisymm (imageSubobject_comp_le h f)
    (Subobject.mk_le_mk_of_comm (inv (image.preComp h f)) (by simp))

theorem imageSubobject_le {A B : C} {X : Subobject B} (f : A ⟶ B) [HasImage f] (h : A ⟶ X)
    (w : h ≫ X.arrow = f) : imageSubobject f ≤ X :=
  Subobject.le_of_comm
    ((imageSubobjectIso f).hom ≫
      image.lift
        { I := (X : C)
          e := h
          m := X.arrow })
    (by rw [assoc, image.lift_fac, imageSubobject_arrow])

theorem imageSubobject_le_mk {A B : C} {X : C} (g : X ⟶ B) [Mono g] (f : A ⟶ B) [HasImage f]
    (h : A ⟶ X) (w : h ≫ g = f) : imageSubobject f ≤ Subobject.mk g :=
  imageSubobject_le f (h ≫ (Subobject.underlyingIso g).inv) (by simp [w])

/-- Given a commutative square between morphisms `f` and `g`,
we have a morphism in the category from `imageSubobject f` to `imageSubobject g`. -/
def imageSubobjectMap {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
    (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    (imageSubobject f : C) ⟶ (imageSubobject g : C) :=
  (imageSubobjectIso f).hom ≫ image.map sq ≫ (imageSubobjectIso g).inv

@[reassoc (attr := simp)]
theorem imageSubobjectMap_arrow {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
    (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    imageSubobjectMap sq ≫ (imageSubobject g).arrow = (imageSubobject f).arrow ≫ sq.right := by
  simp only [imageSubobjectMap, Category.assoc, imageSubobject_arrow']
  erw [image.map_ι, ← Category.assoc, imageSubobject_arrow]

theorem image_map_comp_imageSubobjectIso_inv {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
    [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    image.map sq ≫ (imageSubobjectIso _).inv =
      (imageSubobjectIso _).inv ≫ imageSubobjectMap sq := by
  ext
  simpa using image.map_ι sq

theorem imageSubobjectIso_comp_image_map {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
    [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    (imageSubobjectIso _).hom ≫ image.map sq =
      imageSubobjectMap sq ≫ (imageSubobjectIso _).hom := by
  erw [← Iso.comp_inv_eq, Category.assoc, ← (imageSubobjectIso f).eq_inv_comp,
    image_map_comp_imageSubobjectIso_inv sq]

end Image

end Limits

end CategoryTheory
