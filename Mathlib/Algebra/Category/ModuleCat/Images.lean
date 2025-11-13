/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# The category of R-modules has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `ModuleCat R` is an abelian category.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

attribute [local ext] Subtype.ext

section

-- implementation details of `HasImage` for ModuleCat; use the API, not these
/-- The image of a morphism in `ModuleCat R` is just the bundling of `LinearMap.range f` -/
def image : ModuleCat R :=
  ModuleCat.of R (LinearMap.range f.hom)

/-- The inclusion of `image f` into the target -/
def image.ι : image f ⟶ H :=
  ofHom (LinearMap.range f.hom).subtype

instance : Mono (image.ι f) :=
  ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

/-- The corestriction map to the image -/
def factorThruImage : G ⟶ image f :=
  ofHom f.hom.rangeRestrict

theorem image.fac : factorThruImage f ≫ image.ι f = f :=
  rfl

attribute [local simp] image.fac

variable {f}

/-- The universal property for the image factorisation -/
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I :=
  ofHom
  { toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f → F'.I)
    map_add' := fun x y => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [LinearMap.map_add]
      change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl
    map_smul' := fun c x => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [LinearMap.map_smul]
      change (F'.e ≫ F'.m) _ = _ • (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl }

theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

end

/-- The factorisation of any morphism in `ModuleCat R` through a mono. -/
def monoFactorisation : MonoFactorisation f where
  I := image f
  m := image.ι f
  e := factorThruImage f

/-- The factorisation of any morphism in `ModuleCat R` through a mono has the universal property of
the image. -/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := image.lift
  lift_fac := image.lift_fac

/-- The categorical image of a morphism in `ModuleCat R` agrees with the linear algebraic range. -/
noncomputable def imageIsoRange {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    Limits.image f ≅ ModuleCat.of R (LinearMap.range f.hom) :=
  IsImage.isoExt (Image.isImage f) (isImage f)

@[simp, reassoc, elementwise]
theorem imageIsoRange_inv_image_ι {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (imageIsoRange f).inv ≫ Limits.image.ι f = ModuleCat.ofHom (LinearMap.range f.hom).subtype :=
  IsImage.isoExt_inv_m _ _

@[simp, reassoc, elementwise]
theorem imageIsoRange_hom_subtype {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (imageIsoRange f).hom ≫ ModuleCat.ofHom (LinearMap.range f.hom).subtype = Limits.image.ι f := by
  rw [← imageIsoRange_inv_image_ι f, Iso.hom_inv_id_assoc]

end ModuleCat
