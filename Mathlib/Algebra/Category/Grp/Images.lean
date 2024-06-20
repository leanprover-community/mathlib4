/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Images

#align_import algebra.category.Group.images from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The category of commutative additive groups has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `AddCommGrp` is an abelian category.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace AddCommGrp

set_option linter.uppercaseLean3 false

-- Note that because `injective_of_mono` is currently only proved in `Type 0`,
-- we restrict to the lowest universe here for now.
variable {G H : AddCommGrp.{0}} (f : G ⟶ H)

attribute [local ext] Subtype.ext_val

section

-- implementation details of `IsImage` for `AddCommGrp`; use the API, not these
/-- the image of a morphism in `AddCommGrp` is just the bundling of `AddMonoidHom.range f` -/
def image : AddCommGrp :=
  AddCommGrp.of (AddMonoidHom.range f)
#align AddCommGroup.image AddCommGrp.image

/-- the inclusion of `image f` into the target -/
def image.ι : image f ⟶ H :=
  f.range.subtype
#align AddCommGroup.image.ι AddCommGrp.image.ι

instance : Mono (image.ι f) :=
  ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

/-- the corestriction map to the image -/
def factorThruImage : G ⟶ image f :=
  f.rangeRestrict
#align AddCommGroup.factor_thru_image AddCommGrp.factorThruImage

theorem image.fac : factorThruImage f ≫ image.ι f = f := by
  ext
  rfl
#align AddCommGroup.image.fac AddCommGrp.image.fac

attribute [local simp] image.fac

variable {f}

/-- the universal property for the image factorisation -/
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I where
  toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f → F'.I)
  map_zero' := by
    haveI := F'.m_mono
    apply injective_of_mono F'.m
    change (F'.e ≫ F'.m) _ = _
    rw [F'.fac, AddMonoidHom.map_zero]
    exact (Classical.indefiniteDescription (fun y => f y = 0) _).2
  map_add' := by
    intro x y
    haveI := F'.m_mono
    apply injective_of_mono F'.m
    rw [AddMonoidHom.map_add]
    change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
    rw [F'.fac]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    rfl
#align AddCommGroup.image.lift AddCommGrp.image.lift

theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl
#align AddCommGroup.image.lift_fac AddCommGrp.image.lift_fac

end

/-- the factorisation of any morphism in `AddCommGrp` through a mono. -/
def monoFactorisation : MonoFactorisation f where
  I := image f
  m := image.ι f
  e := factorThruImage f
#align AddCommGroup.mono_factorisation AddCommGrp.monoFactorisation

/-- the factorisation of any morphism in `AddCommGrp` through a mono has
the universal property of the image. -/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := image.lift
  lift_fac := image.lift_fac
#align AddCommGroup.is_image AddCommGrp.isImage

/-- The categorical image of a morphism in `AddCommGrp`
agrees with the usual group-theoretical range.
-/
noncomputable def imageIsoRange {G H : AddCommGrp.{0}} (f : G ⟶ H) :
    Limits.image f ≅ AddCommGrp.of f.range :=
  IsImage.isoExt (Image.isImage f) (isImage f)
#align AddCommGroup.image_iso_range AddCommGrp.imageIsoRange

end AddCommGrp
