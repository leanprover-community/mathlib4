/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# The category of commutative additive groups has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `AddCommGrpCat` is an abelian category.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace AddCommGrpCat


-- Note that because `injective_of_mono` is currently only proved in `Type 0`,
-- we restrict to the lowest universe here for now.
variable {G H : AddCommGrpCat.{0}} (f : G ⟶ H)

attribute [local ext] Subtype.ext

section

-- implementation details of `IsImage` for `AddCommGrpCat`; use the API, not these
/-- the image of a morphism in `AddCommGrpCat` is just the bundling of `AddMonoidHom.range f` -/
def image : AddCommGrpCat :=
  AddCommGrpCat.of (AddMonoidHom.range f.hom)

/-- the inclusion of `image f` into the target -/
def image.ι : image f ⟶ H :=
  ofHom f.hom.range.subtype

instance : Mono (image.ι f) :=
  ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

/-- the corestriction map to the image -/
def factorThruImage : G ⟶ image f :=
  ofHom f.hom.rangeRestrict

theorem image.fac : factorThruImage f ≫ image.ι f = f := by
  ext
  rfl

attribute [local simp] image.fac

variable {f}

/-- the universal property for the image factorisation -/
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I :=
  ofHom
  { toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f → F'.I)
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
      rfl }

theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

end

/-- the factorisation of any morphism in `AddCommGrpCat` through a mono. -/
def monoFactorisation : MonoFactorisation f where
  I := image f
  m := image.ι f
  e := factorThruImage f

/-- the factorisation of any morphism in `AddCommGrpCat` through a mono has
the universal property of the image. -/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := image.lift
  lift_fac := image.lift_fac

/-- The categorical image of a morphism in `AddCommGrpCat`
agrees with the usual group-theoretical range.
-/
noncomputable def imageIsoRange {G H : AddCommGrpCat.{0}} (f : G ⟶ H) :
    Limits.image f ≅ AddCommGrpCat.of f.hom.range :=
  IsImage.isoExt (Image.isImage f) (isImage f)

end AddCommGrpCat
