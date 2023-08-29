/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Images

#align_import algebra.category.Group.images from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The category of commutative additive groups has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `AddCommGroupCat` is an abelian category.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace AddCommGroupCat

set_option linter.uppercaseLean3 false

-- Note that because `injective_of_mono` is currently only proved in `Type 0`,
-- we restrict to the lowest universe here for now.
variable {G H : AddCommGroupCat.{0}} (f : G ⟶ H)

attribute [local ext] Subtype.ext_val

section

-- implementation details of `IsImage` for `AddCommGroupCat`; use the API, not these
/-- the image of a morphism in `AddCommGroupCat` is just the bundling of `AddMonoidHom.range f` -/
def image : AddCommGroupCat :=
  AddCommGroupCat.of (AddMonoidHom.range f)
#align AddCommGroup.image AddCommGroupCat.image

/-- the inclusion of `image f` into the target -/
def image.ι : image f ⟶ H :=
  f.range.subtype
#align AddCommGroup.image.ι AddCommGroupCat.image.ι

instance : Mono (image.ι f) :=
  ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

/-- the corestriction map to the image -/
def factorThruImage : G ⟶ image f :=
  f.rangeRestrict
#align AddCommGroup.factor_thru_image AddCommGroupCat.factorThruImage

theorem image.fac : factorThruImage f ≫ image.ι f = f := by
  ext
  -- ⊢ ↑(factorThruImage f ≫ ι f) x✝ = ↑f x✝
  rfl
  -- 🎉 no goals
#align AddCommGroup.image.fac AddCommGroupCat.image.fac

attribute [local simp] image.fac

variable {f}

/-- the universal property for the image factorisation -/
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I where
  toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f → F'.I)
  map_zero' := by
    haveI := F'.m_mono
    -- ⊢ (fun x => ↑F'.e ↑(Classical.indefiniteDescription (fun x_1 => ↑f x_1 = ↑x) ( …
    apply injective_of_mono F'.m
    -- ⊢ ↑F'.m ((fun x => ↑F'.e ↑(Classical.indefiniteDescription (fun x_1 => ↑f x_1  …
    change (F'.e ≫ F'.m) _ = _
    -- ⊢ ↑(F'.e ≫ F'.m) ↑(Classical.indefiniteDescription (fun x => ↑f x = ↑0) (_ : ↑ …
    rw [F'.fac, AddMonoidHom.map_zero]
    -- ⊢ ↑f ↑(Classical.indefiniteDescription (fun x => ↑f x = ↑0) (_ : ↑0 ∈ AddMonoi …
    exact (Classical.indefiniteDescription (fun y => f y = 0) _).2
    -- 🎉 no goals
  map_add' := by
    intro x y
    -- ⊢ ZeroHom.toFun { toFun := fun x => ↑F'.e ↑(Classical.indefiniteDescription (f …
    haveI := F'.m_mono
    -- ⊢ ZeroHom.toFun { toFun := fun x => ↑F'.e ↑(Classical.indefiniteDescription (f …
    apply injective_of_mono F'.m
    -- ⊢ ↑F'.m (ZeroHom.toFun { toFun := fun x => ↑F'.e ↑(Classical.indefiniteDescrip …
    rw [AddMonoidHom.map_add]
    -- ⊢ ↑F'.m (ZeroHom.toFun { toFun := fun x => ↑F'.e ↑(Classical.indefiniteDescrip …
    change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
    -- ⊢ ↑(F'.e ≫ F'.m) ↑(Classical.indefiniteDescription (fun x_1 => ↑f x_1 = ↑(x +  …
    rw [F'.fac]
    -- ⊢ ↑f ↑(Classical.indefiniteDescription (fun x_1 => ↑f x_1 = ↑(x + y)) (_ : ↑(x …
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    -- ⊢ ↑(x + y) = ↑f ↑(Classical.indefiniteDescription (fun x_1 => ↑f x_1 = ↑x) (_  …
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    -- ⊢ ↑(x + y) = ↑x + ↑f ↑(Classical.indefiniteDescription (fun x => ↑f x = ↑y) (_ …
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    -- ⊢ ↑(x + y) = ↑x + ↑y
    rfl
    -- 🎉 no goals
#align AddCommGroup.image.lift AddCommGroupCat.image.lift

theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f := by
  ext x
  -- ⊢ ↑(lift F' ≫ F'.m) x = ↑(ι f) x
  change (F'.e ≫ F'.m) _ = _
  -- ⊢ ↑(F'.e ≫ F'.m) ↑(Classical.indefiniteDescription (fun x_1 => ↑f x_1 = ↑x) (_ …
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  -- ⊢ ↑x = ↑(ι f) x
  rfl
  -- 🎉 no goals
#align AddCommGroup.image.lift_fac AddCommGroupCat.image.lift_fac

end

/-- the factorisation of any morphism in `AddCommGroupCat` through a mono. -/
def monoFactorisation : MonoFactorisation f where
  I := image f
  m := image.ι f
  e := factorThruImage f
#align AddCommGroup.mono_factorisation AddCommGroupCat.monoFactorisation

/-- the factorisation of any morphism in `AddCommGroupCat` through a mono has
the universal property of the image. -/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := image.lift
  lift_fac := image.lift_fac
#align AddCommGroup.is_image AddCommGroupCat.isImage

/-- The categorical image of a morphism in `AddCommGroupCat`
agrees with the usual group-theoretical range.
-/
noncomputable def imageIsoRange {G H : AddCommGroupCat.{0}} (f : G ⟶ H) :
    Limits.image f ≅ AddCommGroupCat.of f.range :=
  IsImage.isoExt (Image.isImage f) (isImage f)
#align AddCommGroup.image_iso_range AddCommGroupCat.imageIsoRange

end AddCommGroupCat
