/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Limits.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Creates

/-!
# Limits of monoid objects.

If `C` has limits (of a given shape), so does `Mon C`,
and the forgetful functor preserves these limits.

(This could potentially replace many individual constructions for concrete categories,
in particular `MonCat`, `SemiRingCat`, `RingCat`, and `AlgCat R`.)
-/

@[expose] public section


open CategoryTheory Limits Monoidal MonoidalCategory

universe v u w

noncomputable section

namespace CategoryTheory
namespace Mon

variable {J : Type w} [Category* J]
variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

open MonObj

set_option backward.isDefEq.respectTransparency false in
/--
We construct the limit object of a functor `F : J ⥤ Mon C` given a limit cone `c` of
`F ⋙ forget C`.
-/
@[simps!]
def limit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    Mon C where
  X := c.pt
  mon.one := hc.lift
    { pt := _
      π.app X := η[(F.obj X).X] }
  mon.mul := hc.lift
    { pt := _
      π.app X := (c.π.app X ⊗ₘ c.π.app X) ≫ μ[(F.obj X).X]
      π.naturality i j f := by have := c.π.naturality f; simp_all }
  mon.one_mul := hc.hom_ext <| by simp [whiskerRight_comp_tensorHom_assoc]
  mon.mul_one := hc.hom_ext <| by simp [whiskerLeft_comp_tensorHom_assoc]
  mon.mul_assoc := by
    apply hc.hom_ext
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, IsLimit.fac,
      mon_tauto, implies_true]

set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `Mon.hasLimits`: a limiting cone over a functor `F : J ⥤ Mon C`.
-/
@[simps]
def limitCone (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) : Cone F where
  pt := limit F c hc
  π.app j := .mk' (c.π.app j)
  π.naturality j j' f := Hom.ext' (c.π.naturality f)

/-- The image of the proposed limit cone for `F : J ⥤ Mon C` under the forgetful functor
`forget C : Mon C ⥤ C` is isomorphic to the limit cone of `F ⋙ forget C`.
-/
@[simps!]
def forgetMapConeLimitConeIso (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    (forget C).mapCone (limitCone F c hc) ≅ c :=
  Cone.ext (Iso.refl _) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `Mon.hasLimitsOfShape`:
the proposed cone over a functor `F : J ⥤ Mon C` is a limit cone.
-/
@[simps]
def limitConeIsLimit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    IsLimit (limitCone F c hc) where
  lift s :=
    { hom := hc.lift ((Mon.forget C).mapCone s)
      isMonHom_hom.mul_hom := hc.hom_ext <| by simp
      isMonHom_hom.one_hom := hc.hom_ext <| by simp }
  fac s h := by ext; simp
  uniq s m w := Hom.ext' <| hc.hom_ext fun j ↦ by simpa using congr($(w j).hom)

/--
A helper definition to show that the forgetful functor `forget C : Mon C ⥤ C` creates limits:
given a limit cone `c` of `F ⋙ forget C`, we can lift it to a limit cone of `F`.
-/
def limitConeLiftsToLimit (F : J ⥤ Mon C) (c : Cone (F ⋙ Mon.forget C)) (hc : IsLimit c) :
    LiftsToLimit F (forget C) c hc where
  liftedCone := limitCone F c hc
  validLift := forgetMapConeLimitConeIso _ _ _
  makesLimit := limitConeIsLimit _ _ _

instance (F : J ⥤ Mon C) : CreatesLimit F (forget C) :=
  createsLimitOfReflectsIso (limitConeLiftsToLimit _)

instance : CreatesLimitsOfShape J (forget C) := ⟨inferInstance⟩
instance : CreatesLimitsOfSize.{w} (forget C) := ⟨inferInstance⟩
instance : CreatesLimits (forget C) := ⟨inferInstance⟩

instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Mon C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget C)

instance [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (Mon.forget C) :=
  CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape _

end Mon
end CategoryTheory
