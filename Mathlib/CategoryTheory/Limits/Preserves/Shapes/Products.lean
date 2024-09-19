/-
Copyright (c) 2020 Scott Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving products

Constructions to relate the notions of preserving products and reflecting products
to concrete fans.

In particular, we show that `piComparison G f` is an isomorphism iff `G` preserves
the limit of `f`.
-/


noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable {J : Type w} (f : J → C)

/-- The map of a fan is a limit iff the fan consisting of the mapped morphisms is a limit. This
essentially lets us commute `Fan.mk` with `Functor.mapCone`.
-/
def isLimitMapConeFanMkEquiv {P : C} (g : ∀ j, P ⟶ f j) :
    IsLimit (Functor.mapCone G (Fan.mk P g)) ≃
      IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j)) := by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  · refine Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  refine Cones.ext (Iso.refl _) fun j =>
      by dsimp; cases j; simp

/-- The property of preserving products expressed in terms of fans. -/
def isLimitFanMkObjOfIsLimit [PreservesLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ g)) :
    IsLimit (Fan.mk (G.obj P) fun j => G.map (g j) : Fan fun j => G.obj (f j)) :=
  isLimitMapConeFanMkEquiv _ _ _ (PreservesLimit.preserves t)

/-- The property of reflecting products expressed in terms of fans. -/
def isLimitOfIsLimitFanMkObj [ReflectsLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j))) :
    IsLimit (Fan.mk P g) :=
  ReflectsLimit.reflects ((isLimitMapConeFanMkEquiv _ _ _).symm t)

section

variable [HasProduct f]

/--
If `G` preserves products and `C` has them, then the fan constructed of the mapped projection of a
product is a limit.
-/
def isLimitOfHasProductOfPreservesLimit [PreservesLimit (Discrete.functor f) G] :
    IsLimit (Fan.mk _ fun j : J => G.map (Pi.π f j) : Fan fun j => G.obj (f j)) :=
  isLimitFanMkObjOfIsLimit G f _ (productIsProduct _)

variable [HasProduct fun j : J => G.obj (f j)]

/-- If `pi_comparison G f` is an isomorphism, then `G` preserves the limit of `f`. -/
def PreservesProduct.ofIsoComparison [i : IsIso (piComparison G f)] :
    PreservesLimit (Discrete.functor f) G := by
  apply preservesLimitOfPreservesLimitCone (productIsProduct f)
  apply (isLimitMapConeFanMkEquiv _ _ _).symm _
  refine @IsLimit.ofPointIso _ _ _ _ _ _ _
    (limit.isLimit (Discrete.functor fun j : J => G.obj (f j))) ?_
  apply i

variable [PreservesLimit (Discrete.functor f) G]

/--
If `G` preserves limits, we have an isomorphism from the image of a product to the product of the
images.
-/
def PreservesProduct.iso : G.obj (∏ᶜ f) ≅ ∏ᶜ fun j => G.obj (f j) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasProductOfPreservesLimit G f) (limit.isLimit _)

@[simp]
theorem PreservesProduct.iso_hom : (PreservesProduct.iso G f).hom = piComparison G f :=
  rfl

instance : IsIso (piComparison G f) := by
  rw [← PreservesProduct.iso_hom]
  infer_instance

end

/-- The map of a cofan is a colimit iff the cofan consisting of the mapped morphisms is a colimit.
This essentially lets us commute `Cofan.mk` with `Functor.mapCocone`.
-/
def isColimitMapCoconeCofanMkEquiv {P : C} (g : ∀ j, f j ⟶ P) :
    IsColimit (Functor.mapCocone G (Cofan.mk P g)) ≃
      IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j)) := by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  · refine Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  refine Cocones.ext (Iso.refl _) fun j => by dsimp; cases j; simp

/-- The property of preserving coproducts expressed in terms of cofans. -/
def isColimitCofanMkObjOfIsColimit [PreservesColimit (Discrete.functor f) G] {P : C}
    (g : ∀ j, f j ⟶ P) (t : IsColimit (Cofan.mk _ g)) :
    IsColimit (Cofan.mk (G.obj P) fun j => G.map (g j) : Cofan fun j => G.obj (f j)) :=
  isColimitMapCoconeCofanMkEquiv _ _ _ (PreservesColimit.preserves t)

/-- The property of reflecting coproducts expressed in terms of cofans. -/
def isColimitOfIsColimitCofanMkObj [ReflectsColimit (Discrete.functor f) G] {P : C}
    (g : ∀ j, f j ⟶ P)
    (t : IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j))) :
    IsColimit (Cofan.mk P g) :=
  ReflectsColimit.reflects ((isColimitMapCoconeCofanMkEquiv _ _ _).symm t)

section

variable [HasCoproduct f]

/-- If `G` preserves coproducts and `C` has them,
then the cofan constructed of the mapped inclusion of a coproduct is a colimit.
-/
def isColimitOfHasCoproductOfPreservesColimit [PreservesColimit (Discrete.functor f) G] :
    IsColimit (Cofan.mk _ fun j : J => G.map (Sigma.ι f j) : Cofan fun j => G.obj (f j)) :=
  isColimitCofanMkObjOfIsColimit G f _ (coproductIsCoproduct _)

variable [HasCoproduct fun j : J => G.obj (f j)]

/-- If `sigma_comparison G f` is an isomorphism, then `G` preserves the colimit of `f`. -/
def PreservesCoproduct.ofIsoComparison [i : IsIso (sigmaComparison G f)] :
    PreservesColimit (Discrete.functor f) G := by
  apply preservesColimitOfPreservesColimitCocone (coproductIsCoproduct f)
  apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
  refine @IsColimit.ofPointIso _ _ _ _ _ _ _
    (colimit.isColimit (Discrete.functor fun j : J => G.obj (f j))) ?_
  apply i

variable [PreservesColimit (Discrete.functor f) G]

/-- If `G` preserves colimits,
we have an isomorphism from the image of a coproduct to the coproduct of the images.
-/
def PreservesCoproduct.iso : G.obj (∐ f) ≅ ∐ fun j => G.obj (f j) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCoproductOfPreservesColimit G f)
    (colimit.isColimit _)

@[simp]
theorem PreservesCoproduct.inv_hom : (PreservesCoproduct.iso G f).inv = sigmaComparison G f := rfl

instance : IsIso (sigmaComparison G f) := by
  rw [← PreservesCoproduct.inv_hom]
  infer_instance

end

end CategoryTheory.Limits
