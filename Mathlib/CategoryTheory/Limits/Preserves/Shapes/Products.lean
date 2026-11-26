/-
Copyright (c) 2020 Kim Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Preserving products

Constructions to relate the notions of preserving products and reflecting products
to concrete fans.

In particular, we show that `piComparison G f` is an isomorphism iff `G` preserves
the limit of `f`.
-/

@[expose] public section


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
@[to_dual
/-- The map of a cofan is a colimit iff the cofan consisting of the mapped morphisms is a colimit.
This essentially lets us commute `Cofan.mk` with `Functor.mapCocone`.
-/]
def isLimitMapConeFanMkEquiv {P : C} (g : ∀ j, P ⟶ f j) :
    IsLimit (Functor.mapCone G (Fan.mk P g)) ≃
      IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j)) := by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  · exact Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  exact Cone.ext (Iso.refl _) fun j ↦ by dsimp; cases j; simp

/-- The property of preserving products expressed in terms of fans. -/
@[to_dual /-- The property of preserving coproducts expressed in terms of cofans. -/]
def isLimitFanMkObjOfIsLimit [PreservesLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ g)) :
    IsLimit (Fan.mk (G.obj P) fun j => G.map (g j) : Fan fun j => G.obj (f j)) :=
  isLimitMapConeFanMkEquiv _ _ _ (isLimitOfPreserves G t)

/-- The property of reflecting products expressed in terms of fans. -/
@[to_dual /-- The property of reflecting coproducts expressed in terms of cofans. -/]
def isLimitOfIsLimitFanMkObj [ReflectsLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j))) :
    IsLimit (Fan.mk P g) :=
  isLimitOfReflects G ((isLimitMapConeFanMkEquiv _ _ _).symm t)

section

variable [HasProduct f]

/--
If `G` preserves products and `C` has them, then the fan constructed of the mapped projection of a
product is a limit.
-/
@[to_dual
/-- If `G` preserves coproducts and `C` has them,
then the cofan constructed of the mapped inclusion of a coproduct is a colimit.
-/]
def isLimitOfHasProductOfPreservesLimit [PreservesLimit (Discrete.functor f) G] :
    IsLimit (Fan.mk _ fun j : J => G.map (Pi.π f j) : Fan fun j => G.obj (f j)) :=
  isLimitFanMkObjOfIsLimit G f _ (productIsProduct _)

variable [HasProduct fun j : J => G.obj (f j)]

insert_to_dual_translation
  CategoryTheory.Limits.PreservesProduct CategoryTheory.Limits.PreservesCoproduct

/-- If `pi_comparison G f` is an isomorphism, then `G` preserves the limit of `f`. -/
@[to_dual
/-- If `sigma_comparison G f` is an isomorphism, then `G` preserves the colimit of `f`. -/]
lemma PreservesProduct.of_iso_comparison [i : IsIso (piComparison G f)] :
    PreservesLimit (Discrete.functor f) G := by
  apply preservesLimit_of_preserves_limit_cone (productIsProduct f)
  apply (isLimitMapConeFanMkEquiv _ _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _
    (limit.isLimit (Discrete.functor fun j : J => G.obj (f j))) i

@[to_dual (attr := reassoc (attr := simp)) map_ι_comp_inv_sigmaComparison]
lemma inv_piComparison_comp_map_π [IsIso (piComparison G f)] (j : J) :
     inv (piComparison G f) ≫ G.map (Pi.π _ j) =
      Pi.π (fun x ↦ (G.obj (f x))) j := by
  simp only [IsIso.inv_comp_eq, piComparison_comp_π]

variable [PreservesLimit (Discrete.functor f) G]

/--
If `G` preserves limits, we have an isomorphism from the image of a product to the product of the
images.
-/
@[to_dual
/-- If `G` preserves colimits,
we have an isomorphism from the image of a coproduct to the coproduct of the images.
-/]
def PreservesProduct.iso : G.obj (∏ᶜ f) ≅ ∏ᶜ fun j => G.obj (f j) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasProductOfPreservesLimit G f) (limit.isLimit _)

@[to_dual (attr := simp) iso_inv]
theorem PreservesProduct.iso_hom : (PreservesProduct.iso G f).hom = piComparison G f :=
  rfl

@[to_dual instIsIsoSigmaComparison]
instance : IsIso (piComparison G f) := by
  rw [← PreservesProduct.iso_hom]
  infer_instance

@[to_dual]
instance {I : Type*} [Category* I] [IsGroupoid I] (F : C ⥤ D) [PreservesLimitsOfShape I F] :
    PreservesLimitsOfShape Iᵒᵖ F :=
  letI : Groupoid I := Groupoid.ofIsGroupoid
  preservesLimitsOfShape_of_equiv (Groupoid.invEquivalence I) F

end

/-- If `F` preserves the limit of every `Discrete.functor f`, it preserves all limits of shape
`Discrete J`. -/
@[to_dual
/-- If `F` preserves the colimit of every `Discrete.functor f`, it preserves all colimits of shape
`Discrete J`. -/]
lemma preservesLimitsOfShape_of_discrete (F : C ⥤ D)
    [∀ (f : J → C), PreservesLimit (Discrete.functor f) F] :
    PreservesLimitsOfShape (Discrete J) F where
  preservesLimit := preservesLimit_of_iso_diagram F (Discrete.natIsoFunctor).symm

instance {I : Type w} (F : C ⥤ D) [PreservesColimitsOfShape (Discrete I) F] :
    PreservesColimitsOfShape (Discrete I)ᵒᵖ F :=
  preservesColimitsOfShape_of_equiv (Discrete.opposite I).symm F

end CategoryTheory.Limits
