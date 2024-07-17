/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.limits.preserves.shapes.binary_products from "leanprover-community/mathlib"@"024a4231815538ac739f52d08dd20a55da0d6b23"

/-!
# Preserving binary products

Constructions to relate the notions of preserving binary products and reflecting binary products
to concrete binary fans.

In particular, we show that `ProdComparison G X Y` is an isomorphism iff `G` preserves
the product of `X` and `Y`.
-/


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section

variable {P X Y Z : C} (f : P ⟶ X) (g : P ⟶ Y)

/--
The map of a binary fan is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `BinaryFan.mk` with `Functor.mapCone`.
-/
def isLimitMapConeBinaryFanEquiv :
    IsLimit (G.mapCone (BinaryFan.mk f g)) ≃ IsLimit (BinaryFan.mk (G.map f) (G.map g)) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm.trans
    (IsLimit.equivIsoLimit
      (Cones.ext (Iso.refl _)
        (by rintro (_ | _) <;> simp)))
#align category_theory.limits.is_limit_map_cone_binary_fan_equiv CategoryTheory.Limits.isLimitMapConeBinaryFanEquiv

/-- The property of preserving products expressed in terms of binary fans. -/
def mapIsLimitOfPreservesOfIsLimit [PreservesLimit (pair X Y) G] (l : IsLimit (BinaryFan.mk f g)) :
    IsLimit (BinaryFan.mk (G.map f) (G.map g)) :=
  isLimitMapConeBinaryFanEquiv G f g (PreservesLimit.preserves l)
#align category_theory.limits.map_is_limit_of_preserves_of_is_limit CategoryTheory.Limits.mapIsLimitOfPreservesOfIsLimit

/-- The property of reflecting products expressed in terms of binary fans. -/
def isLimitOfReflectsOfMapIsLimit [ReflectsLimit (pair X Y) G]
    (l : IsLimit (BinaryFan.mk (G.map f) (G.map g))) : IsLimit (BinaryFan.mk f g) :=
  ReflectsLimit.reflects ((isLimitMapConeBinaryFanEquiv G f g).symm l)
#align category_theory.limits.is_limit_of_reflects_of_map_is_limit CategoryTheory.Limits.isLimitOfReflectsOfMapIsLimit

variable (X Y)
variable [HasBinaryProduct X Y]

/-- If `G` preserves binary products and `C` has them, then the binary fan constructed of the mapped
morphisms of the binary product cone is a limit.
-/
def isLimitOfHasBinaryProductOfPreservesLimit [PreservesLimit (pair X Y) G] :
    IsLimit (BinaryFan.mk (G.map (Limits.prod.fst : X ⨯ Y ⟶ X)) (G.map Limits.prod.snd)) :=
  mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd X Y)
#align category_theory.limits.is_limit_of_has_binary_product_of_preserves_limit CategoryTheory.Limits.isLimitOfHasBinaryProductOfPreservesLimit

variable [HasBinaryProduct (G.obj X) (G.obj Y)]

/-- If the product comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
def PreservesLimitPair.ofIsoProdComparison [i : IsIso (prodComparison G X Y)] :
    PreservesLimit (pair X Y) G := by
  apply preservesLimitOfPreservesLimitCone (prodIsProd X Y)
  apply (isLimitMapConeBinaryFanEquiv _ _ _).symm _
  refine @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (pair (G.obj X) (G.obj Y))) ?_
  apply i
#align category_theory.limits.preserves_limit_pair.of_iso_prod_comparison CategoryTheory.Limits.PreservesLimitPair.ofIsoProdComparison

variable [PreservesLimit (pair X Y) G]

/-- If `G` preserves the product of `(X,Y)`, then the product comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
def PreservesLimitPair.iso : G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasBinaryProductOfPreservesLimit G X Y) (limit.isLimit _)
#align category_theory.limits.preserves_limit_pair.iso CategoryTheory.Limits.PreservesLimitPair.iso

@[simp]
theorem PreservesLimitPair.iso_hom : (PreservesLimitPair.iso G X Y).hom = prodComparison G X Y :=
  rfl
#align category_theory.limits.preserves_limit_pair.iso_hom CategoryTheory.Limits.PreservesLimitPair.iso_hom

@[simp]
theorem PreservesLimitPair.iso_inv_fst :
    (PreservesLimitPair.iso G X Y).inv ≫ G.map prod.fst = prod.fst := by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y), ← Category.assoc, Iso.hom_inv_id]
  simp

@[simp]
theorem PreservesLimitPair.iso_inv_snd :
    (PreservesLimitPair.iso G X Y).inv ≫ G.map prod.snd = prod.snd := by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y), ← Category.assoc, Iso.hom_inv_id]
  simp

instance : IsIso (prodComparison G X Y) := by
  rw [← PreservesLimitPair.iso_hom]
  infer_instance

end

section

variable {P X Y Z : C} (f : X ⟶ P) (g : Y ⟶ P)

/-- The map of a binary cofan is a colimit iff
the cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `BinaryCofan.mk` with `Functor.mapCocone`.
-/
def isColimitMapCoconeBinaryCofanEquiv :
    IsColimit (Functor.mapCocone G (BinaryCofan.mk f g))
    ≃ IsColimit (BinaryCofan.mk (G.map f) (G.map g)) :=
  (IsColimit.precomposeHomEquiv (diagramIsoPair _).symm _).symm.trans
    (IsColimit.equivIsoColimit
      (Cocones.ext (Iso.refl _)
        (by rintro (_ | _) <;> simp)))
#align category_theory.limits.is_colimit_map_cocone_binary_cofan_equiv CategoryTheory.Limits.isColimitMapCoconeBinaryCofanEquiv

/-- The property of preserving coproducts expressed in terms of binary cofans. -/
def mapIsColimitOfPreservesOfIsColimit [PreservesColimit (pair X Y) G]
    (l : IsColimit (BinaryCofan.mk f g)) : IsColimit (BinaryCofan.mk (G.map f) (G.map g)) :=
  isColimitMapCoconeBinaryCofanEquiv G f g (PreservesColimit.preserves l)
#align category_theory.limits.map_is_colimit_of_preserves_of_is_colimit CategoryTheory.Limits.mapIsColimitOfPreservesOfIsColimit

/-- The property of reflecting coproducts expressed in terms of binary cofans. -/
def isColimitOfReflectsOfMapIsColimit [ReflectsColimit (pair X Y) G]
    (l : IsColimit (BinaryCofan.mk (G.map f) (G.map g))) : IsColimit (BinaryCofan.mk f g) :=
  ReflectsColimit.reflects ((isColimitMapCoconeBinaryCofanEquiv G f g).symm l)
#align category_theory.limits.is_colimit_of_reflects_of_map_is_colimit CategoryTheory.Limits.isColimitOfReflectsOfMapIsColimit

variable (X Y)
variable [HasBinaryCoproduct X Y]

/--
If `G` preserves binary coproducts and `C` has them, then the binary cofan constructed of the mapped
morphisms of the binary product cocone is a colimit.
-/
def isColimitOfHasBinaryCoproductOfPreservesColimit [PreservesColimit (pair X Y) G] :
    IsColimit (BinaryCofan.mk (G.map (Limits.coprod.inl : X ⟶ X ⨿ Y)) (G.map Limits.coprod.inr)) :=
  mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod X Y)
#align category_theory.limits.is_colimit_of_has_binary_coproduct_of_preserves_colimit CategoryTheory.Limits.isColimitOfHasBinaryCoproductOfPreservesColimit

variable [HasBinaryCoproduct (G.obj X) (G.obj Y)]

/-- If the coproduct comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
def PreservesColimitPair.ofIsoCoprodComparison [i : IsIso (coprodComparison G X Y)] :
    PreservesColimit (pair X Y) G := by
  apply preservesColimitOfPreservesColimitCocone (coprodIsCoprod X Y)
  apply (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm _
  refine @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (pair (G.obj X) (G.obj Y))) ?_
  apply i
#align category_theory.limits.preserves_colimit_pair.of_iso_coprod_comparison CategoryTheory.Limits.PreservesColimitPair.ofIsoCoprodComparison

variable [PreservesColimit (pair X Y) G]

/--
If `G` preserves the coproduct of `(X,Y)`, then the coproduct comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
def PreservesColimitPair.iso : G.obj X ⨿ G.obj Y ≅ G.obj (X ⨿ Y) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasBinaryCoproductOfPreservesColimit G X Y)
#align category_theory.limits.preserves_colimit_pair.iso CategoryTheory.Limits.PreservesColimitPair.iso

@[simp]
theorem PreservesColimitPair.iso_hom :
    (PreservesColimitPair.iso G X Y).hom = coprodComparison G X Y := rfl
#align category_theory.limits.preserves_colimit_pair.iso_hom CategoryTheory.Limits.PreservesColimitPair.iso_hom

instance : IsIso (coprodComparison G X Y) := by
  rw [← PreservesColimitPair.iso_hom]
  infer_instance

end

end CategoryTheory.Limits
