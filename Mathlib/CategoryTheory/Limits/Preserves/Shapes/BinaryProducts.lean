/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Basic

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

/-- The property of preserving products expressed in terms of binary fans. -/
def mapIsLimitOfPreservesOfIsLimit [PreservesLimit (pair X Y) G] (l : IsLimit (BinaryFan.mk f g)) :
    IsLimit (BinaryFan.mk (G.map f) (G.map g)) :=
  isLimitMapConeBinaryFanEquiv G f g (isLimitOfPreserves G l)

/-- The property of reflecting products expressed in terms of binary fans. -/
def isLimitOfReflectsOfMapIsLimit [ReflectsLimit (pair X Y) G]
    (l : IsLimit (BinaryFan.mk (G.map f) (G.map g))) : IsLimit (BinaryFan.mk f g) :=
  isLimitOfReflects G ((isLimitMapConeBinaryFanEquiv G f g).symm l)

variable (X Y)
variable [HasBinaryProduct X Y]

/-- If `G` preserves binary products and `C` has them, then the binary fan constructed of the mapped
morphisms of the binary product cone is a limit.
-/
def isLimitOfHasBinaryProductOfPreservesLimit [PreservesLimit (pair X Y) G] :
    IsLimit (BinaryFan.mk (G.map (Limits.prod.fst : X ⨯ Y ⟶ X)) (G.map Limits.prod.snd)) :=
  mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd X Y)

variable [HasBinaryProduct (G.obj X) (G.obj Y)]

/-- If the product comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
lemma PreservesLimitPair.of_iso_prod_comparison [i : IsIso (prodComparison G X Y)] :
    PreservesLimit (pair X Y) G := by
  apply preservesLimit_of_preserves_limit_cone (prodIsProd X Y)
  apply (isLimitMapConeBinaryFanEquiv _ _ _).symm _
  refine @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (pair (G.obj X) (G.obj Y))) ?_
  apply i

variable [PreservesLimit (pair X Y) G]

/-- If `G` preserves the product of `(X,Y)`, then the product comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
def PreservesLimitPair.iso : G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasBinaryProductOfPreservesLimit G X Y) (limit.isLimit _)

@[simp]
theorem PreservesLimitPair.iso_hom : (PreservesLimitPair.iso G X Y).hom = prodComparison G X Y :=
  rfl

@[simp, reassoc]
theorem PreservesLimitPair.iso_inv_fst :
    (PreservesLimitPair.iso G X Y).inv ≫ G.map prod.fst = prod.fst := by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y), ← Category.assoc, Iso.hom_inv_id]
  simp

@[simp, reassoc]
theorem PreservesLimitPair.iso_inv_snd :
    (PreservesLimitPair.iso G X Y).inv ≫ G.map prod.snd = prod.snd := by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y), ← Category.assoc, Iso.hom_inv_id]
  simp

instance : IsIso (prodComparison G X Y) := by
  rw [← PreservesLimitPair.iso_hom]
  infer_instance

/-- If the product comparison maps of `G` at every pair `(X,Y)` is an
isomorphism, then `G` preserves binary products. -/
lemma preservesBinaryProducts_of_isIso_prodComparison
    [HasBinaryProducts C] [HasBinaryProducts D]
    [i : ∀ {X Y : C}, IsIso (prodComparison G X Y)] :
    PreservesLimitsOfShape (Discrete WalkingPair) G where
  preservesLimit := by
    intro K
    have : PreservesLimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) G :=
      PreservesLimitPair.of_iso_prod_comparison ..
    apply preservesLimit_of_iso_diagram G (diagramIsoPair K).symm

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

/-- The property of preserving coproducts expressed in terms of binary cofans. -/
def mapIsColimitOfPreservesOfIsColimit [PreservesColimit (pair X Y) G]
    (l : IsColimit (BinaryCofan.mk f g)) : IsColimit (BinaryCofan.mk (G.map f) (G.map g)) :=
  isColimitMapCoconeBinaryCofanEquiv G f g (isColimitOfPreserves G l)

/-- The property of reflecting coproducts expressed in terms of binary cofans. -/
def isColimitOfReflectsOfMapIsColimit [ReflectsColimit (pair X Y) G]
    (l : IsColimit (BinaryCofan.mk (G.map f) (G.map g))) : IsColimit (BinaryCofan.mk f g) :=
  isColimitOfReflects G ((isColimitMapCoconeBinaryCofanEquiv G f g).symm l)

variable (X Y)
variable [HasBinaryCoproduct X Y]

/--
If `G` preserves binary coproducts and `C` has them, then the binary cofan constructed of the mapped
morphisms of the binary product cocone is a colimit.
-/
def isColimitOfHasBinaryCoproductOfPreservesColimit [PreservesColimit (pair X Y) G] :
    IsColimit (BinaryCofan.mk (G.map (Limits.coprod.inl : X ⟶ X ⨿ Y)) (G.map Limits.coprod.inr)) :=
  mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod X Y)

variable [HasBinaryCoproduct (G.obj X) (G.obj Y)]

/-- If the coproduct comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
lemma PreservesColimitPair.of_iso_coprod_comparison [i : IsIso (coprodComparison G X Y)] :
    PreservesColimit (pair X Y) G := by
  apply preservesColimit_of_preserves_colimit_cocone (coprodIsCoprod X Y)
  apply (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm _
  refine @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (pair (G.obj X) (G.obj Y))) ?_
  apply i

variable [PreservesColimit (pair X Y) G]

/--
If `G` preserves the coproduct of `(X,Y)`, then the coproduct comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
def PreservesColimitPair.iso : G.obj X ⨿ G.obj Y ≅ G.obj (X ⨿ Y) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasBinaryCoproductOfPreservesColimit G X Y)

@[simp]
theorem PreservesColimitPair.iso_hom :
    (PreservesColimitPair.iso G X Y).hom = coprodComparison G X Y := rfl

instance : IsIso (coprodComparison G X Y) := by
  rw [← PreservesColimitPair.iso_hom]
  infer_instance

/-- If the coproduct comparison maps of `G` at every pair `(X,Y)` is an
isomorphism, then `G` preserves binary coproducts. -/
lemma preservesBinaryCoproducts_of_isIso_coprodComparison
    [HasBinaryCoproducts C] [HasBinaryCoproducts D]
    [i : ∀ {X Y : C}, IsIso (coprodComparison G X Y)] :
    PreservesColimitsOfShape (Discrete WalkingPair) G where
  preservesColimit := by
    intro K
    have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) G :=
      PreservesColimitPair.of_iso_coprod_comparison ..
    apply preservesColimit_of_iso_diagram G (diagramIsoPair K).symm

end

end CategoryTheory.Limits
