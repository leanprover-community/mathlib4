/-
Copyright (c) 2026 Leopold Mayer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leopold Mayer
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Biproducts in functor categories

We show that if `C` has binary biproducts, then the functor category `D ⥤ C` also
has binary biproducts
(`CategoryTheory.Limits.BinaryBiproduct.functorCategoryHasBinaryBiproducts`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Limits.BinaryBiproduct

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

variable {D : Type*} [Category* D]

variable (F G : D ⥤ C)

noncomputable section

/-- The biproduct `F ⊞ G` of two functors `F` and `G` -/
@[simps]
def biprodFunc : D ⥤ C where
  obj P := F.obj P ⊞ G.obj P
  map f := biprod.map (F.map f) (G.map f)

/-- The projection `F ⊞ G ⟶ F` onto the first summand -/
@[simps]
def biprodFunc.fst : biprodFunc F G ⟶ F where
  app X := biprod.fst

/-- The projection `F ⊞ G ⟶ G` onto the second summand -/
@[simps]
def biprodFunc.snd : biprodFunc F G ⟶ G where
  app X := biprod.snd

/-- The inclusion `F ⟶ F ⊞ G` of the first summand -/
@[simps]
def biprodFunc.inl : F ⟶ biprodFunc F G where
  app X := biprod.inl

/-- The inclusion `G ⟶ F ⊞ G` of the second summand -/
@[simps]
def biprodFunc.inr : G ⟶ biprodFunc F G where
  app X := biprod.inr

/-- The binary bicone associated to the biproduct of functors `F` and `G` -/
@[simps]
def funcBinaryBicone : BinaryBicone F G where
  pt := biprodFunc F G
  fst := biprodFunc.fst F G
  snd := biprodFunc.snd F G
  inl := biprodFunc.inl F G
  inr := biprodFunc.inr F G

/-- Applying `toCone` to the bicone associated with `F` and `G` gives a limit cone. -/
def funcBinaryBicone.isLimit : IsLimit (funcBinaryBicone F G).toCone :=
  evaluationJointlyReflectsLimits _ fun d => by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ ((BinaryBiproduct.isLimit) (F.obj d) (G.obj d))
    · symm; apply pairComp
    · refine Cones.ext (Iso.refl _) ?_
      rintro (_ | _ | _) <;> cat_disch

/-- Applying `toCocone` to the bicone associated with `F` and `G` gives a colimit cocone. -/
def funcBinaryBicone.isColimit : IsColimit (funcBinaryBicone F G).toCocone :=
  evaluationJointlyReflectsColimits _ fun d => by
    refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ ((BinaryBiproduct.isColimit) (F.obj d) (G.obj d))
    · symm; apply pairComp
    · refine Cocones.ext (Iso.refl _) ?_
      rintro (_ | _ | _) <;> cat_disch

/-- The bicone associated with `F` and `G` is a bilimit bicone. -/
@[simps]
def funcBinaryBicone.isBilimit : (funcBinaryBicone F G).IsBilimit where
  isLimit := funcBinaryBicone.isLimit F G
  isColimit := funcBinaryBicone.isColimit F G

/-- Construction of the binary biproduct data for functors `F` and `G` -/
@[simps]
def funcBinaryBiproductData : BinaryBiproductData F G where
  bicone := funcBinaryBicone F G
  isBilimit := funcBinaryBicone.isBilimit F G

/-- If `C` has binary biproducts, then the functor category `D ⥤ C` does too. -/
instance functorCategoryHasBinaryBiproducts : HasBinaryBiproducts (D ⥤ C) where
  has_binary_biproduct F G := ⟨⟨funcBinaryBiproductData F G⟩⟩

end

end BinaryBiproduct

end Limits

end CategoryTheory
