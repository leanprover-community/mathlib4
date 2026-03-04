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

@[expose] public noncomputable section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

variable {D : Type*} [Category* D]

variable (F G : D ⥤ C)

/-- The binary bicone associated to the biproduct of functors `F` and `G` -/
@[simps]
def pointwiseBinaryBicone : BinaryBicone F G where
  pt :=
    { obj P := F.obj P ⊞ G.obj P
      map f := biprod.map (F.map f) (G.map f) }
  fst := { app X := biprod.fst }
  snd := { app X := biprod.snd }
  inl := { app X := biprod.inl }
  inr := { app X := biprod.inr }

/-- The bicone associated with `F` and `G` is a bilimit bicone. -/
@[simps]
def pointwiseBinaryBicone.isBilimit : (pointwiseBinaryBicone F G).IsBilimit where
  isLimit := evaluationJointlyReflectsLimits _ fun d => by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (BinaryBiproduct.isLimit (F.obj d) (G.obj d))
    · exact (pairComp F G ((evaluation D C).obj d)).symm
    · exact Cones.ext (Iso.refl _) <| by rintro (_ | _ | _)<;> cat_disch
  isColimit := evaluationJointlyReflectsColimits _ fun d => by
    refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ (BinaryBiproduct.isColimit (F.obj d) (G.obj d))
    · exact (pairComp F G ((evaluation D C).obj d)).symm
    · exact Cocones.ext (Iso.refl _) <| by rintro (_ | _ | _)<;> cat_disch

/-- Construction of the binary biproduct data for functors `F` and `G` -/
@[simps]
def pointwiseBinaryBiproductData : BinaryBiproductData F G where
  bicone := pointwiseBinaryBicone F G
  isBilimit := pointwiseBinaryBicone.isBilimit F G

/-- If `C` has binary biproducts, then the functor category `D ⥤ C` does too. -/
instance functorCategoryHasBinaryBiproducts : HasBinaryBiproducts (D ⥤ C) where
  has_binary_biproduct F G := ⟨⟨pointwiseBinaryBiproductData F G⟩⟩

end CategoryTheory.Limits
