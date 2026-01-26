import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Results on the category of rings requiring linear algebra

## Results

- `CommRingCat.nontrivial_of_isPushout_of_isField`: the pushout of non-trivial rings over a field
  is non-trivial.

-/

public section

universe u

open CategoryTheory Limits TensorProduct

namespace CommRingCat

lemma nontrivial_of_isPushout_of_isField {A B C D : CommRingCat.{u}}
    (hA : IsField A) {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ D} {inr : C ⟶ D}
    [Nontrivial B] [Nontrivial C]
    (h : IsPushout f g inl inr) : Nontrivial D := by
  letI : Field A := hA.toField
  algebraize [f.hom, g.hom]
  let e : D ≅ .of (B ⊗[A] C) :=
    IsColimit.coconePointUniqueUpToIso h.isColimit (CommRingCat.pushoutCoconeIsColimit A B C)
  let e' : D ≃ B ⊗[A] C := e.commRingCatIsoToRingEquiv.toEquiv
  exact e'.nontrivial

end CommRingCat
