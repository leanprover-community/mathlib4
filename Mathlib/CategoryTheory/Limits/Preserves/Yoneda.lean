/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Yoneda preserves certain colimits

We prove the isomorphism `Hom(YX, colim_i Fi) ≅ colim_i Hom(YX, Fi)`, where `Y` is the Yoneda
embedding. We state this in a way that is functorial in `X`.

The proof combines the Yoneda lemma with the fact that colimits in functor categories are computed
pointwise.

## See also

There is also a relative version of this statement where `F` lands in `Over A` for some presheaf
`A`, see `CategoryTheory.Comma.Presheaf`.

## Future work

Another way to express this preservation property would be
`PreservesColimit F (coyoneda.obj (Opposite.op (yoneda.obj X)))` for all `X : C`.
-/

universe v u

namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {J : Type v} [SmallCategory J] (F : J ⥤ Cᵒᵖ ⥤ Type v)

/-- Naturally in `X`, we have `Hom(YX, colim_i Fi) ≅ colim_i Hom(YX, Fi)`. -/
noncomputable def yonedaYonedaColimit :
    yoneda.op ⋙ yoneda.obj (colimit F) ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) := calc
  yoneda.op ⋙ yoneda.obj (colimit F)
    ≅ colimit F ⋙ uliftFunctor.{u} := yonedaOpCompYonedaObj (colimit F)
  _ ≅ F.flip ⋙ colim ⋙ uliftFunctor.{u} := isoWhiskerRight (colimitIsoFlipCompColim _) _
  _ ≅ F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙ colim :=
        isoWhiskerLeft _ (preservesColimitNatIso _)
  _ ≅ (evaluation _ _ ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u}) ⋙
          (whiskeringLeft _ _ _).obj F ⋙ colim :=
        Iso.refl _
  _ ≅ (yoneda.op ⋙ coyoneda) ⋙ (whiskeringLeft _ _ _).obj F ⋙ colim :=
        isoWhiskerRight curriedYonedaLemma.symm _
  _ ≅ yoneda.op ⋙ (F ⋙ yoneda).flip ⋙ colim := Iso.refl _
  _ ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) := isoWhiskerLeft _ (colimitIsoFlipCompColim _).symm

end CategoryTheory
