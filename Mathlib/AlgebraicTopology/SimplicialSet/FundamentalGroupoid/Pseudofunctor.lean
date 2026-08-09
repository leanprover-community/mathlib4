/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# ...

-/

@[expose] public section

universe u

open CategoryTheory Bicategory

namespace SSet

variable {X Y Z T : SSet.{u}}

--set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma mapFundamentalGroupoid_id_comp (f : X ⟶ Y) :
    (mapFundamentalGroupoidComp (𝟙 X) f).inv ≫
      Functor.whiskerRight (mapFundamentalGroupoidId X).hom _ ≫
        (Functor.leftUnitor _).hom =
    (congrMapFundamentalGroupoid (by simp)).hom := by
  ext x
  simp
  sorry

@[reassoc]
lemma mapFundamentalGroupoid_comp_id (f : X ⟶ Y) :
    (mapFundamentalGroupoidComp f (𝟙 Y)).inv ≫
      Functor.whiskerLeft _ (mapFundamentalGroupoidId Y).hom ≫
        (Functor.rightUnitor _).hom =
    (congrMapFundamentalGroupoid (by simp)).hom := by
  sorry

@[reassoc]
lemma mapFundamentalGroupoid_assoc (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (f₃ : Z ⟶ T) :
    (mapFundamentalGroupoidComp (f₁ ≫ f₂) f₃).inv ≫
      Functor.whiskerRight (mapFundamentalGroupoidComp f₁ f₂).inv _ ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (mapFundamentalGroupoidComp f₂ f₃).hom ≫
            (mapFundamentalGroupoidComp f₁ (f₂ ≫ f₃)).hom =
    (congrMapFundamentalGroupoid (by simp)).hom := by
  sorry

namespace FundamentalGroupoid

@[simps!]
def pseudofunctor : LocallyDiscrete SSet.{u} ⥤ᵖ  Cat.{u, u} :=
  LocallyDiscrete.mkPseudofunctor (fun X ↦ .of (FundamentalGroupoid X))
    (fun f ↦ (mapFundamentalGroupoid f).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (mapFundamentalGroupoidId X))
    (fun f g ↦ Cat.Hom.isoMk ((mapFundamentalGroupoidComp f g).symm))
    (fun f₁ f₂ f₃ ↦ by ext : 1; apply mapFundamentalGroupoid_assoc)
    (fun f ↦ by ext : 1; apply mapFundamentalGroupoid_id_comp)
    (fun f ↦ by ext : 1; apply mapFundamentalGroupoid_comp_id)

end FundamentalGroupoid

end SSet
