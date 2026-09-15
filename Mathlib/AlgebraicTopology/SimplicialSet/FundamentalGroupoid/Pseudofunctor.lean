/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# The fundamental groupoid, as a pseudofunctor

In this file, we define the pseudofunctor
`SSet.FundamentalGroupoid.pseudofunctor : LocallyDiscrete SSet ⥤ᵖ  Cat`
which sends a simplicial set to its fundamental groupoid.

-/

@[expose] public section

universe u

open CategoryTheory Bicategory

namespace SSet

variable {X Y Z T : SSet.{u}}

@[reassoc]
lemma mapFundamentalGroupoid_id_comp (f : X ⟶ Y) :
    (mapFundamentalGroupoidComp (𝟙 X) f).inv ≫
      Functor.whiskerRight (mapFundamentalGroupoidId X).hom _ ≫
        (Functor.leftUnitor _).hom =
    (congrMapFundamentalGroupoidOfEq (by simp)).hom := by
  cat_disch

@[reassoc]
lemma mapFundamentalGroupoid_comp_id (f : X ⟶ Y) :
    (mapFundamentalGroupoidComp f (𝟙 Y)).inv ≫
      Functor.whiskerLeft _ (mapFundamentalGroupoidId Y).hom ≫
        (Functor.rightUnitor _).hom =
    (congrMapFundamentalGroupoidOfEq (by simp)).hom := by
  cat_disch

@[reassoc]
lemma mapFundamentalGroupoid_assoc (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (f₃ : Z ⟶ T) :
    (mapFundamentalGroupoidComp (f₁ ≫ f₂) f₃).inv ≫
      Functor.whiskerRight (mapFundamentalGroupoidComp f₁ f₂).inv _ ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (mapFundamentalGroupoidComp f₂ f₃).hom ≫
            (mapFundamentalGroupoidComp f₁ (f₂ ≫ f₃)).hom =
    (congrMapFundamentalGroupoidOfEq (by simp)).hom := by
  cat_disch

namespace FundamentalGroupoid

/-- The pseudofunctor which sends a simplicial set to its
fundamental groupoid. -/
@[simps!]
def pseudofunctor : LocallyDiscrete SSet.{u} ⥤ᵖ  Cat.{u, u} :=
  LocallyDiscrete.mkPseudofunctor (fun X ↦ .of (FundamentalGroupoid X))
    (fun f ↦ (mapFundamentalGroupoid f).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (mapFundamentalGroupoidId X))
    (fun f g ↦ Cat.Hom.isoMk ((mapFundamentalGroupoidComp f g).symm))
    (fun _ _ _ ↦ by ext : 1; apply mapFundamentalGroupoid_assoc)
    (fun _ ↦ by ext : 1; apply mapFundamentalGroupoid_id_comp)
    (fun _ ↦ by ext : 1; apply mapFundamentalGroupoid_comp_id)

end FundamentalGroupoid

end SSet
