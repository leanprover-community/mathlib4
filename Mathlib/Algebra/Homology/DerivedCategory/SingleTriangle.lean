/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The distinguished triangle of a short exact sequence in an abelian category

Given a short exact short complex `S` in an abelian category, we construct
the associated distinguished triangle in the derived category:
`(singleFunctor C 0).obj S.X₁ ⟶ (singleFunctor C 0).obj S.X₂ ⟶ (singleFunctor C 0).obj S.X₃ ⟶ ...`

## TODO
* when the canonical t-structure on the derived category is formalized, refactor
  this definition to make it a particular case of the triangle induced by a short
  exact sequence in the heart of a t-structure

-/

assert_not_exists TwoSidedIdeal

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open Category DerivedCategory Pretriangulated

namespace ShortComplex

variable {S : ShortComplex C} (hS : S.ShortExact)

namespace ShortExact

/-- The connecting homomorphism
`(singleFunctor C 0).obj S.X₃ ⟶ ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧` in the derived
category of `C` when `S` is a short exact short complex in `C`. -/
noncomputable def singleδ : (singleFunctor C 0).obj S.X₃ ⟶
    ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧ :=
  (((SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)).hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) ≫
    (((SingleFunctors.evaluation _ _ 0).mapIso
      (singleFunctorsPostcompQIso C)).inv.app S.X₁)⟦(1 : ℤ)⟧'

/-- The (distinguished) triangle in the derived category of `C` given by a
short exact short complex in `C`. -/
@[simps!]
noncomputable def singleTriangle : Triangle (DerivedCategory C) :=
  Triangle.mk ((singleFunctor C 0).map S.f)
    ((singleFunctor C 0).map S.g) hS.singleδ

/-- Given a short exact complex `S` in `C` that is short exact (`hS`), this is the
canonical isomorphism between the triangle `hS.singleTriangle` in the derived category
and the triangle attached to the corresponding short exact sequence of cochain complexes
after the application of the single functor. -/
@[simps!]
noncomputable def singleTriangleIso :
    hS.singleTriangle ≅
      triangleOfSES (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) := by
  let e := (SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostcompQIso C)
  refine Triangle.isoMk _ _ (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) ?_ ?_ ?_
  · cat_disch
  · cat_disch
  · dsimp [singleδ, e]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, SingleFunctors.inv_hom_id_hom_app]
    erw [Functor.map_id]
    rw [comp_id]

/-- The distinguished triangle in the derived category of `C` given by a
short exact short complex in `C`. -/
lemma singleTriangle_distinguished :
    hS.singleTriangle ∈ distTriang (DerivedCategory C) :=
  isomorphic_distinguished _ (triangleOfSES_distinguished (hS.map_of_exact
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0))) _ (singleTriangleIso hS)

end ShortExact

end ShortComplex

end CategoryTheory
