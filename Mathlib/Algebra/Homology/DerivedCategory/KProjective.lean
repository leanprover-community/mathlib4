/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-!
# Morphisms from K-projective complexes in the derived category

In this file, we show that if `K : CochainComplex C ℤ` is K-projective,
then for any `L : HomotopyCategory C (.up ℤ)`, the functor `DerivedCategory.Qh`
induces a bijection from the type of morphisms `(HomotopyCategory.quotient _ _).obj K) ⟶ L`
(i.e. homotopy classes of morphisms of cochain complexes) to the type of
morphisms in the derived category.

-/

@[expose] public section

universe w v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

lemma CochainComplex.IsKProjective.Qh_map_bijective [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (L : HomotopyCategory C (ComplexShape.up ℤ))
    [K.IsKProjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient _ _).obj K ⟶ L) → _ ) :=
  (CochainComplex.IsKProjective.leftOrthogonal K).map_bijective_of_isTriangulated _ _
