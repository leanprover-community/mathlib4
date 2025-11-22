/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Morphisms to K-injective complexes in the derived category

In this file, we show that if `L : CochainComplex C ℤ` is K-injective,
then for any `K : HomotopyCategory C (.up ℤ)`, the functor `DerivedCategory.Qh`
induces a bijection from the type of morphisms `K ⟶ (HomotopyCategory.quotient _ _).obj L)`
(i.e. homotopy classes of morphisms of cochain complexes) to the type of
morphisms in the derived category.

-/

@[expose] public section

universe w v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

lemma CochainComplex.IsKInjective.Qh_map_bijective [HasDerivedCategory C]
    (K : HomotopyCategory C (ComplexShape.up ℤ))
    (L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      (K ⟶ (HomotopyCategory.quotient _ _).obj L) → _ ) :=
  (CochainComplex.IsKInjective.rightOrthogonal L).map_bijective_of_isTriangulated _ _
