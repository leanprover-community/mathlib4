/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech

/-!
# Cech cohomology

Given a family of objects `U : ι → C` in a category `C` that has finite products,
we define a Cech complex functor
`cechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` which sends a presheaf
`P : Cᵒᵖ ⥤ A` in a preadditive category (where products exist) to the cochain
complex which in degree `n` consists of the product, indexed by `i : Fin (n + 1) → ι`,
of the value of `P` on the product of the objects `U (i a)` for `a : Fin (n + 1)`.

-/

@[expose] public section

universe w t v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]

namespace Limits.FormalCoproduct

open Opposite

variable (E : SimplicialObject (FormalCoproduct.{w} C))

/-- Given a simplicial object `E` in the category `FormalCoproduct C`, this is the
functor `(Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A` which sends `P : Cᵒᵖ ⥤ A` to the
cosimplicial object which sends `⦋n⦌` to the "evaluation" of `P` on `E _⦋n⦌`. -/
@[simps!]
noncomputable def cosimplicialObjectFunctor :
    (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  evalOp.{w} C A ⋙ (Functor.whiskeringLeft _ _ _).obj E.rightOp

variable [Preadditive A]

/-- Given a simplicial object `E` in the category `FormalCoproduct C`, this is the
functor `(Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` which sends `P : Cᵒᵖ ⥤ A` to the
cochain complex which in degree `n` consists of the "evaluation" of `P` on `E _⦋n⦌`. -/
@[simps!]
noncomputable def cochainComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  cosimplicialObjectFunctor E ⋙ AlgebraicTopology.alternatingCofaceMapComplex A

end Limits.FormalCoproduct

variable [HasFiniteProducts C] [Preadditive A] {ι : Type w} (U : ι → C)

/-- Given a family of objects `U : ι → C`, this is the Cech complex functor
`(Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` which sends a presheaf `P : Cᵒᵖ ⥤ A` to the
cochain complex which in degree `n` consists of the product,
indexed by `x : Fin (n + 1) → ι`, of the value of `P` on the product of the
objects `U (x i)` for `i : Fin (n + 1)`. -/
noncomputable def cechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech

end CategoryTheory
