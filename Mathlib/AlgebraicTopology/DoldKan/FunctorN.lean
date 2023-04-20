/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.functor_n
! leanprover-community/mathlib commit 1995c7bbdbb0adb1b6d5acdc654f6cf46ed96cfa
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.PInfty

/-!

# Construction of functors N for the Dold-Kan correspondence

TODO (@joelriou) continue adding the various files referenced below

In this file, we construct functors `N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)`
and `N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)`
for any preadditive category `C`. (The indices of these functors are the number of occurrences
of `karoubi` at the source or the target.)

In the case `C` is additive, the functor `N₂` shall be the functor of the equivalence
`category_theory.preadditive.dold_kan.equivalence` defined in `equivalence_additive.lean`.

In the case the category `C` is pseudoabelian, the composition of `N₁` with the inverse of the
equivalence `chain_complex C ℕ ⥤ karoubi (chain_complex C ℕ)` will be the functor
`category_theory.idempotents.dold_kan.N` of the equivalence of categories
`category_theory.idempotents.dold_kan.equivalence : simplicial_object C ≌ chain_complex C ℕ`
defined in `equivalence_pseudoabelian.lean`.

When the category `C` is abelian, a relation between `N₁` and the
normalized Moore complex functor shall be obtained in `normalized.lean`.

(See `equivalence.lean` for the general strategy of proof.)

-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Idempotents

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C]

/-- The functor `simplicial_object C ⥤ karoubi (chain_complex C ℕ)` which maps
`X` to the formal direct factor of `K[X]` defined by `P_infty`. -/
@[simps]
def n₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)
    where
  obj X :=
    { pt := AlternatingFaceMapComplex.obj X
      p := pInfty
      idem := pInfty_idem }
  map X Y f :=
    { f := pInfty ≫ AlternatingFaceMapComplex.map f
      comm := by
        ext
        simp }
  map_id' X := by
    ext
    dsimp
    simp
  map_comp' X Y Z f g := by
    ext
    simp
#align algebraic_topology.dold_kan.N₁ AlgebraicTopology.DoldKan.n₁

/-- The extension of `N₁` to the Karoubi envelope of `simplicial_object C`. -/
@[simps]
def n₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ) :=
  (functorExtension₁ _ _).obj n₁
#align algebraic_topology.dold_kan.N₂ AlgebraicTopology.DoldKan.n₂

end DoldKan

end AlgebraicTopology

