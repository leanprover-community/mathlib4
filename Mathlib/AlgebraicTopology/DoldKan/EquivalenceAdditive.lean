/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.equivalence_additive
! leanprover-community/mathlib commit 19d6240dcc5e5c8bd6e1e3c588b92e837af76f9e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.NCompGamma

/-! The Dold-Kan equivalence for additive categories.

This file defines `preadditive.dold_kan.equivalence` which is the equivalence
of categories `karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ)`.

-/


noncomputable section

open
  CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents AlgebraicTopology.DoldKan

variable {C : Type _} [Category C] [Preadditive C]

namespace CategoryTheory

namespace Preadditive

namespace DoldKan

/-- The functor `karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)` of
the Dold-Kan equivalence for additive categories. -/
@[simps]
def n : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ) :=
  N₂
#align category_theory.preadditive.dold_kan.N CategoryTheory.Preadditive.DoldKan.n

variable [HasFiniteCoproducts C]

/-- The inverse functor `karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C)` of
the Dold-Kan equivalence for additive categories. -/
@[simps]
def Γ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C) :=
  Γ₂
#align category_theory.preadditive.dold_kan.Γ CategoryTheory.Preadditive.DoldKan.Γ

/-- The Dold-Kan equivalence `karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ)`
for additive categories. -/
@[simps]
def equivalence : Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)
    where
  Functor := n
  inverse := Γ
  unitIso := Γ₂N₂
  counitIso := n₂Γ₂
  functor_unitIso_comp' P := by
    let α := N.map_iso (Γ₂N₂.app P)
    let β := N₂Γ₂.app (N.obj P)
    symm
    change 𝟙 _ = α.hom ≫ β.hom
    rw [← iso.inv_comp_eq, comp_id, ← comp_id β.hom, ← iso.inv_comp_eq]
    exact AlgebraicTopology.DoldKan.identity_n₂_objectwise P
#align category_theory.preadditive.dold_kan.equivalence CategoryTheory.Preadditive.DoldKan.equivalence

end DoldKan

end Preadditive

end CategoryTheory

