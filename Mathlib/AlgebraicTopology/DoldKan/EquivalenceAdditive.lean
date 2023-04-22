/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.equivalence_additive
! leanprover-community/mathlib commit 19d6240dcc5e5c8bd6e1e3c588b92e837af76f9e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.AlgebraicTopology.DoldKan.NCompGamma

/-! The Dold-Kan equivalence for additive categories.

This file defines `Preadditive.DoldKan.equivalence` which is the equivalence
of categories `Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)`.

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Idempotents AlgebraicTopology.DoldKan

variable {C : Type _} [Category C] [Preadditive C]

namespace CategoryTheory

namespace Preadditive

namespace DoldKan

/-- The functor `Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)` of
the Dold-Kan equivalence for additive categories. -/
@[simp]
def N : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ) :=
  N₂
set_option linter.uppercaseLean3 false in
#align category_theory.preadditive.dold_kan.N CategoryTheory.Preadditive.DoldKan.N

variable [HasFiniteCoproducts C]

/-- The inverse functor `Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C)` of
the Dold-Kan equivalence for additive categories. -/
@[simp]
def Γ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C) :=
  Γ₂
#align category_theory.preadditive.dold_kan.Γ CategoryTheory.Preadditive.DoldKan.Γ

/-- The Dold-Kan equivalence `Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)`
for additive categories. -/
@[simps]
def equivalence : Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ) where
  functor := N
  inverse := Γ
  unitIso := Γ₂N₂
  counitIso := N₂Γ₂
  functor_unitIso_comp P := by
    -- porting note: the proof had to be tweaked to avoid timeouts
    suffices N₂Γ₂.inv.app (N₂.obj P) = N₂.map (Γ₂N₂.hom.app P) by
      dsimp only [N]
      erw [← this, ← N₂Γ₂.inv_hom_id_app (N₂.obj P)]
    rw [← cancel_mono (N₂.map (Γ₂N₂.natTrans.app P)),
      AlgebraicTopology.DoldKan.identity_N₂_objectwise P, ← N₂.map_comp]
    simp only [← Γ₂N₂_inv, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app,
      Functor.id_obj, N₂.map_id]
#align category_theory.preadditive.dold_kan.equivalence CategoryTheory.Preadditive.DoldKan.equivalence

end DoldKan

end Preadditive

end CategoryTheory
