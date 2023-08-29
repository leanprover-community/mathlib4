/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.NCompGamma

#align_import algebraic_topology.dold_kan.equivalence_additive from "leanprover-community/mathlib"@"32a7e535287f9c73f2e4d2aef306a39190f0b504"

/-! The Dold-Kan equivalence for additive categories.

This file defines `Preadditive.DoldKan.equivalence` which is the equivalence
of categories `Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Idempotents AlgebraicTopology.DoldKan

variable {C : Type*} [Category C] [Preadditive C]

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
    let α := N.mapIso (Γ₂N₂.app P)
    -- ⊢ N.map (NatTrans.app Γ₂N₂.hom P) ≫ NatTrans.app N₂Γ₂.hom (N.obj P) = 𝟙 (N.obj …
    let β := N₂Γ₂.app (N.obj P)
    -- ⊢ N.map (NatTrans.app Γ₂N₂.hom P) ≫ NatTrans.app N₂Γ₂.hom (N.obj P) = 𝟙 (N.obj …
    symm
    -- ⊢ 𝟙 (N.obj P) = N.map (NatTrans.app Γ₂N₂.hom P) ≫ NatTrans.app N₂Γ₂.hom (N.obj …
    change 𝟙 _ = α.hom ≫ β.hom
    -- ⊢ 𝟙 (N.obj ((𝟭 (Karoubi (SimplicialObject C))).obj P)) = α.hom ≫ β.hom
    rw [← Iso.inv_comp_eq, comp_id, ← comp_id β.hom, ← Iso.inv_comp_eq]
    -- ⊢ β.inv ≫ α.inv = 𝟙 ((𝟭 (Karoubi (ChainComplex C ℕ))).obj (N.obj P))
    exact AlgebraicTopology.DoldKan.identity_N₂_objectwise P
    -- 🎉 no goals
#align category_theory.preadditive.dold_kan.equivalence CategoryTheory.Preadditive.DoldKan.equivalence

end DoldKan

end Preadditive

end CategoryTheory
