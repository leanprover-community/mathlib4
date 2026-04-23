/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.NCompGamma
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-! The Dold-Kan equivalence for additive categories.

This file defines `Preadditive.DoldKan.equivalence` which is the equivalence
of categories `Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Idempotents AlgebraicTopology.DoldKan

variable {C : Type*} [Category* C] [Preadditive C]

namespace CategoryTheory

namespace Preadditive

namespace DoldKan

/-- The functor `Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)` of
the Dold-Kan equivalence for additive categories. -/
@[simp]
def N : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ) :=
  N₂

variable [HasFiniteCoproducts C]

/-- The inverse functor `Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C)` of
the Dold-Kan equivalence for additive categories. -/
@[simp]
def Γ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C) :=
  Γ₂

set_option backward.isDefEq.respectTransparency false in
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
    let β := N₂Γ₂.app (N.obj P)
    symm
    change 𝟙 _ = α.hom ≫ β.hom
    rw [← Iso.inv_comp_eq, comp_id, ← comp_id β.hom, ← Iso.inv_comp_eq]
    exact AlgebraicTopology.DoldKan.identity_N₂_objectwise P

end DoldKan

end Preadditive

end CategoryTheory
