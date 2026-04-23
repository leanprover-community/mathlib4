/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.Bound.Init
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

/-!
# Morphisms between bounded complexes are small

Let `C` be an abelian category. Assuming `HasExt.{w} C`, we show that
if two cochain complexes `K` and `L` are cohomologically in a single degree,
then the type of morphisms from `K` to `L⟦n⟧` in the derived category is `w`-small
for any `n : ℤ`, which we phrase here by saying that
`HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso _ _) ℤ K L` hold.

## TODO
* When more definitions are introduced for t-structures (e.g. the heart),
  show that the conclusion holds when `K` and `L` are cohomologically bounded.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

open Localization Limits ZeroObject DerivedCategory Pretriangulated

namespace HasExt

set_option backward.isDefEq.respectTransparency false in
variable {C} in
lemma hasSmallLocalizedShiftedHom_of_isLE_of_isGE
    [HasExt.{w} C] (K L : CochainComplex C ℤ)
    (a b : ℤ) [K.IsGE a] [K.IsLE a] [L.IsGE b] [L.IsLE b] :
    HasSmallLocalizedShiftedHom.{w}
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K L := by
  letI := HasDerivedCategory.standard
  obtain ⟨X, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (Q.obj K) a
  obtain ⟨Y, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (Q.obj L) b
  simp only [hasSmallLocalizedShiftedHom_iff _ _ Q]
  exact fun p q ↦ small_of_injective (f := fun φ ↦
    ((singleFunctors C).shiftIso p (a - p) a (by simp)).inv.app X ≫
      eX.inv⟦p⟧' ≫ φ ≫ eY.hom⟦q⟧' ≫
        ((singleFunctors C).shiftIso q (b - q) b (by simp)).hom.app Y)
    (fun φ₁ φ₂ h ↦ by simpa [cancel_epi, cancel_mono] using h)

instance [HasExt.{w} C] (K L : CochainComplex C ℤ)
    [K.IsGE 0] [K.IsLE 0] [L.IsGE 0] [L.IsLE 0] :
    HasSmallLocalizedShiftedHom.{w}
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K L :=
  HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0

end HasExt

end CategoryTheory
