/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
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

/-! The homological functor

In this file, it is shown that if `C` is an abelian category,
then `homologyFunctor C (ComplexShape.up ℤ) n` is a homological functor
`HomotopyCategory C (ComplexShape.up ℤ) ⥤ C`. As distinguished triangles
in the homotopy category can be characterized in terms of degreewise split
short exact sequences of cochain complexes, this follows from the homology
sequence associated to a short exact sequence of homological complexes.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

namespace HomotopyCategory

instance (n : ℤ) : (homologyFunctor C (ComplexShape.up ℤ) n).IsHomological :=
  Functor.IsHomological.mk' _ (fun T hT => by
    rw [distinguished_iff_iso_trianglehOfDegreewiseSplit] at hT
    obtain ⟨S, σ, ⟨e⟩⟩ := hT
    have hS := HomologicalComplex.shortExact_of_degreewise_shortExact S
      (fun n => (σ n).shortExact)
    exact ⟨_, e, (ShortComplex.exact_iff_of_iso
      (S.mapNatIso (homologyFunctorFactors C (ComplexShape.up ℤ) n))).2 (hS.homology_exact₂ n)⟩)

end HomotopyCategory
