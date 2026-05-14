/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyFiber
public import Mathlib.AlgebraicTopology.ModelCategory.PathObject
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
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

/-!
# Precylinder and pre-path objects in the category of homological complexes

In this file, we upgrade the definitions `HomologicalComplex.cylinder` and
`HomologicalComplex.pathObject` to pre-cylinder objects and pre-path
objects in the sense of homotopical algebra.

-/

@[expose] public section

open CategoryTheory Limits HomotopicalAlgebra

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {ι : Type*} {c : ComplexShape ι} [DecidableRel c.Rel]
  (K : HomologicalComplex C c)
  [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]

/-- The precylinder object of a homological complex that is given by
`HomologicalComplex.cylinder`. -/
@[simps]
noncomputable def precylinder [K.HasCylinder] : Precylinder K where
  I := K.cylinder
  i₀ := cylinder.ι₀ _
  i₁ := cylinder.ι₁ _
  π := cylinder.π _

/-- The pre-path object of a homological complex that is given by
 `HomologicalComplex.pathObject`. -/
@[simps]
noncomputable def prepathObject [K.HasPathObject] : PrepathObject K where
  P := K.pathObject
  p₀ := pathObject.π₀ _
  p₁ := pathObject.π₁ _
  ι := pathObject.ι _

end HomologicalComplex
