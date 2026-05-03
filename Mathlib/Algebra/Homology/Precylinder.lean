/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyFiber
public import Mathlib.AlgebraicTopology.ModelCategory.PathObject

/-! Precylinder and prepath objects in the category of cochain complexes

-/

@[expose] public section

open CategoryTheory Limits HomotopicalAlgebra

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {ι : Type*} {c : ComplexShape ι} [DecidableRel c.Rel]
  (K : HomologicalComplex C c)
  [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]

/-- The precylinder object of a homological complex. -/
@[simps]
noncomputable def precylinder [K.HasCylinder] : Precylinder K where
  I := K.cylinder
  i₀ := cylinder.ι₀ _
  i₁ := cylinder.ι₁ _
  π := cylinder.π _

/-- The pre-path object of a homological complex. -/
@[simps]
noncomputable def prepathObject [K.HasPathObject] : PrepathObject K where
  P := K.pathObject
  p₀ := pathObject.π₀ _
  p₁ := pathObject.π₁ _
  ι := pathObject.ι _

end HomologicalComplex
