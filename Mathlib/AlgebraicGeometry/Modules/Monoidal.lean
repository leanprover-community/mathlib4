/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Topology.Sheaves.Points

/-!
# The category of modules over a scheme is monoidal


-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace SheafOfModules Bicategory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

end AlgebraicGeometry.Scheme.Modules
