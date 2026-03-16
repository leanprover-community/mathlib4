/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.QuasicoherentMonoidal
public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.Topology.Sheaves.Points

/-!
# The category of modules over a scheme is monoidal


-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

noncomputable instance : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

abbrev isQuasicoherent : ObjectProperty X.Modules :=
  SheafOfModules.isQuasicoherent X.ringCatSheaf

instance : (isQuasicoherent X).IsMonoidal :=
  SheafOfModules.isMonoidal_isQuasicoherent (R := X.sheaf)

end AlgebraicGeometry.Scheme.Modules
