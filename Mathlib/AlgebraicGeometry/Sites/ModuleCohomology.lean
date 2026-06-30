/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The module structure on the cohomology of a sheaf of modules

If `X` is a scheme over `R` via `f : X ⟶ Spec R`, the cohomology groups of any sheaf of modules
`F : X.Modules` naturally have the structure of `R`-modules. In this file we
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {R : CommRingCat} (f : X ⟶ Spec R) (F : X.Modules)

/--
The cohomology of a sheaf of modules in degree `n`
-/
abbrev H := ((SheafOfModules.toSheaf _).obj F).H

/-- The `R`-module structure on the degree-`n` cohomology of the abelian sheaf underlying an
`𝒪_X`-module `F`, where `R` acts through a morphism `f : X ⟶ Spec R` via `smulEnd`. -/
@[reducible] noncomputable def cohomologyModule (n : ℕ) : Module R (F.H n) :=
  Abelian.Ext.moduleOfRingHom (smulEnd f F) n

/--
For a morphism `f : X ⟶ Spec R` and a sheaf of modules `F : X.Modules`, `F.h f n` gives the finrank
of the `n`th cohomology group of `F` as an `R`-module.
-/
noncomputable def h (n : ℕ) :=
  letI := F.cohomologyModule f n
  Module.finrank R (F.H n)

end AlgebraicGeometry.Scheme.Modules
