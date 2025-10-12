/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Modules.Presheaf

/-!
# The category of sheaves of modules over a scheme

In this file, we define the abelian category of sheaves of modules
`X.Modules` over a scheme `X`.

-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The category of sheaves of modules over a scheme. -/
abbrev Modules := SheafOfModules.{u} X.ringCatSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
noncomputable instance : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  inferInstance

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
noncomputable instance : Abelian X.Modules := inferInstance

end AlgebraicGeometry.Scheme
