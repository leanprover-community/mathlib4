/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Points

/-!
# The closed symmetric monoidal category of modules on a scheme

The tensor product and internal hom are inherited from sheaves of modules over the
structure sheaf.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory

variable (X : Scheme.{u})

noncomputable instance : MonoidalCategory X.Modules :=
  SheafOfModulesOfCommRing.monoidalCategory X.sheaf

noncomputable instance : SymmetricCategory X.Modules :=
  SheafOfModulesOfCommRing.symmetricCategory X.sheaf

noncomputable instance : MonoidalClosed X.Modules :=
  SheafOfModulesOfCommRing.monoidalClosed X.sheaf
