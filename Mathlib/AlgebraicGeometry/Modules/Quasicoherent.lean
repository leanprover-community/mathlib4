/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackPreserves

/-!
# Quasicoherent Sheaves

-/

public section

namespace AlgebraicGeometry.Scheme.Modules

/-- The pullback of a quasicoherent sheaf is quasicoherent -/
instance {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent :=
  SheafOfModules.IsQuasicoherent.pullback _

end AlgebraicGeometry.Scheme.Modules
