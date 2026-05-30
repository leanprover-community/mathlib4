/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Quasicoherent Sheaves

A module `M : X.Modules` is quasicoherent if it locally admits a presentation.

-/

public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The pullback of a quasicoherent sheaf is quasicoherent -/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent := SheafOfModules.IsQuasicoherent.pullback.{u} _

/-- The pullback of a locally free sheaf is locally free -/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) [M.IsLocallyFree] :
    ((pullback f).obj M).IsLocallyFree := SheafOfModules.IsLocallyFree.pullback.{u} _

end AlgebraicGeometry.Scheme.Modules
