/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Quasicoherent Sheaves

A module `M : X.Modules` is quasicoherent if it locally admits a presentation.

-/

@[expose] public section

universe u v₁ u₁

section

open CategoryTheory TopologicalSpace Topology Module

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

#check freeLocus R M

end AlgebraicGeometry.Scheme.Modules
