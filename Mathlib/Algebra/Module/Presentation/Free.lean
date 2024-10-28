/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Presentation of free modules

A module is free iff it admits a presentation with generators but no relations.

-/

universe v u

namespace Module

variable {A : Type u} [Ring A] (M : Type v) [AddCommGroup M] [Module A M]
  (relations : Relations A)

end Module
