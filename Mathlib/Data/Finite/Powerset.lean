/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Fintype.Powerset

/-!
# Finiteness of powersets
-/

variable {α : Type*}

namespace Finite

instance [Finite α] : Finite (Set α) := inferInstance

end Finite
