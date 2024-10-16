/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Vector

/-!
# Finiteness of powersets
-/

variable {α : Type*}

namespace Finite

instance [Finite α] : Finite (Set α) := by
  cases nonempty_fintype α
  infer_instance

end Finite
