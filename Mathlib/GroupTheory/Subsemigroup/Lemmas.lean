/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.GroupTheory.Subsemigroup.Center

/-!
# Centers of semigroups, as subsemigroups.
-/

@[expose] public section

variable {M : Type*} [Mul M]

namespace Subsemigroup

@[to_additive]
theorem center_prod {N : Type*} [Mul N] : center (M × N) = prod (center M) (center N) :=
  SetLike.coe_injective Set.center_prod

end Subsemigroup
