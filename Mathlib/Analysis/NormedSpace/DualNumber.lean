/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.NormedSpace.TrivSqZeroExt

/-!
# Results on `DualNumber R` related to the norm

These are just restatements of similar statements about `TrivSqZeroExt R M`.

## Main results

* `exp_eps`

-/

open NormedSpace -- For `NormedSpace.exp`.

namespace DualNumber

open TrivSqZeroExt

variable {R : Type*} [CommRing R] [Algebra ℚ R]

variable [UniformSpace R] [TopologicalRing R] [CompleteSpace R] [T2Space R]

@[simp]
theorem exp_eps : exp (eps : DualNumber R) = 1 + eps :=
  exp_inr _

@[simp]
theorem exp_smul_eps (r : R) : exp (r • eps : DualNumber R) = 1 + r • eps := by
  rw [eps, ← inr_smul, exp_inr]

end DualNumber
