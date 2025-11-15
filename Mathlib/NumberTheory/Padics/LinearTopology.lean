/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.Valued.LinearTopology
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# p-adic integers have a linear topology

## Implementation details

We rely on the scoped `Valued ℚ_[p] ℝ≥0` instance to get that the p-adic integers have
a linear topology via `IsLinearTopology.of_valued'`. We transfer that back to
`IsLinearTopology ℤ_[p] ℤ_[p]` via the definitional equality.
-/

variable {p : ℕ} [Fact (Nat.Prime p)]

section
open NormedField Valued
instance : IsLinearTopology ℤ_[p] ℤ_[p] := inferInstanceAs (IsLinearTopology 𝒪[ℚ_[p]] 𝒪[ℚ_[p]])
instance : IsLinearTopology ℤ_[p] ℚ_[p] := inferInstanceAs (IsLinearTopology 𝒪[ℚ_[p]] ℚ_[p])
end
