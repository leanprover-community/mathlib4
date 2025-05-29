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

We don't have `Valued ℚ_[p] Γ₀` for any `Γ₀` unless we open `NormedField`, which converts
`NormedField ℚ_[p]` to `Valued ℚ_[p] ℝ≥0`, which is what allows us to refer to `𝒪[ℚ_[p]]`.
Since `ℤ_[p]` is `{x : ℚ_[p] // ‖x‖ ≤ 1}`, then that is definitionally `𝒪[ℚ_[p]]` when
the valuation is based on the norm. That allows us to tansfer `IsDiscreteValuationRing`.

Conversely, we rely on the `Valued ℚ_[p] ℝ≥0` instance to that the p-adic integers have
a linear topology via `IsLinearTopology.of_valued`. We transfer that back to
`IsLinearTopology ℤ_[p] ℤ_[p]` via the definitional equality.
-/

variable {p : ℕ} [Fact (Nat.Prime p)]

section
open NormedField Valued
instance : IsDiscreteValuationRing 𝒪[ℚ_[p]] := inferInstanceAs (IsDiscreteValuationRing ℤ_[p])
instance : IsLinearTopology ℤ_[p] ℤ_[p] := inferInstanceAs (IsLinearTopology 𝒪[ℚ_[p]] 𝒪[ℚ_[p]])
end
