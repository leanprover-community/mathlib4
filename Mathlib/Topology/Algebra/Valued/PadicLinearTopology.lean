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

-/

variable {p : ℕ} [Fact (Nat.Prime p)]

section
open NormedField Valued
-- we don't have `Valued ℚ_[p] Γ₀` for any `Γ₀`, and even if we did
-- the definition of `ℤ_[p]` would not necessarily line up
instance : IsDiscreteValuationRing 𝒪[ℚ_[p]] := inferInstanceAs (IsDiscreteValuationRing ℤ_[p])
instance : IsLinearTopology ℤ_[p] ℤ_[p] := inferInstanceAs (IsLinearTopology 𝒪[ℚ_[p]] 𝒪[ℚ_[p]])
end
