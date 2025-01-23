import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.InfiniteSum.Defs

noncomputable section

namespace WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {k : Type*} [CommRing k]
    [CharP k p] (x : ℕ → k)
    -- (n : ℕ) (a : kˣ) (A : WittVector p k) (bs : Fin (n + 1) → k)

local notation "𝕎" => WittVector p

namespace PAdicTopology

scoped instance withIdeal : WithIdeal (𝕎 k) where
  i := Ideal.span {(p : 𝕎 k)}
#synth UniformSpace (𝕎 k)

-- #synth IsAdicComplete (Ideal.span {(p : 𝕎 k)} ) (𝕎 k)

scoped instance completeSpace : CompleteSpace (𝕎 k) := sorry

theorem summable_p_pow_mul (x : ℕ → 𝕎 k) : Summable (fun n ↦ ((p ^ n) * x n)) := sorry

end PAdicTopology

open PAdicTopology



end WittVector

end
