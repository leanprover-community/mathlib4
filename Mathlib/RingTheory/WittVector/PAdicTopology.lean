import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

noncomputable section

namespace WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {k : Type*} [CommRing k]
    [CharP k p] (x : ℕ → k)
    -- (n : ℕ) (a : kˣ) (A : WittVector p k) (bs : Fin (n + 1) → k)

local notation "𝕎" => WittVector p

namespace PAdicTopology

scoped instance : TopologicalSpace (𝕎 k) := (Ideal.span {(p : 𝕎 k)}).adicTopology



end PAdicTopology

open PAdicTopology



end WittVector

end
