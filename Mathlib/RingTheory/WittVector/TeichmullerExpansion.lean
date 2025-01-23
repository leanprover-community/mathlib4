import Mathlib.RingTheory.WittVector.PAdicTopology
import Mathlib.RingTheory.WittVector.Teichmuller

noncomputable section

namespace WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {k : Type*} [CommRing k]
    [CharP k p] (x : ℕ → k)
    -- (n : ℕ) (a : kˣ) (A : WittVector p k) (bs : Fin (n + 1) → k)

local notation "𝕎" => WittVector p

open PAdicTopology

def teichmullerSummation : 𝕎 k := ∑' n, (p ^ n : 𝕎 k) * teichmuller p (x n)

theorem summable_teichmullerSummation : Summable (fun n ↦ (p ^ n : 𝕎 k) * teichmuller p (x n)) :=
    summable_p_pow_mul _

-- teichmullerExpansionAux ℕ → k
def teichmullerExpansion : 𝕎 k ≃ (ℕ → k) := sorry

end WittVector

end
