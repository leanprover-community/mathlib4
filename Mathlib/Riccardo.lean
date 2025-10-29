import Mathlib

open NumberField NumberField.IsCMField

variable {K : Type*} [Field K] [NumberField K] (p : ℕ) [IsCyclotomicExtension {p} ℚ K]
  (ζ : (𝓞 K)ˣ) (hζ : IsPrimitiveRoot ζ p)

theorem unit_inv_conj_is_root_of_unity [IsTotallyComplex K]
    [IsCMField K] (u : (𝓞 K)ˣ) [H : Fact (p.Prime)] (hp : 2 < p) :
    ∃ m : ℕ, u * (unitsComplexConj K u)⁻¹ = (ζ ^ m) ^ 2 := by
  rw [← unitsMulComplexConjInv_apply]
  have := index_unitsMulComplexConjInv_range_dvd K
  have : ∀ ζ, ζ ^ 2 ∈ (unitsMulComplexConjInv K).range := sorry
  
  sorry
