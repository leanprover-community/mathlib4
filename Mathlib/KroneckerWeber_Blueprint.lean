import Mathlib

section maximalAbelian

variable {K L : Type*} [Field K] [Field L] [Algebra K L]


lemma galois_sup (F₁ F₂ : IntermediateField K L) [IsGalois K F₁] [Module.Finite K F₁]
    [IsGalois K F₂] [Module.Finite K F₂] :
    IsGalois K ↥(F₁ ⊔ F₂) := by
  sorry

lemma abelian_sup (F₁ F₂ : IntermediateField K L)
    [IsGalois K F₁] [IsMulCommutative (F₁ ≃ₐ[K] F₁)] [Module.Finite K F₁]
    [IsGalois K F₂] [IsMulCommutative (F₂ ≃ₐ[K] F₂)] [Module.Finite K F₂] :
    IsMulCommutative (↥(F₁ ⊔ F₂) ≃ₐ[K] (↥(F₁ ⊔ F₂))) := by
  sorry

variable (K L) in
def maximalAbelianSubfield : IntermediateField K L := sorry

instance maximalAbelianSubfield_isGalois : IsGalois K (maximalAbelianSubfield K L) := sorry

instance maximalAbelianSubfield_isAbelian :
    IsMulCommutative ((maximalAbelianSubfield K L) ≃ₐ[K] (maximalAbelianSubfield K L)) := sorry

theorem maximalAbelianSubfield_isMaximal (F : IntermediateField K L) [IsGalois K F]
    [IsMulCommutative (F ≃ₐ[K] F)] : F ≤ maximalAbelianSubfield K L := sorry

end maximalAbelian

open NumberField

variable {p : ℕ} (hp : p.Prime)

lemma lemma_1_3 {K : Type*} [Field K] [NumberField K] (F₁ F₂ : IntermediateField ℚ K)
  [IsGalois ℚ F₁] [IsCyclic (F₁ ≃ₐ[ℚ] F₁)] (h₁ : Module.finrank ℚ F₁ = p)
  [IsGalois ℚ F₂] [IsCyclic (F₂ ≃ₐ[ℚ] F₂)] (h₂ : Module.finrank ℚ F₂ = p) (h_top : F₁ ⊔ F₂ = ⊤)
  (h_cyc : IsCyclic (K ≃ₐ[ℚ] K)) : F₁ ≤ F₂ ∨ F₂ ≤ F₁ := sorry

lemma lemma_1_4 {m : ℕ} {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    [IsMulCommutative (K ≃ₐ[ℚ] K)] (h₁ : Module.finrank ℚ K = p ^ m)
    (h₂ : ∀ (Q : Ideal (𝓞 K)) (_ : Q.IsPrime), ¬ (p ∣ (Ideal.absNorm Q)) →
      Algebra.IsUnramifiedAt ℤ Q)
    (E : Type*) [Field E] [CharZero E] [IsCyclotomicExtension {p ^ (m + 1)} ℚ E] :
    Nonempty (K →+* E) := sorry
