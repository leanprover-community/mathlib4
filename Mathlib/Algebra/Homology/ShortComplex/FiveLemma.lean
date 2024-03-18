import Mathlib.Algebra.Homology.ShortComplex.ShortComplexFive
import Mathlib.Algebra.Homology.ShortComplex.FourLemma

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type _} [Category C] [Abelian C]
  {K L : ShortComplex₅ C} (φ : K ⟶ L)

namespace ShortComplex₅

lemma five_lemma (hK : K.Exact) (hL : L.Exact)
    (hφ₁ : Epi φ.τ₁) (hφ₂ : IsIso φ.τ₂) (hφ₄ : IsIso φ.τ₄) (h₅ : Mono φ.τ₅) :
    IsIso φ.τ₃ := by
  have : Mono φ.τ₃ := ShortComplex₄.four_lemma_mono (shortComplex₄Functor₁₂₃₄.map φ)
    hK.exact₁₂₃₄ hL.exact₂ hφ₁ (inferInstance : Mono φ.τ₂) (inferInstance : Mono φ.τ₄)
  have : Epi φ.τ₃ := ShortComplex₄.four_lemma_epi (shortComplex₄Functor₂₃₄₅.map φ)
    hL.exact₂₃₄₅ hK.exact₄ (inferInstance : Epi φ.τ₂) (inferInstance : Epi φ.τ₄) h₅
  apply isIso_of_mono_of_epi

end ShortComplex₅
