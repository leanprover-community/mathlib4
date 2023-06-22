import Mathlib.Algebra.Homology.ShortComplex.Ab

namespace CategoryTheory

namespace ShortComplex

variable {C : Type _} [Category C] [ConcreteCategory C] [Abelian C]
  [HasForget₂ C Ab] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

lemma exact_iff_exact_map_forget₂ : S.Exact ↔ (S.map (forget₂ C Ab)).Exact :=
  (S.exact_map_iff_of_faithful (forget₂ C Ab)).symm

lemma exact_iff_of_concrete_category :
  S.Exact ↔ ∀ (x₂ : (forget₂ C Ab).obj S.X₂) (_ : ((forget₂ C Ab).map S.g) x₂ = 0),
    ∃ (x₁ : (forget₂ C Ab).obj S.X₁), ((forget₂ C Ab).map S.f) x₁ = x₂ := by
  rw [S.exact_iff_exact_map_forget₂, ab_exact_iff]
  rfl

end ShortComplex

end CategoryTheory
