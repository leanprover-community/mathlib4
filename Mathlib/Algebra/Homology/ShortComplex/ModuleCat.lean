import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits

universe v u

namespace CategoryTheory

open Limits

namespace ShortComplex

variable {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{v} R))

instance : PreservesColimits (forget₂ (ModuleCat.{v} R) Ab) := by
  sorry

lemma moduleCat_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ :=
  S.exact_iff_of_concrete_category

end ShortComplex

end CategoryTheory
