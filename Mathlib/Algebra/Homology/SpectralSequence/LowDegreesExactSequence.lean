import Mathlib.Algebra.Homology.SpectralSequence.Basic

open CategoryTheory Category

namespace CohomologicalSpectralSequence

variable {C : Type _} [Category C] [Abelian C]

variable {r₀ : ℤ} (E : CohomologicalSpectralSequence C r₀) [E.IsFirstQuadrant]

lemma rMin_zero_zero_le_of_isFirstQuadrant (hr₀ : r₀ ≤ 2):
    E.rMin ⟨0, 0⟩ ≤ 2 :=
  (E.rMin_le_of_isFirstQuadrant _).trans (by aesop)

lemma rMin_one_zero_le_of_isFirstQuadrant (hr₀ : r₀ ≤ 2):
    E.rMin ⟨1, 0⟩ ≤ 2 :=
  (E.rMin_le_of_isFirstQuadrant _).trans (by aesop)

lemma rMin_two_zero_le_of_isFirstQuadrant (hr₀ : r₀ ≤ 3):
    E.rMin ⟨2, 0⟩ ≤ 3 :=
  (E.rMin_le_of_isFirstQuadrant _).trans (by
    refine' max_le _ (max_le _ _)
    all_goals dsimp ; linarith)

lemma rMin_zero_one_le_of_isFirstQuadrant (hr₀ : r₀ ≤ 3):
    E.rMin ⟨0, 1⟩ ≤ 3 :=
  (E.rMin_le_of_isFirstQuadrant _).trans (by
    refine' max_le _ (max_le _ _)
    all_goals dsimp ; linarith)

instance : E.CollapsesAt 0 1 where
  condition := fun k hk => by
    apply E.isZero_pageInfinity_of_isFirstQuadrant
    dsimp [cohomologicalStripes]
    by_contra'
    apply hk
    linarith

namespace LowDegreesExactSequence

variable {E}
variable {X : ℤ → C} (h : E.StronglyConvergesTo X) (hr₀ : r₀ ≤ 2)

noncomputable def E₂ZeroZeroIsoAbutmentZero : E.page 2 hr₀ ⟨0, 0⟩ ≅ X 0 :=
  E.isoPageInfinityOfLE ⟨0, 0⟩ 2 (E.rMin_zero_zero_le_of_isFirstQuadrant hr₀) ≪≫
    (h.stronglyConvergesToInDegree 0).pageInfinityIsoAbutment 1 ⟨0, 0⟩ rfl

end LowDegreesExactSequence

end CohomologicalSpectralSequence
