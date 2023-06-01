import Mathlib.Algebra.Homology.SpectralSequence.Basic

open CategoryTheory Category Limits

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

@[simps!]
noncomputable def EInfinityShortComplexDegreeOne : ShortComplex C :=
  (h.stronglyConvergesToInDegree 1).shortComplexPageInfinityToAbutmentAbutmentToPageInfinity
    (homOfLE (show 1 ≤ 2 by linarith)) ⟨1, 0⟩ ⟨0, 1⟩ (by aesop) (by aesop) (by aesop)
    (fun k hk => by
      apply E.isZero_pageInfinity_of_isFirstQuadrant
      dsimp [cohomologicalStripes]
      by_contra'
      linarith)
    (fun k hk => by
      apply E.isZero_pageInfinity_of_isFirstQuadrant
      dsimp [cohomologicalStripes]
      by_contra'
      linarith)

lemma EInfinityShortComplexDegreeOne_shortExact :
    (EInfinityShortComplexDegreeOne h).ShortExact := by
  apply (h.stronglyConvergesToInDegree
    1).shortComplexPageInfinityToAbutmentAbutmentToPageInfinity_exact
  intro k _ _
  exfalso
  linarith

@[simps]
noncomputable def shortComplexDegreeOne : ShortComplex C where
  X₁ := E.page 2 hr₀ ⟨1,0⟩
  X₂ := X 1
  X₃ := E.page 3 (by linarith) ⟨0,1⟩
  f := (E.isoPageInfinityOfLE ⟨1,0⟩ 2 (E.rMin_one_zero_le_of_isFirstQuadrant hr₀)).hom ≫
      (EInfinityShortComplexDegreeOne h).f
  g := (EInfinityShortComplexDegreeOne h).g ≫
      (E.isoPageInfinityOfLE ⟨0,1⟩ 3 (E.rMin_zero_one_le_of_isFirstQuadrant (by linarith))).inv
  zero := by simp only [assoc, ShortComplex.zero_assoc, comp_zero, zero_comp]

lemma shortComplexDegreeOne_shortExact : (shortComplexDegreeOne h hr₀).ShortExact := by
  refine' ShortComplex.shortExact_of_iso _ (EInfinityShortComplexDegreeOne_shortExact h)
  refine' ShortComplex.isoMk
    (E.isoPageInfinityOfLE ⟨1,0⟩ 2 (E.rMin_one_zero_le_of_isFirstQuadrant hr₀)).symm (Iso.refl _)
    (E.isoPageInfinityOfLE ⟨0,1⟩ 3 (E.rMin_zero_one_le_of_isFirstQuadrant (by linarith))).symm _ _
  all_goals aesop_cat

end LowDegreesExactSequence

end CohomologicalSpectralSequence
