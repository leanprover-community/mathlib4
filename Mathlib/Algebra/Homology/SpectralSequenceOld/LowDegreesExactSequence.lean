/-import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortComplexFour
import Mathlib.Algebra.Homology.ShortComplex.ShortComplexFive

open CategoryTheory Category Limits

namespace CohomologicalSpectralSequence

variable {C : Type _} [Category C] [Abelian C]

variable {r₀ : ℤ} (E : CohomologicalSpectralSequence C r₀) [E.IsFirstQuadrant]

lemma rMin_zero_zero_le_of_isFirstQuadrant [E.HasPage 2] :
    E.rMin ⟨0, 0⟩ ≤ 2 := by
  have := E.le_of_hasPage 2
  exact (E.rMin_le_of_isFirstQuadrant ⟨0, 0⟩).trans (by aesop_cat)

lemma rMin_one_zero_le_of_isFirstQuadrant [E.HasPage 2] :
    E.rMin ⟨1, 0⟩ ≤ 2 := by
  have := E.le_of_hasPage 2
  exact (E.rMin_le_of_isFirstQuadrant _).trans (by aesop_cat)

lemma rMin_two_zero_le_of_isFirstQuadrant [E.HasPage 3] :
    E.rMin ⟨2, 0⟩ ≤ 3 :=
  have := E.le_of_hasPage 3
  (E.rMin_le_of_isFirstQuadrant _).trans (by aesop_cat)

lemma rMin_zero_one_le_of_isFirstQuadrant [E.HasPage 3] :
    E.rMin ⟨0, 1⟩ ≤ 3 :=
  have := E.le_of_hasPage 3
  (E.rMin_le_of_isFirstQuadrant _).trans (by aesop_cat)

instance : E.CollapsesAt 0 1 where
  condition := fun k hk => by
    apply E.isZero_pageInfinity_of_isFirstQuadrant
    dsimp [cohomologicalStripes]
    by_contra!
    apply hk
    linarith

section

variable {E}
variable {H : ℤ → C} (h : E.StronglyConvergesTo H)

lemma hasEdgeMonoAtVerticalLine (p q r : ℤ) [E.HasPage r] (hr : p + 1 ≤ r) :
    E.HasEdgeMonoAt ⟨p, q⟩ r := by
  by_cases h : 0 ≤ q
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le h
    apply hasEdgeMonoAt_of_isFirstQuadrant
    exact hr
  · simp only [not_le] at h
    constructor
    intro pq hpq
    apply IsZero.eq_of_tgt
    apply isZero_of_isFirstQuadrant
    exact Or.inr h

lemma hasEdgeEpiAtHorizontalLine (p q r : ℤ) [E.HasPage r] (hr : q + 2 ≤ r) :
    E.HasEdgeEpiAt ⟨p, q⟩ r := by
  by_cases h : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le h
    apply hasEdgeEpiAt_of_isFirstQuadrant
    dsimp
    exact hr
  · simp only [not_le] at h
    constructor
    intro pq hpq
    apply IsZero.eq_of_src
    apply isZero_of_isFirstQuadrant
    exact Or.inl h

section

variable [E.HasPage 2]

instance (n : ℤ): E.HasEdgeMonoAt ⟨0, n⟩ 2 := E.hasEdgeMonoAtVerticalLine 0 n 2 (by linarith)
instance (n : ℤ): E.HasEdgeMonoAt ⟨1, n⟩ 2 := E.hasEdgeMonoAtVerticalLine 1 n 2 (by linarith)
instance (n : ℤ) : E.HasEdgeEpiAt ⟨n, 0⟩ 2 := E.hasEdgeEpiAtHorizontalLine _ _ 2 (by linarith)

end

namespace LowDegreesExactSequence

noncomputable def E₂ZeroZeroIsoAbutmentZero [E.HasPage 2] : E.page 2 ⟨0, 0⟩ ≅ H 0 :=
  E.isoPageInfinityOfLE ⟨0, 0⟩ 2 E.rMin_zero_zero_le_of_isFirstQuadrant ≪≫
    (h.stronglyConvergesToInDegree 0).pageInfinityIsoAbutment 1 ⟨0, 0⟩ rfl

@[simps!]
noncomputable def EInfinityShortComplexDegreeOne : ShortComplex C :=
  (h.stronglyConvergesToInDegree 1).shortComplexPageInfinityToAbutmentAbutmentToPageInfinity
    (homOfLE (show 1 ≤ 2 by linarith)) ⟨1, 0⟩ ⟨0, 1⟩ (by aesop) (by aesop) (by aesop)
    (fun k hk => by
      apply E.isZero_pageInfinity_of_isFirstQuadrant
      dsimp [cohomologicalStripes]
      by_contra!
      linarith)
    (fun k hk => by
      apply E.isZero_pageInfinity_of_isFirstQuadrant
      dsimp [cohomologicalStripes]
      by_contra!
      linarith)

lemma EInfinityShortComplexDegreeOne_shortExact :
    (EInfinityShortComplexDegreeOne h).ShortExact := by
  apply (h.stronglyConvergesToInDegree
    1).shortComplexPageInfinityToAbutmentAbutmentToPageInfinity_exact
  intro k _ _
  exfalso
  linarith

@[simps X₁ X₂ X₃]
noncomputable def shortComplexDegreeOne [E.HasPage 2] : ShortComplex C where
  X₁ := E.page 2 ⟨1,0⟩
  X₂ := H 1
  X₃ := E.page 3 ⟨0,1⟩
  f := (E.isoPageInfinityOfLE ⟨1,0⟩ 2 E.rMin_one_zero_le_of_isFirstQuadrant).hom ≫
      (EInfinityShortComplexDegreeOne h).f
  g := (EInfinityShortComplexDegreeOne h).g ≫
      (E.isoPageInfinityOfLE ⟨0,1⟩ 3 E.rMin_zero_one_le_of_isFirstQuadrant).inv
  zero := by simp only [assoc, ShortComplex.zero_assoc, comp_zero, zero_comp]

lemma shortComplexDegreeOne_shortExact [E.HasPage 2] : (shortComplexDegreeOne h).ShortExact := by
  refine' ShortComplex.shortExact_of_iso _ (EInfinityShortComplexDegreeOne_shortExact h)
  refine' ShortComplex.isoMk
    (E.isoPageInfinityOfLE ⟨1,0⟩ 2 E.rMin_one_zero_le_of_isFirstQuadrant).symm (Iso.refl _)
    (E.isoPageInfinityOfLE ⟨0,1⟩ 3 E.rMin_zero_one_le_of_isFirstQuadrant).symm _ _
  all_goals dsimp [shortComplexDegreeOne] ; aesop_cat

instance [E.HasPage 2] : Mono (shortComplexDegreeOne h).f :=
  (shortComplexDegreeOne_shortExact h).mono_f

instance [E.HasPage 2] : Epi (shortComplexDegreeOne h).g :=
  (shortComplexDegreeOne_shortExact h).epi_g


variable (E)

@[simps]
noncomputable def shortComplex₄d₂ [E.HasPage 2] : ShortComplex₄ C where
  X₁ := E.page 3 ⟨0, 1⟩
  X₂ := E.page 2 ⟨0, 1⟩
  X₃ := E.page 2 ⟨2, 0⟩
  X₄ := E.page 3 ⟨2, 0⟩
  f := E.edgeMonoStep ⟨0, 1⟩ 2 3 rfl
  g := E.d 2 ⟨0, 1⟩ ⟨2, 0⟩ rfl
  h := E.edgeEpiStep ⟨2,0⟩ 2 3 rfl

lemma shortComplex₄d₂_exact [E.HasPage 2] :
    (LowDegreesExactSequence.shortComplex₄d₂ E).Exact where
  exact₂ := E.edgeMonoStepShortComplex_exact _ _ _ _ _ _
  exact₃ := E.edgeEpiStepShortComplex_exact _ _ _ _ _ _

variable {E}

noncomputable def E₃TwoZeroMonoAbutmentTwo [E.HasPage 3] : E.page 3 ⟨2, 0⟩ ⟶ H 2 :=
    (E.isoPageInfinityOfLE ⟨2, 0⟩ 3 E.rMin_two_zero_le_of_isFirstQuadrant).hom ≫
    (h.stronglyConvergesToInDegree 2).pageInfinityToAbutment 1 ⟨2, 0⟩ rfl
      (fun k hk => by
        apply isZero_pageInfinity_of_isFirstQuadrant
        dsimp [cohomologicalStripes]
        exact Or.inr (by linarith))

instance [E.HasPage 3] : Mono (E₃TwoZeroMonoAbutmentTwo h) := by
  dsimp [E₃TwoZeroMonoAbutmentTwo]
  infer_instance

@[simps!]
noncomputable def shortComplex₄ [E.HasPage 2] : ShortComplex₄ C :=
  ShortComplex₄.connectShortComplex (LowDegreesExactSequence.shortComplexDegreeOne h)
    (shortComplex₄d₂ E).shortComplex₁ (Iso.refl _)
    ((shortComplexDegreeOne h).g ≫ E.edgeMonoStep ⟨0, 1⟩ 2 3 rfl) (by simp)

lemma shortComplex₄_exact [E.HasPage 2] :
    (shortComplex₄ h).Exact := by
  apply ShortComplex₄.connectShortComplex_exact'
  · exact (shortComplexDegreeOne_shortExact h).exact
  · exact (shortComplex₄d₂_exact E).exact₂
  · infer_instance
  · dsimp
    infer_instance

@[simps!]
noncomputable def shortComplex₄' [E.HasPage 2] : ShortComplex₄ C :=
  ShortComplex₄.connectShortComplex (shortComplex₄d₂ E).shortComplex₂
    (ShortComplex.mk _ _ (cokernel.condition
      (LowDegreesExactSequence.E₃TwoZeroMonoAbutmentTwo h))) (Iso.refl _)
    (E.edgeEpiStep ⟨2, 0⟩ 2 3 rfl ≫ LowDegreesExactSequence.E₃TwoZeroMonoAbutmentTwo h) (by simp)

lemma shortComplex₄'_exact [E.HasPage 2] :
    (shortComplex₄' h).Exact := by
  apply ShortComplex₄.connectShortComplex_exact'
  · exact (shortComplex₄d₂_exact E).exact₃
  · exact ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  · dsimp
    infer_instance
  · infer_instance

end LowDegreesExactSequence

variable (E)

noncomputable def lowDegreesShortComplex₅ [E.HasPage 2] : ShortComplex₅ C where
  X₁ := E.page 2 ⟨1, 0⟩
  X₂ := H 1
  X₃ := E.page 2 ⟨0, 1⟩
  X₄ := E.page 2 ⟨2, 0⟩
  X₅ := H 2
  f := (LowDegreesExactSequence.shortComplexDegreeOne h).f
  g := (LowDegreesExactSequence.shortComplexDegreeOne h).g ≫ E.edgeMonoStep ⟨0, 1⟩ 2 3 rfl
  h := E.d 2 ⟨0, 1⟩ ⟨2, 0⟩ rfl
  i := E.edgeEpiStep ⟨2, 0⟩ 2 3 rfl ≫ LowDegreesExactSequence.E₃TwoZeroMonoAbutmentTwo h

instance [E.HasPage 2] : Mono (E.lowDegreesShortComplex₅ h).f := by
  dsimp [lowDegreesShortComplex₅]
  infer_instance

lemma lowDegreesShortComplex₅_exact [E.HasPage 2] :
    (E.lowDegreesShortComplex₅ h).Exact where
  exact₂ := (LowDegreesExactSequence.shortComplex₄_exact h).exact₂
  exact₃ := (LowDegreesExactSequence.shortComplex₄_exact h).exact₃
  exact₄ := (LowDegreesExactSequence.shortComplex₄'_exact h).exact₂

end

end CohomologicalSpectralSequence
-/
