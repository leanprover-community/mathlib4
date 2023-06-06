import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Homology.SpectralSequence.SpectralObject
import Mathlib.Algebra.Homology.SpectralSequence.ZTilde

open CategoryTheory Category Limits

variable {C : Type _} [Category C] [Abelian C]

namespace CategoryTheory

namespace Abelian

namespace SpectralObject

open CohomologicalSpectralSequence

variable (X : SpectralObject C ℤt)

@[simps]
def Bounds.quadrantUR (p q : ℤ) : Bounds ℤt where
  γ₁ _ := ℤt.mk q
  γ₂ n := ℤt.mk (n - p + 1)

abbrev Bounds.firstQuadrant := Bounds.quadrantUR 0 0

noncomputable def toE₂CohomologicalSpectralSequence : E₂CohomologicalSpectralSequence C where
  page' r hr := fun ⟨p, q⟩ =>
    (X.E (p+q-1) (p+q) (p+q+1) (by linarith) (by linarith)).obj
      (ιℤt.mapArrow₃.obj (Arrow₃.mkOfLE (q-r+2) q (q+1) (q+r-1)))
  d' := sorry
  d_comp_d' := sorry
  iso' := sorry

pp_extended_field_notation toE₂CohomologicalSpectralSequence

noncomputable def toE₂CohomologicalSpectralSequencePageIso (r : ℤ)
    [X.toE₂CohomologicalSpectralSequence.HasPage r] (p q : ℤ)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hpq : p + q = n₁) (q₀ q₁ q₂ : ℤ)
    (hq₀ : q₀ + r - 2 = q) (hq₁ : q + 1 = q₁) (hq₂ : q₁ + r - 2 = q₂) :
    X.toE₂CohomologicalSpectralSequence.page r ⟨p, q⟩ ≅
      (X.E n₀ n₁ n₂ hn₁ hn₂).obj (ιℤt.mapArrow₃.obj (by
        have := X.toE₂CohomologicalSpectralSequence.le_of_hasPage r
        exact Arrow₃.mkOfLE q₀ q q₁ q₂)) :=
  eqToIso (by
    obtain rfl : n₀ = p + q - 1 := by linarith
    obtain rfl : n₁ = p + q := by linarith
    obtain rfl : n₂ = p + q + 1 := by linarith
    obtain rfl : q₀ = q-r+2 := by linarith
    obtain rfl : q₁ = q+1 := by linarith
    obtain rfl : q₂ = q+r-1 := by linarith
    rfl)

noncomputable def toE₂CohomologicalSpectralSequenceE₂pageIso
    (p q : ℤ) (n : ℤ) (hn : p + q = n) (q' : ℤ) (hq' : q + 1 = q') :
    X.toE₂CohomologicalSpectralSequence.page 2 ⟨p, q⟩ ≅
      (X.H n).obj (ιℤt.mapArrow.obj (Arrow.mkOfLE q q')) :=
  X.toE₂CohomologicalSpectralSequencePageIso 2 p q (n-1) n (n+1)
    (by linarith) _ hn q q' q' (by linarith) (by linarith) (by linarith) ≪≫
    X.EObjIsoH (n-1) n (n+1) _ rfl _ (by dsimp ; infer_instance) (by dsimp ; infer_instance)

lemma toE₂CohomologicalSpectralSequence_isZero_page
    (r : ℤ) [X.toE₂CohomologicalSpectralSequence.HasPage r] (p₀ q₀ : ℤ)
    [X.IsStationary (Bounds.quadrantUR p₀ q₀)] (pq : ℤ × ℤ) (hpq : pq.1 < p₀ ∨ pq.2 < q₀) :
    IsZero (X.toE₂CohomologicalSpectralSequence.page r pq) := by
  obtain ⟨p, q⟩ := pq
  apply X.isZero_E_of_isZero_H
  dsimp at hpq ⊢
  cases hpq
  . apply X.isZero₂_H (Bounds.quadrantUR p₀ q₀)
    apply homOfLE
    dsimp
    simp
    linarith
  . apply X.isZero₁_H (Bounds.quadrantUR p₀ q₀)
    apply homOfLE
    dsimp
    simp
    linarith

instance [X.IsStationary Bounds.firstQuadrant] :
    X.toE₂CohomologicalSpectralSequence.IsFirstQuadrant where
  isZero := by
    intro r hr pq hpq
    exact X.toE₂CohomologicalSpectralSequence_isZero_page r 0 0 pq hpq

noncomputable def toE₂CohomologicalSpectralSequencePageTwoIso (p q n : ℤ) (h : p + q = n)
    (q' : ℤ) (hq' : q + 1 = q'):
    X.toE₂CohomologicalSpectralSequence.page 2 ⟨p, q⟩ ≅
      (X.H n).obj (Arrow.mk (homOfLE (show ℤt.mk q ≤ ℤt.mk q'
        by simp only [ℤt.mk_le_mk_iff] ; linarith))) := by
  refine' X.toE₂CohomologicalSpectralSequencePageIso 2 p q (n-1) n (n+1)
    (by linarith) (by linarith) h q q' q' (by linarith) hq' (by linarith) ≪≫ _
  refine' X.EObjIsoH (n-1) n (n+1) _ rfl _ _ _
  all_goals dsimp ; infer_instance

noncomputable def toE₂CohomologicalSpectralSequencePageInfinityIso (pq : ℤ × ℤ) (n : ℤ)
    (h : pq.1 + pq.2 = n) (q' : ℤ) (hq' : pq.2 + 1 = q') [X.IsStationary Bounds.firstQuadrant] :
    X.toE₂CohomologicalSpectralSequence.pageInfinity pq ≅
      (ιℤt.mapArrow ⋙ X.EInfty (n-1) n (n+1) (by linarith) rfl).obj (Arrow.mkOfLE pq.2 q') :=
  sorry

noncomputable def toE₂CohomologicalSpectralSequenceStronglyConvergesToOfBoundsFirstQuadrant
    [X.IsStationary Bounds.firstQuadrant] :
  X.toE₂CohomologicalSpectralSequence.StronglyConvergesTo
    (fun n => (X.H n).obj (Arrow.mkOfLE ⊥ ⊤ bot_le)) where
  stronglyConvergesToInDegree n :=
    { hasInfinityPageAt := inferInstance
      filtration' := ιℤt ⋙ X.filtration' n
      exists_isZero_filtration' := sorry
      exists_isIso_filtration'_hom := sorry
      π' := fun i pq hpq => by
        sorry
      epi_π' := sorry
      comp_π' := sorry
      exact' := sorry }


end SpectralObject

end Abelian

end CategoryTheory
