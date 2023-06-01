import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Homology.SpectralSequence.SpectralObject
import Mathlib.Algebra.Homology.SpectralSequence.ZTilde

open CategoryTheory Category Limits

variable {C : Type _} [Category C] [Abelian C]

namespace CategoryTheory

namespace Abelian

namespace SpectralObject

variable (X : SpectralObject C ℤt)

@[simps]
def Bounds.quadrantUR (p q : ℤ) : Bounds ℤt where
  γ₁ _ := ℤt.mk q
  γ₂ n := ℤt.mk (n - p + 1)

abbrev Bounds.firstQuadrant := Bounds.quadrantUR 0 0

/-noncomputable def toE₂CohomologicalSpectralSequence : CohomologicalSpectralSequence C 2 where
  page r hr := fun ⟨p, q⟩ =>
    (X.E (p+q-1) (p+q) (p+q+1) (by linarith) (by linarith)).obj
      (ιℤt.mapArrow₃.obj (Arrow₃.mkOfLE (q-r+2) q (q+1) (q+r-1)))
  d := sorry
  d_comp_d := sorry
  iso := sorry

noncomputable def toE₂CohomologicalSpectralSequencePageIso (r : ℤ) (hr : 2 ≤ r) (p q : ℤ)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hpq : p + q = n₁) (q₀ q₁ q₂ : ℤ)
    (hq₀ : q₀ + r - 2 = q) (hq₁ : q + 1 = q₁) (hq₂ : q₁ + r - 2 = q₂) :
    X.toE₂CohomologicalSpectralSequence.page r hr ⟨p, q⟩ ≅
      (X.E n₀ n₁ n₂ hn₁ hn₂).obj (ιℤt.mapArrow₃.obj (Arrow₃.mkOfLE q₀ q q₁ q₂)) :=
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
    X.toE₂CohomologicalSpectralSequence.page 2 (le_refl 2) ⟨p, q⟩ ≅
      (X.H n).obj (Arrow.mk (ιℤt.map (homOfLE
        (show q ≤ q' by simp only [← hq', le_add_iff_nonneg_right])))) :=
  X.toE₂CohomologicalSpectralSequencePageIso 2 _ p q (n-1) n (n+1)
    (by linarith) _ hn q q' q' (by linarith) (by linarith) (by linarith) ≪≫
    X.EObjIsoH (n-1) n (n+1) _ rfl _ (by dsimp ; infer_instance) (by dsimp ; infer_instance)

lemma toE₂CohomologicalSpectralSequence_isZero_page (r : ℤ) (hr : 2 ≤ r) (p₀ q₀ : ℤ)
    [X.IsStationary (Bounds.quadrantUR p₀ q₀)] (pq : ℤ × ℤ) (hpq : pq.1 < p₀ ∨ pq.2 < q₀) :
    IsZero (X.toE₂CohomologicalSpectralSequence.page r hr pq) := by
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

instance [X.IsStationary (Bounds.firstQuadrant)] :
    X.toE₂CohomologicalSpectralSequence.IsFirstQuadrant where
  isZero := by
    intro r hr pq hpq
    exact X.toE₂CohomologicalSpectralSequence_isZero_page r hr 0 0 pq hpq-/

end SpectralObject

end Abelian

end CategoryTheory
