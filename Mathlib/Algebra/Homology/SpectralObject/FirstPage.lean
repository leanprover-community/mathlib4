import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

namespace CategoryTheory

open Category ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  [∀ r, DecidableRel (c r).Rel]
  (data : SpectralSequenceMkData ι c r₀)

namespace SpectralSequenceMkData

class HasFirstPageComputation : Prop where
  hi₀₁ (pq : κ) : data.i₀ r₀ (by rfl) pq = data.i₁ pq
  hi₂₃ (pq : κ) : data.i₂ pq = data.i₃ r₀ (by rfl) pq

instance : mkDataE₂Cohomological.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; congr 1; linarith
  hi₂₃ pq := by dsimp; congr 1; linarith

instance : mkDataE₂CohomologicalNat.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; congr 1; linarith
  hi₂₃ pq := by dsimp; congr 1; linarith

section

variable [data.HasFirstPageComputation]

lemma hi₀₁ (pq : κ) :
    data.i₀ r₀ (by rfl) pq = data.i₁ pq := by
  apply HasFirstPageComputation.hi₀₁

lemma hi₂₃ (pq : κ) :
    data.i₂ pq = data.i₃ r₀ (by rfl) pq := by
  apply HasFirstPageComputation.hi₂₃

end

end SpectralSequenceMkData

variable [data.HasFirstPageComputation] [X.HasSpectralSequence data]

noncomputable def spectralSequenceFirstPageXIso (pq : κ) (n : ℤ) (hn : n = data.deg pq)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq) :
    ((X.spectralSequence data).page r₀).X pq ≅ (X.H n).obj (mk₁ (homOfLE' i₁ i₂
      (by simpa only [hi₁, hi₂] using data.le₁₂ pq))) :=
  X.spectralSequencePageXIso data r₀ _ _ _ _ _ _ hn _ _ _ _
    (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) ≪≫
    X.EIsoH (n - 1) n (n + 1) (by simp) rfl (homOfLE _)

lemma spectralSequenceFirstPageXIso_hom (pq : κ) (n : ℤ) (hn : n = data.deg pq)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₂ : ℤ) (hn₀ : n₀ + 1 = n) (hn₂ : n + 1 = n₂) :
    (X.spectralSequenceFirstPageXIso data pq n hn i₁ i₂ hi₁ hi₂).hom =
      (X.spectralSequencePageXIso data r₀ _ _ _ _ _ _ hn _ _ _ _
        (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃])).hom ≫
        (X.EIsoH n₀ n n₂ hn₀ hn₂ _).hom := by
  obtain rfl : n₀ = n - 1 := by linarith
  obtain rfl := hn₂
  rfl

lemma spectralSequenceFirstPageXIso_inv (pq : κ) (n : ℤ) (hn : n = data.deg pq)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₂ : ℤ) (hn₀ : n₀ + 1 = n) (hn₂ : n + 1 = n₂) :
    (X.spectralSequenceFirstPageXIso data pq n hn i₁ i₂ hi₁ hi₂).inv =
      (X.EIsoH n₀ n n₂ hn₀ hn₂ _).inv ≫
      (X.spectralSequencePageXIso data r₀ _ _ _ _ _ _ hn _ _ _ _
        (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃])).inv := by
  obtain rfl : n₀ = n - 1 := by linarith
  obtain rfl := hn₂
  rfl

lemma spectralSequence_first_page_eq (pq pq' : κ)
    (hpq : (c r₀).Rel pq pq') (n n' : ℤ) (hn : n = data.deg pq)
    (hn' : n + 1 = n') (i j k : ι)
    (hi : i = data.i₁ pq') (hj : j = data.i₁ pq) (hk : k = data.i₂ pq) :
    ((X.spectralSequence data).page r₀).d pq pq' =
      (X.spectralSequenceFirstPageXIso data pq n hn j k hj hk).hom ≫ X.δ n n' hn' (homOfLE' i j
        (by simpa only [hi, hj, data.hc₁₃ r₀ (by rfl) pq pq' hpq, ← data.hi₂₃ pq']
          using data.le₁₂ pq'))
        (homOfLE' j k (by simpa only [hj, hk] using data.le₁₂ pq)) ≫
      (X.spectralSequenceFirstPageXIso data pq' n'
        (by rw [← hn', hn, data.hc r₀ (by rfl) pq pq' hpq]) i j hi
        (by rw [hj, ← data.hc₀₂ r₀ (by rfl) pq pq' hpq, data.hi₀₁ pq])).inv := by
  dsimp
  simp only [assoc, X.spectralSequenceFirstPageXIso_hom data pq n hn
    j k hj hk (n - 1) n' (by simp) hn',
    ← X.d_EIsoH_hom_assoc (n - 1) n n' (n' + 1) (by simp) hn' rfl,
    X.spectralSequenceFirstPageXIso_inv data pq' n'
      (by rw [← hn', hn, data.hc r₀ (by rfl) pq pq' hpq]) i j hi
      (by rw [hj, data.hi₂₃, data.hc₁₃ r₀ (by rfl) pq pq' hpq]) n (n' + 1) hn' rfl,
    Iso.hom_inv_id_assoc]
  apply spectralSequence_page_d_eq
  exact hpq

end SpectralObject

end Abelian

end CategoryTheory
