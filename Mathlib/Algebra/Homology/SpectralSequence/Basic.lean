import Mathlib.Algebra.Homology.ShortComplex.Refinements
import Mathlib.Tactic.Linarith

open CategoryTheory Category Limits ZeroObject

variable (C : Type _) [Category C] [Abelian C] (degrees : ℤ → ℤ × ℤ) (r₀ : ℤ)

structure SpectralSequence where
  page (r : ℤ) (hr : r₀ ≤ r) (pq : ℤ × ℤ) : C
  d (r : ℤ) (hr : r₀ ≤ r) (pq pq' : ℤ × ℤ) (h : pq + degrees r = pq') :
    page r hr pq ⟶ page r hr pq'
  d_comp_d (r : ℤ) (hr : r₀ ≤ r) (pq₁ pq₂ pq₃ : ℤ × ℤ)
    (h₁₂ : pq₁ + degrees r = pq₂) (h₂₃ : pq₂ + degrees r = pq₃) :
      d r hr _ _ h₁₂ ≫ d r hr _ _ h₂₃ = 0
  iso (r r' : ℤ) (hr : r₀ ≤ r) (hr' : r + 1 = r') (pq₁ pq₂ pq₃ : ℤ × ℤ)
    (h₁₂ : pq₁ + degrees r = pq₂) (h₂₃ : pq₂ + degrees r = pq₃) :
      (ShortComplex.mk _ _ (d_comp_d r hr pq₁ pq₂ pq₃ h₁₂ h₂₃)).homology ≅
        page r' (hr.trans (by simp only [← hr', le_add_iff_nonneg_right])) pq₂

abbrev CohomologicalSpectralSequence :=
  SpectralSequence C (fun r => ⟨r, 1-r⟩)

abbrev E₀CohomologicalSpectralSequence :=
  CohomologicalSpectralSequence C 0

abbrev E₁CohomologicalSpectralSequence :=
  CohomologicalSpectralSequence C 1

abbrev E₂CohomologicalSpectralSequence :=
  CohomologicalSpectralSequence C 2

abbrev HomologicalSpectralSequence :=
  SpectralSequence C (fun r => ⟨-r, r-1⟩)

abbrev E₀HomologicalSpectralSequence :=
  HomologicalSpectralSequence C 0

abbrev E₁HomologicalSpectralSequence :=
  HomologicalSpectralSequence C 1

abbrev E₂HomologicalSpectralSequence :=
  HomologicalSpectralSequence C 2

namespace SpectralSequence

variable {C r₀ degrees}
variable (E : SpectralSequence C degrees r₀)

def pageIsoOfEq (r r' : ℤ) (hr : r₀ ≤ r) (hr' : r = r') (pq : ℤ × ℤ) :
    E.page r hr pq ≅ E.page r' (hr.trans (by rw [hr'])) pq :=
  eqToIso (by congr)

class HasInfinityPageAt (pq : ℤ × ℤ) : Prop where
  d_to : ∃ (r' : ℤ) (hr' : r₀ ≤ r'),
    ∀ (r : ℤ) (hr : r' ≤ r) (pq' : ℤ × ℤ) (hpq' : pq' + degrees r = pq),
      E.d r (hr'.trans hr) pq' pq hpq' = 0
  d_from : ∃ (r' : ℤ) (hr' : r₀ ≤ r'),
    ∀ (r : ℤ) (hr : r' ≤ r) (pq' : ℤ × ℤ) (hpq' : pq + degrees r = pq'),
      E.d r (hr'.trans hr) pq pq' hpq' = 0

noncomputable def rmin (pq : ℤ × ℤ) [h : E.HasInfinityPageAt pq] : ℤ :=
  max h.d_to.choose h.d_from.choose

lemma LErmin (pq : ℤ × ℤ) [h : E.HasInfinityPageAt pq] :
    r₀ ≤ E.rmin pq :=
  h.d_to.choose_spec.choose.trans (le_max_left _ _)

lemma d_to_eq_zero (pq : ℤ × ℤ) (r r' : ℤ) [h : E.HasInfinityPageAt pq]
    (hr : E.rmin pq ≤ r) (_ : r + 1 = r') (pq' : ℤ × ℤ)
    (hpq' : pq' + degrees r = pq) :
      E.d r ((E.LErmin pq).trans hr) pq' pq hpq' = 0 :=
  h.d_to.choose_spec.choose_spec r ((le_max_left _ _).trans hr) _ _

lemma d_from_eq_zero (pq : ℤ × ℤ) (r r' : ℤ) [h : E.HasInfinityPageAt pq]
    (hr : E.rmin pq ≤ r) (_ : r + 1 = r') (pq' : ℤ × ℤ)
    (hpq' : pq + degrees r = pq') :
      E.d r ((E.LErmin pq).trans hr) pq pq' hpq' = 0 :=
  h.d_from.choose_spec.choose_spec r ((le_max_right _ _).trans hr) _ _

noncomputable def isoPageSucc (pq : ℤ × ℤ) [E.HasInfinityPageAt pq] (r r' : ℤ)
  (hr : E.rmin pq ≤ r) (hr' : r + 1 = r') :
    E.page r ((E.LErmin pq).trans hr) pq ≅
      E.page r' (((E.LErmin pq).trans hr).trans
        (by simp only [← hr', le_add_iff_nonneg_right])) pq := by
    refine' Iso.symm _ ≪≫ E.iso r r' ((E.LErmin pq).trans hr) hr'
      (pq - degrees r) pq (pq + degrees r) (by simp) rfl
    refine' (ShortComplex.HomologyData.ofZeros _ _ _).left.homologyIso
    . exact E.d_to_eq_zero pq r r' hr hr' _ _
    . exact E.d_from_eq_zero pq r r' hr hr' _ _

noncomputable def isoPageOfAddNat
  (pq : ℤ × ℤ) [E.HasInfinityPageAt pq] (r : ℤ) (hr : E.rmin pq ≤ r) (k : ℕ) :
    E.page r ((E.LErmin pq).trans hr) pq ≅
      E.page (r+k) (((E.LErmin pq).trans hr).trans (by simp)) pq := by
  induction' k with _ e
  . exact E.pageIsoOfEq _ _ _ (by simp) _
  . exact e ≪≫ E.isoPageSucc _ _ _ (hr.trans (by simp))
      (by simp only [Nat.cast_succ, add_assoc])

noncomputable def isoPageOfLE (pq : ℤ × ℤ) [E.HasInfinityPageAt pq]
    (r r' : ℤ) (hr : E.rmin pq ≤ r) (hr' : r ≤ r') :
    E.page r ((E.LErmin pq).trans hr) pq ≅
      E.page r' (((E.LErmin pq).trans hr).trans hr') pq :=
  E.isoPageOfAddNat pq r hr
    (Int.eq_ofNat_of_zero_le (show 0 ≤ r' - r by linarith)).choose ≪≫
      E.pageIsoOfEq _ _ _
        (by linarith [(Int.eq_ofNat_of_zero_le (show 0 ≤ r' - r by linarith)).choose_spec]) _

lemma isoPageOfLE_eq (pq : ℤ × ℤ) [E.HasInfinityPageAt pq]
    (r r' : ℤ) (hr : E.rmin pq ≤ r) (k : ℕ) (hr' : r + k = r') :
    E.isoPageOfLE pq r r' hr
      (by simp only [← hr', le_add_iff_nonneg_right, Nat.cast_nonneg]) =
      E.isoPageOfAddNat pq r hr k ≪≫ E.pageIsoOfEq _ _ _ hr' _ := by
  have : 0 ≤ r' - r := by simp only [← hr', add_sub_cancel', Nat.cast_nonneg]
  obtain rfl : (Int.eq_ofNat_of_zero_le this).choose = k := by
    linarith [(Int.eq_ofNat_of_zero_le this).choose_spec]
  rfl

noncomputable def pageInfinity (pq : ℤ × ℤ) : C := by
  by_cases E.HasInfinityPageAt pq
  . exact E.page (E.rmin pq) (E.LErmin pq) pq
  . exact 0

noncomputable def pageInfinityIso (pq : ℤ × ℤ) [h : E.HasInfinityPageAt pq] :
    E.pageInfinity pq ≅ E.page (E.rmin pq) (E.LErmin pq) pq :=
  eqToIso (by dsimp [pageInfinity] ; rw [dif_pos h])

noncomputable def isoPageInfinityOfLE (pq : ℤ × ℤ) [E.HasInfinityPageAt pq]
    (r : ℤ) (hr : E.rmin pq ≤ r) :
    E.page r ((E.LErmin pq).trans hr) pq ≅ E.pageInfinity pq :=
  Iso.symm (E.pageInfinityIso pq ≪≫ E.isoPageOfLE pq _ _ (by rfl) hr)

end SpectralSequence
