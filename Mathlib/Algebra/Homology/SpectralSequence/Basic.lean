import Mathlib.Algebra.Homology.ShortComplex.Refinements
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Tactic.Linarith

open CategoryTheory Category Limits ZeroObject

lemma Set.has_min_of_ℤ (S : Set ℤ) (hS : S.Nonempty) (m₀ : ℤ)
    (hm₀ : ∀ (x : ℤ) (_ : x ∈ S), m₀ ≤ x) :
    ∃ (m : ℤ) (_ : m ∈ S), ∀ (x : ℤ) (_ : x ∈ S), m ≤ x := by
  let T : Set ℕ := fun i => m₀ + i ∈ S
  obtain ⟨x, hx⟩ := hS
  have hx' : 0 ≤ x - m₀ := by linarith [hm₀ x hx]
  obtain ⟨t₀, ht₀⟩ := Int.eq_ofNat_of_zero_le hx'
  obtain rfl : x = m₀ + t₀ := by linarith
  have hT : T.Nonempty := ⟨t₀, hx⟩
  let μ := (Nat.lt_wfRel.wf).min T hT
  refine' ⟨m₀ + μ, (Nat.lt_wfRel.wf).min_mem T hT, fun y hy => _⟩
  have hy' : 0 ≤ y - m₀ := by linarith [hm₀ y hy]
  obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le hy'
  obtain rfl : y = m₀ + t := by linarith
  simp only [ge_iff_le, add_le_add_iff_left, Nat.cast_le]
  exact (Nat.lt_wfRel.wf).min_le hy _

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

def toSet (pq : ℤ × ℤ) : Set ℤ := fun r => ∃ (hr : r₀ ≤ r), ∀ (r' : ℤ) (hr' : r ≤ r'),
  (∀ (pq' : ℤ × ℤ) (hpq' : pq' + degrees r' = pq), E.d r' (hr.trans hr') pq' pq hpq' = 0)

def fromSet (pq : ℤ × ℤ) : Set ℤ := fun r => ∃ (hr : r₀ ≤ r), ∀ (r' : ℤ) (hr' : r ≤ r'),
  (∀ (pq' : ℤ × ℤ) (hpq' : pq + degrees r' = pq'), E.d r' (hr.trans hr') pq pq' hpq' = 0)

class HasInfinityPageAt (pq : ℤ × ℤ) : Prop where
  nonemptyToSet' : (E.toSet pq).Nonempty
  nonemptyFromSet' : (E.fromSet pq).Nonempty

section

variable (pq : ℤ × ℤ) [h : E.HasInfinityPageAt pq]

lemma nonemptyToSet : (E.toSet pq).Nonempty := HasInfinityPageAt.nonemptyToSet'
lemma nonemptyFromSet : (E.fromSet pq).Nonempty := HasInfinityPageAt.nonemptyFromSet'

noncomputable def rToMin : ℤ :=
  (Set.has_min_of_ℤ _ (E.nonemptyToSet pq) r₀ (fun _ hx => hx.1)).choose

lemma rToMin_mem : E.rToMin pq ∈ E.toSet pq :=
  (Set.has_min_of_ℤ _ (E.nonemptyToSet pq) r₀ (fun _ hx => hx.1)).choose_spec.choose

lemma rToMin_le (r : ℤ) (hr : r ∈ E.toSet pq) :
    E.rToMin pq ≤ r :=
  (Set.has_min_of_ℤ _ (E.nonemptyToSet pq) r₀ (fun _ hx => hx.1)).choose_spec.choose_spec r hr

lemma le_rToMin :
    r₀ ≤ E.rToMin pq := (E.rToMin_mem pq).1

lemma d_to_eq_zero (r r' : ℤ) (hr : E.rToMin pq ≤ r) (_ : r + 1 = r') (pq' : ℤ × ℤ)
    (hpq' : pq' + degrees r = pq) :
      E.d r ((E.le_rToMin pq).trans hr) pq' pq hpq' = 0 :=
  (E.rToMin_mem pq).2 r hr pq' hpq'

noncomputable def rFromMin : ℤ :=
  (Set.has_min_of_ℤ _ (E.nonemptyFromSet pq) r₀ (fun _ hx => hx.1)).choose

lemma rFromMin_mem : E.rFromMin pq ∈ E.fromSet pq :=
  (Set.has_min_of_ℤ _ (E.nonemptyFromSet pq) r₀ (fun _ hx => hx.1)).choose_spec.choose

lemma rFromMin_le (r : ℤ) (hr : r ∈ E.fromSet pq) :
    E.rFromMin pq ≤ r :=
  (Set.has_min_of_ℤ _ (E.nonemptyFromSet pq) r₀ (fun _ hx => hx.1)).choose_spec.choose_spec r hr

lemma le_rFromMin :
    r₀ ≤ E.rFromMin pq := (E.rFromMin_mem pq).1

lemma d_from_eq_zero (r r' : ℤ) (hr : E.rFromMin pq ≤ r) (_ : r + 1 = r') (pq' : ℤ × ℤ)
    (hpq' : pq + degrees r = pq') :
      E.d r ((E.le_rFromMin pq).trans hr) pq pq' hpq' = 0 :=
  (E.rFromMin_mem pq).2 r hr pq' hpq'

noncomputable def rMin : ℤ := max (E.rToMin pq) (E.rFromMin pq)

lemma rFromMin_le_rMin : E.rFromMin pq ≤ E.rMin pq := le_max_right _ _

lemma rToMin_le_rMin : E.rToMin pq ≤ E.rMin pq := le_max_left _ _

lemma le_rMin :
    r₀ ≤ E.rMin pq :=
  (E.le_rFromMin pq).trans (E.rFromMin_le_rMin pq)

noncomputable def isoPageSucc (r r' : ℤ)
  (hr : E.rMin pq ≤ r) (hr' : r + 1 = r') :
    E.page r ((E.le_rMin pq).trans hr) pq ≅
      E.page r' (((E.le_rMin pq).trans hr).trans
        (by simp only [← hr', le_add_iff_nonneg_right])) pq := by
    refine' Iso.symm _ ≪≫ E.iso r r' ((E.le_rMin pq).trans hr) hr'
      (pq - degrees r) pq (pq + degrees r) (by simp) rfl
    refine' (ShortComplex.HomologyData.ofZeros _ _ _).left.homologyIso
    . exact E.d_to_eq_zero pq r r' ((E.rToMin_le_rMin pq).trans hr) hr' _ _
    . exact E.d_from_eq_zero pq r r' ((E.rFromMin_le_rMin pq).trans hr) hr' _ _

noncomputable def isoPageOfAddNat (r : ℤ) (hr : E.rMin pq ≤ r) (k : ℕ) :
    E.page r ((E.le_rMin pq).trans hr) pq ≅
      E.page (r+k) (((E.le_rMin pq).trans hr).trans (by simp)) pq := by
  induction' k with _ e
  . exact E.pageIsoOfEq _ _ _ (by simp) _
  . exact e ≪≫ E.isoPageSucc _ _ _ (hr.trans (by simp))
      (by simp only [Nat.cast_succ, add_assoc])

noncomputable def isoPageOfLE
    (r r' : ℤ) (hr : E.rMin pq ≤ r) (hr' : r ≤ r') :
    E.page r ((E.le_rMin pq).trans hr) pq ≅
      E.page r' (((E.le_rMin pq).trans hr).trans hr') pq :=
  E.isoPageOfAddNat pq r hr
    (Int.eq_ofNat_of_zero_le (show 0 ≤ r' - r by linarith)).choose ≪≫
      E.pageIsoOfEq _ _ _
        (by linarith [(Int.eq_ofNat_of_zero_le (show 0 ≤ r' - r by linarith)).choose_spec]) _

lemma isoPageOfLE_eq
    (r r' : ℤ) (hr : E.rMin pq ≤ r) (k : ℕ) (hr' : r + k = r') :
    E.isoPageOfLE pq r r' hr
      (by simp only [← hr', le_add_iff_nonneg_right, Nat.cast_nonneg]) =
      E.isoPageOfAddNat pq r hr k ≪≫ E.pageIsoOfEq _ _ _ hr' _ := by
  have : 0 ≤ r' - r := by simp only [← hr', add_sub_cancel', Nat.cast_nonneg]
  obtain rfl : (Int.eq_ofNat_of_zero_le this).choose = k := by
    linarith [(Int.eq_ofNat_of_zero_le this).choose_spec]
  rfl

end

noncomputable def pageInfinity (pq : ℤ × ℤ) : C := by
  by_cases E.HasInfinityPageAt pq
  . exact E.page (E.rMin pq) (E.le_rMin pq) pq
  . exact 0

noncomputable def pageInfinityIso (pq : ℤ × ℤ) [E.HasInfinityPageAt pq] :
    E.pageInfinity pq ≅ E.page (E.rMin pq) (E.le_rMin pq) pq := eqToIso (dif_pos _)

noncomputable def isoPageInfinityOfLE (pq : ℤ × ℤ) [E.HasInfinityPageAt pq]
    (r : ℤ) (hr : E.rMin pq ≤ r) :
    E.page r ((E.le_rMin pq).trans hr) pq ≅ E.pageInfinity pq :=
  Iso.symm (E.pageInfinityIso pq ≪≫ E.isoPageOfLE pq _ _ (by rfl) hr)

structure ConvergenceStripes where
  stripe : ℤ × ℤ → ℤ
  position (n i : ℤ) : ℤ × ℤ
  position_stripe (n i : ℤ) : stripe (position n i) = n

variable (c : ConvergenceStripes)

structure StronglyConvergesToInDegree (n : ℤ) (X : C) where
  hasInfinityPageAt : ∀ (pq : ℤ × ℤ) (_ : c.stripe pq = n), E.HasInfinityPageAt pq
  filtration : ℤ ⥤ MonoOver X
  isZero_filtration :
    ∃ (j : ℤ), ∀ (i : ℤ) (_ : i ≤ j),
      IsZero ((filtration ⋙ MonoOver.forget X ⋙ Over.forget X).obj i)
  isIso_filtration_hom :
    ∃ (i : ℤ), ∀ (j : ℤ) (_ : i ≤ j), IsIso ((filtration ⋙ MonoOver.forget X).obj j).hom
  π (i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq) :
    (filtration ⋙ MonoOver.forget X ⋙ Over.forget X).obj i ⟶ E.pageInfinity pq
  epi_π (i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq) : Epi (π i pq hpq)
  comp_π (i j : ℤ) (hij : i + 1 = j) (pq : ℤ × ℤ) (hpq : c.position n j = pq) :
    (filtration ⋙ MonoOver.forget X ⋙ Over.forget X).map
      (homOfLE (show i ≤ j by linarith)) ≫ π j pq hpq = 0
  exact (i j : ℤ) (hij : i + 1 = j) (pq : ℤ × ℤ) (hpq : c.position n j = pq) :
    (ShortComplex.mk _ _ (comp_π i j hij pq hpq)).Exact

variable (X : ℤ → C)

structure StronglyConvergesTo where
  stronglyConvergesToInDegree (n : ℤ) : E.StronglyConvergesToInDegree c n (X n)

variable (h : E.StronglyConvergesTo c X)

lemma StronglyConvergesTo.hasInfinityPageAt (pq : ℤ × ℤ) :
    E.HasInfinityPageAt pq :=
  (h.stronglyConvergesToInDegree (c.stripe pq)).hasInfinityPageAt pq rfl

end SpectralSequence
