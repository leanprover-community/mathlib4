/-import Mathlib.Algebra.Homology.ShortComplex.Refinements
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Tactic.Linarith

open CategoryTheory Category Limits ZeroObject

lemma Int.eq_add_ofNat_of_le {i j : ℤ} (hij : i ≤ j) :
    ∃ (d : ℕ), j = i + d := by
  have h : 0 ≤ j - i := by linarith
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le h
  exact ⟨d, by linarith⟩

lemma Set.has_min_of_ℤ (S : Set ℤ) (hS : S.Nonempty) (m₀ : ℤ)
    (hm₀ : ∀ (x : ℤ) (_ : x ∈ S), m₀ ≤ x) :
    ∃ (m : ℤ) (_ : m ∈ S), ∀ (x : ℤ) (_ : x ∈ S), m ≤ x := by
  let T : Set ℕ := fun i => m₀ + i ∈ S
  obtain ⟨x, hx⟩ := hS
  obtain ⟨t₀, rfl⟩ := Int.eq_add_ofNat_of_le (hm₀ x hx)
  have hT : T.Nonempty := ⟨t₀, hx⟩
  let μ := (Nat.lt_wfRel.wf).min T hT
  refine' ⟨m₀ + μ, (Nat.lt_wfRel.wf).min_mem T hT, fun y hy => _⟩
  have hy' : 0 ≤ y - m₀ := by linarith [hm₀ y hy]
  obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le hy'
  obtain rfl : y = m₀ + t := by linarith
  simp only [ge_iff_le, add_le_add_iff_left, Nat.cast_le]
  exact (Nat.lt_wfRel.wf).min_le hy _

variable (C : Type _) [Category C] [Abelian C] (degrees : ℤ → ℤ × ℤ) (r₀ : ℤ)

structure SpectralSequence' where
  page' (r : ℤ) (hr : r₀ ≤ r) (pq : ℤ × ℤ) : C
  d' (r : ℤ) (hr : r₀ ≤ r) (pq pq' : ℤ × ℤ) (h : pq + degrees r = pq') :
    page' r hr pq ⟶ page' r hr pq'
  d_comp_d' (r : ℤ) (hr : r₀ ≤ r) (pq₁ pq₂ pq₃ : ℤ × ℤ)
    (h₁₂ : pq₁ + degrees r = pq₂) (h₂₃ : pq₂ + degrees r = pq₃) :
      d' r hr _ _ h₁₂ ≫ d' r hr _ _ h₂₃ = 0
  iso' (r r' : ℤ) (hr : r₀ ≤ r) (hr' : r + 1 = r') (pq₁ pq₂ pq₃ : ℤ × ℤ)
    (h₁₂ : pq₁ + degrees r = pq₂) (h₂₃ : pq₂ + degrees r = pq₃) :
      (ShortComplex.mk _ _ (d_comp_d' r hr pq₁ pq₂ pq₃ h₁₂ h₂₃)).homology ≅
        page' r' (hr.trans (by simp only [← hr', le_add_iff_nonneg_right]; linarith)) pq₂

abbrev CohomologicalSpectralSequence :=
  SpectralSequence' C (fun r => ⟨r, 1-r⟩)

abbrev E₀CohomologicalSpectralSequence :=
  CohomologicalSpectralSequence C 0

abbrev E₁CohomologicalSpectralSequence :=
  CohomologicalSpectralSequence C 1

abbrev E₂CohomologicalSpectralSequence :=
  CohomologicalSpectralSequence C 2

abbrev HomologicalSpectralSequence :=
  SpectralSequence' C (fun r => ⟨-r, r-1⟩)

abbrev E₀HomologicalSpectralSequence :=
  HomologicalSpectralSequence C 0

abbrev E₁HomologicalSpectralSequence :=
  HomologicalSpectralSequence C 1

abbrev E₂HomologicalSpectralSequence :=
  HomologicalSpectralSequence C 2


namespace SpectralSequence'

variable {C r₀ degrees}
variable (E : SpectralSequence' C degrees r₀)

@[pp_dot]
class HasPage (E : SpectralSequence' C degrees r₀) (r : ℤ) : Prop where
  le' : r₀ ≤ r

instance : E.HasPage r₀ where
  le' := by rfl

lemma le_of_hasPage (r : ℤ) [h : E.HasPage r] : r₀ ≤ r :=
  h.le'

lemma hasPage_of_le (r₁ r₂ : ℤ) (h : r₁ ≤ r₂) [E.HasPage r₁] : E.HasPage r₂ where
  le' := (E.le_of_hasPage r₁).trans h

instance (a b : ℤ) [E.HasPage a] : E.HasPage (max a b) :=
  E.hasPage_of_le a (max a b) (le_max_left _ _)

instance (a b : ℤ) [E.HasPage b] : E.HasPage (max a b) :=
  E.hasPage_of_le b (max a b) (le_max_right _ _)

instance [E.HasPage 0] : E.HasPage 1 := E.hasPage_of_le 0 1 (by simp)
instance [E.HasPage 1] : E.HasPage 2 := E.hasPage_of_le 1 2 (by linarith)
instance [E.HasPage 2] : E.HasPage 3 := E.hasPage_of_le 2 3 (by linarith)
instance [E.HasPage 3] : E.HasPage 4 := E.hasPage_of_le 3 4 (by linarith)
instance [E.HasPage 4] : E.HasPage 5 := E.hasPage_of_le 4 5 (by linarith)

@[pp_dot]
def page (r : ℤ) [E.HasPage r] (pq : ℤ × ℤ):= E.page' r (E.le_of_hasPage r) pq

@[pp_dot]
def d (r : ℤ) [E.HasPage r] (pq pq' : ℤ × ℤ) (hpq' : pq + degrees r = pq') :
    E.page r pq ⟶ E.page r pq' :=
  E.d' r (E.le_of_hasPage r) pq pq' hpq'

@[reassoc (attr := simp)]
lemma d_comp_d (r : ℤ) [E.HasPage r] (pq₁ pq₂ pq₃ : ℤ × ℤ)
    (h₁₂ : pq₁ + degrees r = pq₂) (h₂₃ : pq₂ + degrees r = pq₃) :
    E.d r pq₁ pq₂ h₁₂ ≫ E.d r pq₂ pq₃ h₂₃ = 0 := by apply E.d_comp_d'

@[simps]
def shortComplex' (r : ℤ) [E.HasPage r] (pq₁ pq₂ pq₃ : ℤ × ℤ)
    (h₁₂ : pq₁ + degrees r = pq₂) (h₂₃ : pq₂ + degrees r = pq₃) : ShortComplex C :=
  (ShortComplex.mk _ _ (E.d_comp_d r pq₁ pq₂ pq₃ h₁₂ h₂₃))

@[simps!]
def shortComplex'Iso (r : ℤ) [E.HasPage r] (pq₁ pq₂ pq₃ pq₁' pq₂' pq₃' : ℤ × ℤ)
    (h₁₂ : pq₁ + degrees r = pq₂) (h₂₃ : pq₂ + degrees r = pq₃)
    (h₁₂' : pq₁' + degrees r = pq₂') (h₂₃' : pq₂' + degrees r = pq₃')
    (h₂ : pq₂ = pq₂') :
    E.shortComplex' r pq₁ pq₂ pq₃ h₁₂ h₂₃ ≅
      E.shortComplex' r pq₁' pq₂' pq₃' h₁₂' h₂₃' := by
  refine' ShortComplex.isoMk
    (eqToIso (by dsimp ; congr ; rw [← add_left_inj (degrees r), h₁₂, h₁₂', h₂]))
    (eqToIso (by dsimp ; congr)) (eqToIso (by dsimp ; congr ; rw [← h₂₃, ← h₂₃', h₂])) _ _
  · subst h₂
    obtain rfl : pq₁ = pq₁' := by simpa only [add_left_inj] using h₁₂.trans h₁₂'.symm
    dsimp
    rw [id_comp, comp_id]
  · subst h₂
    obtain rfl : pq₃ = pq₃' := h₂₃.symm.trans h₂₃'
    dsimp
    rw [id_comp, comp_id]

@[simps!]
def shortComplex (r : ℤ) [E.HasPage r] (pq : ℤ × ℤ) : ShortComplex C :=
  E.shortComplex' r (pq - degrees r) pq (pq + degrees r) (by simp) (by simp)

@[pp_dot]
def iso (r r' : ℤ) [E.HasPage r] [E.HasPage r'] (hr' : r + 1 = r') (pq : ℤ × ℤ) :
  (E.shortComplex r pq).homology ≅ E.page r' pq :=
  E.iso' r r' (E.le_of_hasPage r) hr' _ pq _ _ _

/-- This means that the differential to an object E_r^{p,q} is zero (both r and (p,q) fixed) -/
class HasEdgeMonoAt (pq : ℤ × ℤ) (r : ℤ) [E.HasPage r] : Prop where
  zero : ∀ (pq' : ℤ × ℤ) (hpq' : pq' + degrees r = pq), E.d r pq' pq hpq' = 0

@[simp]
lemma d_eq_zero_of_hasEdgeMonoAt (r : ℤ) (pq pq' : ℤ × ℤ)
    (hpq' : pq' + degrees r = pq) [E.HasPage r] [E.HasEdgeMonoAt pq r] :
    E.d r pq' pq hpq' = 0 :=
  HasEdgeMonoAt.zero _ _

@[pp_dot]
noncomputable def edgeMonoStep (pq : ℤ × ℤ) (r r' : ℤ) (hr : r + 1 = r')
  [E.HasPage r] [E.HasPage r'] [E.HasEdgeMonoAt pq r] :
  E.page r' pq ⟶ E.page r pq :=
      (E.iso r r' hr pq).inv ≫ (ShortComplex.asIsoHomologyπ  _
          (by apply E.d_eq_zero_of_hasEdgeMonoAt)).inv ≫ ShortComplex.iCycles _

instance (pq : ℤ × ℤ) (r r' : ℤ) (hr : r + 1 = r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeMonoAt pq r] :
    Mono (E.edgeMonoStep pq r r' hr) := by
  dsimp [edgeMonoStep]
  infer_instance

@[reassoc (attr := simp)]
lemma edgeMonoStep_comp_d (pq : ℤ × ℤ) (r r' : ℤ) (hr : r + 1 = r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeMonoAt pq r] (pq' : ℤ × ℤ) (hpq' : pq + degrees r = pq') :
    E.edgeMonoStep pq r r' hr ≫ E.d r pq pq' hpq' = 0 := by
  subst hpq'
  dsimp [edgeMonoStep]
  erw [assoc, assoc, (E.shortComplex r pq).iCycles_g, comp_zero, comp_zero]

@[reassoc (attr := simp)]
lemma iso_hom_comp_edgeMonoStep (pq : ℤ × ℤ) (r r' : ℤ) (hr : r + 1 = r')
  [E.HasPage r] [E.HasPage r'] [E.HasEdgeMonoAt pq r]  :
    (E.iso r r' hr pq).hom ≫ E.edgeMonoStep pq r r' hr =
      (ShortComplex.asIsoHomologyπ  _
        (by apply E.d_eq_zero_of_hasEdgeMonoAt)).inv ≫ ShortComplex.iCycles _ := by
  simp [edgeMonoStep]

@[simps]
noncomputable def edgeMonoStepShortComplex (pq : ℤ × ℤ) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeMonoAt pq r]
    (pq' : ℤ × ℤ) (hpq' : pq + degrees r = pq') : ShortComplex C :=
  ShortComplex.mk _ _ (E.edgeMonoStep_comp_d pq r r' hr pq' hpq')

lemma edgeMonoStepShortComplex_exact (pq : ℤ × ℤ) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeMonoAt pq r]
    (pq' : ℤ × ℤ) (hpq' : pq + degrees r = pq') :
    (E.edgeMonoStepShortComplex pq r r' hr pq' hpq').Exact := by
  subst pq'
  apply ShortComplex.exact_of_f_is_kernel
  refine' IsLimit.ofIsoLimit ((E.shortComplex r pq).cyclesIsKernel) _
  exact Fork.ext ((E.shortComplex r pq).asIsoHomologyπ (by simp) ≪≫
    E.iso r r' hr pq) (by simp)

/-- This means that the differential from an object E_r^{p,q} is zero (both r and (p,q) fixed) -/
class HasEdgeEpiAt (pq : ℤ × ℤ) (r : ℤ) [E.HasPage r] : Prop where
  zero : ∀ (pq' : ℤ × ℤ) (hpq' : pq + degrees r = pq'), E.d r pq pq' hpq' = 0

@[simp]
lemma d_eq_zero_of_hasEdgeEpiAt (r : ℤ) (pq pq' : ℤ × ℤ)
    (hpq' : pq + degrees r = pq') [E.HasPage r] [E.HasEdgeEpiAt pq r] :
    E.d r pq pq' hpq' = 0 :=
  HasEdgeEpiAt.zero _ _

@[pp_dot]
noncomputable def edgeEpiStep (pq : ℤ × ℤ) (r r' : ℤ) (hr : r + 1 = r') [E.HasPage r]
    [E.HasPage r'] [E.HasEdgeEpiAt pq r] :
    E.page r pq ⟶
      E.page r' pq :=
      (E.shortComplex r pq).pOpcycles ≫ (ShortComplex.asIsoHomologyι _
        (by apply E.d_eq_zero_of_hasEdgeEpiAt)).inv ≫ (E.iso r r' hr pq).hom

instance (pq : ℤ × ℤ) (r r' : ℤ) (hr : r + 1 = r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeEpiAt pq r] : Epi (E.edgeEpiStep pq r r' hr) := by
  dsimp [edgeEpiStep]
  apply epi_comp

@[reassoc (attr := simp)]
lemma d_comp_edgeEpiStep (pq : ℤ × ℤ) (r r' : ℤ) (hr : r + 1 = r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeEpiAt pq r] (pq' : ℤ × ℤ) (hpq' : pq' + degrees r = pq) :
    E.d r pq' pq hpq' ≫ E.edgeEpiStep pq r r' hr = 0 := by
  obtain rfl : pq' = pq - degrees r := by rw [← hpq', add_sub_cancel]
  dsimp [edgeEpiStep]
  erw [(E.shortComplex r pq).f_pOpcycles_assoc, zero_comp]

@[simps]
noncomputable def edgeEpiStepShortComplex (pq : ℤ × ℤ) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r']
    [E.HasEdgeEpiAt pq r] (pq' : ℤ × ℤ) (hpq' : pq' + degrees r = pq) : ShortComplex C :=
  ShortComplex.mk _ _ (E.d_comp_edgeEpiStep pq r r' hr pq' hpq')

lemma edgeEpiStepShortComplex_exact (pq : ℤ × ℤ) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeEpiAt pq r]
    (pq' : ℤ × ℤ) (hpq' : pq' + degrees r = pq) :
    (E.edgeEpiStepShortComplex pq r r' hr pq' hpq').Exact := by
  obtain rfl : pq' = pq - degrees r := by aesop
  apply ShortComplex.exact_of_g_is_cokernel
  refine' IsColimit.ofIsoColimit ((E.shortComplex r pq).opcyclesIsCokernel) _
  exact Cofork.ext (((E.shortComplex r pq).asIsoHomologyι (by simp)).symm ≪≫
    E.iso r r' hr pq) rfl

def pageIsoOfEq (r r' : ℤ) [E.HasPage r] [E.HasPage r'] (hr' : r = r') (pq : ℤ × ℤ) :
    E.page r pq ≅ E.page r' pq := eqToIso (by congr)

def hasEdgeMonoSet (pq : ℤ × ℤ) : Set ℤ :=
  fun r => ∀ (r' : ℤ) (_ : r ≤ r'), ∃ (_ : E.HasPage r'), E.HasEdgeMonoAt pq r'

def hasEdgeEpiSet (pq : ℤ × ℤ) : Set ℤ :=
  fun r => ∀ (r' : ℤ) (_ : r ≤ r'), ∃ (_ : E.HasPage r'), E.HasEdgeEpiAt pq r'

class HasInfinityPageAt (pq : ℤ × ℤ) : Prop where
  nonempty_hasEdgeMonoSet': (E.hasEdgeMonoSet pq).Nonempty
  nonempty_hasEdgeEpiSet' : (E.hasEdgeEpiSet pq).Nonempty

section

variable (pq : ℤ × ℤ) [h : E.HasInfinityPageAt pq]

lemma nonempty_hasEdgeMonoSet : (E.hasEdgeMonoSet pq).Nonempty :=
  HasInfinityPageAt.nonempty_hasEdgeMonoSet'
lemma nonempty_hasEdgeEpiSet : (E.hasEdgeEpiSet pq).Nonempty :=
  HasInfinityPageAt.nonempty_hasEdgeEpiSet'

noncomputable def rToMin : ℤ :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeMonoSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le')).choose

lemma rToMin_mem : E.rToMin pq ∈ E.hasEdgeMonoSet pq :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeMonoSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le')).choose_spec.choose

lemma rToMin_le (r : ℤ) (hr : r ∈ E.hasEdgeMonoSet pq) :
    E.rToMin pq ≤ r :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeMonoSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le')).choose_spec.choose_spec r hr

lemma le_rToMin :
    r₀ ≤ E.rToMin pq :=
  ((E.rToMin_mem pq) _ (by rfl)).choose.le'

lemma hasPage_of_rToMin_le (r : ℤ) (hr : E.rToMin pq ≤ r) :
    E.HasPage r :=
  ((E.rToMin_mem pq) r hr).choose

instance : E.HasPage (E.rToMin pq) :=
  E.hasPage_of_rToMin_le pq _ (by rfl)

lemma d_to_eq_zero (r : ℤ) [E.HasPage r] (hr : E.rToMin pq ≤ r) (pq' : ℤ × ℤ)
    (hpq' : pq' + degrees r = pq) :
      E.d r pq' pq hpq' = 0 := by
  have := ((E.rToMin_mem pq) r hr).choose_spec
  rw [d_eq_zero_of_hasEdgeMonoAt]

noncomputable def rFromMin : ℤ :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeEpiSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le')).choose

lemma rFromMin_mem : E.rFromMin pq ∈ E.hasEdgeEpiSet pq :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeEpiSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le')).choose_spec.choose

lemma rFromMin_le (r : ℤ) (hr : r ∈ E.hasEdgeEpiSet pq) :
    E.rFromMin pq ≤ r :=
  (Set.has_min_of_ℤ _ (E.nonempty_hasEdgeEpiSet pq) r₀
    (fun x hx => (hx x (by rfl)).choose.le')).choose_spec.choose_spec r hr

lemma le_rFromMin :
    r₀ ≤ E.rFromMin pq :=
  ((E.rFromMin_mem pq) _ (by rfl)).choose.le'

lemma hasPage_of_rFromMin_le (r : ℤ) (hr : E.rFromMin pq ≤ r) :
    E.HasPage r :=
  ((E.rFromMin_mem pq) r hr).choose

instance : E.HasPage (E.rFromMin pq) :=
  E.hasPage_of_rFromMin_le pq _ (by rfl)

lemma d_from_eq_zero (r : ℤ) [E.HasPage r] (hr : E.rFromMin pq ≤ r) (pq' : ℤ × ℤ)
    (hpq' : pq + degrees r = pq') :
      E.d r pq pq' hpq' = 0 := by
  have := ((E.rFromMin_mem pq) r hr).choose_spec
  rw [d_eq_zero_of_hasEdgeEpiAt]

noncomputable def rMin : ℤ := max (E.rToMin pq) (E.rFromMin pq)

lemma rFromMin_le_rMin : E.rFromMin pq ≤ E.rMin pq := le_max_right _ _

lemma rToMin_le_rMin : E.rToMin pq ≤ E.rMin pq := le_max_left _ _

lemma le_rMin :
    r₀ ≤ E.rMin pq :=
  (E.le_rFromMin pq).trans (E.rFromMin_le_rMin pq)

instance : E.HasPage (E.rMin pq) :=
  E.hasPage_of_rToMin_le pq _ (E.rToMin_le_rMin pq)

noncomputable def isoPageSucc (r r' : ℤ) [E.HasPage r] [E.HasPage r']
  (hr : E.rMin pq ≤ r) (hr' : r + 1 = r') :
    E.page r pq ≅
      E.page r' pq := by
    refine' Iso.symm _ ≪≫ E.iso r r' hr' pq
    refine' (ShortComplex.HomologyData.ofZeros _ _ _).left.homologyIso
    · exact E.d_to_eq_zero pq r ((E.rToMin_le_rMin pq).trans hr) _ _
    · exact E.d_from_eq_zero pq r ((E.rFromMin_le_rMin pq).trans hr) _ _

instance (r : ℤ) [E.HasPage r] (k : ℕ) : E.HasPage (r + k) :=
  E.hasPage_of_le r (r+k) (by simp only [le_add_iff_nonneg_right, Nat.cast_nonneg])

noncomputable def isoPageOfAddNat (r : ℤ) [E.HasPage r] (hr : E.rMin pq ≤ r) (k : ℕ) :
    E.page r pq ≅
      E.page (r+k) pq := by
  induction' k with _ e
  · exact E.pageIsoOfEq _ _ (by simp) _
  · exact e ≪≫ E.isoPageSucc _ _ _ (hr.trans (by simp))
      (by simp only [Nat.cast_succ, add_assoc])

noncomputable def isoPageOfLE'
    (r r' : ℤ) [E.HasPage r] [E.HasPage r'] (hr : E.rMin pq ≤ r) (k : ℕ) (hk : r + k = r') :
    E.page r pq ≅ E.page r' pq :=
  E.isoPageOfAddNat pq r hr k ≪≫ E.pageIsoOfEq _ _ hk _

noncomputable def isoPageOfLE
    (r r' : ℤ) [E.HasPage r] [E.HasPage r'] (hr : E.rMin pq ≤ r) (hr' : r ≤ r') :
    E.page r pq ≅ E.page r' pq :=
  E.isoPageOfLE' pq r r' hr _ (Int.eq_add_ofNat_of_le hr').choose_spec.symm

lemma isoPageOfLE_eq
    (r r' : ℤ) [E.HasPage r] [E.HasPage r'] (hr : E.rMin pq ≤ r) (k : ℕ) (hr' : r + k = r') :
    E.isoPageOfLE pq r r' hr
      (by simp only [← hr', le_add_iff_nonneg_right, Nat.cast_nonneg]) =
    E.isoPageOfLE' pq r r' hr k hr' := by
  dsimp only [isoPageOfLE]
  congr
  linarith [(Int.eq_add_ofNat_of_le (show r ≤ r' by linarith)).choose_spec]

end

@[pp_dot]
noncomputable def pageInfinity (pq : ℤ × ℤ) : C := by
  by_cases E.HasInfinityPageAt pq
  · exact E.page (E.rMin pq) pq
  · exact 0

@[pp_dot]
noncomputable def pageInfinityIso (pq : ℤ × ℤ) [E.HasInfinityPageAt pq] :
    E.pageInfinity pq ≅ E.page (E.rMin pq) pq := eqToIso (dif_pos _)

@[pp_dot]
noncomputable def isoPageInfinityOfLE (pq : ℤ × ℤ) [E.HasInfinityPageAt pq]
    (r : ℤ) (hr : E.rMin pq ≤ r) [E.HasPage r] :
    E.page r pq ≅ E.pageInfinity pq :=
  Iso.symm (E.pageInfinityIso pq ≪≫ E.isoPageOfLE pq _ _ (by rfl) hr)

structure ConvergenceStripes where
  stripe : ℤ × ℤ → ℤ
  position (n i : ℤ) : ℤ × ℤ
  position_stripe (n i : ℤ) : stripe (position n i) = n := by aesop

variable (c : ConvergenceStripes)

lemma ConvergenceStripes.stripe_eq (n i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq) :
    c.stripe pq = n := by
  rw [← hpq, c.position_stripe]

class CollapsesAt (n i : ℤ) where
  condition : ∀ (k : ℤ) (_ : k ≠ i), IsZero (E.pageInfinity (c.position n k))

lemma isZero_of_collapsesAt (n i : ℤ) [h : E.CollapsesAt c n i]
    (k : ℤ) (hk : k ≠ i) : IsZero (E.pageInfinity (c.position n k)) :=
  h.condition k hk

lemma isZero_of_collapsesAt_ofLT (n i : ℤ) [E.CollapsesAt c n i]
    (k : ℤ) (hk : k < i) : IsZero (E.pageInfinity (c.position n k)) :=
  E.isZero_of_collapsesAt c n i k (by linarith)

lemma isZero_of_collapsesAt_ofGT (n i : ℤ) [E.CollapsesAt c n i]
    (k : ℤ) (hk : i < k) : IsZero (E.pageInfinity (c.position n k)) :=
  E.isZero_of_collapsesAt c n i k (by linarith)

structure StronglyConvergesToInDegree (n : ℤ) (X : C) where
  hasInfinityPageAt : ∀ (pq : ℤ × ℤ) (_ : c.stripe pq = n), E.HasInfinityPageAt pq
  filtration' : ℤ ⥤ MonoOver X
  exists_isZero_filtration' :
    ∃ (j : ℤ), IsZero ((filtration' ⋙ MonoOver.forget X ⋙ Over.forget X).obj j)
  exists_isIso_filtration'_hom :
    ∃ (i : ℤ), IsIso ((filtration' ⋙ MonoOver.forget X).obj i).hom
  π' (i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq) :
    (filtration' ⋙ MonoOver.forget X ⋙ Over.forget X).obj i ⟶ E.pageInfinity pq
  epi_π' (i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq) : Epi (π' i pq hpq)
  comp_π' (i j : ℤ) (hij : i + 1 = j) (pq : ℤ × ℤ) (hpq : c.position n j = pq) :
    (filtration' ⋙ MonoOver.forget X ⋙ Over.forget X).map
      (homOfLE (show i ≤ j by linarith)) ≫ π' j pq hpq = 0
  exact' (i j : ℤ) (hij : i + 1 = j) (pq : ℤ × ℤ) (hpq : c.position n j = pq) :
    (ShortComplex.mk _ _ (comp_π' i j hij pq hpq)).Exact

namespace StronglyConvergesToInDegree

variable {E c}
variable {n : ℤ} {X : C} (h : E.StronglyConvergesToInDegree c n X)

def filtration : ℤ ⥤ C := h.filtration' ⋙ MonoOver.forget X ⋙ Over.forget X

def filtrationι (i : ℤ) : h.filtration.obj i ⟶ X :=
  ((h.filtration' ⋙ MonoOver.forget X).obj i).hom

instance (i : ℤ) : Mono (h.filtrationι i) := by
  dsimp [filtrationι]
  infer_instance

lemma exists_isZero_filtration_obj :
    ∃ (j : ℤ), IsZero (h.filtration.obj j) := h.exists_isZero_filtration'

lemma exists_isIso_filtrationι :
    ∃ (i : ℤ), IsIso (h.filtrationι i) := h.exists_isIso_filtration'_hom

@[reassoc (attr := simp)]
lemma filtration_map_ι {i j : ℤ} (φ : i ⟶ j) :
    h.filtration.map φ ≫ h.filtrationι j = h.filtrationι i := by
  simp [filtration, filtrationι]

def π (i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq) :
    h.filtration.obj i ⟶ E.pageInfinity pq := h.π' i pq hpq

instance (i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq) :
    Epi (h.π i pq hpq) := h.epi_π' i pq hpq

lemma comp_π {i j : ℤ} (φ : i ⟶ j) (hij : i < j) (pq : ℤ × ℤ) (hpq : c.position n j = pq) :
    h.filtration.map φ ≫ h.π j pq hpq = 0 := by
  have eq : φ = homOfLE (show i ≤ j-1 by linarith) ≫
    homOfLE (show j-1 ≤ j by linarith) := rfl
  erw [eq, Functor.map_comp, assoc, h.comp_π' (j-1) j (by linarith) pq hpq,
    comp_zero]

instance {i j : ℤ} (f : i ⟶ j) :
    Mono (h.filtration.map f) :=
  mono_of_mono_fac (MonoOver.w (h.filtration'.map f))

lemma shortExact {i j : ℤ} (φ : i ⟶ j) (hij : i + 1 = j) (pq : ℤ × ℤ) (hpq : c.position n j = pq) :
    (ShortComplex.mk _ _
      (h.comp_π φ (by simpa only [← hij] using lt_add_one i) pq hpq)).ShortExact where
  exact := h.exact' i j hij pq hpq

lemma isIso_filtration_map_succ_iff {i j : ℤ} (φ : i ⟶ j) (hij : i + 1 = j) :
    IsIso (h.filtration.map φ) ↔ IsZero (E.pageInfinity (c.position n j)) :=
  (h.shortExact φ hij (c.position n j) rfl).isIso_f_iff

lemma isIso_filtration_map_iff {i j : ℤ} (φ : i ⟶ j) :
    IsIso (h.filtration.map φ) ↔
      ∀ (k : ℤ), i < k → k ≤ j → IsZero (E.pageInfinity (c.position n k)) := by
  let H := fun (d : ℕ) => ∀ {i j : ℤ} (φ : i ⟶ j) (_ : i + d = j),
    IsIso (h.filtration.map φ) ↔
      ∀ (k : ℤ), i < k → k ≤ j → IsZero (E.pageInfinity (c.position n k))
  suffices ∀ (d : ℕ), H d by
    obtain ⟨d, hd⟩ := Int.eq_add_ofNat_of_le (leOfHom φ)
    exact this d φ hd.symm
  intro d
  induction' d with d hd
  · intro i j φ hij
    simp only [Nat.zero_eq, Nat.cast_zero, add_zero] at hij
    subst hij
    obtain rfl : φ = 𝟙 _ := Subsingleton.elim _ _
    constructor
    · intros
      exfalso
      linarith
    · intro
      infer_instance
  · intro i j' φ hij'
    simp only [Nat.cast_succ, ← add_assoc ] at hij'
    subst hij'
    have hij : i ≤ i + d := by linarith
    have hjj' : i + d ≤ i + d + 1 := by linarith
    have fac : h.filtration.map φ = h.filtration.map (homOfLE hij) ≫
      h.filtration.map (homOfLE hjj') := by
        rw [← Functor.map_comp]
        congr
    constructor
    · intro h₁₂
      have : Epi (h.filtration.map φ) := IsIso.epi_of_iso (h.filtration.map φ)
      have := epi_of_epi_fac fac.symm
      have h₁ : IsIso (h.filtration.map (homOfLE hjj')) := isIso_of_mono_of_epi _
      have h₂ := IsIso.of_isIso_fac_right fac.symm
      rw [h.isIso_filtration_map_succ_iff _ rfl] at h₁
      rw [hd _ rfl] at h₂
      intro k hk hk'
      by_cases h : k ≤ i + d
      · exact h₂ _ hk h
      · obtain rfl : k = i + d + 1 := by linarith
        exact h₁
    · intro hij'
      have : IsIso (h.filtration.map (homOfLE hij)) := by
        rw [hd _ rfl]
        intro k hk hk'
        exact hij' _ hk (by linarith)
      have : IsIso (h.filtration.map (homOfLE hjj')) := by
        rw [h.isIso_filtration_map_succ_iff _ rfl]
        exact hij' _ (by linarith) (by linarith)
      rw [fac]
      infer_instance

lemma isZero_filtration_obj_iff_of_le (i j : ℤ) (hij : i ≤ j):
    IsZero (h.filtration.obj j) ↔
      (IsZero (h.filtration.obj i) ∧
        ∀ (k : ℤ), i < k → k ≤ j → IsZero (E.pageInfinity (c.position n k))) := by
  rw [← h.isIso_filtration_map_iff (homOfLE hij)]
  constructor
  · intro hj
    have : IsZero (h.filtration.obj i) := by
      simp only [IsZero.iff_id_eq_zero, ← cancel_mono (h.filtration.map (homOfLE hij))]
      exact hj.eq_of_tgt _ _
    exact ⟨this, ⟨0, this.eq_of_src _ _, hj.eq_of_src _ _⟩⟩
  · rintro ⟨hi, _⟩
    exact IsZero.of_iso hi (asIso (h.filtration.map (homOfLE hij))).symm

lemma isZero_filtration_obj_iff (j : ℤ) :
    IsZero (h.filtration.obj j) ↔
      ∀ (k : ℤ) (_ : k ≤ j), IsZero (E.pageInfinity (c.position n k)) := by
  obtain ⟨i, hi⟩ := h.exists_isZero_filtration_obj
  have : ∀ (k : ℤ) (_ : k ≤ i), IsZero (E.pageInfinity (c.position n k)) := by
    intro k hk
    rw [h.isZero_filtration_obj_iff_of_le (k-1) i (by linarith)] at hi
    exact hi.2 k (by linarith) hk
  by_cases hij : j ≤ i
  · rw [h.isZero_filtration_obj_iff_of_le j i (by linarith)] at hi
    simp only [hi.1, true_iff]
    intro k hk
    exact this _ (by linarith)
  · simp only [not_le] at hij
    simp only [h.isZero_filtration_obj_iff_of_le i j (by linarith), hi, true_and]
    constructor
    · intro H k hk
      by_cases hik : i < k
      · exact H k hik hk
      · simp only [not_lt] at hik
        exact this k hik
    · tauto

lemma isIso_filtrationι_iff_of_le (i j : ℤ) (hij : i ≤ j):
    IsIso (h.filtrationι i) ↔
      (IsIso (h.filtrationι j) ∧
        ∀ (k : ℤ), i < k → k ≤ j → IsZero (E.pageInfinity (c.position n k))) := by
  rw [← h.isIso_filtration_map_iff (homOfLE hij)]
  constructor
  · intro hi
    have fac := (h.filtration_map_ι (homOfLE hij))
    have := epi_of_epi_fac fac
    have : IsIso (h.filtrationι j) := isIso_of_mono_of_epi _
    simp only [this, true_and]
    exact IsIso.of_isIso_fac_right fac
  · rintro ⟨_, _⟩
    rw [← h.filtration_map_ι (homOfLE hij)]
    infer_instance

lemma isIso_filtrationι_iff (j : ℤ) :
    IsIso (h.filtrationι j) ↔
      ∀ (k : ℤ) (_ : j < k), IsZero (E.pageInfinity (c.position n k)) := by
  obtain ⟨i, hi⟩ := h.exists_isIso_filtrationι
  have : ∀ (k : ℤ) (_ : i < k), IsZero (E.pageInfinity (c.position n k)) := by
    intro k hk
    rw [h.isIso_filtrationι_iff_of_le i k (by linarith)] at hi
    exact hi.2 k hk (by rfl)
  by_cases hij : i ≤ j
  · rw [h.isIso_filtrationι_iff_of_le i j (by linarith)] at hi
    simp only [hi.1, true_iff]
    intro k hk
    exact this _ (by linarith)
  · simp only [not_le] at hij
    simp only [h.isIso_filtrationι_iff_of_le j i (by linarith), hi, true_and]
    constructor
    · intro H k hk
      by_cases hik : i < k
      · exact this _ hik
      · simp only [not_lt] at hik
        exact H k hk hik
    · tauto

lemma isIso_π_iff' (j : ℤ) (pq : ℤ × ℤ) (hpq : c.position n j = pq) (i : ℤ) (hij : i + 1 = j) :
    IsIso (h.π j pq hpq) ↔ IsZero (h.filtration.obj i) :=
  (h.shortExact (homOfLE (show i ≤ j by linarith)) hij pq hpq).isIso_g_iff

lemma isIso_π_iff (j : ℤ) (pq : ℤ × ℤ) (hpq : c.position n j = pq) :
    IsIso (h.π j pq hpq) ↔ ∀ (k : ℤ) (_ : k < j), IsZero (E.pageInfinity (c.position n k)) := by
  simp only [h.isIso_π_iff' j pq hpq (j-1) (by linarith), isZero_filtration_obj_iff,
    Int.le_sub_one_iff]

section

variable (j : ℤ) (pq : ℤ × ℤ) (hpq : c.position n j = pq)
    (H : ∀ (k : ℤ) (_ : k < j), IsZero (E.pageInfinity (c.position n k)))

@[simps! inv]
noncomputable def pageInfinityIsoFiltration : E.pageInfinity pq ≅ h.filtration.obj j := by
  have := (h.isIso_π_iff j pq hpq).2 H
  exact (asIso (h.π j pq hpq)).symm

@[reassoc (attr := simp)]
lemma pageInfinityToAbutment_hom_π :
    (h.pageInfinityIsoFiltration j pq hpq H).hom ≫ h.π j pq hpq = 𝟙 _ :=
  (h.pageInfinityIsoFiltration j pq hpq H).hom_inv_id

@[reassoc (attr := simp)]
lemma π_pageInfinityToAbutment_hom :
    h.π j pq hpq ≫ (h.pageInfinityIsoFiltration j pq hpq H).hom = 𝟙 _ :=
  (h.pageInfinityIsoFiltration j pq hpq H).inv_hom_id

noncomputable def pageInfinityToAbutment : E.pageInfinity pq ⟶ X :=
  (h.pageInfinityIsoFiltration j pq hpq H).hom ≫ h.filtrationι j

@[reassoc (attr := simp)]
lemma π_pageInfinityToAbutment :
    h.π j pq hpq ≫ h.pageInfinityToAbutment j pq hpq H = h.filtrationι j :=
  (h.pageInfinityIsoFiltration j pq hpq H).inv_hom_id_assoc _

instance : Mono (h.pageInfinityToAbutment j pq hpq H) := by
  dsimp [pageInfinityToAbutment]
  infer_instance

end

section

variable (i : ℤ) (pq : ℤ × ℤ) (hpq : c.position n i = pq)
    (H : ∀ (k : ℤ) (_ : i < k), IsZero (E.pageInfinity (c.position n k)))

@[simps! hom]
noncomputable def filtrationIsoAbutment : h.filtration.obj i ≅ X := by
  have := (h.isIso_filtrationι_iff i).2 H
  exact asIso (h.filtrationι i)

@[reassoc (attr := simp)]
lemma filtrationIsoAbutment_inv_ι : (h.filtrationIsoAbutment i H).inv ≫ h.filtrationι i = 𝟙 X :=
  (h.filtrationIsoAbutment i H).inv_hom_id

@[reassoc (attr := simp)]
lemma ι_filtrationIsoAbutment_inv : h.filtrationι i ≫ (h.filtrationIsoAbutment i H).inv = 𝟙 _ :=
  (h.filtrationIsoAbutment i H).hom_inv_id

@[reassoc]
lemma ι_filtrationIsoAbutment_inv' (j : ℤ) (hj : j ≤ i) :
    h.filtrationι j ≫ (h.filtrationIsoAbutment i H).inv = h.filtration.map (homOfLE hj) := by
  simp only [← cancel_mono (h.filtrationι i), assoc, filtrationIsoAbutment_inv_ι,
    comp_id, filtration_map_ι]

noncomputable def abutmentToPageInfinity : X ⟶ E.pageInfinity pq :=
  (h.filtrationIsoAbutment i H).inv ≫ h.π i pq hpq

@[reassoc (attr := simp)]
lemma ι_abutmentToPageInfinity :
    h.filtrationι i ≫ h.abutmentToPageInfinity i pq hpq H = h.π i pq hpq :=
  (h.filtrationIsoAbutment i H).hom_inv_id_assoc _

instance : Epi (h.abutmentToPageInfinity i pq hpq H) := by
  dsimp [abutmentToPageInfinity]
  apply epi_comp

end


section

variable (i : ℤ) [E.CollapsesAt c n i] (pq : ℤ × ℤ) (hpq : c.position n i = pq)

@[reassoc (attr := simp)]
lemma pageInfinityToAbutment_abutmentToPageInfinity :
    h.pageInfinityToAbutment i pq hpq (E.isZero_of_collapsesAt_ofLT c n i) ≫
      h.abutmentToPageInfinity i pq hpq ((E.isZero_of_collapsesAt_ofGT c n i)) = 𝟙 _ := by
  simp [pageInfinityToAbutment, abutmentToPageInfinity]

@[reassoc (attr := simp)]
lemma abutmentToPageInfinity_pageInfinityToAbutment :
    h.abutmentToPageInfinity i pq hpq (E.isZero_of_collapsesAt_ofGT c n i) ≫
      h.pageInfinityToAbutment i pq hpq (E.isZero_of_collapsesAt_ofLT c n i) = 𝟙 _ := by
  simp [pageInfinityToAbutment, abutmentToPageInfinity]

noncomputable def pageInfinityIsoAbutment : E.pageInfinity pq ≅ X where
  hom := h.pageInfinityToAbutment i pq hpq (E.isZero_of_collapsesAt_ofLT c n i)
  inv := h.abutmentToPageInfinity i pq hpq (E.isZero_of_collapsesAt_ofGT c n i)

end

section

variable {i j : ℤ} (φ : i ⟶ j) (pqi : ℤ × ℤ) (pqj : ℤ × ℤ)
    (hpqi : c.position n i = pqi) (hpqj : c.position n j = pqj) (hij : i ≠ j)
    (Hi : ∀ (k : ℤ) (_ : k < i), IsZero (E.pageInfinity (c.position n k)))
    (Hj : ∀ (k : ℤ) (_ : j < k), IsZero (E.pageInfinity (c.position n k)))
    (Hij : ∀ (k : ℤ) (_ : i < k) (_ : k < j), IsZero (E.pageInfinity (c.position n k)))

lemma pageInfinityToAbutment_abutmentToPageInfinity_eq_zero :
    h.pageInfinityToAbutment i pqi hpqi Hi ≫
      h.abutmentToPageInfinity j pqj hpqj Hj = 0 := by
  dsimp [pageInfinityToAbutment, abutmentToPageInfinity]
  rw [assoc, Preadditive.IsIso.comp_left_eq_zero,
    ι_filtrationIsoAbutment_inv'_assoc _ _ _ i (leOfHom φ), comp_π]
  by_contra!
  apply hij
  linarith [leOfHom φ]

@[simps]
noncomputable def shortComplexPageInfinityToAbutmentAbutmentToPageInfinity : ShortComplex C :=
  ShortComplex.mk _ _
    (h.pageInfinityToAbutment_abutmentToPageInfinity_eq_zero φ pqi pqj hpqi hpqj hij Hi Hj)

def shortComplexPageInfinityToAbutmentAbutmentToPageInfinity_exact :
    (h.shortComplexPageInfinityToAbutmentAbutmentToPageInfinity φ
      pqi pqj hpqi hpqj hij Hi Hj).ShortExact := by
  have := (h.isIso_π_iff i pqi hpqi).2 Hi
  have := (h.isIso_filtrationι_iff j).2 Hj
  let φ₁ : i ⟶ j-1 := homOfLE (by
    by_contra!
    apply hij
    linarith [leOfHom φ])
  let φ₂ : j-1 ⟶ j := homOfLE (by linarith)
  have : IsIso (h.filtration.map φ₁) := (h.isIso_filtration_map_iff φ₁).2 (by
    intro k hik hkj
    exact Hij k hik (by linarith))
  refine' ShortComplex.shortExact_of_iso _
    ((h.shortExact φ₂ (by linarith) pqj hpqj))
  refine' ShortComplex.isoMk ((asIso (h.filtration.map φ₁)).symm ≪≫ asIso (h.π i pqi hpqi))
    (asIso (h.filtrationι j)) (Iso.refl _) _ _
  all_goals aesop_cat

end

end StronglyConvergesToInDegree

variable (X : ℤ → C)

structure StronglyConvergesTo where
  stronglyConvergesToInDegree (n : ℤ) : E.StronglyConvergesToInDegree c n (X n)

variable (h : E.StronglyConvergesTo c X)

lemma StronglyConvergesTo.hasInfinityPageAt (pq : ℤ × ℤ) :
    E.HasInfinityPageAt pq :=
  (h.stronglyConvergesToInDegree (c.stripe pq)).hasInfinityPageAt pq rfl

end SpectralSequence'

namespace CohomologicalSpectralSequence

variable {C r₀}
variable (E : CohomologicalSpectralSequence C r₀)

def cohomologicalStripes : SpectralSequence'.ConvergenceStripes where
  stripe pq := pq.1 + pq.2
  position n i := ⟨n+1-i, i-1⟩

abbrev CollapsesAt (n i : ℤ) :=
  SpectralSequence'.CollapsesAt E cohomologicalStripes n i

abbrev StronglyConvergesToInDegree (n : ℤ) (X : C) :=
  SpectralSequence'.StronglyConvergesToInDegree E cohomologicalStripes n X

abbrev StronglyConvergesTo (X : ℤ → C) :=
  SpectralSequence'.StronglyConvergesTo E cohomologicalStripes X

class IsFirstQuadrant : Prop :=
  isZero (r : ℤ) [E.HasPage r] (pq : ℤ × ℤ) (hpq : pq.1 < 0 ∨ pq.2 < 0) : IsZero (E.page r pq)

section IsFirstQuadrant

variable [E.IsFirstQuadrant]

lemma isZero_of_isFirstQuadrant (r : ℤ) [E.HasPage r] (pq : ℤ × ℤ)
    (hpq : pq.1 < 0 ∨ pq.2 < 0) : IsZero (E.page r pq) := IsFirstQuadrant.isZero _ _ hpq

lemma hasEdgeMonoAt_of_isFirstQuadrant (pq : ℤ × ℤ) (r : ℤ) [E.HasPage r] (h : pq.1 + 1 ≤ r) :
    E.HasEdgeMonoAt pq r where
  zero := by
    rintro pq' rfl
    refine' IsZero.eq_of_src (isZero_of_isFirstQuadrant _ _ _ (Or.inl _)) _ _
    dsimp at h
    linarith

lemma hasEdgeEpiAt_of_isFirstQuadrant (pq : ℤ × ℤ) (r : ℤ) [E.HasPage r] (h : pq.2 + 2 ≤ r) :
    E.HasEdgeEpiAt pq r where
  zero := by
    rintro pq' rfl
    refine' IsZero.eq_of_tgt (isZero_of_isFirstQuadrant _ _ _ (Or.inr _)) _ _
    dsimp
    linarith

instance (pq : ℤ × ℤ) : E.HasInfinityPageAt pq where
  nonempty_hasEdgeEpiSet' := by
    by_cases h : pq.2 < 0
    · refine' ⟨max r₀ 1, _⟩
      intro r' hr'
      have : E.HasPage r' := E.hasPage_of_le r₀ _ ((le_max_left _ _ ).trans hr')
      exact ⟨this, ⟨fun pq' hpq' =>
        IsZero.eq_of_src (isZero_of_isFirstQuadrant _ _ _ (Or.inr h)) _ _⟩⟩
    · refine' ⟨max r₀ (pq.2 + 2), _⟩
      intro r' hr'
      have : E.HasPage r' := E.hasPage_of_le r₀ _ ((le_max_left _ _ ).trans hr')
      exact ⟨this, E.hasEdgeEpiAt_of_isFirstQuadrant pq r' ((le_max_right _ _).trans hr')⟩
  nonempty_hasEdgeMonoSet' := by
    by_cases h : pq.1 < 0
    · refine' ⟨max r₀ 0, _⟩
      intro r' hr'
      have : E.HasPage r' := E.hasPage_of_le r₀ _ ((le_max_left _ _ ).trans hr')
      refine' ⟨this, ⟨fun pq' hpq' =>
        IsZero.eq_of_tgt (isZero_of_isFirstQuadrant _ _ _ (Or.inl h)) _ _⟩⟩
    · refine' ⟨max r₀ (pq.1 + 1), _⟩
      intro r' hr'
      have : E.HasPage r' := E.hasPage_of_le r₀ _ ((le_max_left _ _ ).trans hr')
      exact ⟨this, E.hasEdgeMonoAt_of_isFirstQuadrant pq r' ((le_max_right _ _).trans hr')⟩

lemma rToMin_le_of_isFirstQuadrant (pq : ℤ × ℤ) :
    E.rToMin pq ≤ max r₀ (pq.1 + 1) :=
  E.rToMin_le _ _ (fun r hr => by
    have : E.HasPage r := E.hasPage_of_le r₀ _ ((le_max_left _ _ ).trans hr)
    refine' ⟨this, _⟩
    apply hasEdgeMonoAt_of_isFirstQuadrant
    exact (le_max_right _ _ ).trans hr)

lemma rFromMin_le_of_isFirstQuadrant (pq : ℤ × ℤ) :
    E.rFromMin pq ≤ max r₀ (pq.2 + 2) :=
  E.rFromMin_le _ _ (fun r hr => by
    have : E.HasPage r := E.hasPage_of_le r₀ _ ((le_max_left _ _ ).trans hr)
    refine' ⟨this, _⟩
    apply hasEdgeEpiAt_of_isFirstQuadrant
    exact (le_max_right _ _ ).trans hr)

lemma rMin_le_of_isFirstQuadrant (pq : ℤ × ℤ) :
    E.rMin pq ≤ max r₀ (max (pq.1 + 1) (pq.2 + 2)) := by
  apply max_le
  · apply (E.rToMin_le_of_isFirstQuadrant pq).trans
    apply max_le
    · apply le_max_left
    · exact (le_max_left _ _).trans (le_max_right _ _)
  · apply (E.rFromMin_le_of_isFirstQuadrant pq).trans
    apply max_le
    · apply le_max_left
    · exact (le_max_right _ _).trans (le_max_right _ _)

lemma isZero_pageInfinity_of_isFirstQuadrant (pq : ℤ × ℤ)
    (hpq : pq.1 < 0 ∨ pq.2 < 0) : IsZero (E.pageInfinity pq) :=
  IsZero.of_iso (E.isZero_of_isFirstQuadrant _ _ hpq)
    (E.isoPageInfinityOfLE pq (E.rMin pq) (by rfl)).symm

end IsFirstQuadrant

end CohomologicalSpectralSequence

-/
