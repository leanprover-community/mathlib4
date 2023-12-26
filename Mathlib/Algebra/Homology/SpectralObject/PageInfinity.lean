import Mathlib.Algebra.Homology.SpectralSequenceNew.LowDegreesExactSequence
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

namespace CategoryTheory

open Category ComposableArrows Limits

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  [∀ r, DecidableRel (c r).Rel]
  (data : SpectralSequenceMkData ι c r₀) [HasSpectralSequence X data]

lemma spectralSequence_page_d_eq_zero_iff_isIso₁
    (r r' : ℤ) (hrr' : r + 1 = r') [(X.spectralSequence data).HasPage r]
    [(X.spectralSequence data).HasPage r']
    (pq' pq'' : κ) (hpq' : (c r).Rel pq' pq'') (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq')
    (i₀' i₀ i₁ i₂ i₃ : ι)
    (hi₀' : i₀' = X.i₀ data r' pq')
    (hi₀ : i₀ = X.i₀ data r pq')
    (hi₁ : i₁ = data.i₁ pq')
    (hi₂ : i₂ = data.i₂ pq')
    (hi₃ : i₃ = X.i₃ data r pq') :
    ((X.spectralSequence data).page r).d pq' pq'' = 0 ↔
      IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
        (fourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (X.le₀'₀ data hrr' pq' hi₀' hi₀)
          (X.le₀₁ data r pq' hi₀ hi₁) (X.le₁₂ data pq' hi₁ hi₂)
          (X.le₂₃ data r pq' hi₂ hi₃))) := by
  let S := ((spectralSequence X data).page r).sc' ((c r).prev  pq') pq' pq''
  let H : S.HomologyData :=
    X.spectralSequenceHomologyData data r r' hrr' _ pq' pq'' rfl ((c r).next_eq' hpq')
      n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀' i₀ i₁ i₂ i₃ _ hi₀' hi₀ hi₁ hi₂ hi₃ rfl
  let e := X.spectralSequencePageXIso data r pq' n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃
  let φ := (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
    (fourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (X.le₀'₀ data hrr' pq' hi₀' hi₀)
      (X.le₀₁ data r pq' hi₀ hi₁) (X.le₁₂ data pq' hi₁ hi₂) (X.le₂₃ data r pq' hi₂ hi₃)))
  have fac : H.left.i = φ ≫ e.inv := rfl
  have eq₁ : IsIso φ ↔ IsIso H.left.i := by
    apply (MorphismProperty.RespectsIso.isomorphisms C).arrow_mk_iso_iff
    refine' Arrow.isoMk (Iso.refl _) e.symm _
    rw [Iso.refl_hom, Arrow.mk_hom, Arrow.mk_hom, fac, Iso.symm_hom]
    apply id_comp
  have eq₂ : IsIso H.left.i ↔ S.g = 0 := by
    constructor
    · intro
      rw [← cancel_epi H.left.i, H.left.wi, comp_zero]
    · exact H.left.isIso_i
  change _ ↔ IsIso φ
  rw [eq₁, eq₂]
  rfl

lemma spectralSequence_page_d_eq_zero_iff_isIso₂
    (r r' : ℤ) (hrr' : r + 1 = r') [(X.spectralSequence data).HasPage r]
    [(X.spectralSequence data).HasPage r']
    (pq pq' : κ) (hpq' : (c r).Rel pq pq') (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq')
    (i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀ : i₀ = X.i₀ data r pq')
    (hi₁ : i₁ = data.i₁ pq')
    (hi₂ : i₂ = data.i₂ pq')
    (hi₃ : i₃ = X.i₃ data r pq')
    (hi₃' : i₃' = X.i₃ data r' pq') :
    ((X.spectralSequence data).page r).d pq pq' = 0 ↔
      IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
        (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃'
          (X.le₀₁ data r pq' hi₀ hi₁) (X.le₁₂ data pq' hi₁ hi₂)
          (X.le₂₃ data r pq' hi₂ hi₃) (X.le₃₃' data hrr' pq' hi₃ hi₃'))) := by
  let S := ((spectralSequence X data).page r).sc' pq pq' ((c r).next pq')
  let H : S.HomologyData := X.spectralSequenceHomologyData data r r' hrr'
    pq pq' _ ((c r).prev_eq' hpq') rfl n₀ n₁ n₂ hn₁ hn₂ hn₁'
    _ i₀ i₁ i₂ i₃ i₃' rfl hi₀ hi₁ hi₂ hi₃ hi₃'
  let e := X.spectralSequencePageXIso data r pq' n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃
  let φ := (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
    (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃' (X.le₀₁ data r pq' hi₀ hi₁) (X.le₁₂ data pq' hi₁ hi₂)
    (X.le₂₃ data r pq' hi₂ hi₃) (X.le₃₃' data hrr' pq' hi₃ hi₃')))
  have fac : H.right.p = e.hom ≫ φ := rfl
  have eq₁ : IsIso H.right.p ↔ IsIso φ := by
    apply (MorphismProperty.RespectsIso.isomorphisms C).arrow_mk_iso_iff
    refine' Arrow.isoMk e (Iso.refl _) _
    rw [Arrow.mk_hom, Arrow.mk_hom, Iso.refl_hom, fac]
    exact (comp_id _).symm
  have eq₂ : IsIso H.right.p ↔ S.f = 0 := by
    constructor
    · intro
      rw [← cancel_mono H.right.p, H.right.wp, zero_comp]
    · exact H.right.isIso_p
  change _ ↔ IsIso φ
  rw [← eq₁, eq₂]
  rfl

lemma spectralSequence_page_d_eq_zero_of_isZero₁
    (r r' : ℤ) (hrr' : r + 1 = r') [(X.spectralSequence data).HasPage r]
    [(X.spectralSequence data).HasPage r']
    (pq' pq'' : κ) (n₂ : ℤ)
    (hn₂ : n₂ = data.deg pq' + 1)
    (i₀' i₀ : ι)
    (hi₀' : i₀' = X.i₀ data r' pq')
    (hi₀ : i₀ = X.i₀ data r pq')
    (h : IsZero ((X.H n₂).obj (mk₁ (homOfLE (X.le₀'₀ data hrr' pq' hi₀' hi₀))))) :
    ((X.spectralSequence data).page r).d pq' pq'' = 0 := by
  by_cases hpq' : (c r).Rel pq' pq''
  · rw [X.spectralSequence_page_d_eq_zero_iff_isIso₁ data r r' hrr' pq' pq'' hpq'
      (data.deg pq' - 1) (data.deg pq') n₂ (by simp) hn₂.symm rfl _ _ _ _ _ hi₀' hi₀ rfl rfl rfl]
    apply X.isIso_EMap_fourδ₁Toδ₀_of_isZero
    exact h
  · exact HomologicalComplex.shape _ _ _ hpq'

lemma spectralSequence_page_d_eq_zero_of_isZero₂
    (r r' : ℤ) (hrr' : r + 1 = r') [(X.spectralSequence data).HasPage r]
    [(X.spectralSequence data).HasPage r']
    (pq pq' : κ) (n₀ : ℤ) (hn₀ : n₀ = data.deg pq' - 1)
    (i₃ i₃' : ι)
    (hi₃ : i₃ = X.i₃ data r pq')
    (hi₃' : i₃' = X.i₃ data r' pq')
    (h : IsZero ((X.H n₀).obj (mk₁ (homOfLE (X.le₃₃' data hrr' pq' hi₃ hi₃'))))) :
    ((X.spectralSequence data).page r).d pq pq' = 0 := by
  by_cases hpq : (c r).Rel pq pq'
  · rw [X.spectralSequence_page_d_eq_zero_iff_isIso₂ data r r' hrr' pq pq' hpq
      n₀ (data.deg pq') _ (by linarith) rfl rfl _ _ _ i₃ i₃' rfl rfl rfl hi₃ hi₃']
    apply X.isIso_EMap_fourδ₄Toδ₃_of_isZero
    exact h
  · exact HomologicalComplex.shape _ _ _ hpq

lemma spectralSequenceHasEdgeEpiAt_iff (pq : κ) (r : ℤ) [(X.spectralSequence data).HasPage r] :
    (X.spectralSequence data).HasEdgeEpiAt pq r ↔
      ∀ (pq' : κ) (_ : (c r).Rel pq pq')
        (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (_ : n₁ = data.deg pq)
        (i₀' i₀ i₁ i₂ i₃ : ι)
        (hi₀' : i₀' = X.i₀ data (r + 1) pq)
        (hi₀ : i₀ = X.i₀ data r pq)
        (hi₁ : i₁ = data.i₁ pq)
        (hi₂ : i₂ = data.i₂ pq)
        (hi₃ : i₃ = X.i₃ data r pq),
          IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
          (fourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (X.le₀'₀ data rfl pq hi₀' hi₀)
            (X.le₀₁ data r pq hi₀ hi₁) (X.le₁₂ data pq hi₁ hi₂)
            (X.le₂₃ data r pq hi₂ hi₃))) := by
  constructor
  · intro h pq' hpq n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃
    rw [← X.spectralSequence_page_d_eq_zero_iff_isIso₁ data r _ rfl pq pq' hpq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃]
    apply (X.spectralSequence data).d_eq_zero_of_hasEdgeEpiAt
  · intro h
    constructor
    intro pq'
    by_cases hpq : (c r).Rel pq pq'
    · rw [X.spectralSequence_page_d_eq_zero_iff_isIso₁ data r _ rfl pq pq' hpq
        (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by simp) rfl rfl _ _ _ _ _
        rfl rfl rfl rfl rfl]
      apply h pq' hpq
      all_goals rfl
    · exact HomologicalComplex.shape _ _ _ hpq

lemma spectralSequenceHasEdgeEpiAt (r r' : ℤ) (hrr' : r + 1 = r')
    [(X.spectralSequence data).HasPage r] [(X.spectralSequence data).HasPage r']
    (pq : κ) (n₂ : ℤ) (hn₂ : n₂ = data.deg pq + 1) (i₀' i₀ : ι)
    (hi₀' : i₀' = X.i₀ data r' pq)
    (hi₀ : i₀ = X.i₀ data r pq)
    (h : IsZero ((X.H n₂).obj (mk₁ (homOfLE (X.le₀'₀ data hrr' pq hi₀' hi₀))))) :
    (X.spectralSequence data).HasEdgeEpiAt pq r where
  zero pq' := X.spectralSequence_page_d_eq_zero_of_isZero₁ data r r' hrr' pq pq' n₂ hn₂
    i₀' i₀ hi₀' hi₀ h

lemma mem_spectralSequence_hasEdgeEpiSet (r : ℤ)
    [(X.spectralSequence data).HasPage r] (pq : κ)
    (n₂ : ℤ) (hn₂ : n₂ = data.deg pq + 1)
    (isZero : ∀ (i j : ι) (hij : i ≤ j)
      (_ : j ≤ X.i₀ data r pq),
      IsZero ((X.H n₂).obj (mk₁ (homOfLE hij)))) :
    r ∈ (X.spectralSequence data).hasEdgeEpiSet pq := by
  intro r' hrr'
  have := (X.spectralSequence data).hasPage_of_LE _ _ hrr'
  refine' ⟨inferInstance,
    X.spectralSequenceHasEdgeEpiAt data r' (r' + 1) rfl pq n₂ hn₂ _ _ rfl rfl _⟩
  apply isZero
  apply data.antitone_i₀
  linarith

lemma spectralSequenceHasEdgeEpiAtFrom (r : ℤ)
    [(X.spectralSequence data).HasPage r] (pq : κ)
    (n₂ : ℤ) (hn₂ : n₂ = data.deg pq + 1)
    [(X.spectralSequence data).HasPageInfinityAt pq]
    (isZero : ∀ (i j : ι) (hij : i ≤ j)
      (_ : j ≤ X.i₀ data r pq),
      IsZero ((X.H n₂).obj (mk₁ (homOfLE hij)))) :
    (X.spectralSequence data).HasEdgeEpiAtFrom pq r where
  le := (X.spectralSequence data).rFromMin_LE pq r
    (X.mem_spectralSequence_hasEdgeEpiSet data r pq n₂ hn₂ isZero)

lemma spectralSequenceHasEdgeMonoAt_iff (pq : κ) (r : ℤ) [(X.spectralSequence data).HasPage r] :
    (X.spectralSequence data).HasEdgeMonoAt pq r ↔
      ∀ (pq' : κ) (_ : (c r).Rel pq' pq)
        (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (_ : n₁ = data.deg pq)
        (i₀ i₁ i₂ i₃ i₃' : ι)
        (hi₀ : i₀ = X.i₀ data r pq)
        (hi₁ : i₁ = data.i₁ pq)
        (hi₂ : i₂ = data.i₂ pq)
        (hi₃ : i₃ = X.i₃ data r pq)
        (hi₃' : i₃' = X.i₃ data (r + 1) pq),
          IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
          (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃'
            (X.le₀₁ data r pq hi₀ hi₁) (X.le₁₂ data pq hi₁ hi₂)
            (X.le₂₃ data r pq hi₂ hi₃) (X.le₃₃' data rfl pq hi₃ hi₃'))) := by
  constructor
  · intro h pq' hpq n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃'
    rw [← X.spectralSequence_page_d_eq_zero_iff_isIso₂ data r _ rfl pq' pq hpq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃']
    apply (X.spectralSequence data).d_eq_zero_of_hasEdgeMonoAt
  · intro h
    constructor
    intro pq'
    by_cases hpq : (c r).Rel pq' pq
    · rw [X.spectralSequence_page_d_eq_zero_iff_isIso₂ data r _ rfl pq' pq hpq
        (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by simp) rfl rfl _ _ _ _ _
        rfl rfl rfl rfl rfl]
      apply h pq' hpq
      all_goals rfl
    · exact HomologicalComplex.shape _ _ _ hpq

/-lemma spectralSequence_edgeMonoStep_eq
    (pq : κ) (r r' : ℤ) (hrr' : r + 1 = r') [(X.spectralSequence data).HasPage r]
    [(X.spectralSequence data).HasPage r']
    [(X.spectralSequence data).HasEdgeMonoAt pq r]
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq)
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀' : i₀' = X.i₀ data r' pq)
    (hi₀ : i₀ = X.i₀ data r pq)
    (hi₁ : i₁ = data.i₁ pq)
    (hi₂ : i₂ = data.i₂ pq)
    (hi₃ : i₃ = X.i₃ data r pq)
    (hi₃' : i₃' = X.i₃ data r' pq) :
    (X.spectralSequence data).edgeMonoStep pq r r' hrr' = sorry :=
  let e₁ := (X.spectralSequencePageXIso data r' pq n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃').hom
  let e₂ := (X.spectralSequencePageXIso data r pq n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃).inv
  sorry-/

lemma spectralSequenceHasEdgeMonoAt (r r' : ℤ) (hrr' : r + 1 = r')
    [(X.spectralSequence data).HasPage r] [(X.spectralSequence data).HasPage r']
    (pq : κ) (n₀ : ℤ) (hn₀ : n₀ = data.deg pq - 1) (i₃ i₃' : ι)
    (hi₃ : i₃ = X.i₃ data r pq)
    (hi₃' : i₃' = X.i₃ data r' pq)
    (h : IsZero ((X.H n₀).obj (mk₁ (homOfLE (X.le₃₃' data hrr' pq hi₃ hi₃'))))) :
    (X.spectralSequence data).HasEdgeMonoAt pq r where
  zero pq' := X.spectralSequence_page_d_eq_zero_of_isZero₂ data r r' hrr' pq' pq n₀ hn₀
    i₃ i₃' hi₃ hi₃' h

lemma mem_spectralSequence_hasEdgeMonoSet (r : ℤ)
    [(X.spectralSequence data).HasPage r] (pq : κ)
    (n₀ : ℤ) (hn₀ : n₀ = data.deg pq - 1)
    (isZero : ∀ (i j : ι) (hij : i ≤ j)
      (_ : X.i₃ data r pq ≤ i),
      IsZero ((X.H n₀).obj (mk₁ (homOfLE hij)))) :
    r ∈ (X.spectralSequence data).hasEdgeMonoSet pq := by
  intro r' hrr'
  have := (X.spectralSequence data).hasPage_of_LE _ _ hrr'
  refine' ⟨inferInstance,
    X.spectralSequenceHasEdgeMonoAt data r' (r' + 1) rfl pq n₀ hn₀ _ _ rfl rfl _⟩
  apply isZero
  apply data.monotone_i₃
  linarith

lemma spectralSequenceHasEdgeMonoAtFrom (r : ℤ)
    [(X.spectralSequence data).HasPage r] (pq : κ)
    (n₀ : ℤ) (hn₀ : n₀ = data.deg pq - 1)
    [(X.spectralSequence data).HasPageInfinityAt pq]
    (isZero : ∀ (i j : ι) (hij : i ≤ j) (_ : X.i₃ data r pq ≤ i),
      IsZero ((X.H n₀).obj (mk₁ (homOfLE hij)))) :
    (X.spectralSequence data).HasEdgeMonoAtFrom pq r where
  le := (X.spectralSequence data).rToMin_LE pq r
    (X.mem_spectralSequence_hasEdgeMonoSet data r pq n₀ hn₀ isZero)

lemma hasPageInfinityAt (r : ℤ) [(X.spectralSequence data).HasPage r] (pq : κ)
    (n₀ n₂ : ℤ) (hn₀ : n₀ = data.deg pq - 1) (hn₂ : n₂ = data.deg pq + 1)
    (isZero₁ : ∀ (i j : ι) (hij : i ≤ j) (_ : j ≤ X.i₀ data r pq),
      IsZero ((X.H n₂).obj (mk₁ (homOfLE hij))))
    (isZero₂ : ∀ (i j : ι) (hij : i ≤ j) (_ : X.i₃ data r pq ≤ i),
      IsZero ((X.H n₀).obj (mk₁ (homOfLE hij)))) :
    (X.spectralSequence data).HasPageInfinityAt pq where
  nonempty_hasEdgeEpiSet := ⟨r, X.mem_spectralSequence_hasEdgeEpiSet data r pq n₂ hn₂ isZero₁⟩
  nonempty_hasEdgeMonoSet := ⟨r, X.mem_spectralSequence_hasEdgeMonoSet data r pq n₀ hn₀ isZero₂⟩

variable [OrderBot ι] [OrderTop ι]

noncomputable def pageInfinity (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (i j : ι) (hij : i ≤ j) : C :=
  X.E n₀ n₁ n₂ hn₁ hn₂ (homOfLE bot_le) (homOfLE hij) (homOfLE le_top)

section

variable (Y : SpectralObject C ℤt) [Y.IsFirstQuadrant]

instance (pq : ℕ × ℕ) : Y.E₂SpectralSequenceNat.HasPageInfinityAt pq := by
  obtain ⟨r, _, _⟩ : ∃ (r : ℤ), pq.1 + 1 ≤ r ∧ pq.2 + 2 ≤ r :=
    ⟨max (pq.1 + 1) (pq.2 + 2), le_max_left _ _, le_max_right _ _⟩
  have : Y.E₂SpectralSequenceNat.HasPage r := Y.E₂SpectralSequenceNat.hasPage_of_LE 2 r
    (by linarith)
  apply Y.hasPageInfinityAt mkDataE₂CohomologicalNat r pq _ _ rfl rfl
  · intro i j hij hj
    apply isZero₁_of_isFirstQuadrant
    refine' hj.trans _
    dsimp
    simp only [ℤt.mk_le_mk_iff]
    linarith
  · intro i j hij hj
    apply isZero₂_of_isFirstQuadrant
    refine' lt_of_lt_of_le _ hj
    dsimp
    simp only [ℤt.mk_lt_mk_iff]
    linarith

end

end SpectralObject

end Abelian

end CategoryTheory
