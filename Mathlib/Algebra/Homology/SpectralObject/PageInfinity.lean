/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.LowDegreesExactSequence
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The infinity page

-/

@[expose] public section

namespace CategoryTheory

open Category ComposableArrows Limits

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  --[∀ r, DecidableRel (c r).Rel]
  (data : SpectralSequenceMkData ι c r₀) [HasSpectralSequence X data]

lemma spectralSequence_page_d_eq_zero_iff_isIso₁
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
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
        (fourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (X.le₀'₀ data hrr' hr pq' hi₀' hi₀)
          (X.le₀₁ data r hr pq' hi₀ hi₁) (X.le₁₂ data pq' hi₁ hi₂)
          (X.le₂₃ data r hr pq' hi₂ hi₃))) := by
  let S := ((spectralSequence X data).page r).sc' ((c r).prev  pq') pq' pq''
  let H : S.HomologyData :=
    X.spectralSequenceHomologyData data r r' hrr' hr _ pq' pq'' rfl ((c r).next_eq' hpq')
      n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀' i₀ i₁ i₂ i₃ _ hi₀' hi₀ hi₁ hi₂ hi₃ rfl
  let e := X.spectralSequencePageXIso data r hr pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃
  let φ := (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
    (fourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (X.le₀'₀ data hrr' hr pq' hi₀' hi₀)
      (X.le₀₁ data r hr pq' hi₀ hi₁) (X.le₁₂ data pq' hi₁ hi₂) (X.le₂₃ data r hr pq' hi₂ hi₃)))
  have fac : H.left.i = φ ≫ e.inv := rfl
  have eq₁ : IsIso φ ↔ IsIso H.left.i := by
    apply (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    refine Arrow.isoMk (Iso.refl _) e.symm ?_
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
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
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
          (X.le₀₁ data r hr pq' hi₀ hi₁) (X.le₁₂ data pq' hi₁ hi₂)
          (X.le₂₃ data r hr pq' hi₂ hi₃) (X.le₃₃' data hrr' hr pq' hi₃ hi₃'))) := by
  let S := ((spectralSequence X data).page r).sc' pq pq' ((c r).next pq')
  let H : S.HomologyData := X.spectralSequenceHomologyData data r r' hrr' hr
    pq pq' _ ((c r).prev_eq' hpq') rfl n₀ n₁ n₂ hn₁ hn₂ hn₁'
    _ i₀ i₁ i₂ i₃ i₃' rfl hi₀ hi₁ hi₂ hi₃ hi₃'
  let e := X.spectralSequencePageXIso data r hr pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃
  let φ := (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
    (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃' (X.le₀₁ data r hr pq' hi₀ hi₁) (X.le₁₂ data pq' hi₁ hi₂)
    (X.le₂₃ data r hr pq' hi₂ hi₃) (X.le₃₃' data hrr' hr pq' hi₃ hi₃')))
  have fac : H.right.p = e.hom ≫ φ := rfl
  have eq₁ : IsIso H.right.p ↔ IsIso φ := by
    apply (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    refine Arrow.isoMk e (Iso.refl _) ?_
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
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq' pq'' : κ) (n₂ : ℤ)
    (hn₂ : n₂ = data.deg pq' + 1)
    (i₀' i₀ : ι)
    (hi₀' : i₀' = X.i₀ data r' pq')
    (hi₀ : i₀ = X.i₀ data r pq')
    (h : IsZero ((X.H n₂).obj (mk₁ (homOfLE (X.le₀'₀ data hrr' hr pq' hi₀' hi₀))))) :
    ((X.spectralSequence data).page r).d pq' pq'' = 0 := by
  by_cases hpq' : (c r).Rel pq' pq''
  · rw [X.spectralSequence_page_d_eq_zero_iff_isIso₁ data r r' hrr' hr pq' pq'' hpq'
      (data.deg pq' - 1) (data.deg pq') n₂ (by simp) hn₂.symm rfl _ _ _ _ _ hi₀' hi₀ rfl rfl rfl]
    apply X.isIso_EMap_fourδ₁Toδ₀_of_isZero
    exact h
  · exact HomologicalComplex.shape _ _ _ hpq'

lemma spectralSequence_page_d_eq_zero_of_isZero₂
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq pq' : κ) (n₀ : ℤ) (hn₀ : n₀ = data.deg pq' - 1)
    (i₃ i₃' : ι)
    (hi₃ : i₃ = X.i₃ data r pq')
    (hi₃' : i₃' = X.i₃ data r' pq')
    (h : IsZero ((X.H n₀).obj (mk₁ (homOfLE (X.le₃₃' data hrr' hr pq' hi₃ hi₃'))))) :
    ((X.spectralSequence data).page r).d pq pq' = 0 := by
  by_cases hpq : (c r).Rel pq pq'
  · rw [X.spectralSequence_page_d_eq_zero_iff_isIso₂ data r r' hrr' hr pq pq' hpq
      n₀ (data.deg pq') _ (by lia) rfl rfl _ _ _ i₃ i₃' rfl rfl rfl hi₃ hi₃']
    apply X.isIso_EMap_fourδ₄Toδ₃_of_isZero
    exact h
  · exact HomologicalComplex.shape _ _ _ hpq

lemma spectralSequenceHasEdgeEpiAt_iff (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
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
          (fourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (X.le₀'₀ data rfl hr pq hi₀' hi₀)
            (X.le₀₁ data r hr pq hi₀ hi₁) (X.le₁₂ data pq hi₁ hi₂)
            (X.le₂₃ data r hr pq hi₂ hi₃))) := by
  constructor
  · intro h pq' hpq n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃
    rw [← X.spectralSequence_page_d_eq_zero_iff_isIso₁ data r _ rfl hr pq pq' hpq
      n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃]
    apply (X.spectralSequence data).d_eq_zero_of_hasEdgeEpiAt
  · intro h
    refine ⟨hr, fun pq' ↦ ?_⟩
    by_cases hpq : (c r).Rel pq pq'
    · rw [X.spectralSequence_page_d_eq_zero_iff_isIso₁ data r _ rfl hr pq pq' hpq
        (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by simp) rfl rfl _ _ _ _ _
        rfl rfl rfl rfl rfl]
      apply h pq' hpq
      all_goals rfl
    · exact HomologicalComplex.shape _ _ _ hpq

lemma spectralSequenceHasEdgeEpiAt (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (n₂ : ℤ) (hn₂ : n₂ = data.deg pq + 1) (i₀' i₀ : ι)
    (hi₀' : i₀' = X.i₀ data r' pq)
    (hi₀ : i₀ = X.i₀ data r pq)
    (h : IsZero ((X.H n₂).obj (mk₁ (homOfLE (X.le₀'₀ data hrr' hr pq hi₀' hi₀))))) :
    (X.spectralSequence data).HasEdgeEpiAt pq r where
  zero pq' := X.spectralSequence_page_d_eq_zero_of_isZero₁ data r r' hrr' hr pq pq' n₂ hn₂
    i₀' i₀ hi₀' hi₀ h

lemma mem_spectralSequence_hasEdgeEpiSet (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (n₂ : ℤ) (hn₂ : n₂ = data.deg pq + 1)
    (isZero : ∀ (i j : ι) (hij : i ≤ j)
      (_ : j ≤ X.i₀ data r pq),
      IsZero ((X.H n₂).obj (mk₁ (homOfLE hij)))) :
    r ∈ (X.spectralSequence data).hasEdgeEpiSet pq := by
  refine ⟨hr, fun r' hrr' ↦ X.spectralSequenceHasEdgeEpiAt data r' (r' + 1) rfl
    (by lia) pq n₂ hn₂ _ _ rfl rfl ?_⟩
  apply isZero
  apply data.antitone_i₀
  lia

lemma spectralSequenceHasEdgeEpiAtFrom (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (n₂ : ℤ) (hn₂ : n₂ = data.deg pq + 1)
    [(X.spectralSequence data).HasPageInfinityAt pq]
    (isZero : ∀ (i j : ι) (hij : i ≤ j)
      (_ : j ≤ X.i₀ data r pq),
      IsZero ((X.H n₂).obj (mk₁ (homOfLE hij)))) :
    (X.spectralSequence data).HasEdgeEpiAtFrom pq r where
  le := (X.spectralSequence data).rFromMin_LE pq r
    (X.mem_spectralSequence_hasEdgeEpiSet data r hr pq n₂ hn₂ isZero)

lemma spectralSequenceHasEdgeMonoAt_iff (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
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
            (X.le₀₁ data r hr pq hi₀ hi₁) (X.le₁₂ data pq hi₁ hi₂)
            (X.le₂₃ data r hr pq hi₂ hi₃) (X.le₃₃' data rfl hr pq hi₃ hi₃'))) := by
  constructor
  · intro h pq' hpq n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃'
    rw [← X.spectralSequence_page_d_eq_zero_iff_isIso₂ data r _ rfl hr pq' pq hpq
      n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃']
    apply (X.spectralSequence data).d_eq_zero_of_hasEdgeMonoAt
  · intro h
    refine ⟨hr, fun pq' ↦ ?_⟩
    by_cases hpq : (c r).Rel pq' pq
    · rw [X.spectralSequence_page_d_eq_zero_iff_isIso₂ data r _ rfl hr pq' pq hpq
        (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by simp) rfl rfl _ _ _ _ _
        rfl rfl rfl rfl rfl]
      apply h pq' hpq
      all_goals rfl
    · exact HomologicalComplex.shape _ _ _ hpq

lemma spectralSequenceHasEdgeMonoAt (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (n₀ : ℤ) (hn₀ : n₀ = data.deg pq - 1) (i₃ i₃' : ι)
    (hi₃ : i₃ = X.i₃ data r pq)
    (hi₃' : i₃' = X.i₃ data r' pq)
    (h : IsZero ((X.H n₀).obj (mk₁ (homOfLE (X.le₃₃' data hrr' hr pq hi₃ hi₃'))))) :
    (X.spectralSequence data).HasEdgeMonoAt pq r where
  zero pq' := X.spectralSequence_page_d_eq_zero_of_isZero₂ data r r' hrr' hr pq' pq n₀ hn₀
    i₃ i₃' hi₃ hi₃' h

lemma mem_spectralSequence_hasEdgeMonoSet (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (n₀ : ℤ) (hn₀ : n₀ = data.deg pq - 1)
    (isZero : ∀ (i j : ι) (hij : i ≤ j)
      (_ : X.i₃ data r pq ≤ i),
      IsZero ((X.H n₀).obj (mk₁ (homOfLE hij)))) :
    r ∈ (X.spectralSequence data).hasEdgeMonoSet pq := by
  refine ⟨hr, fun r' hrr' ↦
    X.spectralSequenceHasEdgeMonoAt data r' (r' + 1) rfl (by lia) pq n₀ hn₀ _ _ rfl rfl ?_⟩
  --have := (X.spectralSequence data).hasPage_of_LE _ _ hrr'
  apply isZero
  apply data.monotone_i₃
  lia

lemma spectralSequenceHasEdgeMonoAtFrom (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (n₀ : ℤ) (hn₀ : n₀ = data.deg pq - 1)
    [(X.spectralSequence data).HasPageInfinityAt pq]
    (isZero : ∀ (i j : ι) (hij : i ≤ j) (_ : X.i₃ data r pq ≤ i),
      IsZero ((X.H n₀).obj (mk₁ (homOfLE hij)))) :
    (X.spectralSequence data).HasEdgeMonoAtFrom pq r where
  le := (X.spectralSequence data).rToMin_LE pq r
    (X.mem_spectralSequence_hasEdgeMonoSet data r hr pq n₀ hn₀ isZero)

@[reassoc]
lemma spectralSequence_edgeMonoStep_compatibility
    (pq : κ) (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    [(X.spectralSequence data).HasEdgeMonoAt pq r]
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq)
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀' : i₀' = X.i₀ data r' pq)
    (hi₀ : i₀ = X.i₀ data r pq)
    (hi₁ : i₁ = data.i₁ pq)
    (hi₂ : i₂ = data.i₂ pq)
    (hi₃ : i₃ = X.i₃ data r pq)
    (hi₃' : i₃' = X.i₃ data r' pq) :
    X.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀' i₁ i₂ i₃ i₃' _ _
      (X.le₂₃ data r hr pq hi₂ hi₃) (X.le₃₃' data hrr' hr pq hi₃ hi₃') ≫
    (X.spectralSequencePageXIso data r' (by lia) pq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃').inv ≫
    (X.spectralSequence data).edgeMonoStep pq r r' hrr' =
      X.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀' i₀ i₁ i₂ i₃ (X.le₀'₀ data hrr' hr pq hi₀' hi₀) _ _ _ ≫
    ((X.spectralSequencePageXIso data r hr pq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃)).inv := by
  let H := X.spectralSequenceHomologyData data r r' hrr' hr _ pq _ rfl rfl n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'
  refine Eq.trans ?_
    ((X.spectralSequence data).leftHomologyData_π_edgeMonoStep_compatibility r r' _
      pq _ rfl rfl H.left)
  congr 1
  dsimp [SpectralSequence.edgeMonoStep]
  simp only [homOfLE_leOfHom, Iso.hom_inv_id_assoc]
  obtain rfl : n₀ = n₁ - 1 := by lia
  subst hn₁' hn₂ hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'
  rw [HomologicalComplex.homologyIsoSc'_eq_rfl]
  dsimp [spectralSequencePageXIso, SpectralSequence.pageXIso]
  erw [id_comp, id_comp]
  simp only [← assoc]
  congr 2
  apply id_comp

@[reassoc]
lemma spectralSequence_edgeEpiStep_compatibility
    (pq : κ) (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    [(X.spectralSequence data).HasEdgeEpiAt pq r]
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq)
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀' : i₀' = X.i₀ data r' pq)
    (hi₀ : i₀ = X.i₀ data r pq)
    (hi₁ : i₁ = data.i₁ pq)
    (hi₂ : i₂ = data.i₂ pq)
    (hi₃ : i₃ = X.i₃ data r pq)
    (hi₃' : i₃' = X.i₃ data r' pq) :
    (X.spectralSequence data).edgeEpiStep pq r r' hrr' ≫
    (X.spectralSequencePageXIso data r' (by lia) pq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃').hom ≫
    X.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀' i₀ i₁ i₂ i₃' (X.le₀'₀ data hrr' hr pq hi₀' hi₀) _ _ _ =
    (X.spectralSequencePageXIso data r hr pq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃).hom ≫
    X.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₃' _ _ _
      (X.le₃₃' data hrr' hr pq hi₃ hi₃') := by
  let H := X.spectralSequenceHomologyData data r r' hrr' hr _ pq _ rfl rfl n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'
  refine Eq.trans ?_ ((X.spectralSequence data).rightHomologyData_ι_edgeEpiStep_compatibility
      r r' _ pq _ rfl rfl H.right)
  congr 1
  simp only [← assoc]
  congr 1
  simp only [homOfLE_leOfHom, assoc]
  obtain rfl : n₀ = n₁ - 1 := by lia
  subst hn₁' hn₂ hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'
  rw [HomologicalComplex.homologyIsoSc'_eq_rfl]
  dsimp [spectralSequencePageXIso, SpectralSequence.pageXIso]
  erw [id_comp]
  dsimp [SpectralSequence.iso, spectralSequence,
    SpectralSequence.homologyIso, SpectralSequence.homologyIso']
  erw [id_comp, spectralSequenceHomologyData_right_homologyIso_eq_left_homologyIso, Iso.inv_hom_id]

lemma hasPageInfinityAt (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (n₀ n₂ : ℤ) (hn₀ : n₀ = data.deg pq - 1) (hn₂ : n₂ = data.deg pq + 1)
    (isZero₁ : ∀ (i j : ι) (hij : i ≤ j) (_ : j ≤ X.i₀ data r pq),
      IsZero ((X.H n₂).obj (mk₁ (homOfLE hij))))
    (isZero₂ : ∀ (i j : ι) (hij : i ≤ j) (_ : X.i₃ data r pq ≤ i),
      IsZero ((X.H n₀).obj (mk₁ (homOfLE hij)))) :
    (X.spectralSequence data).HasPageInfinityAt pq where
  nonempty_hasEdgeEpiSet := ⟨r, X.mem_spectralSequence_hasEdgeEpiSet data r hr pq n₂ hn₂ isZero₁⟩
  nonempty_hasEdgeMonoSet := ⟨r, X.mem_spectralSequence_hasEdgeMonoSet data r hr pq n₀ hn₀ isZero₂⟩

@[reassoc]
lemma spectralSequence_edgeMonoSteps_compatibility
    (pq : κ) (r r' : ℤ) (hrr' : r ≤ r') (hr : r₀ ≤ r)
    [(X.spectralSequence data).HasPageInfinityAt pq]
    [(X.spectralSequence data).HasEdgeMonoAtFrom pq r]
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq)
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀' : i₀' = X.i₀ data r' pq)
    (hi₀ : i₀ = X.i₀ data r pq)
    (hi₁ : i₁ = data.i₁ pq)
    (hi₂ : i₂ = data.i₂ pq)
    (hi₃ : i₃ = X.i₃ data r pq)
    (hi₃' : i₃' = X.i₃ data r' pq) :
    X.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀' i₁ i₂ i₃ i₃' _ _
      (X.le₂₃ data r hr pq hi₂ hi₃) (X.monotone_i₃ data r r' hrr' hr pq hi₃ hi₃') ≫
      (X.spectralSequencePageXIso data r' (by lia) pq n₀ n₁ n₂ hn₁ hn₂ hn₁'
        i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃').inv ≫
      (X.spectralSequence data).edgeMonoSteps pq r r' hrr' =
        X.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀' i₀ i₁ i₂ i₃
          (X.antitone_i₀ data r r' hrr' hr pq hi₀ hi₀') _ _ _ ≫
        (X.spectralSequencePageXIso data r hr pq n₀ n₁ n₂ hn₁ hn₂ hn₁'
        i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃).inv := by
  obtain ⟨k, hk⟩ := Int.le.dest hrr'
  revert r r' i₀' i₀ i₁ i₂ i₃ i₃'
  induction k with
  | zero =>
    intro r r' hrr'  _ _ i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' h
    obtain rfl : r' = r := by simpa using h.symm
    obtain rfl : i₀' = i₀ := by rw [hi₀, hi₀']
    obtain rfl : i₃' = i₃ := by rw [hi₃, hi₃']
    simp only [SpectralSequence.edgeMonoSteps_eq_id, comp_id]
    rfl
  | succ k hk =>
    intro r r'' hrr'' _ _ i₀'' i₀ i₁ i₂ i₃ i₃'' hi₀'' hi₀ hi₁ hi₂ hi₃ hi₃'' h
    simp only [Nat.cast_succ] at h
    rw [← (X.spectralSequence data).edgeMonoSteps_comp pq r (r + k) r''
        (by lia) (by lia),
      ← X.EMapFourδ₄Toδ₃'_comp n₀ n₁ n₂ hn₁ hn₂ i₀'' i₁ i₂ i₃ _ i₃'' _ _ _
      (X.monotone_i₃ data r (r + k) (by lia) (by lia) pq hi₃ rfl)
      (X.monotone_i₃ data (r + k) r'' (by lia) (by lia) pq rfl hi₃''), assoc,
      (X.spectralSequence data).edgeMonoSteps_eq_edgeMonoStep pq (r + k) r'' (by lia),
      X.spectralSequence_edgeMonoStep_compatibility_assoc data pq (r + k) r'' (by lia) (by lia)
      n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀'' _ i₁ i₂ _ i₃'' hi₀'' rfl hi₁ hi₂ rfl hi₃'',
      ← EMapFourδ₁Toδ₀'_EMapFourδ₃Toδ₃'_assoc,
      hk r (r + k) (by lia) (by lia) _ i₀ i₁ i₂ i₃ _ rfl hi₀ hi₁ hi₂ hi₃ rfl rfl,
      X.EMapFourδ₁Toδ₀'_comp_assoc]

@[reassoc]
lemma spectralSequence_edgeEpiSteps_compatibility
    (pq : κ) (r r' : ℤ) (hrr' : r ≤ r') (hr : r₀ ≤ r)
    [(X.spectralSequence data).HasPageInfinityAt pq]
    [(X.spectralSequence data).HasEdgeEpiAtFrom pq r]
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq)
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀' : i₀' = X.i₀ data r' pq)
    (hi₀ : i₀ = X.i₀ data r pq)
    (hi₁ : i₁ = data.i₁ pq)
    (hi₂ : i₂ = data.i₂ pq)
    (hi₃ : i₃ = X.i₃ data r pq)
    (hi₃' : i₃' = X.i₃ data r' pq) :
    (X.spectralSequence data).edgeEpiSteps pq r r' hrr' ≫
      (X.spectralSequencePageXIso data r' (by lia) pq n₀ n₁ n₂ hn₁ hn₂ hn₁'
        i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃').hom ≫
        X.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀' i₀ i₁ i₂ i₃'
          (X.antitone_i₀ data r r' hrr' hr pq hi₀ hi₀') _ _ _ =
      (X.spectralSequencePageXIso data r hr pq n₀ n₁ n₂ hn₁ hn₂ hn₁'
        i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃).hom ≫
        X.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₃' _ _ _
          (X.monotone_i₃ data r r' hrr' hr pq hi₃ hi₃') := by
  obtain ⟨k, hk⟩ := Int.le.dest hrr'
  revert r r' i₀' i₀ i₁ i₂ i₃ i₃'
  induction k with
  | zero =>
    intro r r' hrr' _ _ i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' h
    obtain rfl : r' = r := by simpa using h.symm
    obtain rfl : i₀' = i₀ := by rw [hi₀, hi₀']
    obtain rfl : i₃' = i₃ := by rw [hi₃, hi₃']
    simp only [SpectralSequence.edgeEpiSteps_eq_id, id_comp]
    rfl
  | succ k hk =>
    intro r r'' hrr'' _ _ i₀'' i₀ i₁ i₂ i₃ i₃'' hi₀'' hi₀ hi₁ hi₂ hi₃ hi₃'' h
    simp only [Nat.cast_succ] at h
    rw [← (X.spectralSequence data).edgeEpiSteps_comp pq r (r + k) r''
      (by lia) (by lia),
      ← X.EMapFourδ₁Toδ₀'_comp n₀ n₁ n₂ hn₁ hn₂ i₀'' _ i₀ i₁ i₂ i₃''
      (X.antitone_i₀ data (r + k) r'' (by lia) (by lia) pq rfl hi₀'')
      (X.antitone_i₀ data r (r + k) (by lia) (by lia) pq hi₀ rfl), assoc,
      (X.spectralSequence data).edgeEpiSteps_eq_edgeEpiStep pq (r + k) r'' (by lia),
      X.spectralSequence_edgeEpiStep_compatibility_assoc data pq (r + k) r'' (by lia) (by lia)
        n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀'' _ i₁ i₂ _ i₃'' hi₀'' rfl hi₁ hi₂ rfl hi₃'',
      ← EMapFourδ₁Toδ₀'_EMapFourδ₃Toδ₃',
      reassoc_of% (hk r (r + k) (by lia) (by lia) _ i₀ i₁ i₂ i₃ _ rfl hi₀ hi₁ hi₂ hi₃ rfl rfl),
      X.EMapFourδ₄Toδ₃'_comp]

variable [OrderBot ι] [OrderTop ι]

noncomputable def pageInfinity (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (i j : ι) (hij : i ≤ j) : C :=
  X.E n₀ n₁ n₂ hn₁ hn₂ (homOfLE bot_le) (homOfLE hij) (homOfLE le_top)

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  (i₀ i₁ i₂ i₃ : ι) (hi₀₁ : i₀ ≤ i₁) (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃)
  (isZero₀ : IsZero ((X.H n₂).obj (mk₁ (homOfLE' ⊥ i₀ bot_le))))
  (isZero₃ : IsZero ((X.H n₀).obj (mk₁ (homOfLE' i₃ ⊤ le_top))))

noncomputable def EIsoPageInfinity :
    X.E n₀ n₁ n₂ hn₁ hn₂ (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃) ≅
      X.pageInfinity n₀ n₁ n₂ hn₁ hn₂ i₁ i₂ hi₁₂ :=
  (X.isoEMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ ⊥ i₀ i₁ i₂ i₃ bot_le hi₀₁ hi₁₂ hi₂₃ isZero₀).symm ≪≫
    X.isoEMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ ⊥ i₁ i₂ i₃ ⊤ bot_le hi₁₂ hi₂₃ le_top isZero₃

@[reassoc (attr := simp)]
lemma EMapFourδ₁Toδ₀'_EObjIsoPageInfinity_hom :
    X.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ ⊥ i₀ i₁ i₂ i₃ bot_le hi₀₁ hi₁₂ hi₂₃ ≫
      (X.EIsoPageInfinity n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ hi₀₁ hi₁₂ hi₂₃ isZero₀ isZero₃).hom =
    X.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ ⊥ i₁ i₂ i₃ ⊤ bot_le hi₁₂ hi₂₃ le_top := by
  simp [EIsoPageInfinity]

/-- EMapFourδ₄Toδ₃'_EObjIsoPageInfinity_inv' -/
@[reassoc (attr := simp)]
lemma EMapFourδ₄Toδ₃'_EObjIsoPageInfinity_inv' :
    X.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ ⊥ i₁ i₂ i₃ ⊤ bot_le hi₁₂ hi₂₃ le_top ≫
    (X.EIsoPageInfinity n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ hi₀₁ hi₁₂ hi₂₃ isZero₀ isZero₃).inv =
    X.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ ⊥ i₀ i₁ i₂ i₃ bot_le hi₀₁ hi₁₂ hi₂₃ := by
  simp [EIsoPageInfinity]

end

class StationaryAt (pq : κ) : Prop where
  exists_isZero₀ : ∃ (k : ℕ), ∀ (i j : ι) (hij : i ≤ j) (_ : j ≤ X.i₀ data (r₀ + k) pq),
    IsZero ((X.H (data.deg pq + 1)).obj (mk₁ (homOfLE hij)))
  exists_isZero₃ : ∃ (k : ℕ), ∀ (i j : ι) (hij : i ≤ j) (_ : X.i₃ data (r₀ + k) pq ≤ i),
    IsZero ((X.H (data.deg pq - 1)).obj (mk₁ (homOfLE hij)))

section

variable (pq : κ)

def stationarySet (pq : κ) : Set ℕ := fun k =>
  (∀ (i j : ι) (hij : i ≤ j) (_ : j ≤ X.i₀ data (r₀ + k) pq),
    IsZero ((X.H (data.deg pq + 1)).obj (mk₁ (homOfLE hij)))) ∧
  (∀ (i j : ι) (hij : i ≤ j) (_ : X.i₃ data (r₀ + k) pq ≤ i),
    IsZero ((X.H (data.deg pq - 1)).obj (mk₁ (homOfLE hij))))

variable [hpq : X.StationaryAt data pq]

omit [OrderBot ι] [OrderTop ι] [X.HasSpectralSequence data] in
lemma nonempty_stationarySet :
    (X.stationarySet data pq).Nonempty :=
  ⟨max hpq.exists_isZero₀.choose hpq.exists_isZero₃.choose, by
    constructor
    · intro i j hij hj
      refine hpq.exists_isZero₀.choose_spec i j hij (hj.trans ?_)
      apply data.antitone_i₀
      simp
    · intro i j hij hi
      refine hpq.exists_isZero₃.choose_spec i j hij (LE.le.trans ?_ hi)
      apply data.monotone_i₃
      simp⟩

noncomputable def stationaryPage : ℤ :=
  r₀ + (Nat.lt_wfRel.wf).min (X.stationarySet data pq) (X.nonempty_stationarySet data pq)

omit [OrderBot ι] [OrderTop ι] [X.HasSpectralSequence data] in
lemma le₀_stationaryPage (pq : κ) [X.StationaryAt data pq] :
    r₀ ≤ X.stationaryPage data pq := by
  dsimp [stationaryPage]
  lia

omit [OrderBot ι] [OrderTop ι] [X.HasSpectralSequence data] in
lemma stationaryPage_isZero₀ (n : ℤ) (hn : n = data.deg pq + 1)
    (i j : ι) (hij : i ≤ j)
    (hj : j ≤ X.i₀ data (X.stationaryPage data pq) pq (X.le₀_stationaryPage data pq)) :
    IsZero ((X.H n).obj (mk₁ (homOfLE hij))) := by
  subst hn
  exact ((Nat.lt_wfRel.wf).min_mem (X.stationarySet data pq)
    (X.nonempty_stationarySet data pq)).1 i j hij hj

omit [OrderBot ι] [OrderTop ι] [X.HasSpectralSequence data] in
lemma stationaryPage_isZero₃ (n : ℤ) (hn : n = data.deg pq - 1)
    (i j : ι) (hij : i ≤ j)
    (hi : X.i₃ data (X.stationaryPage data pq) pq (X.le₀_stationaryPage data pq) ≤ i) :
    IsZero ((X.H n).obj (mk₁ (homOfLE hij))) := by
  subst hn
  exact ((Nat.lt_wfRel.wf).min_mem (X.stationarySet data pq)
    (X.nonempty_stationarySet data pq)).2 i j hij hi

instance : (spectralSequence X data).HasPageInfinityAt pq where
  nonempty_hasEdgeEpiSet :=
    ⟨_, X.mem_spectralSequence_hasEdgeEpiSet _ _ (X.le₀_stationaryPage data pq) pq _ rfl
      (X.stationaryPage_isZero₀ data pq _ rfl)⟩
  nonempty_hasEdgeMonoSet :=
    ⟨_, X.mem_spectralSequence_hasEdgeMonoSet _ _ (X.le₀_stationaryPage data pq) pq _ rfl
      (X.stationaryPage_isZero₃ data pq _ rfl)⟩

instance : (spectralSequence X data).HasEdgeEpiAtFrom pq (X.stationaryPage data pq) :=
  X.spectralSequenceHasEdgeEpiAtFrom _ _ (X.le₀_stationaryPage data pq) pq _ rfl
    (X.stationaryPage_isZero₀ data pq _ rfl)

instance : (spectralSequence X data).HasEdgeMonoAtFrom pq (X.stationaryPage data pq) :=
  X.spectralSequenceHasEdgeMonoAtFrom _ _ (X.le₀_stationaryPage data pq) pq _ rfl
    (X.stationaryPage_isZero₃ data pq _ rfl)

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq)

noncomputable def spectralSequencePageInfinityIso
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq) :
    (X.spectralSequence data).pageInfinity pq ≅ X.pageInfinity n₀ n₁ n₂ hn₁ hn₂ i₁ i₂
      (X.le₁₂ data pq hi₁ hi₂) :=
  (X.spectralSequence data).pageInfinityIso pq (X.stationaryPage data pq) ≪≫
    X.spectralSequencePageXIso _ _ (X.le₀_stationaryPage data pq) pq n₀ n₁ n₂ hn₁ hn₂ hn₁'
       _ i₁ i₂ _ rfl hi₁ hi₂ rfl ≪≫
      X.EIsoPageInfinity n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ _
        (X.stationaryPage_isZero₀ data pq n₂ (by lia) _ _ _ (by rfl))
        (X.stationaryPage_isZero₃ data pq n₀ (by lia) _ _ _ (by rfl))

lemma spectralSequencePageInfinityIso_hom
    (i₀ i₁ i₂ i₃ : ι) (hi₀ : i₀ = X.i₀ data _ pq (X.le₀_stationaryPage data pq))
      (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
      (hi₃ : i₃ = X.i₃ data (X.stationaryPage data pq) pq) :
  (X.spectralSequencePageInfinityIso data pq n₀ n₁ n₂ hn₁ hn₂ hn₁' i₁ i₂ hi₁ hi₂).hom =
  ((X.spectralSequence data).pageInfinityIso pq (X.stationaryPage data pq)).hom ≫
    (X.spectralSequencePageXIso data _ (X.le₀_stationaryPage data pq) pq n₀ n₁ n₂ hn₁ hn₂ hn₁'
       i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃).hom ≫
      (X.EIsoPageInfinity n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ _
        (X.stationaryPage_isZero₀ data pq n₂ (by lia) _ _ _ (by rw [hi₀]))
        (X.stationaryPage_isZero₃ data pq n₀ (by lia) _ _ _ (by rw [hi₃]))).hom := by
  subst hi₀ hi₃
  rfl

end

end

section

variable (Y : SpectralObject C EInt) [Y.IsFirstQuadrant]

instance (pq : ℕ × ℕ) : Y.StationaryAt mkDataE₂CohomologicalNat pq where
  exists_isZero₀ :=
    ⟨pq.2 + 2, fun i j hij hj => by
      apply isZero₁_of_isFirstQuadrant
      refine hj.trans ?_
      dsimp
      simp only [EInt.mk_le_mk_iff]
      lia⟩
  exists_isZero₃ :=
    ⟨pq.1 + 1, fun i j hij hi => by
      apply isZero₂_of_isFirstQuadrant
      refine lt_of_lt_of_le ?_ hi
      dsimp
      simp only [EInt.mk_lt_mk_iff]
      lia⟩

instance (pq : ℤ × ℤ) : Y.StationaryAt mkDataE₂Cohomological pq where
  exists_isZero₀ := by
    obtain ⟨k, hk⟩ : ∃ (k : ℕ), pq.2 ≤ k := ⟨_, Int.self_le_toNat pq.2⟩
    refine ⟨k, fun i j hij hj => by
      apply isZero₁_of_isFirstQuadrant
      refine hj.trans ?_
      dsimp
      simp only [EInt.mk_le_mk_iff]
      lia⟩
  exists_isZero₃ := by
    obtain ⟨k, hk⟩ : ∃ (k : ℕ), pq.1 ≤ k := ⟨_, Int.self_le_toNat pq.1⟩
    refine ⟨k, fun i j hij hi => by
      apply isZero₂_of_isFirstQuadrant
      refine lt_of_lt_of_le ?_ hi
      dsimp
      simp only [EInt.mk_lt_mk_iff, sub_lt_sub_iff_right]
      lia⟩

end

section

variable (Y : SpectralObject C EInt) [Y.IsThirdQuadrant]

instance (pq : ℕ × ℕ) : Y.StationaryAt mkDataE₂HomologicalNat pq where
  exists_isZero₀ := ⟨pq.1, fun i j hij hj => by
      apply isZero₂_of_isThirdQuadrant
      refine hj.trans ?_
      dsimp
      simp only [EInt.mk_le_mk_iff]
      lia⟩
  exists_isZero₃ := ⟨pq.2, fun i j hij hi => by
      apply isZero₁_of_isThirdQuadrant
      refine lt_of_lt_of_le ?_ hi
      dsimp
      simp only [neg_add_cancel_comm_assoc, EInt.mk_lt_mk_iff, sub_pos]
      lia⟩

end

end SpectralObject

end Abelian

end CategoryTheory
