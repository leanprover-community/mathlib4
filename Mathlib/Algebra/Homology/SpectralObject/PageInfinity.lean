/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.LowDegreesExactSequence
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

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
  (data : SpectralSequenceDataCore ι c r₀) [HasSpectralSequence X data]

lemma spectralSequence_page_d_eq_zero_iff_isIso₁
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq' pq'' : κ) (hpq' : (c r).Rel pq' pq'') (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq')
    (i₀' i₀ i₁ i₂ i₃ : ι)
    (hi₀' : i₀' = data.i₀ r' pq')
    (hi₀ : i₀ = data.i₀ r pq')
    (hi₁ : i₁ = data.i₁ pq')
    (hi₂ : i₂ = data.i₂ pq')
    (hi₃ : i₃ = data.i₃ r pq') :
    ((X.spectralSequence data).page r).d pq' pq'' = 0 ↔
      IsIso (X.map _ _ _ _ _ _ (fourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq' hi₀' hi₀)
          (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂)
          (data.le₂₃' r hr pq' hi₂ hi₃)) n₀ n₁ n₂) := by
  let S := ((spectralSequence X data).page r).sc' ((c r).prev  pq') pq' pq''
  let H : S.HomologyData :=
    X.spectralSequenceHomologyData data r r' hrr' hr _ pq' pq'' rfl ((c r).next_eq' hpq')
      i₀' i₀ i₁ i₂ i₃ _ hi₀' hi₀ hi₁ hi₂ hi₃ rfl n₀ n₁ n₂ hn₁'
  let e := X.spectralSequencePageXIso data r hr pq'
    i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁'
  let φ := (X.map _ _ _ _ _ _ (fourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq' hi₀' hi₀)
    (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂)
    (data.le₂₃' r hr pq' hi₂ hi₃)) n₀ n₁ n₂)
  have fac : H.left.i = φ ≫ e.inv := X.spectralSequenceHomologyData_left_i ..
  have eq₁ : IsIso φ ↔ IsIso H.left.i := by
    apply (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    refine Arrow.isoMk (Iso.refl _) e.symm ?_
    dsimp
    rw [fac]
    apply id_comp
  have eq₂ : IsIso H.left.i ↔ S.g = 0 := by
    constructor
    · intro
      rw [← cancel_epi H.left.i, H.left.wi, comp_zero]
    · exact H.left.isIso_i
  change _ ↔ IsIso φ
  rw [eq₁, eq₂]
  rfl

set_option backward.defeqAttrib.useBackward true in
lemma spectralSequence_page_d_eq_zero_iff_isIso₂
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq pq' : κ) (hpq' : (c r).Rel pq pq') (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq')
    (i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀ : i₀ = data.i₀ r pq')
    (hi₁ : i₁ = data.i₁ pq')
    (hi₂ : i₂ = data.i₂ pq')
    (hi₃ : i₃ = data.i₃ r pq')
    (hi₃' : i₃' = data.i₃ r' pq') :
    ((X.spectralSequence data).page r).d pq pq' = 0 ↔
      IsIso (X.map _ _ _ _ _ _
        (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃'
          (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂)
          (data.le₂₃' r hr pq' hi₂ hi₃) (data.le₃₃' hrr' hr pq' hi₃ hi₃'))
          n₀ n₁ n₂ hn₁ hn₂) := by
  let S := ((spectralSequence X data).page r).sc' pq pq' ((c r).next pq')
  let H : S.HomologyData :=
    X.spectralSequenceHomologyData data r r' hrr' hr pq pq' _ ((c r).prev_eq' hpq') rfl
      _ i₀ i₁ i₂ i₃ i₃' rfl hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁'
  let e := X.spectralSequencePageXIso data r hr pq'
    i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁'
  let φ := X.map _ _ _ _ _ _ (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃'
    (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂)
    (data.le₂₃' r hr pq' hi₂ hi₃) (data.le₃₃' hrr' hr pq' hi₃ hi₃')) n₀ n₁ n₂
  have fac : H.right.p = e.hom ≫ φ := X.spectralSequenceHomologyData_right_p ..
  have eq₁ : IsIso H.right.p ↔ IsIso φ := by
    apply (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    refine Arrow.isoMk e (Iso.refl _) ?_
    dsimp
    rw [fac]
    symm
    apply comp_id
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
    (hi₀' : i₀' = data.i₀ r' pq')
    (hi₀ : i₀ = data.i₀ r pq')
    (h : IsZero ((X.H n₂).obj (mk₁ (homOfLE (data.i₀_le' hrr' hr pq' hi₀' hi₀))))) :
    ((X.spectralSequence data).page r).d pq' pq'' = 0 := by
  by_cases hpq' : (c r).Rel pq' pq''
  · rw [X.spectralSequence_page_d_eq_zero_iff_isIso₁ data r r' hrr' hr pq' pq'' hpq'
      (data.deg pq' - 1) (data.deg pq') n₂ (by simp) hn₂.symm rfl _ _ _ _ _ hi₀' hi₀ rfl rfl rfl]
    exact X.isIso_map_fourδ₁Toδ₀_of_isZero _ _ _ _ _ _ _ _ _ h
  · exact HomologicalComplex.shape _ _ _ hpq'

lemma spectralSequence_page_d_eq_zero_of_isZero₂
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq pq' : κ) (n₀ : ℤ) (hn₀ : n₀ = data.deg pq' - 1)
    (i₃ i₃' : ι)
    (hi₃ : i₃ = data.i₃ r pq')
    (hi₃' : i₃' = data.i₃ r' pq')
    (h : IsZero ((X.H n₀).obj (mk₁ (homOfLE (data.le₃₃' hrr' hr pq' hi₃ hi₃'))))) :
    ((X.spectralSequence data).page r).d pq pq' = 0 := by
  by_cases hpq : (c r).Rel pq pq'
  · rw [X.spectralSequence_page_d_eq_zero_iff_isIso₂ data r r' hrr' hr pq pq' hpq
      n₀ (data.deg pq') _ (by lia) rfl rfl _ _ _ i₃ i₃' rfl rfl rfl hi₃ hi₃']
    exact X.isIso_map_fourδ₄Toδ₃_of_isZero _ _ _ _ _ _ _ _ _ h
  · exact HomologicalComplex.shape _ _ _ hpq

lemma spectralSequenceHasEdgeEpiAt_iff (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (X.spectralSequence data).HasEdgeEpiAt pq r ↔
      ∀ (pq' : κ) (_ : (c r).Rel pq pq')
        (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (_ : n₁ = data.deg pq)
        (i₀' i₀ i₁ i₂ i₃ : ι)
        (hi₀' : i₀' = data.i₀ (r + 1) pq)
        (hi₀ : i₀ = data.i₀ r pq)
        (hi₁ : i₁ = data.i₁ pq)
        (hi₂ : i₂ = data.i₂ pq)
        (hi₃ : i₃ = data.i₃ r pq),
          IsIso (X.map  _ _ _ _ _ _
          (fourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.i₀_le' rfl hr pq hi₀' hi₀)
            (data.le₀₁' r hr pq hi₀ hi₁) (data.le₁₂' pq hi₁ hi₂)
            (data.le₂₃' r hr pq hi₂ hi₃)) n₀ n₁ n₂ hn₁ hn₂) := by
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
    (hi₀' : i₀' = data.i₀ r' pq)
    (hi₀ : i₀ = data.i₀ r pq)
    (h : IsZero ((X.H n₂).obj (mk₁ (homOfLE (data.i₀_le' hrr' hr pq hi₀' hi₀))))) :
    (X.spectralSequence data).HasEdgeEpiAt pq r where
  zero pq' := X.spectralSequence_page_d_eq_zero_of_isZero₁ data r r' hrr' hr pq pq' n₂ hn₂
    i₀' i₀ hi₀' hi₀ h

lemma mem_spectralSequence_hasEdgeEpiSet (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (n₂ : ℤ) (hn₂ : n₂ = data.deg pq + 1)
    (isZero : ∀ (i j : ι) (hij : i ≤ j)
      (_ : j ≤ data.i₀ r pq),
      IsZero ((X.H n₂).obj (mk₁ (homOfLE hij)))) :
    r ∈ (X.spectralSequence data).hasEdgeEpiSet pq := by
  refine ⟨hr, fun r' hrr' ↦ X.spectralSequenceHasEdgeEpiAt data r' (r' + 1) rfl
    (by lia) pq n₂ hn₂ _ _ rfl rfl ?_⟩
  apply isZero
  exact data.antitone_i₀ _ _ _

lemma spectralSequenceHasEdgeEpiAtFrom (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (n₂ : ℤ) (hn₂ : n₂ = data.deg pq + 1)
    [(X.spectralSequence data).HasPageInfinityAt pq]
    (isZero : ∀ (i j : ι) (hij : i ≤ j)
      (_ : j ≤ data.i₀ r pq),
      IsZero ((X.H n₂).obj (mk₁ (homOfLE hij)))) :
    (X.spectralSequence data).HasEdgeEpiAtFrom pq r where
  le := (X.spectralSequence data).rFromMin_LE pq r
    (X.mem_spectralSequence_hasEdgeEpiSet data r hr pq n₂ hn₂ isZero)

lemma spectralSequenceHasEdgeMonoAt_iff (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (X.spectralSequence data).HasEdgeMonoAt pq r ↔
      ∀ (pq' : κ) (_ : (c r).Rel pq' pq)
        (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (_ : n₁ = data.deg pq)
        (i₀ i₁ i₂ i₃ i₃' : ι)
        (hi₀ : i₀ = data.i₀ r pq)
        (hi₁ : i₁ = data.i₁ pq)
        (hi₂ : i₂ = data.i₂ pq)
        (hi₃ : i₃ = data.i₃ r pq)
        (hi₃' : i₃' = data.i₃ (r + 1) pq),
          IsIso (X.map _ _ _ _ _ _
          (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃'
            (data.le₀₁' r hr pq hi₀ hi₁) (data.le₁₂' pq hi₁ hi₂)
            (data.le₂₃' r hr pq hi₂ hi₃) (data.le₃₃' rfl hr pq hi₃ hi₃')) n₀ n₁ n₂ hn₁ hn₂) := by
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
    (hi₃ : i₃ = data.i₃ r pq)
    (hi₃' : i₃' = data.i₃ r' pq)
    (h : IsZero ((X.H n₀).obj (mk₁ (homOfLE (data.le₃₃' hrr' hr pq hi₃ hi₃'))))) :
    (X.spectralSequence data).HasEdgeMonoAt pq r where
  zero pq' := X.spectralSequence_page_d_eq_zero_of_isZero₂ data r r' hrr' hr pq' pq n₀ hn₀
    i₃ i₃' hi₃ hi₃' h

lemma mem_spectralSequence_hasEdgeMonoSet (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (n₀ : ℤ) (hn₀ : n₀ = data.deg pq - 1)
    (isZero : ∀ (i j : ι) (hij : i ≤ j)
      (_ : data.i₃ r pq ≤ i),
      IsZero ((X.H n₀).obj (mk₁ (homOfLE hij)))) :
    r ∈ (X.spectralSequence data).hasEdgeMonoSet pq := by
  refine ⟨hr, fun r' hrr' ↦
    X.spectralSequenceHasEdgeMonoAt data r' (r' + 1) rfl (by lia) pq n₀ hn₀ _ _ rfl rfl ?_⟩
  --have := (X.spectralSequence data).hasPage_of_LE _ _ hrr'
  apply isZero
  exact data.monotone_i₃ _ _ _

lemma spectralSequenceHasEdgeMonoAtFrom (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (n₀ : ℤ) (hn₀ : n₀ = data.deg pq - 1)
    [(X.spectralSequence data).HasPageInfinityAt pq]
    (isZero : ∀ (i j : ι) (hij : i ≤ j) (_ : data.i₃ r pq ≤ i),
      IsZero ((X.H n₀).obj (mk₁ (homOfLE hij)))) :
    (X.spectralSequence data).HasEdgeMonoAtFrom pq r where
  le := (X.spectralSequence data).rToMin_LE pq r
    (X.mem_spectralSequence_hasEdgeMonoSet data r hr pq n₀ hn₀ isZero)

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma spectralSequence_edgeMonoStep_compatibility
    (pq : κ) (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    [(X.spectralSequence data).HasEdgeMonoAt pq r]
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq)
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀' : i₀' = data.i₀ r' pq)
    (hi₀ : i₀ = data.i₀ r pq)
    (hi₁ : i₁ = data.i₁ pq)
    (hi₂ : i₂ = data.i₂ pq)
    (hi₃ : i₃ = data.i₃ r pq)
    (hi₃' : i₃' = data.i₃ r' pq) :
    X.mapFourδ₄Toδ₃' i₀' i₁ i₂ i₃ i₃' _ _
      (data.le₂₃' r hr pq hi₂ hi₃) (data.le₃₃' hrr' hr pq hi₃ hi₃') n₀ n₁ n₂ hn₁ hn₂  ≫
    (X.spectralSequencePageXIso data r' (by lia) pq
      i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).inv ≫
    (X.spectralSequence data).edgeMonoStep pq r r' hrr' =
      X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq hi₀' hi₀) _ _ _ n₀ n₁ n₂ hn₁ hn₂  ≫
    ((X.spectralSequencePageXIso data r hr pq
      i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂)).inv := by
  rw [← X.spectralSequenceHomologyData_left_i data r r' hrr' hr _ pq _ rfl rfl
    i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'  n₀ n₁ n₂ hn₁' hn₁,
    ← ((X.spectralSequence data).leftHomologyData_π_edgeMonoStep_compatibility r r' _
    pq _ rfl rfl),
    X.spectralSequence_iso_hom_assoc data r r' hrr' hr _ pq _ rfl rfl i₀' i₀ i₁ i₂ i₃ i₃'
    hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁', Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  dsimp

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma spectralSequence_edgeEpiStep_compatibility
    (pq : κ) (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    [(X.spectralSequence data).HasEdgeEpiAt pq r]
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq)
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀' : i₀' = data.i₀ r' pq)
    (hi₀ : i₀ = data.i₀ r pq)
    (hi₁ : i₁ = data.i₁ pq)
    (hi₂ : i₂ = data.i₂ pq)
    (hi₃ : i₃ = data.i₃ r pq)
    (hi₃' : i₃' = data.i₃ r' pq) :
    (X.spectralSequence data).edgeEpiStep pq r r' hrr' ≫
    (X.spectralSequencePageXIso data r' (by lia) pq
      i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).hom ≫
    X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃' (data.i₀_le' hrr' hr pq hi₀' hi₀) _ _ _ n₀ n₁ n₂ hn₁ hn₂  =
    (X.spectralSequencePageXIso data r hr pq
      i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃  n₀ n₁ n₂ hn₁' hn₁ hn₂).hom ≫
    X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃' _ _ _
      (data.le₃₃' hrr' hr pq hi₃ hi₃') n₀ n₁ n₂ hn₁ hn₂ := by
  rw [← X.spectralSequenceHomologyData_right_p data r r' hrr' hr _ pq _ rfl rfl
    i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'  n₀ n₁ n₂ hn₁' hn₁,
    ← ((X.spectralSequence data).rightHomologyData_ι_edgeEpiStep_compatibility
      r r' _ pq _ rfl rfl),
    X.spectralSequence_iso_inv_assoc data r r' hrr' hr _ pq _ rfl rfl i₀' i₀ i₁ i₂ i₃ i₃'
    hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁', Iso.inv_hom_id_assoc,
    X.spectralSequenceHomologyData_right_homologyIso_eq_left_homologyIso data r r' hrr' hr
    _ pq _ rfl rfl i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂]
  simp

lemma hasPageInfinityAt (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (n₀ n₂ : ℤ) (hn₀ : n₀ = data.deg pq - 1) (hn₂ : n₂ = data.deg pq + 1)
    (isZero₁ : ∀ (i j : ι) (hij : i ≤ j) (_ : j ≤ data.i₀ r pq),
      IsZero ((X.H n₂).obj (mk₁ (homOfLE hij))))
    (isZero₂ : ∀ (i j : ι) (hij : i ≤ j) (_ : data.i₃ r pq ≤ i),
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
    (hi₀' : i₀' = data.i₀ r' pq)
    (hi₀ : i₀ = data.i₀ r pq)
    (hi₁ : i₁ = data.i₁ pq)
    (hi₂ : i₂ = data.i₂ pq)
    (hi₃ : i₃ = data.i₃ r pq)
    (hi₃' : i₃' = data.i₃ r' pq) :
    X.mapFourδ₄Toδ₃' i₀' i₁ i₂ i₃ i₃' _ _
      (data.le₂₃' r hr pq hi₂ hi₃)
        (data.monotone_i₃' hrr' hr pq hi₃ hi₃') n₀ n₁ n₂ hn₁ hn₂  ≫
      (X.spectralSequencePageXIso data r' (by lia) pq
        i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).inv ≫
      (X.spectralSequence data).edgeMonoSteps pq r r' hrr' =
        X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.antitone_i₀' hrr' hr pq hi₀ hi₀') _ _ _
          n₀ n₁ n₂ hn₁ hn₂  ≫
        (X.spectralSequencePageXIso data r hr pq
          i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂).inv := by
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
        (by lia) (by lia)]
    have := (data.monotone_i₃' (r' := r + k) (by lia) (by lia) pq hi₃ rfl)
    rw [← X.mapFourδ₄Toδ₃'_comp_assoc i₀'' i₁ i₂ i₃ _ i₃'' _ _ _
      (data.monotone_i₃' (r' := r + k) (by lia) (by lia) pq hi₃ rfl)
      (data.monotone_i₃' (by lia) (by lia) pq rfl hi₃'') ..,
      (X.spectralSequence data).edgeMonoSteps_eq_edgeMonoStep pq (r + k) r'' (by lia),
      X.spectralSequence_edgeMonoStep_compatibility_assoc data pq (r + k) r'' (by lia) (by lia)
        n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀'' _ i₁ i₂ _ i₃'' hi₀'' rfl hi₁ hi₂ rfl hi₃'',
      ← mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'_assoc ..,
      hk r (r + k) _ _ _ i₀ i₁ i₂ i₃ _ rfl hi₀ hi₁ hi₂ hi₃ rfl rfl,
      mapFourδ₁Toδ₀'_comp_assoc ..]

@[reassoc]
lemma spectralSequence_edgeEpiSteps_compatibility
    (pq : κ) (r r' : ℤ) (hrr' : r ≤ r') (hr : r₀ ≤ r)
    [(X.spectralSequence data).HasPageInfinityAt pq]
    [(X.spectralSequence data).HasEdgeEpiAtFrom pq r]
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₁' : n₁ = data.deg pq)
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀' : i₀' = data.i₀ r' pq)
    (hi₀ : i₀ = data.i₀ r pq)
    (hi₁ : i₁ = data.i₁ pq)
    (hi₂ : i₂ = data.i₂ pq)
    (hi₃ : i₃ = data.i₃ r pq)
    (hi₃' : i₃' = data.i₃ r' pq) :
    (X.spectralSequence data).edgeEpiSteps pq r r' hrr' ≫
      (X.spectralSequencePageXIso data r' (by lia) pq
        i₀' i₁ i₂ i₃' hi₀' hi₁ hi₂ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).hom ≫
        X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃'
          (data.antitone_i₀' hrr' hr pq hi₀ hi₀') _ _ _ n₀ n₁ n₂ hn₁ hn₂ =
      (X.spectralSequencePageXIso data r hr pq
        i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂).hom ≫
        X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃' _ _ _
          (data.monotone_i₃' hrr' hr pq hi₃ hi₃') n₀ n₁ n₂ hn₁ hn₂ := by
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
      ← X.mapFourδ₁Toδ₀'_comp i₀'' _ i₀ i₁ i₂ i₃''
      (data.antitone_i₀' (r := r + k) (by lia) (by lia) pq rfl hi₀'')
      (data.antitone_i₀' (by lia) (by lia) pq hi₀ rfl) _ _ _ n₀ n₁ n₂ hn₁ hn₂ , assoc,
      (X.spectralSequence data).edgeEpiSteps_eq_edgeEpiStep pq (r + k) r'' (by lia),
      X.spectralSequence_edgeEpiStep_compatibility_assoc data pq (r + k) r'' (by lia) (by lia)
        n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀'' _ i₁ i₂ _ i₃'' hi₀'' rfl hi₁ hi₂ rfl hi₃'',
      ← mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' ..,
      reassoc_of% (hk r (r + k) (by lia) (by lia) _ i₀ i₁ i₂ i₃ _ rfl hi₀ hi₁ hi₂ hi₃ rfl rfl),
      X.mapFourδ₄Toδ₃'_comp ..]

variable [OrderBot ι] [OrderTop ι]

noncomputable def pageInfinity (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (i j : ι) (hij : i ≤ j) : C :=
  X.E (homOfLE bot_le) (homOfLE hij) (homOfLE le_top) n₀ n₁ n₂ hn₁ hn₂

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  (i₀ i₁ i₂ i₃ : ι) (hi₀₁ : i₀ ≤ i₁) (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃)
  (isZero₀ : IsZero ((X.H n₂).obj (mk₁ (homOfLE' ⊥ i₀ bot_le))))
  (isZero₃ : IsZero ((X.H n₀).obj (mk₁ (homOfLE' i₃ ⊤ le_top))))

noncomputable def EIsoPageInfinity :
    X.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃) n₀ n₁ n₂ hn₁ hn₂ ≅
      X.pageInfinity n₀ n₁ n₂ hn₁ hn₂ i₁ i₂ hi₁₂ :=
  (X.isoMapFourδ₁Toδ₀' ⊥ i₀ i₁ i₂ i₃ bot_le hi₀₁ hi₁₂ hi₂₃ n₀ n₁ n₂ isZero₀ hn₁ hn₂).symm ≪≫
    X.isoMapFourδ₄Toδ₃' ⊥ i₁ i₂ i₃ ⊤ bot_le hi₁₂ hi₂₃ le_top n₀ n₁ n₂ isZero₃ hn₁ hn₂

@[reassoc (attr := simp)]
lemma EMapFourδ₁Toδ₀'_EObjIsoPageInfinity_hom :
    X.mapFourδ₁Toδ₀' ⊥ i₀ i₁ i₂ i₃ bot_le hi₀₁ hi₁₂ hi₂₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      (X.EIsoPageInfinity n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ hi₀₁ hi₁₂ hi₂₃ isZero₀ isZero₃).hom =
    X.mapFourδ₄Toδ₃' ⊥ i₁ i₂ i₃ ⊤ bot_le hi₁₂ hi₂₃ le_top n₀ n₁ n₂ hn₁ hn₂ := by
  simp [EIsoPageInfinity]

set_option backward.isDefEq.respectTransparency false in
/-- EMapFourδ₄Toδ₃'_EObjIsoPageInfinity_inv' -/
@[reassoc (attr := simp)]
lemma EMapFourδ₄Toδ₃'_EObjIsoPageInfinity_inv' :
    X.mapFourδ₄Toδ₃' ⊥ i₁ i₂ i₃ ⊤ bot_le hi₁₂ hi₂₃ le_top n₀ n₁ n₂ hn₁ hn₂ ≫
    (X.EIsoPageInfinity n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ hi₀₁ hi₁₂ hi₂₃ isZero₀ isZero₃).inv =
    X.mapFourδ₁Toδ₀' ⊥ i₀ i₁ i₂ i₃ bot_le hi₀₁ hi₁₂ hi₂₃ n₀ n₁ n₂ hn₁ hn₂ := by
  simp [EIsoPageInfinity]

end

class StationaryAt (pq : κ) : Prop where
  exists_isZero₀ : ∃ (k : ℕ), ∀ (i j : ι) (hij : i ≤ j) (_ : j ≤ data.i₀ (r₀ + k) pq),
    IsZero ((X.H (data.deg pq + 1)).obj (mk₁ (homOfLE hij)))
  exists_isZero₃ : ∃ (k : ℕ), ∀ (i j : ι) (hij : i ≤ j) (_ : data.i₃ (r₀ + k) pq ≤ i),
    IsZero ((X.H (data.deg pq - 1)).obj (mk₁ (homOfLE hij)))

section

variable (pq : κ)

def stationarySet (pq : κ) : Set ℕ := fun k =>
  (∀ (i j : ι) (hij : i ≤ j) (_ : j ≤ data.i₀ (r₀ + k) pq),
    IsZero ((X.H (data.deg pq + 1)).obj (mk₁ (homOfLE hij)))) ∧
  (∀ (i j : ι) (hij : i ≤ j) (_ : data.i₃ (r₀ + k) pq ≤ i),
    IsZero ((X.H (data.deg pq - 1)).obj (mk₁ (homOfLE hij))))

variable [hpq : X.StationaryAt data pq]

omit [OrderBot ι] [OrderTop ι] [X.HasSpectralSequence data] in
lemma nonempty_stationarySet :
    (X.stationarySet data pq).Nonempty :=
  ⟨max hpq.exists_isZero₀.choose hpq.exists_isZero₃.choose, by
    constructor
    · intro i j hij hj
      exact hpq.exists_isZero₀.choose_spec i j hij
        (hj.trans (data.antitone_i₀ _ _ _ (by lia) (by simp)))
    · intro i j hij hi
      exact hpq.exists_isZero₃.choose_spec i j hij
        ((data.monotone_i₃ _ _ _ (by lia) (by simp)).trans hi)⟩

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
    (hj : j ≤ data.i₀ (X.stationaryPage data pq) pq (X.le₀_stationaryPage data pq)) :
    IsZero ((X.H n).obj (mk₁ (homOfLE hij))) := by
  subst hn
  exact ((Nat.lt_wfRel.wf).min_mem (X.stationarySet data pq)
    (X.nonempty_stationarySet data pq)).1 i j hij hj

omit [OrderBot ι] [OrderTop ι] [X.HasSpectralSequence data] in
lemma stationaryPage_isZero₃ (n : ℤ) (hn : n = data.deg pq - 1)
    (i j : ι) (hij : i ≤ j)
    (hi : data.i₃ (X.stationaryPage data pq) pq (X.le₀_stationaryPage data pq) ≤ i) :
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
      (data.le₁₂' pq hi₁ hi₂) :=
  (X.spectralSequence data).pageInfinityIso pq (X.stationaryPage data pq) ≪≫
    X.spectralSequencePageXIso _ _ (X.le₀_stationaryPage data pq) pq
       _ i₁ i₂ _ rfl hi₁ hi₂ rfl n₀ n₁ n₂ hn₁' hn₁ hn₂ ≪≫
      X.EIsoPageInfinity n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ _
        (X.stationaryPage_isZero₀ data pq n₂ (by lia) _ _ _ (by rfl))
        (X.stationaryPage_isZero₃ data pq n₀ (by lia) _ _ _ (by rfl))

lemma spectralSequencePageInfinityIso_hom
    (i₀ i₁ i₂ i₃ : ι) (hi₀ : i₀ = data.i₀ _ pq (X.le₀_stationaryPage data pq))
      (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
      (hi₃ : i₃ = data.i₃ (X.stationaryPage data pq) pq) :
  (X.spectralSequencePageInfinityIso data pq n₀ n₁ n₂ hn₁ hn₂ hn₁' i₁ i₂ hi₁ hi₂).hom =
  ((X.spectralSequence data).pageInfinityIso pq (X.stationaryPage data pq)).hom ≫
    (X.spectralSequencePageXIso data _ (X.le₀_stationaryPage data pq) pq
       i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂).hom ≫
      (X.EIsoPageInfinity n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ _
        (X.stationaryPage_isZero₀ data pq n₂ (by lia) _ _ _ (by rw [hi₀]))
        (X.stationaryPage_isZero₃ data pq n₀ (by lia) _ _ _ (by rw [hi₃]))).hom := by
  subst hi₀ hi₃
  rfl

end

end

section

variable (Y : SpectralObject C EInt) [Y.IsFirstQuadrant]

instance (pq : ℕ × ℕ) : Y.StationaryAt coreE₂CohomologicalNat pq where
  exists_isZero₀ :=
    ⟨pq.2 + 2, fun i j hij hj => by
      apply isZero₁_of_isFirstQuadrant
      exact hj.trans (by simp; lia)⟩
  exists_isZero₃ :=
    ⟨pq.1 + 1, fun i j hij hi => by
      apply isZero₂_of_isFirstQuadrant
      exact lt_of_lt_of_le (by simp; lia) hi⟩

instance (pq : ℤ × ℤ) : Y.StationaryAt coreE₂Cohomological pq where
  exists_isZero₀ := by
    obtain ⟨k, hk⟩ : ∃ (k : ℕ), pq.2 ≤ k := ⟨_, Int.self_le_toNat pq.2⟩
    refine ⟨k, fun i j hij hj => by
      apply isZero₁_of_isFirstQuadrant
      exact hj.trans (by simp; lia)⟩
  exists_isZero₃ := by
    obtain ⟨k, hk⟩ : ∃ (k : ℕ), pq.1 ≤ k := ⟨_, Int.self_le_toNat pq.1⟩
    refine ⟨k, fun i j hij hi => by
      apply isZero₂_of_isFirstQuadrant
      exact lt_of_lt_of_le (by simp; lia) hi⟩

end

section

variable (Y : SpectralObject C EInt) [Y.IsThirdQuadrant]

instance (pq : ℕ × ℕ) : Y.StationaryAt coreE₂HomologicalNat pq where
  exists_isZero₀ := ⟨pq.1, fun i j hij hj => by
      apply isZero₂_of_isThirdQuadrant
      exact hj.trans (by simp; lia)⟩
  exists_isZero₃ := ⟨pq.2, fun i j hij hi => by
      apply isZero₁_of_isThirdQuadrant
      exact lt_of_lt_of_le (by simp) hi⟩

end

end SpectralObject

end Abelian

end CategoryTheory
