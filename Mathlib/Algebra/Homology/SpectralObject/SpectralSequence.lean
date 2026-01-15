/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Homology
public import Mathlib.Algebra.Homology.SpectralObject.HasSpectralSequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Data.EInt.Basic
public import Batteries.Tactic.Lint

/-!
# The spectral sequence of a spectral object

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceMkData ι c r₀)

namespace SpectralSequence

/-- The object on position `pq` on the `r`th page of the spectral sequence. -/
noncomputable def pageX (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : C :=
  X.E (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by simp) rfl
      (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))

/-- The object on position `pq` on the `r`th page of the spectral sequence identifies
to `E^{deg pq}(i₀ ≤ i₁ ≤ i₂ ≤ i₃)`. -/
noncomputable def pageXIso (r : ℤ) (hr : r₀ ≤ r) (pq : κ) (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (h : n₁ = data.deg pq)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq) :
    pageX X data r pq hr ≅ X.E n₀ n₁ n₂ hn₁ hn₂
      (homOfLE (data.le₀₁' r hr pq h₀ h₁))
      (homOfLE (data.le₁₂' pq h₁ h₂))
      (homOfLE (data.le₂₃' r hr pq h₂ h₃)) :=
  eqToIso (by
    obtain rfl : n₀ = n₁ - 1 := by lia
    subst h hn₂ h₀ h₁ h₂ h₃
    rfl)

open Classical in
/-- The differential on the `r`th page of the spectral sequence. -/
noncomputable def pageD (r : ℤ) (pq pq' : κ) (hr : r₀ ≤ r := by lia) :
    pageX X data r pq hr ⟶ pageX X data r pq' hr :=
  if hpq : (c r).Rel pq pq'
    then
      X.d (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (data.deg pq + 2) _ rfl
        (by lia) (homOfLE (data.le₀₁ r pq'))
        (homOfLE (data.le₁₂' pq' rfl (data.hc₀₂ r pq pq' hpq)))
        (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq)) ≫
      (pageXIso _ _ _ _ _ _ _ _ _ _ (data.hc r pq pq' hpq) _ _ _ _ rfl rfl
        (data.hc₀₂ r pq pq' hpq) (data.hc₁₃ r pq pq' hpq)).inv
    else 0

lemma pageD_eq (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq')
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (hn₁' : n₁ = data.deg pq)
    (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ pq') (h₂ : i₂ = data.i₀ r pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r pq) :
    pageD X data r pq pq' =
      (pageXIso _ _ _ _ _ _ _ _ _ _ hn₁' _ _ _ _ h₂ h₃ h₄ h₅).hom ≫
        X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ ≫
        (pageXIso _ _ _ _ _ _ _ _ _ _
          (by simpa only [← hn₂, hn₁'] using data.hc r pq pq' hpq) _ _ _ _ h₀ h₁
          (by rw [h₂, data.hc₀₂ r pq pq' hpq])
          (by rw [h₃, data.hc₁₃ r pq pq' hpq])).inv := by
  subst hn₁' h₀ h₁ h₂ h₃ h₄ h₅
  obtain rfl : n₀ = data.deg pq - 1 := by lia
  obtain rfl : n₂ = data.deg pq + 1 := by lia
  obtain rfl : n₃ = data.deg pq + 2 := by lia
  dsimp [pageD, pageXIso]
  rw [dif_pos hpq, Category.id_comp]
  rfl

@[reassoc (attr := simp)]
lemma pageD_pageD (r : ℤ) (hr : r₀ ≤ r) (pq pq' pq'' : κ) :
    pageD X data r pq pq' hr ≫ pageD X data r pq' pq'' hr = 0 := by
  by_cases hpq : (c r).Rel pq pq'
  · by_cases hpq' : (c r).Rel pq' pq''
    · rw [pageD_eq X data r hr pq pq' hpq (data.deg pq - 1) (data.deg pq) _ _ (by simp)
        rfl rfl (homOfLE (data.le₂₃ r pq''))
        (homOfLE (data.le₁₂' pq' (data.hc₁₃ r pq' pq'' hpq').symm
          (data.hc₀₂ r pq pq' hpq))) (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq))
        (homOfLE (data.le₂₃ r pq)) rfl (data.hc₀₂ r pq' pq'' hpq').symm
        (data.hc₁₃ r pq' pq'' hpq').symm rfl rfl rfl rfl,
        pageD_eq X data r hr pq' pq'' hpq' (data.deg pq) _ _ _ rfl rfl rfl _ _ _ _ _
        (data.hc r pq pq' hpq) rfl rfl (data.hc₀₂ r pq' pq'' hpq').symm
        (data.hc₁₃ r pq' pq'' hpq').symm (data.hc₀₂ r pq pq' hpq)
        (data.hc₁₃ r pq pq' hpq), Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
        d_d_assoc, zero_comp, comp_zero]
    · dsimp only [pageD]
      rw [dif_neg hpq', comp_zero]
  · dsimp only [pageD]
    rw [dif_neg hpq, zero_comp]

/-- The `r`th page of the spectral sequence. -/
@[simps]
noncomputable def page (r : ℤ) (hr : r₀ ≤ r) :
    HomologicalComplex C (c r) where
  X pq := pageX X data r pq
  d := pageD X data r
  shape pq pq' hpq := dif_neg hpq

section

/-- The short complexe of the `r`th page of the spectral sequence on position `pq'`
identifies to the short complex given by the differentials of the spectral object. -/
noncomputable def shortComplexIso (r : ℤ) (hr : r₀ ≤ r) (pq pq' pq'' : κ)
    (hpq : (c r).Rel pq pq') (hpq' : (c r).Rel pq' pq'')
    (n₀ n₁ n₂ n₃ n₄ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) (hn₄ : n₃ + 1 = n₄)
    (hn₂' : n₂ = data.deg pq') :
    (page X data r hr).sc' pq pq' pq'' ≅
      X.dShortComplex n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ (homOfLE (data.le₀₁ r pq''))
        (homOfLE (data.le₁₂ pq'')) (homOfLE (data.le₂₃ r pq''))
        (homOfLE (by simpa only [← data.hc₁₃ r pq' pq'' hpq', data.hc₀₂ r pq pq' hpq]
          using data.le₁₂ pq')) (homOfLE (data.le₀₁ r pq))
        (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq)) := by
  refine ShortComplex.isoMk
    (pageXIso X data _ hr _ _ _ _ _ _ (by have := data.hc r pq pq' hpq; lia) _ _ _ _
      rfl rfl rfl rfl)
    (pageXIso X data _ hr _ _ _ _ _ _ hn₂' _ _ _ _
      (by rw [data.hc₀₂ r pq' pq'' hpq']) (by rw [data.hc₁₃ r pq' pq'' hpq'])
      (by rw [data.hc₀₂ r pq pq' hpq]) (by rw [data.hc₁₃ r pq pq' hpq]))
    (pageXIso X data _ hr _ _ _ _ _ _ (by have := data.hc r pq' pq'' hpq'; lia)
        _ _ _ _ rfl rfl rfl rfl) ?_ ?_
  · dsimp
    rw [pageD_eq X data r hr pq pq' hpq, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    · exact (data.hc₀₂ r pq' pq'' hpq').symm
    · exact (data.hc₁₃ r pq' pq'' hpq').symm
  · dsimp
    rw [pageD_eq X data r hr pq' pq'' hpq', Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    · rfl
    · rfl

section

variable (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  (hn₁' : n₁ = data.deg pq')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' pq')
  (hi₀ : i₀ = data.i₀ r pq')
  (hi₁ : i₁ = data.i₁ pq')
  (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r pq')
  (hi₃' : i₃' = data.i₃ r' pq')

namespace HomologyData

lemma mk₃fac :
    fourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.le₀'₀ hrr' hr pq' hi₀' hi₀)
      (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂) (data.le₂₃' r hr pq' hi₂ hi₃) ≫
      fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃' _ _ _ (data.le₃₃' hrr' hr pq' hi₃ hi₃') =
    fourδ₄Toδ₃' i₀' i₁ i₂ i₃ i₃' _ _ _ (data.le₃₃' hrr' hr pq' hi₃ hi₃') ≫
      fourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃' (data.le₀'₀ hrr' hr pq' hi₀' hi₀) _ _ _ := by
  rfl

lemma kf_w :
    (X.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀' i₀ i₁ i₂ i₃ (data.le₀'₀ hrr' hr pq' hi₀' hi₀)
      (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂) (data.le₂₃' r hr pq' hi₂ hi₃) ≫
        (pageXIso X data _ hr _ _ _ _ _ _ hn₁' _ _ _ _ hi₀ hi₁ hi₂ hi₃).inv) ≫
          (page X data r hr).d pq' pq'' = 0 := by
  by_cases h : (c r).Rel pq' pq''
  · dsimp
    rw [pageD_eq X data r hr pq' pq'' h n₀ n₁ n₂ _ hn₁ hn₂ rfl
      (homOfLE (by simpa only [hi₀', data.i₀_prev r r' _ _ h] using data.le₀₁ r pq''))
      (homOfLE (data.le₀'₀ hrr' hr pq' hi₀' hi₀)) _ _ _ hn₁'
      rfl (by rw [hi₀', data.i₀_prev r r' pq' pq'' h]) hi₀ hi₁ hi₂ hi₃,
      Category.assoc, Iso.inv_hom_id_assoc]
    erw [EMap_fourδ₁Toδ₀_d_assoc, zero_comp]
  · rw [HomologicalComplex.shape _ _ _ h, comp_zero]

@[simp]
noncomputable def kf : KernelFork ((page X data r hr).d pq' pq'') :=
  KernelFork.ofι _ (kf_w X data r r' hrr' hr pq' pq'' n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃)

@[simps!]
noncomputable def ksSc : ShortComplex C :=
  ShortComplex.mk _ _ (kf_w X data r r' hrr' hr pq' pq'' n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃)

instance : Mono (ksSc X data r r' hrr' hr pq' pq'' n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃).f := by
  dsimp
  infer_instance

variable [X.HasSpectralSequence data] in
include hpq' hn₁' in
lemma isIso_EMapFourδ₁Toδ₀' (h : ¬ (c r).Rel pq' pq'') :
    IsIso (X.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂
      i₀' i₀ i₁ i₂ i₃ (data.le₀'₀ hrr' hr pq' hi₀' hi₀) (data.le₀₁' r hr pq' hi₀ hi₁)
        (data.le₁₂' pq' hi₁ hi₂) (data.le₂₃' r hr pq' hi₂ hi₃)) := by
  apply X.isIso_EMap_fourδ₁Toδ₀_of_isZero
  refine X.isZero_H_obj_mk₁_i₀_le' data r r' hrr' hr pq'
    (fun k hk ↦ ?_) _ (by lia) _ _ hi₀' hi₀
  obtain rfl := (c r).next_eq' hk
  subst hpq'
  exact h hk

variable [X.HasSpectralSequence data] in
include hpq' in
lemma ksSc_exact : (ksSc X data r r' hrr' hr pq' pq'' n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃).Exact := by
  by_cases h : (c r).Rel pq' pq''
  · refine ShortComplex.exact_of_iso (Iso.symm ?_)
      (X.dKernelSequence_exact n₀ n₁ n₂ _ hn₁ hn₂ rfl
        (homOfLE (show data.i₀ r pq'' ≤ i₀' by
          simpa only [hi₀', data.i₀_prev r r' _ _ h] using data.le₀₁ r pq''))
        (homOfLE (data.le₀'₀ hrr' hr pq' hi₀' hi₀)) (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
        (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃)) _ rfl)
    refine ShortComplex.isoMk (Iso.refl _)
      (pageXIso X data _ hr _ _ _ _ _ _ hn₁' _ _ _ _ hi₀ hi₁ hi₂ hi₃)
      (pageXIso X data _ hr _ _ _ _ _ _ (by have := data.hc r _ _ h; lia) _ _ _ _
      rfl (by rw [hi₀', data.i₀_prev r r' _ _ h]) (by rw [hi₀, data.hc₀₂ r _ _ h])
        (by rw [hi₁, data.hc₁₃ r _ _ h])) ?_ ?_
    · dsimp
      rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · dsimp
      rw [pageD_eq X data r hr pq' pq'' h n₀ n₁ n₂ _ hn₁ hn₂ rfl
        (homOfLE (show data.i₀ r pq'' ≤ i₀' by
          simpa only [hi₀', data.i₀_prev r r' _ _ h] using data.le₀₁ r pq'')),
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · rfl
      · rw [hi₀', data.i₀_prev r r' _ _ h]
  · rw [ShortComplex.exact_iff_epi]; swap
    · exact (page X data r hr).shape _ _ h
    have := isIso_EMapFourδ₁Toδ₀' X data r r' hrr' hr pq' pq'' hpq' n₀ n₁ n₂ hn₁ hn₂
      hn₁' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ h
    apply epi_comp

variable [X.HasSpectralSequence data] in
noncomputable def hkf :
    IsLimit (kf X data r r' hrr' hr pq' pq'' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃) :=
  (ksSc_exact X data r r' hrr' hr pq' pq'' hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃).fIsKernel

lemma cc_w :
    (page X data r hr).d pq pq' ≫
      (pageXIso  X data _ hr _ _ _ _ _ _ hn₁' _ _ _ _ hi₀ hi₁ hi₂ hi₃).hom ≫
      X.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₃' _ _ _
        (data.le₃₃' hrr' hr pq' hi₃ hi₃') = 0 := by
  by_cases h : (c r).Rel pq pq'
  · dsimp
    rw [pageD_eq X data r hr pq pq' h (n₀ - 1) n₀ n₁ n₂ (by simp) hn₁ hn₂ _
      _ (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃)) (homOfLE (data.le₃₃' hrr' hr pq' hi₃ hi₃'))
      (homOfLE (by simpa only [hi₃', data.i₃_next r r' _ _ h] using data.le₂₃ r pq))
      (by have := data.hc r pq pq' h; lia) hi₀ hi₁ (by rw [hi₂, data.hc₀₂ r _ _ h])
      (by rw [hi₃, data.hc₁₃ r _ _ h]) (by rw [hi₃', data.i₃_next r r' _ _ h]) rfl,
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    erw [d_EMap_fourδ₄Toδ₃]
    rw [comp_zero]
  · rw [HomologicalComplex.shape _ _ _ h, zero_comp]

@[simp]
noncomputable def cc : CokernelCofork ((page X data r hr).d pq pq') :=
  CokernelCofork.ofπ _
    (cc_w X data r r' hrr' hr pq pq' n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃')

@[simps!]
noncomputable def ccSc : ShortComplex C :=
  ShortComplex.mk _ _ (cc_w X data r r' hrr' hr pq pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃')

instance : Epi (ccSc X data r r' hrr' hr pq pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃').g := by
  refine @epi_comp _ _ _ _ _ _ inferInstance _ ?_
  apply epi_EMap
  all_goals rfl

variable [X.HasSpectralSequence data] in
include hpq hn₁' in
lemma isIso_EMapFourδ₄Toδ₃' (h : ¬ (c r).Rel pq pq') :
    IsIso (X.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₃'
      (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂)
      (data.le₂₃' r hr pq' hi₂ hi₃) (data.le₃₃' hrr' hr pq' hi₃ hi₃')) := by
  apply X.isIso_EMap_fourδ₄Toδ₃_of_isZero
  refine X.isZero_H_obj_mk₁_i₃_le' data r r' hrr' hr pq' ?_ _ (by lia) _ _ hi₃ hi₃'
  intro k hk
  obtain rfl := (c r).prev_eq' hk
  subst hpq
  exact h hk

variable [X.HasSpectralSequence data] in
include hpq in
lemma ccSc_exact :
    (ccSc X data r r' hrr' hr pq pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃').Exact := by
  by_cases h : (c r).Rel pq pq'
  · refine ShortComplex.exact_of_iso (Iso.symm ?_)
      (X.dCokernelSequence_exact (n₀ - 1) n₀ n₁ n₂ (by simp) hn₁ hn₂
      (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
      (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃))
      (homOfLE (data.le₃₃' hrr' hr pq' hi₃ hi₃'))
      (show i₃' ⟶ data.i₃ r pq from homOfLE (by
        simpa only [hi₃', data.i₃_next r r' _ _ h] using data.le₂₃ r pq)) _ rfl)
    refine ShortComplex.isoMk
      (pageXIso X data _ hr _ _ _ _ _ _ (by have := data.hc r _ _ h; lia) _ _ _ _
        (by rw [hi₂, data.hc₀₂ r _ _ h]) (by rw [hi₃, data.hc₁₃ r _ _ h])
        (by rw [hi₃', data.i₃_next r r' _ _ h]) rfl)
      (pageXIso X data _ hr _ _ _ _ _ _ hn₁' _ _ _ _ hi₀ hi₁ hi₂ hi₃) (Iso.refl _) ?_ ?_
    · dsimp
      rw [pageD_eq X data r hr pq pq' h (n₀ - 1) n₀ n₁ n₂ (by simp) hn₁ hn₂,
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · exact hi₀
      · exact hi₁
    · dsimp
      rw [Category.comp_id, Iso.cancel_iso_hom_left]
  · rw [ShortComplex.exact_iff_mono]; swap
    · exact (page X data r hr).shape _ _ h
    have := isIso_EMapFourδ₄Toδ₃' X data r r' hrr' hr pq pq' hpq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' h
    dsimp
    infer_instance

variable [X.HasSpectralSequence data] in
noncomputable def hcc :
    IsColimit (cc X data r r' hrr' hr pq pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃') :=
  (ccSc_exact X data r r' hrr' hr pq pq' hpq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃').gIsCokernel

lemma fac :
  (kf X data r r' hrr' hr pq' pq'' n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃).ι ≫
      (cc X data r r' hrr' hr pq pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
        i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃').π  =
    X.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀' i₁ i₂ i₃ i₃' _ _ _ (data.le₃₃' hrr' hr pq' hi₃ hi₃') ≫
      X.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀' i₀ i₁ i₂ i₃'
        (data.le₀'₀ hrr' hr pq' hi₀' hi₀) _ _ _ := by
  dsimp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, EMap_comp] using
    congr_arg (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _)
      (mk₃fac data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃')

end HomologyData

variable [X.HasSpectralSequence data]

open HomologyData in
/-- The homology data for the short complex given by differentials on the
`r`th page of the spectral sequence which shows that the homology identifies
to an object on the next page. -/
@[simps!]
noncomputable def homologyData : ((page X data r hr).sc' pq pq' pq'').HomologyData :=
  ShortComplex.HomologyData.ofEpiMonoFactorisation
    ((page X data r hr).sc' pq pq' pq'')
    (hkf X data r r' hrr' hr pq' pq'' hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃)
    (hcc X data r r' hrr' hr pq pq' hpq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃')
    (fac X data r r' hrr' hr pq pq' pq'' n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀' i₀ i₁ i₂ i₃ i₃'
      hi₀' hi₀ hi₁ hi₂ hi₃ hi₃')

/-- The homology of the differentials on a page of the spectral sequence identifies
to the objects on the next page. -/
noncomputable def homologyIso' :
    ((page X data r hr).sc' pq pq' pq'').homology ≅ (page X data r' (by lia)).X pq' :=
  (homologyData X data r r' hrr' hr pq pq' pq'' hpq hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃').left.homologyIso ≪≫
      (pageXIso X data _ (by lia) _ _ _ _ _ _ hn₁' _ _ _ _ hi₀' hi₁ hi₂ hi₃').symm

/-- The homology of the differentials on a page of the spectral sequence identifies
to the objects on the next page. -/
noncomputable def homologyIso :
    (page X data r hr).homology pq' ≅
      (page X data r' (hr.trans (by rw [← hrr']; exact Int.le.intro 1 rfl))).X pq' :=
  homologyIso' X data r r' hrr' hr _ pq' _ rfl rfl
    (data.deg pq' - 1) (data.deg pq') (data.deg pq' + 1) (by simp)
    rfl rfl _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl

end

end

end SpectralSequence

section

variable [X.HasSpectralSequence data] in
/-- The spectral sequence attached to a spectral object in an abelian category. -/
noncomputable def spectralSequence : SpectralSequence C c r₀ where
  page := SpectralSequence.page X data
  iso r r' pq hrr' hr := SpectralSequence.homologyIso X data r r' hrr' hr pq

variable [X.HasSpectralSequence data]

/-- The objects on the pages of a spectral sequence attached to a spectral object `X`
identifies an object `X.E`. -/
noncomputable def spectralSequencePageXIso (r : ℤ) (hr : r₀ ≤ r)
    (pq : κ) (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (h : n₁ = data.deg pq)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq)
    (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h₃ : i₃ = data.i₃ r pq) :
    ((X.spectralSequence data).page r).X pq ≅
      X.E n₀ n₁ n₂ hn₁ hn₂
        (homOfLE (data.le₀₁' r hr pq h₀ h₁))
        (homOfLE (data.le₁₂' pq h₁ h₂))
        (homOfLE (data.le₂₃' r hr pq h₂ h₃)) :=
  SpectralSequence.pageXIso X data _ hr _ _ _ _ _ _ h _ _ _ _ h₀ h₁ h₂ h₃

lemma spectralSequence_page_d_eq (r : ℤ) (hr : r₀ ≤ r)
    (pq pq' : κ) (hpq : (c r).Rel pq pq')
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (hn₁' : n₁ = data.deg pq)
    (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ pq')
    (h₂ : i₂ = data.i₀ r pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r pq) :
    ((X.spectralSequence data).page r).d pq pq' =
      (X.spectralSequencePageXIso data r hr _ _ _ _ _ _ hn₁' _ _ _ _ h₂ h₃ h₄ h₅).hom ≫
      X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ ≫
      (X.spectralSequencePageXIso data r hr _ _ _ _ _ _
        (by simpa only [← hn₂, hn₁'] using data.hc r pq pq' hpq) _ _ _ _ h₀ h₁
        (by rw [h₂, ← data.hc₀₂ r pq pq' hpq])
        (by rw [h₃, data.hc₁₃ r pq pq' hpq])).inv :=
  SpectralSequence.pageD_eq _ _ _ hr _ _ hpq ..

lemma isZero_spectralSequence_page_X_iff (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (h : n₁ = data.deg pq)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq)
    (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h₃ : i₃ = data.i₃ r pq) :
    IsZero (((X.spectralSequence data).page r).X pq) ↔
      IsZero (X.E n₀ n₁ n₂ hn₁ hn₂
        (homOfLE (data.le₀₁' r hr pq h₀ h₁))
        (homOfLE (data.le₁₂' pq h₁ h₂))
        (homOfLE (data.le₂₃' r hr pq h₂ h₃))) :=
  Iso.isZero_iff (X.spectralSequencePageXIso data r hr pq n₀ n₁ n₂ hn₁ hn₂ h i₀ i₁ i₂ i₃
    h₀ h₁ h₂ h₃)

lemma isZero_spectralSequence_page_X_of_isZero_H (r : ℤ) (hr : r₀ ≤ r)
    (pq : κ) (n : ℤ) (hn : n = data.deg pq)
    (i₁ i₂ : ι) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h : IsZero ((X.H n).obj
      (mk₁ (homOfLE (by simpa only [h₁, h₂] using data.le₁₂ pq) : i₁ ⟶ i₂)))) :
    IsZero (((X.spectralSequence data).page r).X pq) := by
  rw [X.isZero_spectralSequence_page_X_iff data r hr pq (n - 1) n (n + 1) (by simp) rfl hn
    _ i₁ i₂ _ rfl h₁ h₂ rfl]
  apply isZero_E_of_isZero_H
  exact h

/-- isZero_spectralSequence_page_X_of_isZero_H' -/
lemma isZero_spectralSequence_page_X_of_isZero_H' (r : ℤ) (hr : r₀ ≤ r)
    (pq : κ)
    (h : IsZero ((X.H (data.deg pq)).obj (mk₁ (homOfLE (data.le₁₂ pq))))) :
    IsZero (((X.spectralSequence data).page r).X pq) :=
  X.isZero_spectralSequence_page_X_of_isZero_H data r hr pq _ rfl _ _ rfl rfl h

section
variable (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  (hn₁' : n₁ = data.deg pq')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' pq')
  (hi₀ : i₀ = data.i₀ r pq')
  (hi₁ : i₁ = data.i₁ pq')
  (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r pq')
  (hi₃' : i₃' = data.i₃ r' pq')

/-- The homology data for the short complexes given by the differentials
of a spectral sequence attached to a spectral object in an abelian category. -/
@[simps! left_K left_H left_π right_Q right_H right_ι iso_hom iso_inv]
noncomputable def spectralSequenceHomologyData :
    (((X.spectralSequence data).page r hr).sc' pq pq' pq'').HomologyData :=
  SpectralSequence.homologyData X data r r' hrr' hr
    pq pq' pq'' hpq hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'

@[simp]
lemma spectralSequenceHomologyData_left_i :
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃').left.i =
        X.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀' i₀ i₁ i₂ i₃
          (data.le₀'₀ hrr' hr pq' hi₀' hi₀) _ _ _  ≫
          (X.spectralSequencePageXIso data r hr pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
              i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃).inv := rfl

@[simp]
lemma spectralSequenceHomologyData_right_p :
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃').right.p =
        (X.spectralSequencePageXIso data r hr pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
          i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃).hom ≫
          X.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₃' _ _ _
            (data.le₃₃' hrr' hr pq' hi₃ hi₃') := rfl

lemma spectralSequenceHomologyData_right_homologyIso_eq_left_homologyIso :
  (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃').right.homologyIso =
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃').left.homologyIso := by
  ext1
  simp [ShortComplex.HomologyData.right_homologyIso_eq_left_homologyIso_trans_iso]

end

end

section

variable (Y : SpectralObject C EInt)

/-- The `E₂` cohomologial spectral sequence indexed by `ℤ × ℤ` attached to
a first quadrant spectral object indexed by `EInt`. -/
noncomputable abbrev E₂SpectralSequence : E₂CohomologicalSpectralSequence C :=
  Y.spectralSequence mkDataE₂Cohomological

section

variable [Y.IsFirstQuadrant]

example (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hq : q < 0) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) := by
  apply isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr
  apply Y.isZero₁_of_isFirstQuadrant
  simp
  lia

example (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hp : p < 0) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) := by
  apply isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr
  apply Y.isZero₂_of_isFirstQuadrant
  simp
  lia

/-- The `E₂` cohomologial spectral sequence indexed by `ℕ × ℕ` attached to
a first quadrant spectral object indexed by `EInt`. -/
noncomputable abbrev E₂SpectralSequenceNat := Y.spectralSequence mkDataE₂CohomologicalNat

end

section

variable [Y.IsThirdQuadrant]

example (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hq : 0 < q) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) := by
  apply isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr
  apply Y.isZero₁_of_isThirdQuadrant
  simp
  lia

example (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hp : 0 < p) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) := by
  apply isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr
  apply Y.isZero₂_of_isThirdQuadrant
  simp
  lia

/-- The `E₂` homologial spectral sequence indexed by `ℕ × ℕ` attached to
a third quadrant spectral object indexed by `EInt`. -/
noncomputable abbrev E₂HomologicalSpectralSequenceNat := Y.spectralSequence mkDataE₂HomologicalNat

end

end

end SpectralObject

end Abelian

end CategoryTheory
