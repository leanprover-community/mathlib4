import Mathlib.Algebra.Homology.SpectralObject.Homology
import Mathlib.Algebra.Homology.SpectralSequenceNew.Basic
import Mathlib.Algebra.Homology.SpectralSequenceNew.ZTilde

namespace CategoryTheory

open Category Limits ComposableArrows

abbrev homOfLE' {ι : Type*} [Preorder ι] (a b : ι) (h : a ≤ b) : a ⟶ b := homOfLE h

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  (c : ℤ → ComplexShape κ) (r₀ : ℤ)
  [∀ r, DecidableRel (c r).Rel]

variable (ι)

structure SpectralSequenceMkData where
  deg : κ → ℤ
  i₀ (r : ℤ) (hr : r₀ ≤ r) (pq : κ) : ι
  i₁ (pq : κ) : ι
  i₂ (pq : κ) : ι
  i₃ (r : ℤ) (hr : r₀ ≤ r) (pq : κ) : ι
  le₀₁ (r : ℤ) (hr : r₀ ≤ r) (pq : κ) : i₀ r hr pq ≤ i₁ pq
  le₁₂ (pq : κ) : i₁ pq ≤ i₂ pq
  le₂₃ (r : ℤ) (hr : r₀ ≤ r) (pq : κ) : i₂ pq ≤ i₃ r hr pq
  hc (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq') : deg pq + 1 = deg pq'
  hc₀₂ (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq') : i₀ r hr pq = i₂ pq'
  hc₁₃ (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq') : i₁ pq = i₃ r hr pq'

@[simps!]
def mkDataE₂Cohomological :
    SpectralSequenceMkData ℤt (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 2 where
  deg pq := pq.1 + pq.2
  i₀ r hr pq := ℤt.mk (pq.2 - r + 2)
  i₁ pq := ℤt.mk pq.2
  i₂ pq := ℤt.mk (pq.2 + 1)
  i₃ r hr pq := ℤt.mk (pq.2 + r - 1)
  le₀₁ r hr pq := by dsimp; simp only [ℤt.mk_le_mk_iff]; linarith
  le₁₂ pq := by dsimp; simp only [ℤt.mk_le_mk_iff]; linarith
  le₂₃ r hr pq := by dsimp; simp only [ℤt.mk_le_mk_iff]; linarith
  hc := by rintro r _ pq _ rfl; dsimp; linarith
  hc₀₂ := by rintro r hr pq _ rfl; dsimp; congr 1; linarith
  hc₁₃ := by rintro r hr pq _ rfl; dsimp; congr 1; linarith

variable {ι c r₀}

variable (data : SpectralSequenceMkData ι c r₀)

namespace SpectralSequenceMkData

class HasFirstPageComputation : Prop where
  hi₀₁ (pq : κ) : data.i₀ r₀ (by rfl) pq = data.i₁ pq
  hi₂₃ (pq : κ) : data.i₂ pq = data.i₃ r₀ (by rfl) pq

instance : mkDataE₂Cohomological.HasFirstPageComputation where
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


class HasHomologyComputationBasic : Prop where
  prev_rel (r : ℤ) (hr : r₀ ≤ r) (pq : κ) : (c r).Rel ((c r).prev pq) pq
  rel_next (r : ℤ) (hr : r₀ ≤ r) (pq : κ) : (c r).Rel pq ((c r).next pq)
  i₀_prev' (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq') :
      data.i₀ (r + 1) (by linarith) pq = data.i₁ pq'
  i₃_next' (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq') :
      data.i₃ (r + 1) (by linarith) pq' = data.i₂ pq

section

variable [hdata : data.HasHomologyComputationBasic]

lemma prev_rel (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (c r).Rel ((c r).prev pq) pq :=
  hdata.prev_rel r hr pq

lemma rel_next (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (c r).Rel pq ((c r).next pq) :=
  hdata.rel_next r hr pq

lemma i₀_prev (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq pq' : κ)
    (hpq : (c r).Rel pq pq') :
    data.i₀ r' (by linarith) pq = data.i₁ pq' := by
  subst hrr'
  exact HasHomologyComputationBasic.i₀_prev' r hr pq pq' hpq

lemma i₃_next (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq pq' : κ)
    (hpq : (c r).Rel pq pq') :
    data.i₃ r' (by linarith) pq' = data.i₂ pq := by
  subst hrr'
  exact HasHomologyComputationBasic.i₃_next' r hr pq pq' hpq

end

end SpectralSequenceMkData

namespace SpectralSequence

noncomputable def pageX (r : ℤ) (hr : r₀ ≤ r) (pq : κ) : C :=
  X.E (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by simp) rfl
      (homOfLE (data.le₀₁ r hr pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r hr pq))

noncomputable def pageXIso (r : ℤ) (hr : r₀ ≤ r) (pq : κ) (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (h : n₁ = data.deg pq)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r hr pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r hr pq) :
    pageX X data r hr pq ≅ X.E n₀ n₁ n₂ hn₁ hn₂
      (homOfLE' i₀ i₁ (by subst h₀ h₁; exact data.le₀₁ r hr pq))
      (homOfLE' i₁ i₂ (by subst h₁ h₂; exact data.le₁₂ pq))
      (homOfLE' i₂ i₃ (by subst h₂ h₃; exact data.le₂₃ r hr pq)) :=
  eqToIso (by
    obtain rfl : n₀ = n₁ - 1 := by linarith
    subst h hn₂ h₀ h₁ h₂ h₃
    rfl)

noncomputable def paged (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) :
    pageX X data r hr pq ⟶ pageX X data r hr pq' :=
  if hpq : (c r).Rel pq pq'
    then
      X.d (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (data.deg pq + 2) _ rfl
        (by linarith) (homOfLE (data.le₀₁ r hr pq'))
        (homOfLE (by simpa only [data.hc₀₂ r hr pq pq' hpq] using data.le₁₂ pq'))
        (homOfLE (data.le₀₁ r hr pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r hr pq)) ≫
      (pageXIso _ _ _ _ _ _ _ _ _ _ (data.hc r hr pq pq' hpq) _ _ _ _ rfl rfl
        (data.hc₀₂ r hr pq pq' hpq) (data.hc₁₃ r hr pq pq' hpq)).inv
    else 0

lemma paged_eq (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq')
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (hn₁' : n₁ = data.deg pq)
    (h₀ : i₀ = data.i₀ r hr pq') (h₁ : i₁ = data.i₁ pq') (h₂ : i₂ = data.i₀ r hr pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r hr pq) :
    paged X data r hr pq pq' = by
      refine'
        (pageXIso _ _ _ _ _ _ _ _ _ _ hn₁' _ _ _ _ h₂ h₃ h₄ h₅).hom ≫
        X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ ≫
        (pageXIso _ _ _ _ _ _ _ _ _ _
          (by simpa only [← hn₂, hn₁'] using data.hc r hr pq pq' hpq) _ _ _ _ h₀ h₁
          (by rw [h₂, data.hc₀₂ r hr pq pq' hpq])
          (by rw [h₃, data.hc₁₃ r hr pq pq' hpq])).inv := by
  subst hn₁' h₀ h₁ h₂ h₃ h₄ h₅
  obtain rfl : n₀ = data.deg pq - 1 := by linarith
  obtain rfl : n₂ = data.deg pq + 1 := by linarith
  obtain rfl : n₃ = data.deg pq + 2 := by linarith
  dsimp [paged, pageXIso]
  rw [dif_pos hpq, id_comp]
  rfl

@[reassoc (attr := simp)]
lemma paged_paged (r : ℤ) (hr : r₀ ≤ r) (pq pq' pq'' : κ) :
    paged X data r hr pq pq' ≫ paged X data r hr pq' pq'' = 0 := by
  by_cases hpq : (c r).Rel pq pq'
  · by_cases hpq' : (c r).Rel pq' pq''
    · let f₁ := homOfLE (data.le₀₁ r hr pq'')
      let f₂ := homOfLE (data.le₁₂ pq'')
      let f₃ := homOfLE (data.le₂₃ r hr pq'')
      let f₄ : data.i₃ r hr pq'' ⟶ data.i₀ r hr pq := homOfLE (by
        simpa only [← data.hc₁₃ r hr pq' pq'' hpq',
          data.hc₀₂ r hr pq pq' hpq] using data.le₁₂ pq')
      let f₅ := homOfLE (data.le₀₁ r hr pq)
      let f₆ := homOfLE (data.le₁₂ pq)
      let f₇ := homOfLE (data.le₂₃ r hr pq)
      rw [paged_eq X data r hr pq pq' hpq (data.deg pq - 1) (data.deg pq) _ _ (by simp)
        rfl rfl f₃ f₄ f₅ f₆ f₇ rfl (data.hc₀₂ r hr pq' pq'' hpq').symm
        (data.hc₁₃ r hr pq' pq'' hpq').symm rfl rfl rfl rfl,
        paged_eq X data r hr pq' pq'' hpq' (data.deg pq) _ _ _ rfl rfl rfl f₁ f₂ f₃ f₄ f₅
        (data.hc r hr pq pq' hpq) rfl rfl (data.hc₀₂ r hr pq' pq'' hpq').symm
        (data.hc₁₃ r hr pq' pq'' hpq').symm (data.hc₀₂ r hr pq pq' hpq)
        (data.hc₁₃ r hr pq pq' hpq), assoc, assoc, Iso.inv_hom_id_assoc,
        d_d_assoc, zero_comp, comp_zero]
    · dsimp only [paged]
      rw [dif_neg hpq', comp_zero]
  · dsimp only [paged]
    rw [dif_neg hpq, zero_comp]

@[simps]
noncomputable def page (r : ℤ) (hr : r₀ ≤ r) :
    HomologicalComplex C (c r) where
  X pq := pageX X data r hr pq
  d := paged X data r hr
  shape pq pq' hpq := dif_neg hpq

section

variable [data.HasFirstPageComputation]

noncomputable def firstPageXIso (pq : κ) (n : ℤ) (hn : n = data.deg pq)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq) :
    (page X data r₀ (by rfl)).X pq ≅ (X.H n).obj (mk₁ (homOfLE' i₁ i₂
      (by simpa only [hi₁, hi₂] using data.le₁₂ pq))) :=
  pageXIso X data r₀ _ pq (n - 1) n (n + 1) _ rfl hn i₁ i₁ i₂ i₂
    (by rw [hi₁, data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) ≪≫
    X.EIsoH (n - 1) n (n + 1) (by simp) rfl (homOfLE _)

lemma firstPageXIso_hom (pq : κ) (n : ℤ) (hn : n = data.deg pq)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₂ : ℤ) (hn₀ : n₀ + 1 = n) (hn₂ : n + 1 = n₂) :
    (firstPageXIso X data pq n hn i₁ i₂ hi₁ hi₂).hom =
      (pageXIso X data r₀ _ _ _ _ _ _ _ hn _ _ _ _
        (by rw [hi₁, data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃])).hom ≫
        (X.EIsoH n₀ n n₂ hn₀ hn₂ _).hom := by
  obtain rfl : n₀ = n - 1 := by linarith
  obtain rfl := hn₂
  rfl

lemma firstPageXIso_inv (pq : κ) (n : ℤ) (hn : n = data.deg pq)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₂ : ℤ) (hn₀ : n₀ + 1 = n) (hn₂ : n + 1 = n₂) :
    (firstPageXIso X data pq n hn i₁ i₂ hi₁ hi₂).inv =
      (X.EIsoH n₀ n n₂ hn₀ hn₂ _).inv ≫
      (pageXIso X data r₀ _ _ _ _ _ _ _ hn _ _ _ _
        (by rw [hi₁, data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃])).inv := by
  obtain rfl : n₀ = n - 1 := by linarith
  obtain rfl := hn₂
  rfl

def first_page_d_eq (pq pq' : κ) (hpq : (c r₀).Rel pq pq') (n n' : ℤ) (hn : n = data.deg pq)
    (hn' : n + 1 = n') (i j k : ι)
    (hi : i = data.i₁ pq') (hj : j = data.i₁ pq) (hk : k = data.i₂ pq) :
    (page X data r₀ (by rfl)).d pq pq' =
      (firstPageXIso X data pq n hn j k hj hk).hom ≫ X.δ n n' hn' (homOfLE' i j
        (by simpa only [hi, hj, data.hc₁₃ r₀ (by rfl) pq pq' hpq, ← data.hi₂₃ pq']
          using data.le₁₂ pq'))
        (homOfLE' j k (by simpa only [hj, hk] using data.le₁₂ pq)) ≫
      (firstPageXIso X data pq' n'
        (by rw [← hn', hn, data.hc r₀ (by rfl) pq pq' hpq]) i j hi
        (by rw [hj, ← data.hc₀₂ r₀ (by rfl) pq pq' hpq, data.hi₀₁ pq])).inv := by
  dsimp
  simp only [assoc, firstPageXIso_hom X data pq n hn j k hj hk (n - 1) n' (by simp) hn',
    ← X.d_EIsoH_hom_assoc (n - 1) n n' (n' + 1) (by simp) hn' rfl,
    firstPageXIso_inv X data pq' n' (by rw [← hn', hn, data.hc r₀ (by rfl) pq pq' hpq]) i j
      hi (by rw [hj, data.hi₂₃, data.hc₁₃ r₀ (by rfl) pq pq' hpq]) n (n' + 1) hn' rfl,
    Iso.hom_inv_id_assoc]
  apply paged_eq
  exact hpq

end

section

noncomputable def shortComplexIso (r : ℤ) (hr : r₀ ≤ r) (pq pq' pq'' : κ)
    (hpq : (c r).Rel pq pq') (hpq' : (c r).Rel pq' pq'')
    (n₀ n₁ n₂ n₃ n₄ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) (hn₄ : n₃ + 1 = n₄)
    (hn₂' : n₂ = data.deg pq') :
    (page X data r hr).sc' pq pq' pq'' ≅
      X.dShortComplex n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ (homOfLE (data.le₀₁ r hr pq''))
        (homOfLE (data.le₁₂ pq'')) (homOfLE (data.le₂₃ r hr pq''))
        (homOfLE (by simpa only [← data.hc₁₃ r hr pq' pq'' hpq', data.hc₀₂ r hr pq pq' hpq]
          using data.le₁₂ pq')) (homOfLE (data.le₀₁ r hr pq))
        (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r hr pq)) := by
  refine ShortComplex.isoMk
    (pageXIso X data _ _ _ _ _ _ _ _ (by linarith [data.hc r hr pq pq' hpq])
      _ _ _ _ rfl rfl rfl rfl)
    (pageXIso X data _ _ _ _ _ _ _ _ hn₂' _ _ _ _
      (by rw [data.hc₀₂ r hr pq' pq'' hpq']) (by rw [data.hc₁₃ r hr pq' pq'' hpq'])
      (by rw [data.hc₀₂ r hr pq pq' hpq]) (by rw [data.hc₁₃ r hr pq pq' hpq]))
    (pageXIso X data _ _ _ _ _ _ _ _ (by linarith [data.hc r hr pq' pq'' hpq'])
        _ _ _ _ rfl rfl rfl rfl) ?_ ?_
  · dsimp
    rw [paged_eq X data r hr pq pq' hpq, assoc, assoc, Iso.inv_hom_id, comp_id]
  · dsimp
    rw [paged_eq X data r hr pq' pq'' hpq', assoc, assoc, Iso.inv_hom_id, comp_id]

variable [data.HasHomologyComputationBasic]

noncomputable def iso (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq pq' pq'' : κ) (hpq : (c r).Rel pq pq') (hpq' : (c r).Rel pq' pq'') :
    ((page X data r hr).sc' pq pq' pq'').homology ≅ (page X data r' (by linarith)).X pq' :=
  ShortComplex.homologyMapIso (shortComplexIso X data r hr pq pq' pq'' hpq hpq'
    (data.deg pq - 1) (data.deg pq) (data.deg pq') (data.deg pq'') (data.deg pq'' + 1)
    (by simp) (by linarith [data.hc r hr pq pq' hpq])
    (by linarith [data.hc r hr pq' pq'' hpq']) rfl rfl) ≪≫
  (X.dHomologyIso _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl _ rfl) ≪≫ (by
    symm
    apply pageXIso
    · rfl
    · exact (data.i₀_prev r r' hrr' hr pq' pq'' hpq').symm
    · exact (data.hc₁₃ r hr pq' pq'' hpq').symm
    · exact data.hc₀₂ r hr pq pq' hpq
    · exact (data.i₃_next r r' hrr' hr pq pq' hpq).symm)

end

end SpectralSequence

variable [data.HasHomologyComputationBasic]

noncomputable def spectralSequence : SpectralSequence C c r₀ where
  page' := SpectralSequence.page X data
  iso' r r' hrr' pq hr :=
    SpectralSequence.iso X data r r' hrr' hr
      ((c r).prev pq) pq ((c r).next pq) (data.prev_rel r hr pq) (data.rel_next r hr pq)

end SpectralObject

end Abelian

end CategoryTheory
