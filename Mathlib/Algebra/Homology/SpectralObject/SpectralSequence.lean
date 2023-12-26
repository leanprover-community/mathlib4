import Mathlib.Algebra.Homology.SpectralObject.Homology
import Mathlib.Algebra.Homology.SpectralSequenceNew.Basic
import Mathlib.Algebra.Homology.SpectralSequenceNew.ZTilde

namespace ComplexShape

variable {ι : Type*} [DecidableEq ι]  [AddRightCancelSemigroup ι]

instance (u : ι) : DecidableRel (ComplexShape.up' u).Rel := fun _ _ => by
  dsimp [up']
  infer_instance

end ComplexShape

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
  antitone_i₀ (r r' : ℤ) (hr : r₀ ≤ r) (hrr' : r ≤ r') (pq : κ) :
      i₀ r' (by linarith) pq ≤ i₀ r hr pq
  monotone_i₃ (r r' : ℤ) (hr : r₀ ≤ r) (hrr' : r ≤ r') (pq : κ) :
      i₃ r hr pq ≤ i₃ r' (by linarith) pq
  i₀_prev' (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq') :
      i₀ (r + 1) (by linarith) pq = i₁ pq'
  i₃_next' (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq') :
      i₃ (r + 1) (by linarith) pq' = i₂ pq

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
  antitone_i₀ r r' hr hrr' pq := by
    dsimp
    simp only [ℤt.mk_le_mk_iff]
    linarith
  monotone_i₃ r r' hr hrr' pq := by
    dsimp
    simp only [ℤt.mk_le_mk_iff]
    linarith
  i₀_prev' := by
    rintro r hr pq _ rfl
    dsimp
    congr 1
    linarith
  i₃_next' := by
    rintro r hr pq _ rfl
    dsimp
    congr 1
    linarith

@[simps!]
def mkDataE₂CohomologicalNat :
    SpectralSequenceMkData ℤt
    (fun r => ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩) 2 where
  deg pq := pq.1 + pq.2
  i₀ r hr pq := ℤt.mk (pq.2 - r + 2)
  i₁ pq := ℤt.mk pq.2
  i₂ pq := ℤt.mk (pq.2 + 1)
  i₃ r hr pq := ℤt.mk (pq.2 + r - 1)
  le₀₁ r hr pq := by dsimp; simp only [ℤt.mk_le_mk_iff]; linarith
  le₁₂ pq := by dsimp; simp only [ℤt.mk_le_mk_iff]; linarith
  le₂₃ r hr pq := by dsimp; simp only [ℤt.mk_le_mk_iff]; linarith
  hc r _ pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    dsimp
    linarith
  hc₀₂ r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    dsimp
    congr 1
    linarith
  hc₁₃ r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    dsimp
    congr 1
    linarith
  antitone_i₀ r r' hrr' hr pq := by
    dsimp
    rw [ℤt.mk_le_mk_iff]
    linarith
  monotone_i₃ r r' hrr' hr pq := by
    dsimp
    rw [ℤt.mk_le_mk_iff]
    linarith
  i₀_prev' r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    dsimp
    congr 1
    linarith
  i₃_next' r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    dsimp
    congr 1
    linarith

variable {ι c r₀}
variable (data : SpectralSequenceMkData ι c r₀)

namespace SpectralSequenceMkData

lemma i₀_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    data.i₀ r' (by linarith) pq ≤ data.i₀ r hr pq := by
  apply data.antitone_i₀
  linarith

lemma i₃_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    data.i₃ r hr pq ≤ data.i₃ r' (by linarith) pq := by
  apply data.monotone_i₃
  linarith

lemma i₀_prev (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq pq' : κ)
    (hpq : (c r).Rel pq pq') :
    data.i₀ r' (by linarith) pq = data.i₁ pq' := by
  subst hrr'
  exact data.i₀_prev' r hr pq pq' hpq

lemma i₃_next (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq pq' : κ)
    (hpq : (c r).Rel pq pq') :
    data.i₃ r' (by linarith) pq' = data.i₂ pq := by
  subst hrr'
  exact data.i₃_next' r hr pq pq' hpq

end SpectralSequenceMkData

class HasSpectralSequence : Prop where
  isZero_H_obj_mk₁_i₀_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq pq'))
    (n : ℤ) (hn : n = data.deg pq + 1) :
      IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₀_le r r' hrr' hr pq))))
  isZero_H_obj_mk₁_i₃_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq' pq))
    (n : ℤ) (hn : n = data.deg pq - 1) :
      IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₃_le r r' hrr' hr pq))))

variable [X.HasSpectralSequence data]

lemma isZero_H_obj_mk₁_i₀_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq pq'))
    (n : ℤ) (hn : n = data.deg pq + 1) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₀_le r r' hrr' hr pq)))) :=
  HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' hrr' hr pq hpq n hn

lemma isZero_H_obj_mk₁_i₀_le' (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq pq'))
    (n : ℤ) (hn : n = data.deg pq + 1) (i₀' i₀ : ι)
    (hi₀' : i₀' = data.i₀ r' (by linarith) pq)
    (hi₀ : i₀ = data.i₀ r hr pq) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (show i₀' ≤ i₀ by
      simpa only [hi₀', hi₀] using data.i₀_le r r' hrr' hr pq)))) := by
  subst hi₀' hi₀
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' hrr' hr pq hpq n hn

lemma isZero_H_obj_mk₁_i₃_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq' pq))
    (n : ℤ) (hn : n = data.deg pq - 1) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₃_le r r' hrr' hr pq)))) :=
  HasSpectralSequence.isZero_H_obj_mk₁_i₃_le r r' hrr' hr pq hpq n hn

lemma isZero_H_obj_mk₁_i₃_le' (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq' pq))
    (n : ℤ) (hn : n = data.deg pq - 1) (i₃ i₃' : ι)
    (hi₃ : i₃ = data.i₃ r hr pq)
    (hi₃' : i₃' = data.i₃ r' (by linarith) pq) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (show i₃ ≤ i₃' by
      simpa only [hi₃, hi₃'] using data.i₃_le r r' hrr' hr pq)))) := by
  subst hi₃ hi₃'
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₃_le r r' hrr' hr pq hpq n hn

namespace SpectralSequence

instance (E : SpectralObject C ℤt) : E.HasSpectralSequence mkDataE₂Cohomological where
  isZero_H_obj_mk₁_i₀_le r r' hrr' hr pq hpq := by
    exfalso
    exact hpq _ rfl
  isZero_H_obj_mk₁_i₃_le r r' hrr' hr pq hpq := by
    exfalso
    exact hpq (pq - (r, 1-r)) (by simp)

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

section

variable [X.HasSpectralSequence data]

variable (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  (hn₁' : n₁ = data.deg pq')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' (hr.trans ((@Int.le_add_one r r (le_refl _)).trans hrr'.le)) pq')
  (hi₀ : i₀ = data.i₀ r hr pq')
  (hi₁ : i₁ = data.i₁ pq')
  (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r hr pq')
  (hi₃' : i₃' = data.i₃ r' (hr.trans ((@Int.le_add_one r r (le_refl _)).trans hrr'.le)) pq')

namespace HomologyData

def f₁ : i₀' ⟶ i₀ := homOfLE (by simpa only [hi₀, hi₀'] using data.i₀_le r r' hrr' hr pq')
def f₂ : i₀ ⟶ i₁ := homOfLE (by simpa only [hi₀, hi₁] using data.le₀₁ r hr pq')
def f₃ : i₁ ⟶ i₂ := homOfLE (by simpa only [hi₁, hi₂] using data.le₁₂ pq')
def f₄ : i₂ ⟶ i₃ := homOfLE (by simpa only [hi₂, hi₃] using data.le₂₃ r hr pq')
def f₅ : i₃ ⟶ i₃' := homOfLE (by simpa only [hi₃, hi₃'] using data.i₃_le r r' hrr' hr pq')

noncomputable def mk₃i :=
  fourδ₁Toδ₀ (f₁ data r r' hrr' hr pq' i₀' i₀ hi₀' hi₀)
    (f₂ data r hr pq' i₀ i₁ hi₀ hi₁)
    (f₃ data pq' i₁ i₂ hi₁ hi₂) (f₄ data r hr pq' i₂ i₃ hi₂ hi₃) _ rfl

noncomputable def mk₃π :=
  fourδ₄Toδ₃ (f₁ data r r' hrr' hr pq' i₀' i₀ hi₀' hi₀ ≫ f₂ data r hr pq' i₀ i₁ hi₀ hi₁)
    (f₃ data pq' i₁ i₂ hi₁ hi₂) (f₄ data r hr pq' i₂ i₃ hi₂ hi₃)
    (f₅ data r r' hrr' hr pq' i₃ i₃' hi₃ hi₃') _ rfl

noncomputable def mk₃p :=
  fourδ₄Toδ₃
    (f₂ data r hr pq' i₀ i₁ hi₀ hi₁) (f₃ data pq' i₁ i₂ hi₁ hi₂)
    (f₄ data r hr pq' i₂ i₃ hi₂ hi₃) (f₅ data r r' hrr' hr pq' i₃ i₃' hi₃ hi₃') _ rfl

noncomputable def mk₃ι :=
  fourδ₁Toδ₀ (f₁ data r r' hrr' hr pq' i₀' i₀ hi₀' hi₀) (f₂ data r hr pq' i₀ i₁ hi₀ hi₁) (f₃ data pq' i₁ i₂ hi₁ hi₂)
    (f₄ data r hr pq' i₂ i₃ hi₂ hi₃ ≫ f₅ data r r' hrr' hr pq' i₃ i₃' hi₃ hi₃') _ rfl

instance : Mono (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
    (mk₃i data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃)) := by
  dsimp only [mk₃i]
  infer_instance

instance : Epi (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
    (mk₃p data r r' hrr' hr pq' i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃')) := by
  dsimp only [mk₃p]
  infer_instance

instance : Epi (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
    (mk₃π data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃')) := by
  dsimp only [mk₃π]
  infer_instance

instance : Mono (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
    (mk₃ι data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃')) := by
  dsimp only [mk₃ι]
  infer_instance

lemma mk₃fac :
    mk₃i data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ ≫
      mk₃p data r r' hrr' hr pq' i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' =
    mk₃π data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' ≫
      mk₃ι data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' := by
  rfl

lemma kf_w :
    (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
      (mk₃i data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃) ≫
        (pageXIso X data _ _ _ _ _ _ _ _ hn₁' _ _ _ _ hi₀ hi₁ hi₂ hi₃).inv) ≫
      (page X data r hr).d pq' pq'' = 0 := by
  by_cases h : (c r).Rel pq' pq''
  · dsimp [mk₃i]
    rw [paged_eq X data r hr pq' pq'' h n₀ n₁ n₂ _ hn₁ hn₂ rfl
      (homOfLE (by simpa only [hi₀', data.i₀_prev r r' hrr' hr _ _ h] using data.le₀₁ r hr pq''))
      (f₁ data r r' hrr' hr pq' i₀' i₀ hi₀' hi₀) (f₂ data r hr pq' i₀ i₁ hi₀ hi₁)
      (f₃ data pq' i₁ i₂ hi₁ hi₂) (f₄ data r hr pq' i₂ i₃ hi₂ hi₃) hn₁'
      rfl (by rw [hi₀', data.i₀_prev r r' hrr' hr pq' pq'' h]) hi₀ hi₁ hi₂ hi₃,
      assoc, Iso.inv_hom_id_assoc, EMap_fourδ₁Toδ₀_d_assoc, zero_comp]
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

lemma isIso_EMap_mk₃i (h : ¬ (c r).Rel pq' pq'') :
    IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
      (mk₃i data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃)) := by
  apply X.isIso_EMap_fourδ₁Toδ₀_of_isZero
  refine X.isZero_H_obj_mk₁_i₀_le' data r r' hrr' hr pq' ?_ _
    (by linarith) _ _ hi₀' hi₀
  intro k hk
  obtain rfl := (c r).next_eq' hk
  subst hpq'
  exact h hk

lemma ksSc_exact : (ksSc X data r r' hrr' hr pq' pq'' n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃).Exact := by
  by_cases h : (c r).Rel pq' pq''
  · refine ShortComplex.exact_of_iso (Iso.symm ?_)
      (X.dKernelSequence_exact n₀ n₁ n₂ _ hn₁ hn₂ rfl
        (homOfLE (show data.i₀ r hr pq'' ≤ i₀' by
          simpa only [hi₀', data.i₀_prev r r' hrr' hr _ _ h] using data.le₀₁ r hr pq''))
        (f₁ data r r' hrr' hr pq' i₀' i₀ hi₀' hi₀) (f₂ data r hr pq' i₀ i₁ hi₀ hi₁)
        (f₃ data pq' i₁ i₂ hi₁ hi₂) (f₄ data r hr pq' i₂ i₃ hi₂ hi₃) _ rfl)
    refine ShortComplex.isoMk (Iso.refl _)
      (pageXIso X data _ _ _ _ _ _ _ _ hn₁' _ _ _ _ hi₀ hi₁ hi₂ hi₃)
      (pageXIso X data _ _ _ _ _ _ _ _ (by linarith [data.hc r hr _ _ h]) _ _ _ _
        rfl (by rw [hi₀', data.i₀_prev r r' hrr' hr _ _ h]) (by rw [hi₀, data.hc₀₂ r hr _ _ h])
        (by rw [hi₁, data.hc₁₃ r hr _ _ h])) ?_ ?_
    · dsimp
      rw [id_comp, assoc, Iso.inv_hom_id, comp_id]
      rfl
    · dsimp
      rw [paged_eq X data r hr pq' pq'' h n₀ n₁ n₂ _ hn₁ hn₂ rfl
        (homOfLE (show data.i₀ r hr pq'' ≤ i₀' by
          simpa only [hi₀', data.i₀_prev r r' hrr' hr _ _ h] using data.le₀₁ r hr pq''))
        (f₁ data r r' hrr' hr pq' i₀' i₀ hi₀' hi₀) (f₂ data r hr pq' i₀ i₁ hi₀ hi₁)
        (f₃ data pq' i₁ i₂ hi₁ hi₂) (f₄ data r hr pq' i₂ i₃ hi₂ hi₃), assoc, assoc,
        Iso.inv_hom_id, comp_id]
  · rw [ShortComplex.exact_iff_epi]; swap
    · exact (page X data r hr).shape _ _ h
    have := isIso_EMap_mk₃i X data r r' hrr' hr pq' pq'' hpq' n₀ n₁ n₂ hn₁ hn₂
      hn₁' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ h
    apply epi_comp

noncomputable def hkf :
    IsLimit (kf X data r r' hrr' hr pq' pq'' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃) :=
  (ksSc_exact X data r r' hrr' hr pq' pq'' hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃).fIsKernel

lemma cc_w :
    (page X data r hr).d pq pq' ≫
      (pageXIso  X data _ _ _ _ _ _ _ _ hn₁' _ _ _ _ hi₀ hi₁ hi₂ hi₃).hom ≫
      X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
        (mk₃p data r r' hrr' hr pq' i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃') = 0 := by
  by_cases h : (c r).Rel pq pq'
  · dsimp [mk₃p]
    rw [paged_eq X data r hr pq pq' h (n₀ - 1) n₀ n₁ n₂ (by simp) hn₁ hn₂
       (f₂ data r hr pq' i₀ i₁ hi₀ hi₁)
      (f₃ data pq' i₁ i₂ hi₁ hi₂) (f₄ data r hr pq' i₂ i₃ hi₂ hi₃)
      (f₅ data r r' hrr' hr pq' i₃ i₃' hi₃ hi₃')
      (homOfLE (by simpa only [hi₃', data.i₃_next r r' hrr' hr _ _ h] using data.le₂₃ r hr pq))
      (by linarith [data.hc r hr pq pq' h]) hi₀ hi₁ (by rw [hi₂, data.hc₀₂ r hr _ _ h])
      (by rw [hi₃, data.hc₁₃ r hr _ _ h]) (by rw [hi₃', data.i₃_next r r' hrr' hr _ _ h]) rfl,
      assoc, assoc, Iso.inv_hom_id_assoc]
    dsimp
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

lemma isIso_EMap_mk₃p (h : ¬ (c r).Rel pq pq') :
    IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
      (mk₃p data r r' hrr' hr pq' i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃')) := by
  apply X.isIso_EMap_fourδ₄Toδ₃_of_isZero
  refine X.isZero_H_obj_mk₁_i₃_le' data r r' hrr' hr pq' ?_ _ (by linarith) _ _ hi₃ hi₃'
  intro k hk
  obtain rfl := (c r).prev_eq' hk
  subst hpq
  exact h hk

lemma ccSc_exact :
    (ccSc X data r r' hrr' hr pq pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃').Exact := by
  by_cases h : (c r).Rel pq pq'
  · refine ShortComplex.exact_of_iso (Iso.symm ?_)
      (X.dCokernelSequence_exact (n₀ - 1) n₀ n₁ n₂ (by simp) hn₁ hn₂
      (f₂ data r hr pq' i₀ i₁ hi₀ hi₁)
      (f₃ data pq' i₁ i₂ hi₁ hi₂) (f₄ data r hr pq' i₂ i₃ hi₂ hi₃)
      (f₅ data r r' hrr' hr pq' i₃ i₃' hi₃ hi₃')
      (show i₃' ⟶ data.i₃ r hr pq from homOfLE (by
        simpa only [hi₃', data.i₃_next r r' hrr' hr _ _ h] using data.le₂₃ r hr pq)) _ rfl)
    refine ShortComplex.isoMk
      (pageXIso X data _ _ _ _ _ _ _ _ (by linarith [data.hc r hr _ _ h]) _ _ _ _
        (by rw [hi₂, data.hc₀₂ r hr _ _ h]) (by rw [hi₃, data.hc₁₃ r hr _ _ h])
        (by rw [hi₃', data.i₃_next r r' hrr' hr _ _ h]) rfl)
      (pageXIso X data _ _ _ _ _ _ _ _ hn₁' _ _ _ _ hi₀ hi₁ hi₂ hi₃) (Iso.refl _) ?_ ?_
    · dsimp
      rw [paged_eq X data r hr pq pq' h (n₀ - 1) n₀ n₁ n₂ (by simp) hn₁ hn₂
        (f₂ data r hr pq' i₀ i₁ hi₀ hi₁) (f₃ data pq' i₁ i₂ hi₁ hi₂)
        (f₄ data r hr pq' i₂ i₃ hi₂ hi₃) (f₅ data r r' hrr' hr pq' i₃ i₃' hi₃ hi₃'),
        assoc, assoc, Iso.inv_hom_id, comp_id]
    · dsimp
      rw [comp_id, Iso.cancel_iso_hom_left]
      rfl
  · rw [ShortComplex.exact_iff_mono]; swap
    · exact (page X data r hr).shape _ _ h
    have := isIso_EMap_mk₃p X data r r' hrr' hr pq pq' hpq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' h
    exact @mono_comp _ _ _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ this)

noncomputable def hcc :
    IsColimit (cc X data r r' hrr' hr pq pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃') :=
  (ccSc_exact X data r r' hrr' hr pq pq' hpq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃').gIsCokernel

lemma fac :
    (kf X data r r' hrr' hr pq' pq'' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃).ι ≫
      (cc X data r r' hrr' hr pq pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
        i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃').π =
    X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
      (mk₃π data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃') ≫
    X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _
      (mk₃ι data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃') := by
  dsimp
  simpa only [assoc, Iso.inv_hom_id_assoc, EMap_comp] using
    congr_arg (X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _)
      (mk₃fac data r r' hrr' hr pq' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃')

end HomologyData

open HomologyData in
@[simps!]
noncomputable def homologyData : ((page X data r hr).sc' pq pq' pq'').HomologyData :=
  ShortComplex.HomologyData.ofEpiMonoFactorisation
    ((page X data r hr).sc' pq pq' pq'')
    (hkf X data r r' hrr' hr pq' pq'' hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃)
    (hcc X data r r' hrr' hr pq pq' hpq n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃')
    (fac X data r r' hrr' hr pq pq' pq'' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃')

noncomputable def homologyIso' :
    ((page X data r hr).sc' pq pq' pq'').homology ≅ (page X data r' (by linarith)).X pq' :=
  (homologyData X data r r' hrr' hr pq pq' pq'' hpq hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃').left.homologyIso ≪≫
      (pageXIso X data _ _ _ _ _ _ _ _ hn₁' _ _ _ _ hi₀' hi₁ hi₂ hi₃').symm

noncomputable def homologyIso :
    (page X data r hr).homology pq' ≅ (page X data r' (by linarith)).X pq' :=
  homologyIso' X data r r' hrr' hr _ pq' _ rfl rfl
    (data.deg pq' - 1) (data.deg pq') (data.deg pq' + 1) (by simp)
    rfl rfl _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl

end

end

end SpectralSequence

section

variable [X.HasSpectralSequence data]

noncomputable def spectralSequence : SpectralSequence C c r₀ where
  page' := SpectralSequence.page X data
  iso' r r' hrr' pq hr := SpectralSequence.homologyIso X data r r' hrr' hr pq

noncomputable def spectralSequencePageXIso (r : ℤ) [(X.spectralSequence data).HasPage r]
    (pq : κ) (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (h : n₁ = data.deg pq)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r ((X.spectralSequence data).le_of_hasPage r) pq)
    (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h₃ : i₃ = data.i₃ r ((X.spectralSequence data).le_of_hasPage r) pq) :
    ((X.spectralSequence data).page r).X pq ≅
      X.E n₀ n₁ n₂ hn₁ hn₂
        (homOfLE' i₀ i₁ (by subst h₀ h₁; exact data.le₀₁ r _ pq))
        (homOfLE' i₁ i₂ (by subst h₁ h₂; exact data.le₁₂ pq))
        (homOfLE' i₂ i₃ (by subst h₂ h₃; exact data.le₂₃ r _ pq)) :=
  SpectralSequence.pageXIso X data _ _ _ _ _ _ _ _ h _ _ _ _ h₀ h₁ h₂ h₃

lemma spectralSequence_page_d_eq (r : ℤ) [(X.spectralSequence data).HasPage r]
    (pq pq' : κ) (hpq : (c r).Rel pq pq')
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (hn₁' : n₁ = data.deg pq)
    (h₀ : i₀ = data.i₀ r ((X.spectralSequence data).le_of_hasPage r) pq') (h₁ : i₁ = data.i₁ pq')
    (h₂ : i₂ = data.i₀ r ((X.spectralSequence data).le_of_hasPage r) pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r ((X.spectralSequence data).le_of_hasPage r) pq) :
    ((X.spectralSequence data).page r).d pq pq' =
      (X.spectralSequencePageXIso data _ _ _ _ _ _ _ hn₁' _ _ _ _ h₂ h₃ h₄ h₅).hom ≫
        X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ ≫
        (X.spectralSequencePageXIso data _ _ _ _ _ _ _
          (by simpa only [← hn₂, hn₁'] using
            data.hc r ((X.spectralSequence data).le_of_hasPage r) pq pq' hpq) _ _ _ _ h₀ h₁
          (by rw [h₂, data.hc₀₂ r _ pq pq' hpq]) (by rw [h₃, data.hc₁₃ r _ pq pq' hpq])).inv := by
  apply SpectralSequence.paged_eq
  exact hpq

lemma isZero_spectralSequence_page_X_iff (r : ℤ) [(X.spectralSequence data).HasPage r] (pq : κ)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (h : n₁ = data.deg pq)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r ((X.spectralSequence data).le_of_hasPage r) pq)
    (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h₃ : i₃ = data.i₃ r ((X.spectralSequence data).le_of_hasPage r) pq) :
    IsZero (((X.spectralSequence data).page r).X pq) ↔
      IsZero (X.E n₀ n₁ n₂ hn₁ hn₂
        (homOfLE' i₀ i₁ (by subst h₀ h₁; exact data.le₀₁ r _ pq))
        (homOfLE' i₁ i₂ (by subst h₁ h₂; exact data.le₁₂ pq))
        (homOfLE' i₂ i₃ (by subst h₂ h₃; exact data.le₂₃ r _ pq))) :=
  Iso.isZero_iff (X.spectralSequencePageXIso data r pq n₀ n₁ n₂ hn₁ hn₂ h i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃)

lemma isZero_spectralSequence_page_X_of_isZero_H (r : ℤ)
    [(X.spectralSequence data).HasPage r] (pq : κ) (n : ℤ) (hn : n = data.deg pq)
    (i₁ i₂ : ι) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h : IsZero ((X.H n).obj
      (mk₁ (homOfLE' i₁ i₂ (by simpa only [h₁, h₂] using data.le₁₂ pq))))) :
    IsZero (((X.spectralSequence data).page r).X pq) := by
  rw [X.isZero_spectralSequence_page_X_iff data r pq (n - 1) n (n + 1) (by simp) rfl hn
    _ i₁ i₂ _ rfl h₁ h₂ rfl]
  apply isZero_E_of_isZero_H
  exact h

lemma isZero_spectralSequence_page_X_of_isZero_H' (r : ℤ)
    [(X.spectralSequence data).HasPage r] (pq : κ)
    (h : IsZero ((X.H (data.deg pq)).obj (mk₁ (homOfLE (data.le₁₂ pq))))) :
    IsZero (((X.spectralSequence data).page r).X pq) :=
  X.isZero_spectralSequence_page_X_of_isZero_H data r pq _ rfl _ _ rfl rfl h

section
variable (r r' : ℤ) (hrr' : r + 1 = r') [(X.spectralSequence data).HasPage r]
  [(X.spectralSequence data).HasPage r']
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  (hn₁' : n₁ = data.deg pq')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' ((X.spectralSequence data).le_of_hasPage r') pq')
  (hi₀ : i₀ = data.i₀ r ((X.spectralSequence data).le_of_hasPage r) pq')
  (hi₁ : i₁ = data.i₁ pq')
  (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r ((X.spectralSequence data).le_of_hasPage r) pq')
  (hi₃' : i₃' = data.i₃ r' ((X.spectralSequence data).le_of_hasPage r') pq')

@[simps! left_K left_H left_π  right_Q right_H right_ι iso_hom iso_inv]
noncomputable def spectralSequenceHomologyData :
    (((X.spectralSequence data).page r).sc' pq pq' pq'').HomologyData :=
  SpectralSequence.homologyData X data r r' hrr' ((X.spectralSequence data).le_of_hasPage r)
    pq pq' pq'' hpq hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'

@[simp]
lemma spectralSequenceHomologyData_left_i :
    (X.spectralSequenceHomologyData data r r' hrr' pq pq' pq'' hpq hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃').left.i =
        X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ (fourδ₁Toδ₀ _ _ _ _ _ rfl) ≫
          (X.spectralSequencePageXIso data r pq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
            i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃).inv := rfl

@[simp]
lemma spectralSequenceHomologyData_right_p :
    (X.spectralSequenceHomologyData data r r' hrr' pq pq' pq'' hpq hpq' n₀ n₁ n₂ hn₁ hn₂ hn₁'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃').right.p =
        (X.spectralSequencePageXIso data r pq' n₀ n₁ n₂ hn₁ hn₂ hn₁' i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃).hom ≫
          X.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ (fourδ₄Toδ₃ _ _ _ _ _ rfl) := rfl

end

end

section

variable (Y : SpectralObject C ℤt)

class IsFirstQuadrant : Prop where
  isZero₁ (i j : ℤt) (hij : i ≤ j) (hj : j ≤ ℤt.mk 0) (n : ℤ) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))
  isZero₂ (i j : ℤt) (hij : i ≤ j) (n : ℤ) (hi : ℤt.mk n < i) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))

variable [Y.IsFirstQuadrant]

lemma isZero₁_of_isFirstQuadrant (i j : ℤt) (hij : i ≤ j) (hj : j ≤ ℤt.mk 0) (n : ℤ) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) :=
  IsFirstQuadrant.isZero₁ i j hij  hj n

lemma isZero₂_of_isFirstQuadrant (i j : ℤt) (hij : i ≤ j) (n : ℤ) (hi : ℤt.mk n < i) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) :=
  IsFirstQuadrant.isZero₂ i j hij n hi

noncomputable abbrev E₂SpectralSequence := Y.spectralSequence mkDataE₂Cohomological

example (r : ℤ) [Y.E₂SpectralSequence.HasPage r] (p q : ℤ) (hq : q < 0) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) := by
  apply isZero_spectralSequence_page_X_of_isZero_H'
  apply Y.isZero₁_of_isFirstQuadrant
  dsimp
  simp only [ℤt.mk_le_mk_iff]
  linarith

example (r : ℤ) [Y.E₂SpectralSequence.HasPage r] (p q : ℤ) (hp : p < 0) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) := by
  apply isZero_spectralSequence_page_X_of_isZero_H'
  apply Y.isZero₂_of_isFirstQuadrant
  dsimp
  simp only [ℤt.mk_lt_mk_iff]
  linarith

instance : Y.HasSpectralSequence mkDataE₂CohomologicalNat where
  isZero_H_obj_mk₁_i₀_le := by
    rintro r _ rfl hr ⟨p, q⟩ hpq n rfl
    apply isZero₁_of_isFirstQuadrant
    dsimp
    simp only [ℤt.mk_le_mk_iff]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ p + r by linarith)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ q + 1 - r by linarith)
    exact hpq ⟨p', q'⟩ (by
      simp only [ComplexShape.spectralSequenceNat_rel_iff]
      constructor <;> linarith)
  isZero_H_obj_mk₁_i₃_le := by
    rintro r _ rfl hr ⟨p, q⟩ hpq n rfl
    apply isZero₂_of_isFirstQuadrant
    dsimp
    simp only [ℤt.mk_lt_mk_iff]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ p - r by linarith)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ q - 1 + r by linarith)
    exact hpq ⟨p', q'⟩ (by
      simp only [ComplexShape.spectralSequenceNat_rel_iff]
      constructor <;> linarith)

noncomputable abbrev E₂SpectralSequenceNat := Y.spectralSequence mkDataE₂CohomologicalNat

end

end SpectralObject

end Abelian

end CategoryTheory
