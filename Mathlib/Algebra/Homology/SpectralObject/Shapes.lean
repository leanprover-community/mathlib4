/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Algebra.Homology.SpectralSequence.ComplexShape
public import Mathlib.Data.EInt.Basic
public import Batteries.Tactic.Lint

/-!
# Shapes of spectral sequences obtained from a spectral object

-/

/-!
# The spectral sequence of a spectral object

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (c : ℤ → ComplexShape κ) (r₀ : ℤ)

--/-- Given an abelian category `C`, a sequence of complex shapes `c : ℤ → ComplexShape ι`
--and a starting page `r₀ : ℤ`, a spectral sequence involves pages which are homological
--complexes and isomorphisms saying that the homology of a page identifies to the next page. -/

variable (ι)

/-- This data is a recipe in order to produce a spectral sequence starting on
page `r₀` (where the `r`th page is of shape `c r`) from a spectral object
indexed by `ι`. The object on page `r` at the position `pq : κ` shall be
`E^(deg pq)(i₀ ≤ i₁ ≤ i₂ ≤ i₃)`, where `i₀ ≤ i₁ ≤ i₂ ≤ i₃` are elements in the
index type `ι` of the spectral object and `deg pq : ℤ` is a cohomological degree.
The indices `i₀` and `i₃` depends on `r` and `pq`, but `i₁`, `i₂` only depend on `pq`.
Various conditions are added in order to construct the differentials on the pages
and show that the homology of a page identifies to the next page. The spectral sequence
shall be defined when additional conditions are satisfied by the spectral object
(see the typeclass `SpectralObject.HasSpectralSequence`). -/
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
      i₀ r' (by lia) pq ≤ i₀ r hr pq
  monotone_i₃ (r r' : ℤ) (hr : r₀ ≤ r) (hrr' : r ≤ r') (pq : κ) :
      i₃ r hr pq ≤ i₃ r' (by lia) pq
  i₀_prev' (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq') :
      i₀ (r + 1) (by lia) pq = i₁ pq'
  i₃_next' (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq') :
      i₃ (r + 1) (by lia) pq' = i₂ pq

namespace SpectralSequenceMkData

variable {ι c r₀} (data : SpectralSequenceMkData ι c r₀)

lemma i₀_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    data.i₀ r' (by lia) pq ≤ data.i₀ r hr pq := by
  apply data.antitone_i₀
  lia

lemma i₃_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    data.i₃ r hr pq ≤ data.i₃ r' (by lia) pq := by
  apply data.monotone_i₃
  lia

lemma i₀_prev (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq pq' : κ)
    (hpq : (c r).Rel pq pq') :
    data.i₀ r' (by lia) pq = data.i₁ pq' := by
  subst hrr'
  exact data.i₀_prev' r hr pq pq' hpq

lemma i₃_next (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq pq' : κ)
    (hpq : (c r).Rel pq pq') :
    data.i₃ r' (by lia) pq' = data.i₂ pq := by
  subst hrr'
  exact data.i₃_next' r hr pq pq' hpq

end SpectralSequenceMkData

/-- The data which allows to construct an `E₂`-cohomological spectral sequence
indexed by `ℤ × ℤ` from a spectral object indexed by `EInt`. -/
@[simps!]
def mkDataE₂Cohomological :
    SpectralSequenceMkData EInt (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 2 where
  deg pq := pq.1 + pq.2
  i₀ r hr pq := EInt.mk (pq.2 - r + 2)
  i₁ pq := EInt.mk pq.2
  i₂ pq := EInt.mk (pq.2 + 1)
  i₃ r hr pq := EInt.mk (pq.2 + r - 1)
  le₀₁ r hr pq := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r hr pq := by simp; lia
  hc := by rintro r _ pq _ rfl; dsimp; lia
  hc₀₂ := by rintro r hr pq _ rfl; simp; lia
  hc₁₃ := by rintro r hr pq _ rfl; simp; lia
  antitone_i₀ r r' hr hrr' pq := by simp; lia
  monotone_i₃ r r' hr hrr' pq := by simp; lia
  i₀_prev' := by rintro r hr pq _ rfl; dsimp; lia
  i₃_next' := by rintro r hr pq _ rfl; dsimp; lia

/-- The data which allows to construct an `E₂`-cohomological spectral sequence
indexed by `ℕ × ℕ` from a spectral object indexed by `EInt`. (Note: additional
assumptions on the spectral object are required.) -/
@[simps!]
def mkDataE₂CohomologicalNat :
    SpectralSequenceMkData EInt
    (fun r ↦ ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩) 2 where
  deg pq := pq.1 + pq.2
  i₀ r hr pq := EInt.mk (pq.2 - r + 2)
  i₁ pq := EInt.mk pq.2
  i₂ pq := EInt.mk (pq.2 + 1)
  i₃ r hr pq := EInt.mk (pq.2 + r - 1)
  le₀₁ r hr pq := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r hr pq := by simp; lia
  hc r _ pq pq' hpq := by simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq; lia
  hc₀₂ r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  hc₁₃ r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  antitone_i₀ r r' hrr' hr pq := by simp; lia
  monotone_i₃ r r' hrr' hr pq := by simp; lia
  i₀_prev' r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  i₃_next' r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia

-- to be moved
lemma _root_.Fin.clamp_le_clamp {a b : ℕ} (h : a ≤ b) (m : ℕ) :
    Fin.clamp a m ≤ Fin.clamp b m := by
  rw [Fin.le_iff_val_le_val]
  exact min_le_min_right m h

/-- The data which allows to construct an `E₂`-cohomological spectral sequence
indexed by `ℤ × Fin l` from a spectral object indexed by `Fin (l + 1)`. -/
@[simps deg i₀ i₁ i₂ i₃]
def mkDataE₂CohomologicalFin (l : ℕ) :
    SpectralSequenceMkData (Fin (l + 1))
    (fun r ↦ ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩) 2 where
  deg pq := pq.1 + pq.2.1
  i₀ r hr pq := ⟨(pq.2.1 - (r - 2)).toNat, by grind⟩
  i₁ pq := pq.2.castSucc
  i₂ pq := pq.2.succ
  i₃ r hr pq := Fin.clamp (pq.2.1 + (r - 1)).toNat _
  le₀₁ r hr := by rintro ⟨p, q, hq⟩; simp; lia
  le₁₂ pq := by simp [Fin.le_iff_val_le_val]
  le₂₃ r hr pq := by
    simp only [Fin.le_iff_val_le_val, Fin.val_succ, le_min_iff, Fin.clamp]
    grind
  hc _ _ _ _ := fun ⟨h₁, h₂⟩ ↦ by lia
  hc₀₂ r hr := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩
    ext
    grind
  hc₁₃ r hr := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩
    rw [Fin.ext_iff]
    dsimp at h₁ h₂ ⊢
    grind
  antitone_i₀ r r' hr hrr' := by
    rintro ⟨a, ⟨a', _⟩⟩
    dsimp
    rw [Fin.mk_le_mk]
    lia
  monotone_i₃ r r' hr hrr' := by
    rintro ⟨a, ⟨a', _⟩⟩
    dsimp
    rw [Fin.mk_le_mk]
    apply Fin.clamp_le_clamp
    lia
  i₀_prev' r hr := by
    rintro ⟨a, ⟨a', _⟩⟩ ⟨b, ⟨b', _⟩⟩ ⟨h₁, h₂⟩
    ext
    dsimp at h₁ h₂ ⊢
    lia
  i₃_next' r hr := by
    rintro ⟨a, ⟨a', _⟩⟩ ⟨b, ⟨b', _⟩⟩ ⟨h₁, h₂⟩
    ext
    dsimp at h₁ h₂ ⊢
    grind

/-- The data which allows to construct an `E₂`-homological spectral sequence
indexed by `ℕ × ℕ` from a spectral object indexed by `EInt`. (Note: additional
assumptions on the spectral object are required.) -/
@[simps!]
def mkDataE₂HomologicalNat :
    SpectralSequenceMkData EInt
    (fun r ↦ ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 2 where
  deg pq := - pq.1 - pq.2
  i₀ r hr pq := EInt.mk (-pq.2 - r + 2)
  i₁ pq := EInt.mk (-pq.2)
  i₂ pq := EInt.mk (-pq.2 + 1)
  i₃ r hr pq := EInt.mk (-pq.2 + r - 1)
  le₀₁ r hr pq := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r hr pq := by simp; lia
  hc r _ pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  hc₀₂ r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  hc₁₃ r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  antitone_i₀ r r' hrr' hr pq := by simp; lia
  monotone_i₃ r r' hrr' hr pq := by simp; lia
  i₀_prev' r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  i₃_next' r hr pq pq' hpq := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia

end SpectralObject

end Abelian

end CategoryTheory
