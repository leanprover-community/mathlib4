/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Order.WithBotTop

/-!
# Shapes of spectral sequences obtained from a spectral object

This file prepares for the construction of the spectral sequence
of a spectral object in an abelian category which shall be conducted
in the file `Mathlib/Algebra/Homology/SpectralObject/SpectralSequence.lean` (TODO).

In this file, we introduce a structure `SpectralSequenceDataCore` which
contains a recipe for the construction of the pages of the spectral sequence.
For example, from a spectral object `X` indexed by `EInt` the definition
`coreE₂Cohomological` will allow to construct an `E₂` cohomological
spectral sequence such that the object on position `(p, q)` on the `r`th
page is `E^{p + q}(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)`.
The data (and properties) in the structure `SpectralSequenceDataCore` shall allow
to define the pages and the differentials directly from the `SpectralObject` API (TODO).

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (ι c r₀) in
/-- This data is a recipe in order to produce a spectral sequence starting on
page `r₀` (where the `r`th page is of shape `c r`) from a spectral object
indexed by `ι`. The object on page `r` at the position `pq : κ` shall be
`E^(deg pq)(i₀ ≤ i₁ ≤ i₂ ≤ i₃)`, where `i₀ ≤ i₁ ≤ i₂ ≤ i₃` are elements in the
index type `ι` of the spectral object and `deg pq : ℤ` is a cohomological degree.
The indices `i₀` and `i₃` depend on `r` and `pq`, but `i₁`, `i₂` only depend on `pq`.
Various conditions are added in order to construct the differentials on the pages
and show that the homology of a page identifies to the next page; in certain
cases, additional conditions may be required on the spectral object. -/
structure SpectralSequenceDataCore where
  /-- The cohomological degree of objects in the pages -/
  deg : κ → ℤ
  /-- The zeroth index -/
  i₀ (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : ι
  /-- The first index -/
  i₁ (pq : κ) : ι
  /-- The second index -/
  i₂ (pq : κ) : ι
  /-- The third index -/
  i₃ (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : ι
  le₀₁ (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : i₀ r pq ≤ i₁ pq
  le₁₂ (pq : κ) : i₁ pq ≤ i₂ pq
  le₂₃ (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : i₂ pq ≤ i₃ r pq
  hc (r : ℤ) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ ≤ r := by lia) : deg pq + 1 = deg pq'
  hc₀₂ (r : ℤ) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ ≤ r := by lia) : i₀ r pq = i₂ pq'
  hc₁₃ (r : ℤ) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ ≤ r := by lia) : i₁ pq = i₃ r pq'
  antitone_i₀ (r r' : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) (hrr' : r ≤ r' := by lia) :
      i₀ r' pq ≤ i₀ r pq
  monotone_i₃ (r r' : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) (hrr' : r ≤ r' := by lia) :
      i₃ r pq ≤ i₃ r' pq
  i₀_prev (r r' : ℤ) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hrr' : r + 1 = r' := by lia)
      (hr : r₀ ≤ r := by lia) :
      i₀ r' pq = i₁ pq'
  i₃_next (r r' : ℤ) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hrr' : r + 1 = r' := by lia)
      (hr : r₀ ≤ r := by lia) :
      i₃ r' pq' = i₂ pq

namespace SpectralSequenceDataCore

variable (data : SpectralSequenceDataCore ι c r₀)

lemma i₀_le (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    data.i₀ r' pq ≤ data.i₀ r pq :=
  data.antitone_i₀ r r' pq

lemma i₃_le (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    data.i₃ r pq ≤ data.i₃ r' pq :=
  data.monotone_i₃ r r' pq

lemma i₀_le' {r r' : ℤ} (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq' : κ)
    {i₀' i₀ : ι} (hi₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq') :
    i₀' ≤ i₀ := by
  rw [hi₀', hi₀]
  exact data.antitone_i₀ r r' pq'

lemma le₀₁' (r : ℤ) (hr : r₀ ≤ r) (pq' : κ) {i₀ i₁ : ι}
    (hi₀ : i₀ = data.i₀ r pq')
    (hi₁ : i₁ = data.i₁ pq') :
    i₀ ≤ i₁ := by
  have := data.le₀₁ r pq'
  simpa only [hi₀, hi₁] using data.le₀₁ r pq'

lemma le₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') :
    i₁ ≤ i₂ := by
  simpa only [hi₁, hi₂] using data.le₁₂ pq'

lemma le₂₃' (r : ℤ) (hr : r₀ ≤ r) (pq' : κ)
    {i₂ i₃ : ι}
    (hi₂ : i₂ = data.i₂ pq')
    (hi₃ : i₃ = data.i₃ r pq') :
    i₂ ≤ i₃ := by
  simpa only [hi₂, hi₃] using data.le₂₃ r pq'

lemma le₃₃' {r r' : ℤ} (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq' : κ)
    {i₃ i₃' : ι}
    (hi₃ : i₃ = data.i₃ r pq')
    (hi₃' : i₃' = data.i₃ r' pq') :
    i₃ ≤ i₃' := by
  simpa only [hi₃, hi₃'] using data.monotone_i₃ r r' pq'

end SpectralSequenceDataCore

/-- The data which allows to construct an `E₂`-cohomological spectral sequence
indexed by `ℤ × ℤ` from a spectral object indexed by `EInt`. -/
@[simps!]
def coreE₂Cohomological :
    SpectralSequenceDataCore EInt (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 2 where
  deg pq := pq.1 + pq.2
  i₀ r pq hr := (pq.2 - r + 2 :)
  i₁ pq := pq.2
  i₂ pq := (pq.2 + 1 :)
  i₃ r pq hr := (pq.2 + r - 1 :)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc := by rintro r pq _ rfl _; dsimp; lia
  hc₀₂ := by rintro r pq hr rfl _; simp; lia
  hc₁₃ := by rintro r pq hr rfl _; simp; lia
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev := by rintro r r' hr pq rfl _ _; dsimp; lia
  i₃_next := by rintro r r' hr pq rfl _ _; dsimp; lia

end SpectralObject

end Abelian

end CategoryTheory
