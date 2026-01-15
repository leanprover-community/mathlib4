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

This file prepares for the construction of the spectral sequence
of a spectral object in an abelian category which shall be conducted
in the file `Mathlib/Algebra/Homology/SpectralObject/SpectralSequence.lean`.

In this file, we introduce a structure `SpectralSequenceMkData` which
contains a recipe for the construction of the pages of the spectral sequence.
For example, from a spectral object `X` indexed by `EInt` the definition
`mkDataE₂Cohomological` will allow to construct an `E₂` cohomological
spectral sequence such that the object on position `(p, q)` on the `r`th
page is `E^{p + q}(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)`.
The data (and properties) in the structure `SpectralSequenceMkData` allow
to define the pages and the differentials directly from the `SpectralObject`
API from the files
`Mathlib/Algebra/Homology/SpectralObject/Page.lean` and
`Mathlib/Algebra/Homology/SpectralObject/Differentials.lean`.
However, the computation of the homology of the differentials in
`Mathlib/Algebra/Homology/SpectralObject/Homology.lean` may not directly
apply: we introduce a typeclass `HasSpectralSequence` which puts
additional conditions on the spectral object so that the homology of a
page identifies to the next page. These conditions are automatically
satisfied for `mkDataE₂Cohomological`, but this design allows
to obtain a spectral sequence with objects of the pages indexed
by `ℕ × ℕ` instead of `ℤ × ℤ` when suitable conditions are satisfied by
a spectral object indexed by `EInt` (see `mkDataE₂CohomologicalNat`
and the typeclass `IsFirstQuadrant`).

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
cases, additional conditions may be required on the spectral object,
see the typeclass `HasSpectralSequence`. -/
structure SpectralSequenceMkData where
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

namespace SpectralSequenceMkData

variable (data : SpectralSequenceMkData ι c r₀)

lemma i₀_le (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    data.i₀ r' pq ≤ data.i₀ r pq :=
  data.antitone_i₀ r r' pq

lemma i₃_le (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    data.i₃ r pq ≤ data.i₃ r' pq :=
  data.monotone_i₃ r r' pq

lemma le₀'₀ {r r' : ℤ} (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq' : κ)
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

end SpectralSequenceMkData

/-- The data which allows to construct an `E₂`-cohomological spectral sequence
indexed by `ℤ × ℤ` from a spectral object indexed by `EInt`. -/
@[simps!]
def mkDataE₂Cohomological :
    SpectralSequenceMkData EInt (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 2 where
  deg pq := pq.1 + pq.2
  i₀ r pq hr := (pq.2 - r + 2 :)
  i₁ pq := pq.2
  i₂ pq := (pq.2 + 1 :)
  i₃ r pq hr := (pq.2 + r - 1 :)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc := by rintro r pq _ rfl _; dsimp; lia
  hc₀₂ := by rintro r pq hr rfl _ ; simp; lia
  hc₁₃ := by rintro r pq hr rfl _; simp; lia
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev := by rintro r r' hr pq rfl _ _; dsimp; lia
  i₃_next := by rintro r r' hr pq rfl _ _; dsimp; lia

/-- The data which allows to construct an `E₂`-cohomological spectral sequence
indexed by `ℕ × ℕ` from a spectral object indexed by `EInt`. (Note: additional
assumptions on the spectral object are required.) -/
@[simps!]
def mkDataE₂CohomologicalNat :
    SpectralSequenceMkData EInt
    (fun r ↦ ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩) 2 where
  deg pq := pq.1 + pq.2
  i₀ r pq hr := (pq.2 - r + 2 :)
  i₁ pq := (pq.2 : ℤ)
  i₂ pq := (pq.2 + 1 : ℤ)
  i₃ r pq hr := (pq.2 + r - 1 : ℤ)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc r pq pq' hpq hr := by simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq; lia
  hc₀₂ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  hc₁₃ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  i₃_next r r' pq pq' hpq hrr' hr := by
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
  i₀ r pq hr := ⟨(pq.2.1 - (r - 2)).toNat, by grind⟩
  i₁ pq := pq.2.castSucc
  i₂ pq := pq.2.succ
  i₃ r pq hr := Fin.clamp (pq.2.1 + (r - 1)).toNat _
  le₀₁ := by rintro r ⟨p, q, hq⟩ hr; simp; lia
  le₁₂ pq := by simp [Fin.le_iff_val_le_val]
  le₂₃ r pq hr := by
    simp only [Fin.le_iff_val_le_val, Fin.val_succ, le_min_iff, Fin.clamp]
    grind
  hc _ _ _ := fun ⟨h₁, h₂⟩ ↦ by lia
  hc₀₂ r := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩ hr
    ext
    grind
  hc₁₃ r := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩ hr
    rw [Fin.ext_iff]
    dsimp at h₁ h₂ ⊢
    grind
  antitone_i₀ := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ hr hrr'
    dsimp
    rw [Fin.mk_le_mk]
    lia
  monotone_i₃ := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ hr hrr'
    dsimp
    rw [Fin.mk_le_mk]
    apply Fin.clamp_le_clamp
    lia
  i₀_prev := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ ⟨b, ⟨b', _⟩⟩ ⟨h₁, h₂⟩ hrr' hr
    ext
    dsimp at h₁ h₂ ⊢
    lia
  i₃_next := by
    rintro r r' ⟨a, ⟨a', _⟩⟩ ⟨b, ⟨b', _⟩⟩ ⟨h₁, h₂⟩ hrr' hr
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
  i₀ r pq hr := (-pq.2 - r + 2 :)
  i₁ pq := (-pq.2 : ℤ)
  i₂ pq := (-pq.2 + 1 : ℤ)
  i₃ r pq hr := (-pq.2 + r - 1 :)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  hc₀₂ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  hc₁₃ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  i₃_next r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia

variable (X : SpectralObject C ι) (data : SpectralSequenceMkData ι c r₀)

/-- Given `X : SpectralObject C ι` and `data : SpectralSequenceMkData ι c r₀`, this is
the property which allows to construct a spectral sequence by using the recipe given
by `data`. The conditions given allow to show that the homology of a page identifies
to the next page. -/
class HasSpectralSequence : Prop where
  isZero_H_obj_mk₁_i₀_le (r r' : ℤ) (pq : κ)
    (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq pq'))
    (n : ℤ) (hn : n = data.deg pq + 1 )
    (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
      IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₀_le r r' pq))))
  isZero_H_obj_mk₁_i₃_le (r r' : ℤ) (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq' pq))
    (n : ℤ) (hn : n = data.deg pq - 1)
    (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
      IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₃_le r r' pq))))

variable [X.HasSpectralSequence data]

lemma isZero_H_obj_mk₁_i₀_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq pq'))
    (n : ℤ) (hn : n = data.deg pq + 1) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₀_le r r' pq)))) :=
  HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn

/-- isZero_H_obj_mk₁_i₀_le' -/
lemma isZero_H_obj_mk₁_i₀_le' (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq pq'))
    (n : ℤ) (hn : n = data.deg pq + 1) (i₀' i₀ : ι)
    (hi₀' : i₀' = data.i₀ r' pq)
    (hi₀ : i₀ = data.i₀ r pq) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (show i₀' ≤ i₀ by
      simpa only [hi₀', hi₀] using data.i₀_le r r' pq)))) := by
  subst hi₀' hi₀
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn

lemma isZero_H_obj_mk₁_i₃_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq' pq))
    (n : ℤ) (hn : n = data.deg pq - 1) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (data.i₃_le r r' pq)))) :=
  HasSpectralSequence.isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn

/-- isZero_H_obj_mk₁_i₃_le' -/
lemma isZero_H_obj_mk₁_i₃_le' (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq' pq))
    (n : ℤ) (hn : n = data.deg pq - 1) (i₃ i₃' : ι)
    (hi₃ : i₃ = data.i₃ r pq)
    (hi₃' : i₃' = data.i₃ r' pq) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (show i₃ ≤ i₃' by
      simpa only [hi₃, hi₃'] using data.i₃_le r r' pq)))) := by
  subst hi₃ hi₃'
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn

instance (E : SpectralObject C EInt) : E.HasSpectralSequence mkDataE₂Cohomological where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq _ rfl
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq (pq - (r, 1-r)) (by simp)

lemma _root_.Fin.clamp_eq_last (n m : ℕ) (hnm : m ≤ n) :
    Fin.clamp n m = Fin.last _ := by
  ext
  simpa

instance {l : ℕ} (E : SpectralObject C (Fin (l + 1))) :
    E.HasSpectralSequence (mkDataE₂CohomologicalFin l) where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := by
    have : (mkDataE₂CohomologicalFin l).i₀ r' pq =
        (mkDataE₂CohomologicalFin l).i₀ r pq := by
      subst hrr'
      obtain ⟨k, rfl⟩ := Int.le.dest hr
      obtain ⟨p, q, hq⟩ := pq
      ext
      have h : q ≤ k := by
        by_contra!
        simp only [ComplexShape.spectralSequenceFin_rel_iff, not_and, Prod.forall] at hpq
        obtain ⟨t, rfl⟩ := Nat.le.dest (Nat.add_one_le_of_lt this)
        exact hpq _ ⟨t, by lia⟩ rfl (by simp; lia)
      simp_all
      lia
    have := isIso_homOfLE this
    apply E.isZero_H_map_mk₁_of_isIso
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := by
    have : (mkDataE₂CohomologicalFin l).i₃ r pq =
      (mkDataE₂CohomologicalFin l).i₃ r' pq := by
      subst hrr'
      obtain ⟨p, q, hq⟩ := pq
      have h : l < q + r := by
        by_contra!
        obtain ⟨t, ht⟩ := Int.le.dest this
        simp only [ComplexShape.spectralSequenceFin_rel_iff, not_and, Prod.forall] at hpq
        exact hpq (p - r) ⟨l - 1 - t, by lia⟩ (by lia) (by lia)
      dsimp
      rw [add_sub_cancel_right, Fin.clamp_eq_last _ _ (by lia),
        Fin.clamp_eq_last _ _ (by lia)]
    have := isIso_homOfLE this
    apply E.isZero_H_map_mk₁_of_isIso

section

variable (Y : SpectralObject C EInt)

/-- The conditions on a spectral object indexed by `EInt` which allow
to obtain a (convergent) first quadrant `E₂` cohomological spectral sequence. -/
class IsFirstQuadrant : Prop where
  isZero₁ (i j : EInt) (hij : i ≤ j) (hj : j ≤ (0 : ℤ)) (n : ℤ) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))
  isZero₂ (i j : EInt) (hij : i ≤ j) (n : ℤ) (hi : n < i) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))

variable [Y.IsFirstQuadrant]

lemma isZero₁_of_isFirstQuadrant (i j : EInt) (hij : i ≤ j) (hj : j ≤ (0 : ℤ)) (n : ℤ) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) :=
  IsFirstQuadrant.isZero₁ i j hij  hj n

lemma isZero₂_of_isFirstQuadrant (i j : EInt) (hij : i ≤ j) (n : ℤ) (hi : n < i) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) :=
  IsFirstQuadrant.isZero₂ i j hij n hi

instance : Y.HasSpectralSequence mkDataE₂CohomologicalNat where
  isZero_H_obj_mk₁_i₀_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₁_of_isFirstQuadrant
    dsimp
    simp only [WithBotTop.coe_le_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ p + r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ q + 1 - r by lia)
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)
  isZero_H_obj_mk₁_i₃_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₂_of_isFirstQuadrant
    dsimp
    simp only [WithBotTop.coe_lt_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ p - r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ q - 1 + r by lia)
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)

end

section

variable (Y : SpectralObject C EInt)

/-- The conditions on a spectral object indexed by `EInt` which allow
to obtain a (convergent) third quadrant `E₂` cohomological spectral sequence,
or a (convergent) first quadrant `E₂` *homological* spectral sequence -/
class IsThirdQuadrant where
  isZero₁ (i j : EInt) (hij : i ≤ j) (hi : (0 : ℤ) < i) (n : ℤ) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))
  isZero₂ (i j : EInt) (hij : i ≤ j) (n : ℤ) (hj : j ≤ n) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij)))

variable [Y.IsThirdQuadrant]

lemma isZero₁_of_isThirdQuadrant (i j : EInt) (hij : i ≤ j) (hi : (0 : ℤ) < i) (n : ℤ) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) :=
  IsThirdQuadrant.isZero₁ i j hij hi n

lemma isZero₂_of_isThirdQuadrant (i j : EInt) (hij : i ≤ j) (n : ℤ) (hj : j ≤ n) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) :=
  IsThirdQuadrant.isZero₂ i j hij n hj

instance : Y.HasSpectralSequence mkDataE₂HomologicalNat where
  isZero_H_obj_mk₁_i₀_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₂_of_isThirdQuadrant
    dsimp
    simp only [WithBotTop.coe_le_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ p - r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ q + r - 1 by lia)
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)
  isZero_H_obj_mk₁_i₃_le := by
    rintro r _ ⟨p, q⟩ hpq n rfl rfl hr
    apply isZero₁_of_isThirdQuadrant
    dsimp
    simp only [WithBotTop.coe_lt_coe]
    by_contra!
    obtain ⟨p', hp'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ p + r by lia)
    obtain ⟨q', hq'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ q + 1 - r by lia)
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    exact hpq ⟨p', q'⟩ (by constructor <;> lia)

end

end SpectralObject

end Abelian

end CategoryTheory
