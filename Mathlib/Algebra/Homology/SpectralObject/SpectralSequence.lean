/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Homology
public import Mathlib.Algebra.Homology.SpectralObject.HasSpectralSequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Order.WithBotTop

/-!
# The spectral sequence of a spectral object

The main definition in this file is `Abelian.SpectralObject.spectralSequence`.
Assume that `X` is a spectral object indexed by `ι` in an abelian category `C`,
and that we have `data : SpectralSequenceDataCore ι c r₀` for a family
of complex shapes `c : ℤ → ComplexShape κ` for a type `κ` and `r₀ : ℤ`.
Then, under the assumption `X.HasSpectralSequence data` (see the file
`Mathlib/Algebra/Homology/SpectralObject/HasSpectralSequence.lean`),
we obtain `X.spectralSequence data` which is a spectral sequence starting
on page `r₀`, such that the `r`th page (for `r₀ ≤ r`) is a homological
complex of shape `c r`.

## Outline of the construction

The construction of the spectral sequence is as follows. If `r₀ ≤ r`
and `pq : κ`, we define the object of the spectral sequence in position `pq`
on the `r`th page as `E^d(i₀ r pq ≤ i₁ pq ≤ i₂ pq ≤ i₃ r pq)`
where `d := data.deg pq` and the indices `i₀`, `i₁`, `i₂`, `i₃` are given
by `data` (they all depend on `pq`, and `i₀` and `i₃` also depend on the page `r`),
see `spectralSequencePageXIso`.

When `(c r).Rel pq pq'`, the differential from the object in position `pq`
to the object in position `pq'` on the `r`th page can be related to
the differential `X.d` of the spectral object (see the lemma
`spectralSequence_page_d_eq`). Indeed, the assumptions that
are part of `data` give equalities of indices `i₂ r pq' = i₀ r pq`
and `i₃ pq' = i₁ pq`, so that we have a chain of inequalities
`i₀ r pq' ≤ i₁ pq' ≤ i₂ pq' ≤ i₃ r pq' ≤ i₂ pq ≤ i₃ r pq` for which
the API of spectral objects provides a differential
`X.d : E^n(i₀ r pq ≤ i₁ pq ≤ i₂ pq ≤ i₃ r pq) ⟶ E^{n + 1}(i₀ r pq' ≤ i₁ pq' ≤ i₂ pq' ≤ i₃ r pq')`.

Now, fix `r` and three positions `pq`, `pq'` and `pq''` such that
`pq` is the previous object of `pq'` for `c r` and `pq''` is the next
object of `pq'`. (Note that in case there are no nontrivial differentials
to the object `pq'` for the complex shape `c r`, according to the homological
complex API, we have `pq = pq'` and the differential is zero. Similarly,
when there are no nontrivial differentials from the object in position `pq'`,
we have `pq'' = pq` and the corresponding differential is zero.)
In the favourable case where both `(c r).Rel pq pq'` and `(c r).Rel pq' pq''`
hold, the definition `SpectralObject.SpectralSequence.shortComplexIso`
in this file can be used in combination to `SpectralObject.SpectralSequence.dHomologyIso`
in order to compute the homology of the differentials.)

In the general case, using the assumptions in `X.HasSpectralSequence data`,
we provide a limit kernel fork `kf` and
a limit cokernel cofork `cc` of the differentials on the `r`th page,
together with an epi-mono factorization `fac` which allows
to obtain that the homology of the `r`th page identifies to the next page (see the definitions
`SpectralObject.SpectralSequence.homologyData` and
`SpectralObject.spectralSequenceHomologyData`).

## Spectral objects indexed by `EInt`.

When `X` is a spectral object indexed by the extended integers `EInt`,
we obtain the `E₂`-cohomological spectral sequence
`X.E₂SpectralSequence` where the objects of each page are indexed by
`ℤ × ℤ` (the condition `HasSpectralSequence` is automatically satisfied).
Under the `X.IsFirstQuadrant` assumption, we obtain
`X.E₂SpectralSequenceNat` which is a first quadrant `E₂`-spectral
sequence (the objects in the pages are indexed by `ℕ × ℕ` instead
of `ℤ × ℤ`).

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

namespace SpectralSequence

/-- The object on position `pq` on the `r`th page of the spectral sequence. -/
noncomputable def pageX (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : C :=
  X.E (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)

/-- The object on position `pq` on the `r`th page of the spectral sequence identifies
to `E^{deg pq}(i₀ ≤ i₁ ≤ i₂ ≤ i₃)`. -/
noncomputable def pageXIso (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    pageX X data r pq hr ≅ X.E
      (homOfLE (data.le₀₁' r hr pq h₀ h₁))
      (homOfLE (data.le₁₂' pq h₁ h₂))
      (homOfLE (data.le₂₃' r hr pq h₂ h₃))
      n₀ n₁ n₂ hn₁ hn₂ :=
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
      X.d (homOfLE (data.le₀₁ r pq'))
        (homOfLE (data.le₁₂' pq' rfl (data.hc₀₂ r pq pq' hpq)))
        (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
        (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (data.deg pq + 2) ≫
      (pageXIso _ _ _ _ _ _ _ _ _ rfl rfl
        (data.hc₀₂ r pq pq' hpq) (data.hc₁₃ r pq pq' hpq) _ _ _ (data.hc r pq pq' hpq) rfl _).inv
    else 0

set_option backward.isDefEq.respectTransparency false in
lemma pageD_eq (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq')
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ pq') (h₂ : i₂ = data.i₀ r pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r pq)
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    pageD X data r pq pq' =
      (pageXIso _ _ _ _ _ _ _ _ _ h₂ h₃ h₄ h₅ _ _ _ hn₁' _ _).hom ≫
        X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
        (pageXIso _ _ _ _ _ _ _ _ _ h₀ h₁ (by rw [h₂, data.hc₀₂ r pq pq' hpq])
          (by rw [h₃, data.hc₁₃ r pq pq' hpq]) _ _ _
          (by simpa only [← hn₂, hn₁'] using data.hc r pq pq' hpq) _ _).inv := by
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
    · rw [pageD_eq X data r hr pq pq' hpq (homOfLE (data.le₂₃ r pq''))
          (homOfLE (data.le₁₂' pq' (data.hc₁₃ r pq' pq'' hpq').symm
          (data.hc₀₂ r pq pq' hpq))) (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq))
          (homOfLE (data.le₂₃ r pq))
          (data.hc₀₂ r pq' pq'' hpq').symm (data.hc₁₃ r pq' pq'' hpq').symm rfl rfl rfl rfl
          (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (data.deg pq + 2) rfl,
        pageD_eq X data r hr pq' pq'' hpq' (homOfLE (data.le₀₁ r pq''))
          (homOfLE (data.le₁₂ pq'')) (homOfLE (data.le₂₃ r pq''))
          (homOfLE (data.le₁₂' pq' (data.hc₁₃ r pq' pq'' hpq').symm (data.hc₀₂ r pq pq' hpq)))
          (homOfLE (data.le₀₁ r pq)) rfl rfl
          (data.hc₀₂ r pq' pq'' hpq').symm (data.hc₁₃ r pq' pq'' hpq').symm
          (data.hc₀₂ r pq pq' hpq) (data.hc₁₃ r pq pq' hpq)
          _ _ (data.deg pq + 2) _ (data.hc r pq pq' hpq) rfl (by lia) rfl,
        Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
        d_d_assoc .., zero_comp, comp_zero]
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

/-- The short complex of the `r`th page of the spectral sequence on position `pq'`
identifies to the short complex given by the differentials of the spectral object.
Then, the homology of this short complex can be computed using
`SpectralSequence.dHomologyIso`.
(This only applies in the favourable case when there are `pq` and `pq''` such
that `(c r).Rel pq pq'` and `(c r).Rel pq' pq''` hold.) -/
noncomputable def shortComplexIso (r : ℤ) (hr : r₀ ≤ r) (pq pq' pq'' : κ)
    (hpq : (c r).Rel pq pq') (hpq' : (c r).Rel pq' pq'')
    (n₀ n₁ n₂ n₃ n₄ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) (hn₄ : n₃ + 1 = n₄)
    (hn₂' : n₂ = data.deg pq') :
    (page X data r hr).sc' pq pq' pq'' ≅
      X.dShortComplex (homOfLE (data.le₀₁ r pq''))
        (homOfLE (data.le₁₂ pq'')) (homOfLE (data.le₂₃ r pq''))
        (homOfLE (by simpa only [← data.hc₁₃ r pq' pq'' hpq', data.hc₀₂ r pq pq' hpq]
          using data.le₁₂ pq')) (homOfLE (data.le₀₁ r pq))
        (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq)) n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ := by
  refine ShortComplex.isoMk
    (pageXIso _ _ _ hr _ _ _ _ _ rfl rfl rfl rfl _ _ _ (by have := data.hc r pq pq' hpq; lia))
    (pageXIso _ _ _ hr _ _ _ _ _ (by rw [data.hc₀₂ r pq' pq'' hpq'])
    (by rw [data.hc₁₃ r pq' pq'' hpq'])
    (by rw [data.hc₀₂ r pq pq' hpq]) (by rw [data.hc₁₃ r pq pq' hpq]) _ _ _ hn₂')
    (pageXIso _ _ _ hr _ _ _ _ _ rfl rfl rfl rfl _ _ _ (by have := data.hc r pq' pq'' hpq'; lia))
    ?_ ?_
  · simp only [← Iso.comp_inv_eq, Category.assoc]
    exact (pageD_eq X data r hr pq pq' hpq _ _ _ _ _ (data.hc₀₂ r pq' pq'' hpq').symm
      (data.hc₁₃ r pq' pq'' hpq').symm ..).symm
  · simp only [← Iso.comp_inv_eq, Category.assoc]
    exact (pageD_eq X data r hr pq' pq'' hpq' _ _ _ _ _ rfl rfl ..).symm

section

variable (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' pq')
  (hi₀ : i₀ = data.i₀ r pq')
  (hi₁ : i₁ = data.i₁ pq')
  (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r pq')
  (hi₃' : i₃' = data.i₃ r' pq')
  (n₀ n₁ n₂ : ℤ)
  (hn₁' : n₁ = data.deg pq')

namespace HomologyData

set_option backward.isDefEq.respectTransparency false in
lemma kf_w (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq' hi₀' hi₀)
      (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂) (data.le₂₃' r hr pq' hi₂ hi₃)
        n₀ n₁ n₂ hn₁ hn₂ ≫
      (pageXIso X data _ hr _ _ _ _ _ hi₀ hi₁ hi₂ hi₃ _ _ _ hn₁' _ _).inv) ≫
        (page X data r hr).d pq' pq'' = 0 := by
  by_cases h : (c r).Rel pq' pq''
  · dsimp
    rw [pageD_eq X data r hr pq' pq'' h
      (homOfLE (by simpa only [hi₀', data.i₀_prev r r' _ _ h] using data.le₀₁ r pq''))
      (homOfLE (data.i₀_le' hrr' hr pq' hi₀' hi₀)) (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
      (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃)) rfl
      (by rw [hi₀', data.i₀_prev r r' pq' pq'' h]) hi₀ hi₁ hi₂ hi₃ _ _ _ _ hn₁' hn₁ hn₂ rfl,
      Category.assoc, Iso.inv_hom_id_assoc, map_fourδ₁Toδ₀_d_assoc .., zero_comp]
  · rw [HomologicalComplex.shape _ _ _ h, comp_zero]

/-- A (limit) kernel fork of the differential on the `r`th page whose point
identifies to an object `X.E` -/
noncomputable abbrev kf (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    KernelFork ((page X data r hr).d pq' pq'') :=
  KernelFork.ofι _ (kf_w X data r r' hrr' hr pq' pq''
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁')

/-- The (exact) short complex attached to the kernel fork `kf`. -/
@[simps!]
noncomputable def kfSc (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (kf_w X data r r' hrr' hr pq' pq''
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁)

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (kfSc X data r r' hrr' hr pq' pq'' i₀' i₀ i₁ i₂ i₃
      hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂).f := by
  dsimp
  infer_instance

variable [X.HasSpectralSequence data] in
include hpq' hn₁' in
lemma isIso_mapFourδ₁Toδ₀' (h : ¬ (c r).Rel pq' pq'')
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.mapFourδ₁Toδ₀'
      i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq' hi₀' hi₀) (data.le₀₁' r hr pq' hi₀ hi₁)
        (data.le₁₂' pq' hi₁ hi₂) (data.le₂₃' r hr pq' hi₂ hi₃) n₀ n₁ n₂ hn₁ hn₂) := by
  apply X.isIso_map_fourδ₁Toδ₀_of_isZero ..
  refine X.isZero_H_obj_mk₁_i₀_le' data r r' hrr' hr pq' (fun k hk ↦ ?_) _ (by lia) _ _ hi₀' hi₀
  obtain rfl := (c r).next_eq' hk
  subst hpq'
  exact h hk

variable [X.HasSpectralSequence data] in
include hpq' in
lemma kfSc_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (kfSc X data r r' hrr' hr pq' pq'' i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃
      n₀ n₁ n₂ hn₁' hn₁ hn₂).Exact := by
  by_cases h : (c r).Rel pq' pq''
  · refine ShortComplex.exact_of_iso (Iso.symm ?_)
      (X.dKernelSequence_exact
        (homOfLE (show data.i₀ r pq'' ≤ i₀' by
          simpa only [hi₀', data.i₀_prev r r' _ _ h] using data.le₀₁ r pq''))
        (homOfLE (data.i₀_le' hrr' hr pq' hi₀' hi₀)) (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
        (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃)) _ rfl
        n₀ n₁ n₂ (n₂ + 1) hn₁ hn₂ rfl)
    refine ShortComplex.isoMk (Iso.refl _)
      (pageXIso X data _ hr _ _ _ _ _ hi₀ hi₁ hi₂ hi₃ _ _ _ hn₁')
      (pageXIso X data _ hr _ _ _ _ _ rfl (by rw [hi₀', data.i₀_prev r r' _ _ h])
      (by rw [hi₀, data.hc₀₂ r _ _ h]) (by rw [hi₁, data.hc₁₃ r _ _ h]) _ _ _
      (by have := data.hc r _ _ h; lia)) ?_ ?_
    · simp
    · dsimp
      rw [pageD_eq X data r hr pq' pq'' h
        (homOfLE (data.le₀₁' r hr pq'' rfl (by simpa [← data.i₀_prev r r' _ _ h])))
        (homOfLE (data.i₀_le' hrr' hr pq' hi₀' hi₀)) (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
        (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃))
        rfl (by rw [hi₀', data.i₀_prev r r' _ _ h]) hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ (n₂ + 1) hn₁',
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [ShortComplex.exact_iff_epi _ ((page X data r hr).shape _ _ h)]
    have := isIso_mapFourδ₁Toδ₀' X data r r' hrr' hr pq' pq'' hpq'
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' h
    dsimp
    infer_instance

variable [X.HasSpectralSequence data] in
/-- The kernel fork `kf` is a limit. -/
noncomputable def isLimitKf (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsLimit (kf X data r r' hrr' hr pq' pq''
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂) :=
  (kfSc_exact X data r r' hrr' hr pq' pq'' hpq'
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂).fIsKernel

lemma cc_w (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (page X data r hr).d pq pq' ≫
      (pageXIso X data _ hr _ _ _ _ _ hi₀ hi₁ hi₂ hi₃ _ _ _ hn₁').hom ≫
      X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃' _ _ _
        (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂ = 0 := by
  by_cases h : (c r).Rel pq pq'
  · dsimp
    rw [pageD_eq X data r hr pq pq' h (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
      (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃))
      (homOfLE (data.le₃₃' hrr' hr pq' hi₃ hi₃'))
      (homOfLE (by simpa only [hi₃', data.i₃_next r r' _ _ h] using data.le₂₃ r pq))
      hi₀ hi₁ (by rw [hi₂, data.hc₀₂ r _ _ h])
      (by rw [hi₃, data.hc₁₃ r _ _ h]) (by rw [hi₃', data.i₃_next r r' _ _ h]) rfl
      (n₀ - 1) n₀ n₁ n₂ (by have := data.hc r pq pq' h; lia) (by simp) hn₁ hn₂,
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
      d_map_fourδ₄Toδ₃ .., comp_zero]
    rfl
  · rw [HomologicalComplex.shape _ _ _ h, zero_comp]

/-- A (limit) cokernel cofork of the differential on the `r`th page whose point
identifies to an object `X.E` -/
noncomputable abbrev cc (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    CokernelCofork ((page X data r hr).d pq pq') :=
  CokernelCofork.ofπ _
    (cc_w X data r r' hrr' hr pq pq' i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁')

/-- The (exact) short complex attached to the cokernel cofork `cc`. -/
@[simps!]
noncomputable def ccSc (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (cc_w X data r r' hrr' hr pq pq'
    i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁')

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (ccSc X data r r' hrr' hr pq pq'
    i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).g := by
  dsimp
  infer_instance

variable [X.HasSpectralSequence data] in
include hpq hn₁' in
lemma isIso_mapFourδ₄Toδ₃' (h : ¬ (c r).Rel pq pq')
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃'
      (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂)
      (data.le₂₃' r hr pq' hi₂ hi₃) (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂) := by
  apply X.isIso_map_fourδ₄Toδ₃_of_isZero _ _ _ _ _ _ _ _ _ _
  refine X.isZero_H_obj_mk₁_i₃_le' data r r' hrr' hr pq' (fun _ hk ↦ ?_) _ (by lia) _ _ hi₃ hi₃'
  obtain rfl := (c r).prev_eq' hk
  subst hpq
  exact h hk

variable [X.HasSpectralSequence data] in
include hpq in
lemma ccSc_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (ccSc X data r r' hrr' hr pq pq'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').Exact := by
  by_cases h : (c r).Rel pq pq'
  · refine ShortComplex.exact_of_iso (Iso.symm ?_)
      (X.dCokernelSequence_exact
      (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁))
      (homOfLE (data.le₁₂' pq' hi₁ hi₂)) (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃))
      (homOfLE (data.le₃₃' hrr' hr pq' hi₃ hi₃'))
      (show i₃' ⟶ data.i₃ r pq from homOfLE (by
        simpa only [hi₃', data.i₃_next r r' _ _ h] using data.le₂₃ r pq)) _ rfl
      (n₀ - 1) n₀ n₁ n₂ (by simp) hn₁ hn₂)
    refine ShortComplex.isoMk
      (pageXIso X data _ hr _ _ _ _ _
        (by rw [hi₂, data.hc₀₂ r _ _ h]) (by rw [hi₃, data.hc₁₃ r _ _ h])
        (by rw [hi₃', data.i₃_next r r' _ _ h]) rfl _ _ _ (by have := data.hc r _ _ h; lia))
      (pageXIso X data _ hr _ _ _ _ _ hi₀ hi₁ hi₂ hi₃ _ _ _ hn₁') (Iso.refl _) ?_ (by simp)
    dsimp
    rw [pageD_eq X data r hr pq pq' h
          (homOfLE (data.le₀₁' r hr pq' hi₀ hi₁)) (homOfLE (data.le₁₂' pq' hi₁ hi₂))
          (homOfLE (data.le₂₃' r hr pq' hi₂ hi₃)) (homOfLE (data.le₃₃' hrr' hr pq' hi₃ hi₃'))
          (homOfLE (data.le₂₃' r hr pq (by rw [hi₃', data.i₃_next r r' pq pq' h]) rfl))
          hi₀ hi₁ (hi₂.trans (data.hc₀₂ r pq pq' h).symm)
          (hi₃.trans (data.hc₁₃ r pq pq' h).symm) (hi₃'.trans (data.i₃_next r r' pq pq' h)) rfl
          (n₀ - 1) n₀ n₁ n₂ (by have := data.hc r _ _ h; lia),
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · refine (ShortComplex.exact_iff_mono _ ((page X data r hr).shape _ _ h)).mpr ?_
    have := isIso_mapFourδ₄Toδ₃' X data r r' hrr' hr pq pq' hpq
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' h
    dsimp
    infer_instance

variable [X.HasSpectralSequence data] in
/-- The cokernel cofork `cc` is a colimit. -/
noncomputable def isColimitCc (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsColimit (cc X data r r' hrr' hr pq pq'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁') :=
  (ccSc_exact X data r r' hrr' hr pq pq' hpq i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃' ..).gIsCokernel

set_option backward.isDefEq.respectTransparency false in
lemma fac (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
  (kf X data r r' hrr' hr pq' pq'' i₀' i₀ i₁ i₂ i₃
      hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁').ι ≫
    (cc X data r r' hrr' hr pq pq' i₀ i₁ i₂ i₃ i₃'
      hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').π =
  X.mapFourδ₄Toδ₃' i₀' i₁ i₂ i₃ i₃' _ _ _ (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂ ≫
    X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃'
      (data.i₀_le' hrr' hr pq' hi₀' hi₀) _ _ _ n₀ n₁ n₂ := by
  simp [← map_comp]
  rfl

end HomologyData

variable [X.HasSpectralSequence data]

set_option backward.isDefEq.respectTransparency false in
open HomologyData in
/-- The homology data for the short complex given by differentials on the
`r`th page of the spectral sequence which shows that the homology identifies
to an object on the next page. -/
@[simps!]
noncomputable def homologyData (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ((page X data r hr).sc' pq pq' pq'').HomologyData :=
  ShortComplex.HomologyData.ofEpiMonoFactorisation
    ((page X data r hr).sc' pq pq' pq'')
    (isLimitKf X data r r' hrr' hr pq' pq'' hpq' i₀' i₀ i₁ i₂ i₃
      hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁')
    (isColimitCc X data r r' hrr' hr pq pq' hpq i₀ i₁ i₂ i₃ i₃'
      hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁')
    (fac X data r r' hrr' hr pq pq' pq'' i₀' i₀ i₁ i₂ i₃ i₃'
      hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁')

/-- The homology of the differentials on a page of the spectral sequence identifies
to the objects on the next page. -/
noncomputable def homologyIso' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ((page X data r hr).sc' pq pq' pq'').homology ≅ (page X data r' (by lia)).X pq' :=
  (homologyData X data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').left.homologyIso ≪≫
      (pageXIso X data _ (by lia) _ _ _ _ _ hi₀' hi₁ hi₂ hi₃' _ _ _ hn₁').symm

/-- The homology of the differentials on a page of the spectral sequence identifies
to the objects on the next page. -/
noncomputable def homologyIso :
    (page X data r hr).homology pq' ≅
      (page X data r' (hr.trans (by lia))).X pq' :=
  homologyIso' X data r r' hrr' hr _ pq' _ rfl rfl _ _ _ _ _ _ rfl rfl
    rfl rfl rfl rfl (data.deg pq' - 1) (data.deg pq') _ rfl (by lia) rfl

end

end SpectralSequence

section

variable [X.HasSpectralSequence data] in
/-- The spectral sequence attached to a spectral object in an abelian category. -/
@[irreducible]
noncomputable def spectralSequence : SpectralSequence C c r₀ where
  page := SpectralSequence.page X data
  iso r r' pq hrr' hr := SpectralSequence.homologyIso X data r r' hrr' hr pq

variable [X.HasSpectralSequence data]

unseal spectralSequence in
/-- The objects on the pages of a spectral sequence attached to a spectral object `X`
identifies an object `X.E`. -/
noncomputable def spectralSequencePageXIso (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq)
    (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ((X.spectralSequence data).page r).X pq ≅
      X.E (homOfLE (data.le₀₁' r hr pq h₀ h₁)) (homOfLE (data.le₁₂' pq h₁ h₂))
        (homOfLE (data.le₂₃' r hr pq h₂ h₃)) n₀ n₁ n₂ :=
  SpectralSequence.pageXIso X data _ hr _ _ _ _ _ h₀ h₁ h₂ h₃ _ _ _ h

unseal spectralSequence in
lemma spectralSequence_page_d_eq (r : ℤ) (hr : r₀ ≤ r)
    (pq pq' : κ) (hpq : (c r).Rel pq pq')
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ pq')
    (h₂ : i₂ = data.i₀ r pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r pq)
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁' : n₁ = data.deg pq) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    ((X.spectralSequence data).page r).d pq pq' =
      (X.spectralSequencePageXIso data r hr _ _ _ _ _ h₂ h₃ h₄ h₅ _ _ _ hn₁').hom ≫
        X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
          (X.spectralSequencePageXIso data r hr _ _ _ _ _ h₀ h₁
            (by rw [h₂, ← data.hc₀₂ r pq pq' hpq]) (by rw [h₃, data.hc₁₃ r pq pq' hpq]) _ _ _
              (by simpa only [← hn₂, hn₁'] using data.hc r pq pq' hpq)).inv :=
  SpectralSequence.pageD_eq _ _ _ hr _ _ hpq ..

lemma isZero_spectralSequence_page_X_iff (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsZero (((X.spectralSequence data).page r).X pq) ↔
      IsZero (X.E (homOfLE (data.le₀₁' r hr pq h₀ h₁))
        (homOfLE (data.le₁₂' pq h₁ h₂))
        (homOfLE (data.le₂₃' r hr pq h₂ h₃)) n₀ n₁ n₂) :=
  Iso.isZero_iff (X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃
    h₀ h₁ h₂ h₃ n₀ n₁ n₂ h)

lemma isZero_spectralSequence_page_X_of_isZero_H (r : ℤ) (hr : r₀ ≤ r)
    (pq : κ) (n : ℤ) (hn : n = data.deg pq)
    (i₁ i₂ : ι) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h : IsZero ((X.H n).obj
      (mk₁ (homOfLE (by simpa only [h₁, h₂] using data.le₁₂ pq) : i₁ ⟶ i₂)))) :
    IsZero (((X.spectralSequence data).page r).X pq) := by
  rw [X.isZero_spectralSequence_page_X_iff data r hr pq
    _ i₁ i₂ _ rfl h₁ h₂ rfl (n - 1) n (n + 1) hn]
  exact isZero_E_of_isZero_H _ _ _ _ _ _ _ h

lemma isZero_spectralSequence_page_X_of_isZero_H' (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (h : IsZero ((X.H (data.deg pq)).obj (mk₁ (homOfLE (data.le₁₂ pq))))) :
    IsZero (((X.spectralSequence data).page r).X pq) :=
  X.isZero_spectralSequence_page_X_of_isZero_H data r hr pq _ rfl _ _ rfl rfl h

unseal spectralSequence in
/-- The short complex of the `r`th page of the spectral sequence on position `pq'`
identifies to the short complex given by the differentials of the spectral object.
Then, the homology of this short complex can be computed using
`SpectralSequence.dHomologyIso`.
(This only applies in the favourable case when there are `pq` and `pq''` such
that `(c r).Rel pq pq'` and `(c r).Rel pq' pq''` hold.) -/
noncomputable def spectralSequencePageSc'Iso (r : ℤ) (hr : r₀ ≤ r) (pq pq' pq'' : κ)
    (hpq : (c r).Rel pq pq') (hpq' : (c r).Rel pq' pq'')
    (n₀ n₁ n₂ n₃ n₄ : ℤ)
    (hn₂' : n₂ = data.deg pq')
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) (hn₄ : n₃ + 1 = n₄ := by lia) :
    ((X.spectralSequence data).page r).sc' pq pq' pq'' ≅
      X.dShortComplex (homOfLE (data.le₀₁ r pq''))
        (homOfLE (data.le₁₂ pq'')) (homOfLE (data.le₂₃ r pq''))
        (homOfLE (by simpa only [← data.hc₁₃ r pq' pq'' hpq', data.hc₀₂ r pq pq' hpq]
          using data.le₁₂ pq')) (homOfLE (data.le₀₁ r pq))
        (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
        n₀ n₁ n₂ n₃ n₄ :=
  SpectralSequence.shortComplexIso _ _ _ hr _ _ _ hpq hpq' _ _ _ _ _ _ _ _ _ hn₂'

section

variable (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' pq' (hr.trans (by rw [← hrr']; exact Int.le.intro 1 rfl)))
  (hi₀ : i₀ = data.i₀ r pq' hr)
  (hi₁ : i₁ = data.i₁ pq')
  (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r pq' hr)
  (hi₃' : i₃' = data.i₃ r' pq' (hr.trans (by rw [← hrr']; exact Int.le.intro 1 rfl)))
  (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq')

unseal spectralSequence in
/-- The homology data for the short complexes given by the differentials
of a spectral sequence attached to a spectral object in an abelian category. -/
@[simps! left_K left_H left_π right_H right_Q right_ι iso_hom iso_inv]
noncomputable def spectralSequenceHomologyData
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (((X.spectralSequence data).page r hr).sc' pq pq' pq'').HomologyData :=
  SpectralSequence.homologyData X data r r' hrr' hr
    pq pq' pq'' hpq hpq' i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂

unseal spectralSequence in
@[simp]
lemma spectralSequenceHomologyData_left_i
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left.i =
    X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃
      (data.i₀_le' hrr' hr pq' hi₀' hi₀) _ _ _ n₀ n₁ n₂ ≫
        (X.spectralSequencePageXIso data r hr pq'
          i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁').inv :=
  rfl

unseal spectralSequence in
@[simp]
lemma spectralSequenceHomologyData_right_p
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).right.p =
    (X.spectralSequencePageXIso data r hr pq'
      i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁').hom ≫
        X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃' _ _ _
          (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂ := rfl

lemma spectralSequenceHomologyData_right_homologyIso_eq_left_homologyIso
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').right.homologyIso =
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').left.homologyIso := by
  ext1
  simp [ShortComplex.HomologyData.right_homologyIso_eq_left_homologyIso_trans_iso]

unseal spectralSequence in
lemma spectralSequence_iso (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequence data).iso r r' pq' =
    ((X.spectralSequence data).page r).homologyIsoSc' pq pq' pq'' hpq hpq' ≪≫
      (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').left.homologyIso ≪≫
        (X.spectralSequencePageXIso data r' (by lia) _ _ _ _ _
          hi₀' hi₁ hi₂ hi₃' _ _ _ hn₁').symm := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl : n₂ = n₁ + 1 := by lia
  subst hpq hpq' hn₁' hi₀ hi₁ hi₂ hi₃ hi₀' hi₃'
  ext
  simp [spectralSequencePageXIso, spectralSequence, spectralSequenceHomologyData,
    SpectralSequence.homologyIso, SpectralSequence.homologyIso']

@[reassoc]
lemma spectralSequence_iso_inv (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ((X.spectralSequence data).iso r r' pq').inv =
    (X.spectralSequencePageXIso data r'
      (hr.trans (by rw [← hrr']; exact Int.le.intro 1 rfl)) _ _ _ _ _
      hi₀' hi₁ hi₂ hi₃' _ _ _ hn₁').hom ≫
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq' i₀' i₀ i₁ i₂ i₃ i₃'
      hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').left.homologyIso.inv ≫
      (((X.spectralSequence data).page r).homologyIsoSc' pq pq' pq'' hpq hpq').inv := by
  simp [X.spectralSequence_iso data r r' hrr' hr pq pq' pq'' hpq hpq' i₀' i₀ i₁ i₂ i₃ i₃'
    hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂]

@[reassoc]
lemma spectralSequence_iso_hom (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ((X.spectralSequence data).iso r r' pq').hom =
    (((X.spectralSequence data).page r).homologyIsoSc' pq pq' pq'' hpq hpq').hom ≫
    (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq' i₀' i₀ i₁ i₂ i₃ i₃'
      hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').left.homologyIso.hom ≫
    (X.spectralSequencePageXIso data r'
      (hr.trans (by rw [← hrr']; exact Int.le.intro 1 rfl)) _ _ _ _ _
      hi₀' hi₁ hi₂ hi₃' _ _ _ hn₁').inv := by
  simp [X.spectralSequence_iso data r r' hrr' hr pq pq' pq'' hpq hpq' i₀' i₀ i₁ i₂ i₃ i₃'
    hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂]

end


end

section

variable (Y : SpectralObject C EInt)

/-- The `E₂` cohomological spectral sequence indexed by `ℤ × ℤ` attached to
a spectral object indexed by `EInt`. -/
noncomputable abbrev E₂SpectralSequence : E₂CohomologicalSpectralSequence C :=
  Y.spectralSequence coreE₂Cohomological

section

variable [Y.IsFirstQuadrant]

example (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hq : q < 0) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) :=
  isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr _
    (Y.isZero₁_of_isFirstQuadrant _ _ _ (by simp; lia) _)

example (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hp : p < 0) :
    IsZero ((Y.E₂SpectralSequence.page r).X ⟨p, q⟩) :=
  isZero_spectralSequence_page_X_of_isZero_H' _ _ _ hr _
    (Y.isZero₂_of_isFirstQuadrant _ _ _ _ (by simp; lia))

/-- The `E₂` cohomological spectral sequence indexed by `ℕ × ℕ` attached to
a first quadrant spectral object indexed by `EInt`. -/
noncomputable abbrev E₂SpectralSequenceNat := Y.spectralSequence coreE₂CohomologicalNat

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

/-- The `E₂` homological spectral sequence indexed by `ℕ × ℕ` attached to
a third quadrant spectral object indexed by `EInt`. -/
noncomputable abbrev E₂HomologicalSpectralSequenceNat := Y.spectralSequence coreE₂HomologicalNat

end

end

end SpectralObject

end Abelian

end CategoryTheory
