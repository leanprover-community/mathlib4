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

The main definition in this file is `Abelian.SpectralObject.spectralSequence` (TODO).
Assume that `X` is a spectral object indexed by `ι` in an abelian category `C`,
and that we have `data : SpectralSequenceDataCore ι c r₀` for a family
of complexes shapes `c : ℤ → ComplexShape κ` for a type `κ` and `r₀ : ℤ`.
Then, under the assumption `X.HasSpectralSequence data` (see the file
`Mathlib/Algebra/Homology/SpectralObject/HasSpectralSequence.lean`),
we obtain `X.spectralSequence data` (TODO) which is a spectral sequence starting
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
`i₀ r pq' ≤ i₁ pq' ≤ i₂ pq' ≤ i₃ r pq' ≤ i₂ pq ≤ i₄ r pq` for which
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
to obtain that the homology of the `r`th page identifies to the homology
of the next page (see the definitions
`SpectralObject.SpectralSequence.homologyData` (TODO) and
`SpectralObject.spectralSequenceHomologyData` (TODO)).

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
        pageD_eq X data r hr pq' pq'' hpq' _ _ _ _ _ rfl rfl
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
  · dsimp
    rw [pageD_eq X data r hr pq pq' hpq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · exact (data.hc₀₂ r pq' pq'' hpq').symm
    · exact (data.hc₁₃ r pq' pq'' hpq').symm
  · dsimp
    rw [pageD_eq X data r hr pq' pq'' hpq' _ _ _ _ _ rfl rfl _ _ _ _ _ _ _ _ _ _ _ _,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

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
      (pageXIso X data _ hr _ _ _ _ _ hi₀ hi₁ hi₂ hi₃ _ _ _ hn₁' _ _ ).inv) ≫
        (page X data r hr).d pq' pq'' = 0 := by
  by_cases h : (c r).Rel pq' pq''
  · dsimp
    rw [pageD_eq X data r hr pq' pq'' h
      (homOfLE (by simpa only [hi₀', data.i₀_prev r r' _ _ h] using data.le₀₁ r pq''))
      (homOfLE (data.i₀_le' hrr' hr pq' hi₀' hi₀)) _ _ _ rfl
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
  refine X.isZero_H_obj_mk₁_i₀_le' data r r' hrr' hr pq'
    (fun k hk ↦ ?_) _ (by lia) _ _ hi₀' hi₀
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
          (homOfLE (show data.i₀ r pq'' ≤ i₀' by
            simpa only [hi₀', data.i₀_prev r r' _ _ h] using data.le₀₁ r pq''))
          _ _ _ _ _ _ _ _ _ _ n₀ n₁ n₂ (n₂ + 1),
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · rfl
      · rw [hi₀', data.i₀_prev r r' _ _ h]
  · rw [ShortComplex.exact_iff_epi]; swap
    · exact (page X data r hr).shape _ _ h
    have := isIso_mapFourδ₁Toδ₀' X data r r' hrr' hr pq' pq'' hpq'
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' h hn₁ hn₂
    dsimp
    infer_instance

variable [X.HasSpectralSequence data] in
/-- The kernel fork `kf` is a limit. -/
noncomputable def isLimitKf (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsLimit (kf X data r r' hrr' hr pq' pq''
      i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁' hn₁ hn₂) :=
  (kfSc_exact X data r r' hrr' hr pq' pq'' hpq'
    i₀' i₀ i₁ i₂ i₃ hi₀' hi₀ hi₁ hi₂ hi₃  n₀ n₁ n₂ hn₁' hn₁ hn₂).fIsKernel

end HomologyData

end

end SpectralSequence

end SpectralObject

end Abelian

end CategoryTheory
