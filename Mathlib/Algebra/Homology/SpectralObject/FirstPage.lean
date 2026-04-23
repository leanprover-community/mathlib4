/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The first page of the spectral sequence of a spectral object

Let `ι` be a preordered type, `X` a spectral object in an abelian
category indexed by `ι`. Let `data : SpectralSequenceDataCore ι c r₀`.
Assume that `X.HasSpectralSequence data` holds. In this file,
we introduce a property `data.HasFirstPageComputation` which allows
to "compute" the objects of the `r₀`th page of the spectral
sequence attached to `X` in terms of objects of the form `X.H`,
and we compute the differential on the first page in terms of `X.δ`,
see `spectralSequence_first_page_d_eq`.

-/

@[expose] public section

namespace CategoryTheory

open Category ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀)

namespace SpectralSequenceDataCore

/-- Given `data : SpectralSequenceDataCore ι c r₀`, this is the property
that on the page `r₀`, indices `i₀` and `i₁` are equal,
and indices `i₂` and `i₃` are equal. This condition allows
to express the objects of the `r₀`th page of the spectral sequences
obtained using a spectral object `X` indexed by `ι` and `data` as objects
of the form `X.H`, see `SpectralObject.spectralSequenceFirstPageXIso`. -/
class HasFirstPageComputation : Prop where
  hi₀₁ (pq : κ) : data.i₀ r₀ pq = data.i₁ pq
  hi₂₃ (pq : κ) : data.i₂ pq = data.i₃ r₀ pq

export HasFirstPageComputation (hi₀₁ hi₂₃)

instance : coreE₂Cohomological.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

instance : coreE₂CohomologicalNat.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

instance : coreE₂HomologicalNat.HasFirstPageComputation where
  hi₀₁ pq := by dsimp; lia
  hi₂₃ pq := by dsimp; lia

end SpectralSequenceDataCore

variable [data.HasFirstPageComputation] [X.HasSpectralSequence data]

/-- If `data : SpectralSequenceDataCore ι c r₀` is such that
`data.HasFirstPageComputation` holds, this is an isomorphism which
allows to "compute" the objects on the `r₀`th page of the spectral sequence
obtained from a spectral object `X` indexed by `ι` using data as objects
of the form `X.H`. See also `spectralSequence_first_page_d_eq` for the relation
between the differentials of the first page of the spectral sequence and `X.δ`. -/
noncomputable def spectralSequenceFirstPageXIso (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n : ℤ) (hn : n = data.deg pq) :
    ((X.spectralSequence data).page r₀).X pq ≅
      (X.H n).obj (mk₁ (homOfLE (data.le₁₂' pq hi₁ hi₂))) :=
  X.spectralSequencePageXIso data _ (by rfl) _ _ _ _ _
    (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn ≪≫
      X.EIsoH (homOfLE _) (n - 1) n (n + 1)

@[reassoc]
lemma spectralSequenceFirstPageXIso_hom (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n₁ hn₁').hom =
      (X.spectralSequencePageXIso data r₀ (by rfl) _ _ _ _ _
        (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn₁').hom ≫
          (X.EIsoH _ n₀ n₁ n₂ hn₁ hn₂).hom := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

@[reassoc]
lemma spectralSequenceFirstPageXIso_inv (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequenceFirstPageXIso data pq i₁ i₂ hi₁ hi₂ n₁ hn₁').inv =
      (X.EIsoH _ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      (X.spectralSequencePageXIso data r₀ (by rfl) _ _ _ _ _
        (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn₁').inv := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl := hn₂
  rfl

@[reassoc]
lemma spectralSequence_first_page_d_eq (pq pq' : κ)
    (hpq : (c r₀).Rel pq pq') (i j k : ι)
    (hi : i = data.i₁ pq') (hj : j = data.i₁ pq) (hk : k = data.i₂ pq)
    (n n' : ℤ) (hn : n = data.deg pq) (hn' : n + 1 = n' := by lia) :
    ((X.spectralSequence data).page r₀).d pq pq' =
      (X.spectralSequenceFirstPageXIso data pq j k hj hk n hn).hom ≫
      X.δ
        (homOfLE
          (by simpa only [hi, hj, data.hc₁₃ r₀ pq pq' hpq, ← data.hi₂₃ pq']
            using data.le₁₂ pq'))
        (homOfLE (by simpa only [hj, hk] using data.le₁₂ pq)) n n' hn' ≫
      (X.spectralSequenceFirstPageXIso data pq' i j hi
        (by rw [hj, ← data.hc₀₂ r₀ pq pq' hpq, data.hi₀₁ pq]) n'
        (by rw [← hn', hn, data.hc r₀ pq pq' hpq])).inv := by
  simpa [X.spectralSequenceFirstPageXIso_hom data pq j k hj hk (n - 1) n n',
    ← X.d_EIsoH_hom_assoc _ _ (n - 1) n n' (n' + 1),
    X.spectralSequenceFirstPageXIso_inv data pq' i j hi _ _ n' _ _ hn' _]
    using spectralSequence_page_d_eq _ _ _ _ _ _ hpq ..

end SpectralObject

end Abelian

end CategoryTheory
