/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.SetToL1
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Integral of vector-valued function against vector measure

We extend the definition of the Bochner integral (of vector-valued function against `ℝ≥0∞`-valued
measure) to vector measures through a bilinear pairing.
Let `E`, `F` be normed vector spaces, and `G` be a Banach space (complete normed vector space).
We fix a continuous linear pairing `B : E →L[ℝ] F →L[ℝ] → G` and an `F`-valued vector measure `μ`
on a measurable space `α`.
The vector measure `μ` gives the total variation measure `μ.totalvariation` on `α`.
For an L1 function `f : α → E` with respect to this total variation measure,
we define the `G`-valued integral, which is informally written `∫ B (f x) ∂μ x`.

The pairing integral is defined through the general setting `setToL1` which sends a set function to
a continuous linear map on the type of L1 functions, see the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`.

## Main definitions

The pairing integral is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

1. Define the integral of the indicator of a set. This is `cbmApplyMeasure B μ s x = B x (μ s)`.
  `cbmApplyMeasure B μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
  (defined in the file `Mathlib/MeasureTheory/Integral/SetToL1.lean`) with respect to the set `s`.

2. Define the structure `VectorMeasureWithPairing`, combining a pairing of two normed vector spaces
  and a vector measure.

3. Define the pairing integral on L1 functions `f` as `setToL1 (...) f`. Note that, contrary
  to the definition of Bochner integral, here `setToL1` is already a continuous linear map from
  L1 functions, not from step functions.

## Note

Let be `Bμ : VectorMeasureWithPairing`.
We often consider L1 functions with respect to the total variation of `Bμ.vectorMeasure`:
* `α →₁[Bμ.vectorMeasure.variation] E` : `E`-valued functions in L1 space.

-/

public section

open ENNReal Set MeasureTheory VectorMeasure ContinuousLinearMap

namespace MeasureTheory

section cbmApplyMeasure

variable {α E F G : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (B : E →L[ℝ] F →L[ℝ] G) (μ : VectorMeasure α F)

/-- Given a set `s`, return the continuous linear map `fun x : E => B x (μ s)`, where the `B` is a
`G`-valued bilinear form on `E × F` and `μ` is an `F`-valued vector measure. The extension of that
set function through `setToL1` gives the pairing integral of L1 functions. -/
noncomputable def cbmApplyMeasure (s : Set α) : E →L[ℝ] G where
  toFun x := B x (μ s)
  map_add' _ _ := map_add₂ ..
  map_smul' _ _ := map_smulₛₗ₂ ..

@[simp]
theorem cbmApplyMeasure_apply (s : Set α) (x : E) : cbmApplyMeasure B μ s x = B x (μ s) := by
  rfl

theorem cbmApplyMeasure_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hdisj : Disjoint s t) :
    cbmApplyMeasure B μ (s ∪ t) = cbmApplyMeasure B μ s + cbmApplyMeasure B μ t := by
  ext x
  simp [cbmApplyMeasure_apply, of_union hdisj hs ht, (B x).map_add]

theorem norm_cbmApplyMeasure_le (s : Set α) :
    ‖cbmApplyMeasure B μ s‖ ≤ ‖B‖ * ‖μ s‖ := by
  rw [opNorm_le_iff (by positivity)]
  intro x
  grw [cbmApplyMeasure_apply, le_opNorm₂, mul_right_comm]

theorem dominatedFinMeasAdditive_cbmApplyMeasure :
    DominatedFinMeasAdditive (μ.variation)
    (cbmApplyMeasure B μ : Set α → E →L[ℝ] G) ‖B‖ := by
  refine ⟨fun s t hs ht _ _ hdisj => cbmApplyMeasure_union B μ hs ht hdisj, ?_⟩
  intro s hs hsf
  apply (fun s _ _ => (norm_cbmApplyMeasure_le B μ s).trans)
  gcongr
  rw [Measure.real, ← ofReal_le_iff_le_toReal (LT.lt.ne_top hsf), ofReal_norm]
  exact enorm_measure_le_variation μ s

end cbmApplyMeasure

open SimpleFunc L1

section

variable (α E F G : Type*) [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The structure containing a continuous linear pairing and a vector measure,
enabling the dot notation `VectorMeasureWithParing.integral`. -/
structure VectorMeasureWithPairing where
  /-- A continuous linear pairing from `E` `F` into a Banach space `G`. -/
  pairing : E →L[ℝ] F →L[ℝ] G
  /-- An `F`-valued vector measure. -/
  vectorMeasure : VectorMeasure α F

end

namespace VectorMeasureWithPairing

variable {α E F G : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  (Bμ : VectorMeasureWithPairing α E F G)

/-- The pairing integral in L1 space as a continuous linear map. -/
noncomputable def integral : (α →₁[Bμ.vectorMeasure.variation] E) →L[ℝ] G :=
  setToL1 (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure)

@[integral_simps]
theorem integral_add (f g : α →₁[Bμ.vectorMeasure.variation] E) :
    Bμ.integral (f + g) = Bμ.integral f + Bμ.integral g := by
  simp [integral]

@[integral_simps]
theorem integral_neg (f : α →₁[Bμ.vectorMeasure.variation] E) :
    Bμ.integral (-f) = -Bμ.integral f := by
  simp [integral]

@[integral_simps]
theorem integral_sub (f g : α →₁[Bμ.vectorMeasure.variation] E) :
    Bμ.integral (f - g) = Bμ.integral f - Bμ.integral g := by
  simp [integral]

@[integral_simps]
theorem integral_smul (c : ℝ) (f : α →₁[Bμ.vectorMeasure.variation] E) :
    Bμ.integral (c • f) = c • Bμ.integral f := by
  simp [integral]

@[simp]
lemma integral_apply (f : (α →₁[Bμ.vectorMeasure.variation] E)) :
    Bμ.integral f
    = setToL1 (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) f := by
  rfl

theorem integral_le (f : (α →₁[Bμ.vectorMeasure.variation] E)) :
    ‖Bμ.integral f‖ ≤ ‖Bμ.pairing‖ * ‖f‖:= by
  simp only [integral_apply]
  exact norm_setToL1_le_mul_norm
    (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure)
    (norm_nonneg Bμ.pairing) f

theorem norm_integral_le_norm_pairing : ‖Bμ.integral‖ ≤ ‖Bμ.pairing‖ :=
  (ContinuousLinearMap.opNorm_le_iff (norm_nonneg Bμ.pairing)).mpr
  (integral_le Bμ)

theorem nnnorm_integral_le_nnNnorm : ‖Bμ.integral‖₊ ≤ ‖Bμ.pairing‖₊ :=
  norm_integral_le_norm_pairing Bμ

theorem nnnorm_integral_le (f : α →₁[Bμ.vectorMeasure.variation] E) :
    ‖Bμ.integral f‖₊ ≤ ‖Bμ.pairing‖₊ * ‖f‖₊ := integral_le Bμ f

@[continuity]
theorem continuous_integral :
    Continuous fun f : α →₁[Bμ.vectorMeasure.variation] E =>
    Bμ.integral f :=
  (setToL1 (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure)).continuous

end VectorMeasureWithPairing

namespace VectorMeasure

variable {α F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : VectorMeasure α F)

/-- For an `F`-valued vector measure `μ`, `μ.withPairing` is a structure `VectorMeasureWithPairing`
where `pairing` is just the `ℝ`-multiplication, so that `μ.withPairing.integral` is the
`F`-valued integral of `μ`. -/
noncomputable def withPairing : VectorMeasureWithPairing α ℝ F F where
  pairing := lsmul (E := F) ℝ ℝ
  vectorMeasure := μ

/-- The `F`-valued integral with respect to an `F`-valued vector measure as a continuous linear map,
defined as the pairing integral where the pairing is `lsmul`. -/
noncomputable def integral : (α →₁[μ.variation] ℝ) →L[ℝ] F :=
    μ.withPairing.integral

end VectorMeasure

end MeasureTheory
