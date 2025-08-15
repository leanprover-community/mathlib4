/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.MeasureTheory.VectorMeasure.Variation.Lemmas

/-!
# Integral of vector-valued function against vector measure

We extend the definition of the Bochner integral (of vector-valued function against `ℝ≥0∞`-valued
measure) to vector measures through a bilinear pairing.
Let `E`, `F` be normed vector spaces, and `G` be a Banach space (complete normed vector space).
We fix a continuous linear pairing `B : E →L[ℝ] F →L[ℝ] → G` and an `F`-valued vector measure `μ`
on a measurable space `α`.
The vector measure `μ` gives the total variation measure `μ.totalvariation.ennrealToMeasure` on `α`.
For an L1 function `f : α → E` with respect to this total variation measure,
we define the `G`-valued integral, which is informally written `∫ B (f x) ∂μ x`.

The pairing integral is defined through the general setting `setToL1` which sends a set function to
a continuous linear map on the type of L1 functions, see the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`.

## Main definitions

The pairing integral is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

1. Define the integral of the indicator of a set. This is `weightedVectorSMul B μ s x = B x (μ s)`.
  `weightedVectorSMul B μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
  (defined in the file `Mathlib/MeasureTheory/Integral/SetToL1.lean`) with respect to the set `s`.

2. Define the structure `VectorMeasureWithPairing`, combining a pairing of two normed vector spaces
  and a vector measure.

3. Define the pairing integral on L1 functions `f` as `setToL1 (...) f`. Note that, differently
  from the definition of Bochner integral, here `setToL1` is already a continuous linear map from
  L1 functions, not from step functions.

## Note

Let be `Bμ : VectorMeasureWithPairing`.
We often consider L1 functions with respect to the total variation of `Bμ.vectorMeasure`:
* `α →₁[Bμ.vectorMeasure.variation.ennrealToVectorMeasure] E` : `E`-valued functions in L1 space.

-/

open ENNReal Set MeasureTheory VectorMeasure ContinuousLinearMap

namespace MeasureTheory

section weightedVectorSMul

variable {α E F G : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (B : E →L[ℝ] F →L[ℝ] G) (μ : VectorMeasure α F)

/-- Given a set `s`, return the continuous linear map `fun x : E => B x (μ s)`, where the `B` is a
`G`-valued bilinear form on `E` `F` and `μ` is an `F`-valued vector measure. The extension of that
set function through `setToL1` gives the pairing integral of L1 functions. -/
def weightedVectorSMul (s : Set α) : E →L[ℝ] G where
  toFun x := B x (μ s)
  map_add' _ _ := map_add₂ B _ _ (μ s)
  map_smul' _ _ := map_smulₛₗ₂ B _ _ (μ s)

@[simp]
theorem weightedVectorSMul_apply (s : Set α) (x : E) : weightedVectorSMul B μ s x = B x (μ s) := rfl

theorem weightedVectorSMul_union (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hdisj : Disjoint s t) :
    (weightedVectorSMul B μ (s ∪ t) : E →L[ℝ] G)
    = weightedVectorSMul B μ s + weightedVectorSMul B μ t := by
  ext x
  simp only [weightedVectorSMul_apply, ContinuousLinearMap.add_apply]
  rw [← (B x).map_add]
  congr
  exact of_union hdisj hs ht

theorem norm_weightedVectorSMul_le (s : Set α) :
    ‖(weightedVectorSMul B μ s : E →L[ℝ] G)‖ ≤ ‖B‖ * ‖μ s‖ := by
  rw [ContinuousLinearMap.opNorm_le_iff (mul_nonneg (norm_nonneg B) (norm_nonneg (μ s)))]
  intro x
  simp only [weightedVectorSMul_apply]
  apply le_trans (le_opNorm (B x) (μ s))
  rw [mul_assoc, mul_comm _ ‖x‖, ← mul_assoc]
  gcongr
  exact le_opNorm B x

theorem dominatedFinMeasAdditive_weightedVectorSMul :
    DominatedFinMeasAdditive (μ.variation.ennrealToMeasure)
    (weightedVectorSMul B μ : Set α → E →L[ℝ] G) ‖B‖ := by
  refine ⟨fun s t hs ht _ _ hdisj => weightedVectorSMul_union B μ s t hs ht hdisj, ?_⟩
  intro s hs hsf
  apply (fun s _ _ => (norm_weightedVectorSMul_le B μ s).trans)
  gcongr
  rw [Measure.real, ← ofReal_le_iff_le_toReal (LT.lt.ne_top hsf), ennrealToMeasure_apply hs,
    ofReal_norm]
  exact norm_measure_le_variation μ s

end weightedVectorSMul

open SimpleFunc L1

section

variable (α E F G : Type*) [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

structure VectorMeasureWithPairing where
  pairing : E →L[ℝ] F →L[ℝ] G
  vectorMeasure : VectorMeasure α F

end

namespace VectorMeasureWithPairing

variable {α E F G : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  (Bμ : VectorMeasureWithPairing α E F G)

/-- The pairing integral in L1 space as a continuous linear map. -/
noncomputable def pairingIntegral : (α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E) →L[ℝ] G :=
    setToL1 (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)

@[simp]
theorem pairingIntegral_zero :
    Bμ.pairingIntegral (0 : α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E) = 0 := by
  simp [pairingIntegral]

@[integral_simps]
theorem pairingIntegral_add (f g : α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E) :
    Bμ.pairingIntegral (f + g) = Bμ.pairingIntegral f + Bμ.pairingIntegral g := by
  simp [pairingIntegral]

@[integral_simps]
theorem pairingIntegral_neg (f : α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E) :
    Bμ.pairingIntegral (-f) = -Bμ.pairingIntegral f := by
  simp [pairingIntegral]

@[integral_simps]
theorem pairingIntegral_sub (f g : α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E) :
    Bμ.pairingIntegral (f - g) = Bμ.pairingIntegral f - Bμ.pairingIntegral g := by
  simp [pairingIntegral]

@[integral_simps]
theorem pairingIntegral_smul (c : ℝ) (f : α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E) :
    Bμ.pairingIntegral (c • f) = c • Bμ.pairingIntegral f := by
  simp [pairingIntegral]

@[simp]
lemma pairingIntegral_apply (f : (α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E)) :
    Bμ.pairingIntegral f
    = setToL1 (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) f := rfl

theorem pairingIntegral_le (f : (α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E)) :
    ‖Bμ.pairingIntegral f‖ ≤ ‖Bμ.pairing‖ * ‖f‖:= by
  simp only [pairingIntegral_apply]
  exact norm_setToL1_le_mul_norm
    (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
    (norm_nonneg Bμ.pairing) f

theorem norm_pairingIntegral_le_norm_pairing : ‖Bμ.pairingIntegral‖ ≤ ‖Bμ.pairing‖ :=
  (ContinuousLinearMap.opNorm_le_iff (norm_nonneg Bμ.pairing)).mpr
  (pairingIntegral_le Bμ)

theorem nnnorm_pairingIntegral_le_nnNnorm : ‖Bμ.pairingIntegral‖₊ ≤ ‖Bμ.pairing‖₊ :=
  norm_pairingIntegral_le_norm_pairing Bμ

theorem nnnorm_pairingIntegral_le (f : α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E) :
    ‖Bμ.pairingIntegral f‖₊ ≤ ‖Bμ.pairing‖₊ * ‖f‖₊ := pairingIntegral_le Bμ f

@[continuity]
theorem continuous_pairingIntegral :
    Continuous fun f : α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E =>
    Bμ.pairingIntegral f :=
  (setToL1 (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)).continuous

end VectorMeasureWithPairing

section ScalarSMul

/-- The embedding of `ℝ` to the multiple of the identity map as an `F`-valued pairing of
`ℝ` and `F`. -/
def scalarSMulCLM (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] : ℝ →L[ℝ] F →L[ℝ] F where
  toFun c := c • (id ℝ F)
  map_add' _ _ := Module.add_smul _ _ (id ℝ F)
  map_smul' _ _ := IsScalarTower.smul_assoc _ _ (id ℝ F)

end ScalarSMul

namespace VectorMeasure

variable {α F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : VectorMeasure α F)

def withPairing : VectorMeasureWithPairing α ℝ F F where
  pairing := scalarSMulCLM F
  vectorMeasure := μ

/-- The `F`-valued integral with respect to an `F`-valued vector measure, defined as the pairing
integral where the pairing is `scalarSMulCLM`. -/
noncomputable def integral (f : α →₁[μ.variation.ennrealToMeasure] ℝ) : F :=
    μ.withPairing.pairingIntegral f

end VectorMeasure

end MeasureTheory
