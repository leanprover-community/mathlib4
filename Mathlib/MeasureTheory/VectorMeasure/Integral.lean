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
The vector measure `μ` gives the total variation measure `(μ.comp B.flip).variation` on `α`.
For an integrable function `f : α → E` with respect to this total variation measure,
we define the `G`-valued integral, which is informally written `∫ B (f x) ∂μ x`.

The pairing integral is defined through the general setting `setToFun` which sends a set function to
the integral of integrable functions, see the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`.

## Main definitions

The pairing integral is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

1. Define the integral of the indicator of a set. This is `cbmApplyMeasure B μ s x = B x (μ s)`.
  `cbmApplyMeasure B μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
  (defined in the file `Mathlib/MeasureTheory/Integral/SetToL1.lean`) with respect to the set `s`.

2. Define the structure `VectorMeasureWithPairing`, combining a pairing of two normed vector spaces
  and a vector measure.

3. Define the pairing integral on integrable functions `f` as `setToFun (...) f`.

## Note

Let be `Bμ : VectorMeasureWithPairing`.
We often consider integrable functions with respect to the total variation of
`Bμ.transpose` = `Bμ.vectormeasure.comp Bμ.pairing.flip`, which is the reference measure for the
pairing integral.

-/

public section

open ENNReal Set MeasureTheory VectorMeasure ContinuousLinearMap

namespace MeasureTheory

section

variable {α F G : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The composition of an `F`-valued vector measure with a continuous linear map from `F` to `G`. -/
def VectorMeasure.comp (μ : VectorMeasure α F) (X : F →L[ℝ] G) : VectorMeasure α G where
  measureOf' x := X (μ x)
  empty' := by simp
  not_measurable' s hs := by rw [μ.not_measurable hs, ContinuousLinearMap.map_zero]
  m_iUnion' s hs sdisj := ContinuousLinearMap.hasSum X <| μ.m_iUnion hs sdisj

end

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
  toFun x := μ.comp B.flip s x
  map_add' _ _ := map_add₂ ..
  map_smul' _ _ := map_smulₛₗ₂ ..

@[simp]
theorem cbmApplyMeasure_apply (s : Set α) (x : E) : cbmApplyMeasure B μ s x = B x (μ s) := by
  rfl

theorem cbmApplyMeasure_smul (c : ℝ) (s : Set α) (x : E) :
    cbmApplyMeasure B μ s (c • x) = c • cbmApplyMeasure B μ s x := by simp

theorem cbmApplyMeasure_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hdisj : Disjoint s t) :
    cbmApplyMeasure B μ (s ∪ t) = cbmApplyMeasure B μ s + cbmApplyMeasure B μ t := by
  ext x
  simp [cbmApplyMeasure_apply, of_union hdisj hs ht, (B x).map_add]

theorem dominatedFinMeasAdditive_cbmApplyMeasure :
    DominatedFinMeasAdditive (μ.comp B.flip).variation
    (cbmApplyMeasure B μ : Set α → E →L[ℝ] G) 1 := by
  refine ⟨fun s t hs ht _ _ hdisj => cbmApplyMeasure_union B μ hs ht hdisj, ?_⟩
  intro s hs hsf
  simpa using norm_measure_le_variation hsf.ne

theorem norm_cbmApplyMeasure_le (s : Set α) :
    ‖cbmApplyMeasure B μ s‖ ≤ ‖B‖ * ‖μ s‖ := by
  rw [opNorm_le_iff (by positivity)]
  intro x
  grw [cbmApplyMeasure_apply, le_opNorm₂, mul_right_comm]

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
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (Bμ : VectorMeasureWithPairing α E F G)

/-- The composition of the vector-measure part with the paring part, giving the reference
vector measure. -/
noncomputable def transpose : VectorMeasure α (E →L[ℝ] G) :=
  Bμ.vectorMeasure.comp Bμ.pairing.flip

lemma transpose_def : Bμ.transpose = Bμ.vectorMeasure.comp Bμ.pairing.flip := by rfl

variable [CompleteSpace G]

/-- The pairing integral in L1 space as a continuous linear map. -/
noncomputable def integral (f : α → E) : G :=
  setToFun Bμ.transpose.variation Bμ.transpose
    (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) f

@[integral_simps]
theorem integral_add (f g : α → E) (hf : Integrable f Bμ.transpose.variation)
    (hg : Integrable g Bμ.transpose.variation) :
    Bμ.integral (fun x => f x + g x) = Bμ.integral f + Bμ.integral g :=
  setToFun_add (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) hf hg

@[integral_simps]
theorem integral_add' (f g : α → E) (hf : Integrable f Bμ.transpose.variation)
    (hg : Integrable g Bμ.transpose.variation) :
    Bμ.integral (f + g) = Bμ.integral f + Bμ.integral g :=
  setToFun_add (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) hf hg

@[integral_simps]
theorem integral_neg (f : α → E) :
  Bμ.integral (fun x => -f x) = -Bμ.integral f :=
  setToFun_neg (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) f

@[integral_simps]
theorem integral_neg' (f : α → E) :
  Bμ.integral (-f) = -Bμ.integral f :=
  setToFun_neg (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) f

@[integral_simps]
theorem integral_sub (f g : α → E) (hf : Integrable f Bμ.transpose.variation)
    (hg : Integrable g Bμ.transpose.variation) :
    Bμ.integral (fun x => f x - g x) = Bμ.integral f - Bμ.integral g :=
  setToFun_sub (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) hf hg

@[integral_simps]
theorem integral_sub' (f g : α → E) (hf : Integrable f Bμ.transpose.variation)
    (hg : Integrable g Bμ.transpose.variation) :
    Bμ.integral (f - g) = Bμ.integral f - Bμ.integral g :=
  setToFun_sub (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) hf hg

@[integral_simps]
theorem integral_smul (c : ℝ) (f : α → E) :
    Bμ.integral (c • f) = c • Bμ.integral f :=
  setToFun_smul (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure)
    (cbmApplyMeasure_smul Bμ.pairing Bμ.vectorMeasure) c f

@[simp]
lemma integral_apply (f : (α → E)) (hf : Integrable f Bμ.transpose.variation) :
    have : Integrable f (Bμ.vectorMeasure.comp Bμ.pairing.flip).variation := by
      simpa [transpose_def] using hf
    Bμ.integral f =
    L1.setToL1 (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure)
    (this.toL1 f) := by
  simp only [integral, setToFun]
  exact dif_pos (integral_apply._proof_1 Bμ f hf)

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
noncomputable def integral (f : α → ℝ) : F :=
    μ.withPairing.integral f

end VectorMeasure

end MeasureTheory
