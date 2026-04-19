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
We fix a continuous linear pairing `B : E →L[ℝ] F →L[ℝ] G` and an `F`-valued vector measure `μ`
on a measurable space `X`.
The vector measure `μ` gives the total variation measure `(μ.comp B.flip).variation` on `X`.
For an integrable function `f : X → E` with respect to this total variation measure,
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

Let `Bμ : VectorMeasureWithPairing`.
We often consider integrable functions with respect to the total variation of
`Bμ.transpose` = `Bμ.vectormeasure.comp Bμ.pairing.flip`, which is the reference measure for the
pairing integral.

When `f` is not integrable with respect to `Bμ.transpose.variation`, the value of `Bμ.integral f`
is set to `0`. This is an analogous convention to the Bochner integral. However, there are cases
where a natural definition of the integral as an unconditional sum exists, but `f` is not integrable
in this sense: Let `μ` be the `L∞(ℕ)`-valued measure on `ℕ` defined by extending
`{n} => (0,0,..., 1/(n+1),0,0,...)`. The total variation is `∑ n, 1/(n+1) = ∞`, but the sum of
`(0,...,0,1/n,0,...)` in `L∞(ℕ)` is unconditionally convergent.

-/

public section

open ENNReal Set MeasureTheory VectorMeasure ContinuousLinearMap

variable {X E F G : Type*} {mX : MeasurableSpace X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace MeasureTheory

section cbmApplyMeasure

/-- Given a set `s`, return the continuous linear map `fun x : E => B x (μ s)`, where the `B` is a
`G`-valued bilinear form on `E × F` and `μ` is an `F`-valued vector measure. The extension of that
set function through `setToL1` gives the pairing integral of L1 functions. -/
noncomputable def cbmApplyMeasure (B : E →L[ℝ] F →L[ℝ] G) (μ : VectorMeasure X F) (s : Set X) :
    E →L[ℝ] G where
  toFun x := μ.mapRange B.flip.toAddMonoidHom B.flip.continuous s x
  map_add' _ _ := map_add₂ ..
  map_smul' _ _ := map_smulₛₗ₂ ..

@[simp]
theorem cbmApplyMeasure_apply (B : E →L[ℝ] F →L[ℝ] G) (μ : VectorMeasure X F) (s : Set X) (x : E) :
    cbmApplyMeasure B μ s x = B x (μ s) := by
  rfl

theorem cbmApplyMeasure_union (B : E →L[ℝ] F →L[ℝ] G) (μ : VectorMeasure X F) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    cbmApplyMeasure B μ (s ∪ t) = cbmApplyMeasure B μ s + cbmApplyMeasure B μ t := by
  ext x
  simp [cbmApplyMeasure_apply, of_union hdisj hs ht, (B x).map_add]

theorem dominatedFinMeasAdditive_cbmApplyMeasure (B : E →L[ℝ] F →L[ℝ] G) (μ : VectorMeasure X F) :
    DominatedFinMeasAdditive (μ.mapRange B.flip.toAddMonoidHom B.flip.continuous).variation
    (cbmApplyMeasure B μ : Set X → E →L[ℝ] G) 1 := by
  refine ⟨fun s t hs ht _ _ hdisj => cbmApplyMeasure_union B μ hs ht hdisj, ?_⟩
  intro s hs hsf
  simpa using norm_measure_le_variation hsf.ne

theorem norm_cbmApplyMeasure_le (B : E →L[ℝ] F →L[ℝ] G) (μ : VectorMeasure X F) (s : Set X) :
    ‖cbmApplyMeasure B μ s‖ ≤ ‖B‖ * ‖μ s‖ := by
  rw [opNorm_le_iff (by positivity)]
  intro x
  grw [cbmApplyMeasure_apply, le_opNorm₂, mul_right_comm]

end cbmApplyMeasure

open SimpleFunc L1

section

variable (X E F G) [mX] in
/-- The structure containing a continuous linear pairing and a vector measure,
enabling the dot notation `VectorMeasureWithParing.integral`. -/
structure VectorMeasureWithPairing where
  /-- A continuous linear pairing from `E` `F` into a Banach space `G`. -/
  pairing : E →L[ℝ] F →L[ℝ] G
  /-- An `F`-valued vector measure. -/
  vectorMeasure : VectorMeasure X F

end

namespace VectorMeasureWithPairing

/-- The composition of the vector-measure part with the paring part, giving the reference
vector measure. -/
@[expose]
noncomputable def transpose (Bμ : VectorMeasureWithPairing X E F G) : VectorMeasure X (E →L[ℝ] G) :=
  Bμ.vectorMeasure.mapRange Bμ.pairing.flip.toAddMonoidHom Bμ.pairing.flip.continuous

lemma transpose_def (Bμ : VectorMeasureWithPairing X E F G) :
    Bμ.transpose =
    Bμ.vectorMeasure.mapRange Bμ.pairing.flip.toAddMonoidHom Bμ.pairing.flip.continuous := by rfl

/-- `f : X → E` is said to be integrable with respect to `Bμ` if it is integrable with respect to
`Bμ.transpose.variation`. -/
abbrev Integrable (Bμ : VectorMeasureWithPairing X E F G) (f : X → E) : Prop :=
  MeasureTheory.Integrable f Bμ.transpose.variation

open Classical in
/-- The pairing integral in L1 space as a continuous linear map. -/
noncomputable def integral (Bμ : VectorMeasureWithPairing X E F G) (f : X → E) : G :=
  if _ : CompleteSpace G then
  setToFun Bμ.transpose.variation Bμ.transpose
    (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) f
  else 0

@[inherit_doc integral]
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂"Bμ:70 => integral Bμ r

/-- The special case of the pairing integral where the pairing is just the scalar multiplication by
`ℝ` and the `F`-valued vector measure is denoted by `μ`, and the resulting integral is `F`-valued.-/
local notation3 "∫ "(...)", "r:60:(scoped f => f)" ∂•"μ:70 => integral
  (VectorMeasureWithPairing.mk (lsmul (E := E) ℝ ℝ) μ) r

variable {Bμ : VectorMeasureWithPairing X E F G}

@[integral_simps]
theorem integral_fun_add (f g : X → E) (hf : Bμ.Integrable f) (hg : Bμ.Integrable g) :
    ∫ᵛ x, (fun x => f x + g x) x ∂Bμ = ∫ᵛ x, f x ∂Bμ + ∫ᵛ x, g x ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_add (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) hf hg
  · simp [integral, hG]

@[integral_simps]
theorem integral_add (f g : X → E) (hf : Bμ.Integrable f) (hg : Bμ.Integrable g) :
    ∫ᵛ x, (f + g) x ∂Bμ = ∫ᵛ x, f x ∂Bμ + ∫ᵛ x, g x ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_add (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) hf hg
  · simp [integral, hG]

variable (Bμ) in
@[integral_simps]
theorem integral_fun_neg (f : X → E) : ∫ᵛ x, (fun x => -f x) x ∂Bμ = -∫ᵛ x, f x ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_neg (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) f
  · simp [integral, hG]

variable (Bμ) in
@[integral_simps]
theorem integral_neg (f : X → E) : ∫ᵛ x, (-f) x ∂Bμ = -∫ᵛ x, f x ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_neg (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) f
  · simp [integral, hG]

@[integral_simps]
theorem integral_fun_sub (f g : X → E) (hf : Bμ.Integrable f) (hg : Bμ.Integrable g) :
    ∫ᵛ x, (fun x => f x - g x) x ∂Bμ = ∫ᵛ x, f x ∂Bμ - ∫ᵛ x, g x ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_sub (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) hf hg
  · simp [integral, hG]

@[integral_simps]
theorem integral_sub (f g : X → E) (hf : Bμ.Integrable f) (hg : Bμ.Integrable g) :
    ∫ᵛ x, (f - g) x ∂Bμ = ∫ᵛ x, f x ∂Bμ - ∫ᵛ x, g x ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_sub (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure) hf hg
  · simp [integral, hG]

variable (Bμ) in
@[integral_simps]
theorem integral_smul (c : ℝ) (f : X → E) :
    ∫ᵛ x, (fun x => c • f x) x ∂Bμ = c • ∫ᵛ x, f x ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_smul (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure)
      (by simp) c f
  · simp [integral, hG]

variable (Bμ) in
@[integral_simps]
theorem integral_fun_smul (c : ℝ) (f : X → E) :
    ∫ᵛ x, c • f x ∂Bμ = c • ∫ᵛ x, f x ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_smul (dominatedFinMeasAdditive_cbmApplyMeasure Bμ.pairing Bμ.vectorMeasure)
      (by simp) c f
  · simp [integral, hG]

end VectorMeasureWithPairing

end MeasureTheory
