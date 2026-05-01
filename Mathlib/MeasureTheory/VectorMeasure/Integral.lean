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
For an integrable function `f : X → E` with respect to the total variation of the vector measure
on `X` informally written `μ ∘ B.flip`, we define the `G`-valued integral, which is informally
written `∫ B (f x) ∂μ x`.

Such integral is defined through the general setting `setToFun` which sends a set function to the
integral of integrable functions, see the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`.

## Main definitions

The integral against vector measures is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

1. Define the integral of the indicator of a set. This is `cbmApplyMeasure B μ s x = B x (μ s)`.
  `cbmApplyMeasure B μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
  (defined in the file `Mathlib/MeasureTheory/Integral/SetToL1.lean`) with respect to the set `s`.

2. Define the integral on integrable functions `f` as `setToFun (...) f`.

## Notations

* `∫ᵛ x, f x ∂[B; μ]` : the `G`-valued integral of an `E`-valued function `f` against the
  vector measure `μ` paired through `B`.
* `∫ x, f x ∂•μ` : the special case where `f` is a real-valued function and `μ` is an `F`-valued
  vector measure, with the pairing being the scalar multiplication by `ℝ`.

## Note

Let `μ` be a vector measure and `B` be a continuous linear pairing.
We often consider integrable functions with respect to the total variation of
`μ.transpose B` = `μ.mapRange B.flip.toAddMonoidHom B.flip.continuous`, which is the reference
measure for the pairing integral.

When `f` is not integrable with respect to `(μ.transpose B).variation`, the value of
`μ.integral B f` is set to `0`. This is an analogous convention to the Bochner integral. However,
there are cases where a natural definition of the integral as an unconditional sum exists, but `f`
is not integrable in this sense: Let `μ` be the `L∞(ℕ)`-valued measure on `ℕ` defined by extending
`{n} ↦ (0,0,..., 1/(n+1),0,0,...)` and `B` be the trivial coupling (the scalar multiplication by
`ℝ`). The total variation is `∑ n, 1/(n+1) = ∞`, but the sum of `(0,...,0,1/n,0,...)` in `L∞(ℕ)` is
unconditionally convergent.

-/

public section

open ENNReal Set MeasureTheory VectorMeasure ContinuousLinearMap

variable {X E F G : Type*} {mX : MeasurableSpace X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace MeasureTheory

section cbmApplyMeasure

/-- The composition of the vector measure with the linear pairing, giving the reference
vector measure. -/
@[expose]
noncomputable def VectorMeasure.transpose (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure X (E →L[ℝ] G) := μ.mapRange B.flip.toAddMonoidHom B.flip.continuous

/-- Given a set `s`, return the continuous linear map `fun x : E ↦ B x (μ s)` (actually defined
using `mapRange`), where the `B` is a `G`-valued bilinear form on `E × F` and `μ` is an `F`-valued
vector measure. The extension of that set function through `setToFun` gives the pairing integral of
integrable functions. -/
noncomputable def cbmApplyMeasure (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) :
    E →L[ℝ] G where
  toFun x := μ.transpose B s x
  map_add' _ _ := map_add₂ ..
  map_smul' _ _ := map_smulₛₗ₂ ..

lemma transpose_eq_cbmApplyMeasure (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    μ.transpose B = cbmApplyMeasure μ B := by rfl

@[simp]
theorem cbmApplyMeasure_apply (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) (x : E) :
    cbmApplyMeasure μ B s x = B x (μ s) := by
  rfl

theorem cbmApplyMeasure_union (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    cbmApplyMeasure μ B (s ∪ t) = cbmApplyMeasure μ B s + cbmApplyMeasure μ B t := by
  ext x
  simp [of_union hdisj hs ht]

theorem dominatedFinMeasAdditive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    DominatedFinMeasAdditive (μ.transpose B).variation
    (cbmApplyMeasure μ B : Set X → E →L[ℝ] G) 1 := by
  refine ⟨fun s t hs ht _ _ hdisj ↦ cbmApplyMeasure_union μ B hs ht hdisj, fun s hs hsf ↦ ?_⟩
  simpa using norm_measure_le_variation hsf.ne

theorem norm_cbmApplyMeasure_le (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) :
    ‖cbmApplyMeasure μ B s‖ ≤ ‖B‖ * ‖μ s‖ := by
  rw [opNorm_le_iff (by positivity)]
  intro x
  grw [cbmApplyMeasure_apply, le_opNorm₂, mul_right_comm]

end cbmApplyMeasure

namespace VectorMeasure

/-- `f : X → E` is said to be integrable with respect to `μ` and `B` if it is integrable with
respect to `(μ.transpose B).variation`. -/
abbrev Integrable (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (f : X → E) : Prop :=
  MeasureTheory.Integrable f (μ.transpose B).variation

open Classical in
/-- The `G`-valued integral of `E`-valued function and the `F`-valued vector measure `μ` with linear
 paring `B : E →L[ℝ] F →L[ℝ] G` . -/
noncomputable def integral (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (f : X → E) : G :=
  if _ : CompleteSpace G then
  setToFun (μ.transpose B).variation (μ.transpose B)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f
  else 0

@[inherit_doc integral]
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂["B:70"; "μ:70"]" => integral μ B r

/-- The special case of the pairing integral where the pairing is just the scalar multiplication by
`ℝ` and the `F`-valued vector measure is denoted by `μ`, and the resulting integral is `F`-valued.-/
local notation3 "∫ "(...)", "r:60:(scoped f => f)" ∂•"μ:70 => integral μ (lsmul (E := E) ℝ ℝ) r

variable {μ : VectorMeasure X F} {B : E →L[ℝ] F →L[ℝ] G}

@[integral_simps]
theorem integral_fun_add {f g : X → E} (hf : μ.Integrable B f) (hg : μ.Integrable B g) :
    ∫ᵛ x, f x + g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ] := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_add (dominatedFinMeasAdditive_cbmApplyMeasure μ B) hf hg
  · simp [integral, hG]

@[integral_simps]
theorem integral_add {f g : X → E} (hf : μ.Integrable B f) (hg : μ.Integrable B g) :
    ∫ᵛ x, (f + g) x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ] := integral_fun_add hf hg

variable (μ B) in
@[integral_simps]
theorem integral_fun_neg (f : X → E) :
    ∫ᵛ x, -f x ∂[B; μ]= -∫ᵛ x, f x ∂[B; μ] := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, ↓reduceDIte, transpose_eq_cbmApplyMeasure]
    exact setToFun_neg (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f
  · simp [integral, hG]

variable (μ B) in
@[integral_simps]
theorem integral_neg (f : X → E) :
    ∫ᵛ x, (-f) x ∂[B; μ] = -∫ᵛ x, f x ∂[B; μ] := integral_fun_neg μ B f

@[integral_simps]
theorem integral_fun_sub {f g : X → E} (hf : μ.Integrable B f) (hg : μ.Integrable B g) :
    ∫ᵛ x, f x - g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ] := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_sub (dominatedFinMeasAdditive_cbmApplyMeasure μ B) hf hg
  · simp [integral, hG]

@[integral_simps]
theorem integral_sub (f g : X → E) (hf : μ.Integrable B f) (hg : μ.Integrable B g) :
    ∫ᵛ x, (f - g) x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ] := integral_fun_sub hf hg

variable (μ B) in
@[integral_simps]
theorem integral_fun_smul (c : ℝ) (f : X → E) :
    ∫ᵛ x, c • f x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_smul (dominatedFinMeasAdditive_cbmApplyMeasure μ B) (by simp) c f
  · simp [integral, hG]

variable (μ B) in
@[integral_simps]
theorem integral_smul (c : ℝ) (f : X → E) :
    ∫ᵛ x, (c • f) x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] := integral_fun_smul μ B c f

end VectorMeasure

end MeasureTheory
