/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto, Yongxi Lin, Sébastien Gouëzel
-/
module

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

* `∫ᵛ x, f x ∂[B; μ]`: the `G`-valued integral of an `E`-valued function `f` against the `F`-valued
  vector measure `μ` paired through `B`.
* `∫ᵛ x, f x ∂•μ`: the special case where `f` is a real-valued function and `μ` is an `F`-valued
  vector measure, with the pairing being the scalar multiplication by `ℝ`.
* `∫ᵛ x, f x ∂<•μ`: the special case where `f` is an `E`-valued function and `μ` is a signed
  measure, with the pairing being the flip of scalar multiplication.
* `∫ᵛ x in s, f x ∂[B; μ]`: the `G`-valued integral of an `E`-valued function `f` against
  the `F`-valued vector measure `μ` paired through `B`, on the set `s`.
* `∫ᵛ x in s, f x ∂•μ`: the special case where `f` is a real-valued function and `μ` is
  an `F`-valued vector measure, with the pairing being the scalar multiplication by `ℝ`.
* `∫ᵛ x in s, f x ∂<•μ`: the special case where `f` is an `E`-valued function and `μ` is a signed
  measure, with the pairing being the flip of scalar multiplication.

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

open Set MeasureTheory VectorMeasure ContinuousLinearMap
open scoped ENNReal NNReal

variable {ι X Y E F G : Type*} {mX : MeasurableSpace X} [MeasurableSpace Y]
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
using `transpose` through `mapRange`), where the `B` is a `G`-valued bilinear form on `E × F` and
`μ` is an `F`-valued vector measure. The extension of that set function through `setToFun` gives the
pairing integral of `E`-valued integrable functions. -/
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
    DominatedFinMeasAdditive (μ.transpose B).variation (μ.transpose B) 1 := by
  refine ⟨fun s t hs ht _ _ hdisj ↦ cbmApplyMeasure_union μ B hs ht hdisj, fun s hs hsf ↦ ?_⟩
  simpa using! norm_measure_le_variation hsf.ne

theorem norm_cbmApplyMeasure_le (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) :
    ‖cbmApplyMeasure μ B s‖ ≤ ‖B‖ * ‖μ s‖ := by
  rw [opNorm_le_iff (by positivity)]
  intro x
  grw [cbmApplyMeasure_apply, le_opNorm₂, mul_right_comm]

end cbmApplyMeasure

namespace VectorMeasure

variable (μ ν : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) {C : E →L[ℝ] F →L[ℝ] G}
  {f g : X → E} {φ : X → Y}

@[simp] lemma transpose_zero : (0 : VectorMeasure X F).transpose B = 0 := by
  simp [transpose]

lemma transpose_restrict (s : Set X) :
    (μ.restrict s).transpose B = (μ.transpose B).restrict s := by
  by_cases hs : MeasurableSet s
  · ext t ht : 1
    simp [VectorMeasure.restrict_apply, hs, ht, transpose]
  · simp [restrict_not_measurable _ hs]

lemma transpose_map : (μ.map φ).transpose B = (μ.transpose B).map φ := by
  by_cases hφ : Measurable φ; swap
  · simp [map, hφ]
  ext s hs
  simp [transpose, map_apply, hs, hφ]

lemma transpose_add :
    (μ + ν).transpose B = μ.transpose B + ν.transpose B := by
  simp [transpose]

lemma transpose_smul (c : ℝ) :
    (c • μ).transpose B = c • μ.transpose B := by
  simp [transpose, mapRange_smul]

lemma transpose_dirac (x : X) (v : F) :
    (dirac x v).transpose B = dirac x (B.flip v) := by
  ext s hs : 1
  by_cases hx : x ∈ s <;> simp [transpose, hx, hs]

lemma variation_transpose_le :
    (μ.transpose B).variation ≤ ‖B‖₊ • μ.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
  apply opENorm_le_bound _ (fun x ↦ ?_)
  simp only [transpose, mapRange_apply, LinearMap.toAddMonoidHom_coe, coe_coe, flip_apply,
    Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [le_opNorm_enorm, le_opNorm_enorm, enorm_measure_le_variation, ← enorm_eq_nnnorm]
  exact le_of_eq (by ring)

lemma absolutelyContinuous_variation_transpose (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    (μ.transpose B).variation ≪ μ.variation :=
  Measure.absolutelyContinuous_of_le_smul (variation_transpose_le μ B)

instance [IsFiniteMeasure μ.variation] :
    IsFiniteMeasure (μ.transpose B).variation :=
  isFiniteMeasure_of_le _ (variation_transpose_le μ B)

lemma variation_transpose_eq_smul [Nontrivial E] {C : ℝ≥0}
    (hB : ∀ x y, ‖B x y‖₊ = C * ‖x‖₊ * ‖y‖₊) :
    (μ.transpose B).variation = C • μ.variation := by
  apply le_antisymm
  · apply (variation_transpose_le _ _).trans
    gcongr
    apply opNNNorm_le_bound _ _ (fun x ↦ opNNNorm_le_bound _ _ (fun y ↦ by simp [hB]))
  · rcases eq_or_ne C 0 with rfl | hC
    · simp [Measure.zero_le]
    suffices μ.variation ≤ C⁻¹ • (μ.transpose B).variation by
      grw [this, smul_smul, mul_inv_cancel₀ hC, one_smul]
    apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
    have : ‖μ s‖ₑ ≤ C⁻¹ • ‖(μ.transpose B) s‖ₑ := by
      simp only [transpose, mapRange_apply, LinearMap.toAddMonoidHom_coe, coe_coe]
      obtain ⟨x, hx⟩ : ∃ (x : E), x ≠ 0 := exists_ne 0
      have : ‖B.flip (μ s) x‖₊ ≤ ‖B.flip (μ s)‖₊ * ‖x‖₊ := le_opNNNorm _ _
      simp only [flip_apply, hB] at this
      rw [mul_right_comm, mul_le_mul_iff_left₀ (by simpa), ← le_div_iff₀' (by positivity),
        div_eq_inv_mul] at this
      exact ENNReal.coe_le_coe_of_le this
    grw [this, enorm_measure_le_variation, Measure.smul_apply]

lemma variation_transpose_eq [Nontrivial E] (hB : ∀ x y, ‖B x y‖₊ = ‖x‖₊ * ‖y‖₊) :
    (μ.transpose B).variation = μ.variation := by
  have : μ.variation = (1 : ℝ≥0) • μ.variation := by simp
  rw [this]
  apply variation_transpose_eq_smul
  simpa using hB

/-- Control of the variation of the vector measure which appears in the integral of scalar functions
with respect to a vector measure. -/
@[simp] lemma variation_transpose_lsmul :
    (μ.transpose (ContinuousLinearMap.lsmul ℝ ℝ)).variation = μ.variation := by
  apply variation_transpose_eq
  simp [nnnorm_smul, mul_comm]

/-- Control of the variation of the vector measure which appears in the integral of a vector
function with respect to a signed measure. -/
@[simp] lemma variation_transpose_lsmul_flip [Nontrivial E] {μ : SignedMeasure X} :
    (μ.transpose (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip).variation = μ.variation := by
  apply variation_transpose_eq
  simp [nnnorm_smul, mul_comm]

/-- `f : X → E` is said to be integrable with respect to `μ` and `B` if it is integrable with
respect to `(μ.transpose B).variation`. -/
protected abbrev Integrable (μ : VectorMeasure X F) (f : X → E) (B : E →L[ℝ] F →L[ℝ] G) : Prop :=
  MeasureTheory.Integrable f (μ.transpose B).variation

/-- `f : X → E` is said to be integrable with respect to `μ` and `B` on `s` if it is integrable with
respect to the vector measure `μ.restrict s`. When `s` is measurable, this is equivalent to
integrability with respect to `(μ.transpose B).variation.restrict s`. -/
protected abbrev IntegrableOn
    (μ : VectorMeasure X F) (f : X → E) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) : Prop :=
  (μ.restrict s).Integrable f B

open Classical in
/-- The `G`-valued integral of `E`-valued function and the `F`-valued vector measure `μ` with linear
paring `B : E →L[ℝ] F →L[ℝ] G` . This is set to be `0` if `G` is not complete or if `f` is not
integrable with respect to `(μ.transpose B).variation`. Notation `∫ᵛ x, f x ∂[B; μ]`.

When `μ` is `G`-valued, to get the integral in `G` of a real-valued function, take
`B = ContinousLinearMap.lsmul ℝ ℝ`. Notation `∫ᵛ x, f x ∂•μ`.
When `μ` is a signed measure, to get the integral in `G` of a `G`-valued function, take
`B = (ContinousLinearMap.lsmul ℝ ℝ).flip`. Notation `∫ᵛ x, f x ∂<•μ`.
-/
noncomputable def integral (μ : VectorMeasure X F) (f : X → E) (B : E →L[ℝ] F →L[ℝ] G) : G :=
  setToFun (μ.transpose B).variation (μ.transpose B)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f

@[inherit_doc integral]
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂["B:65"; "μ:65"]" => integral μ r B

/-- The special case of the pairing integral where the pairing is just the scalar multiplication by
`ℝ` on `F` and `f` is real-valued. The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂•"μ:70 => integral μ r (lsmul ℝ ℝ)

/-- The special case of the pairing integral where the pairing is just the flip of scalar
multiplication by `ℝ` on `F` and `f` is `F`-valued and `μ` is a signed measure.
The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂<•"μ:70 => integral μ r (lsmul ℝ ℝ).flip

@[inherit_doc integral]
notation3 "∫ᵛ "(...)" in "s", "r:60:(scoped f => f)" ∂["B:70"; "μ:70"]" =>
  integral (VectorMeasure.restrict μ s) r B

/-- The special case of the pairing integral in a set where the pairing is just the scalar
multiplication by `ℝ` on `F` and `f` is real-valued. The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)" in "s", "r:60:(scoped f => f)" ∂•"μ:70 =>
  integral (VectorMeasure.restrict μ s) r (lsmul ℝ ℝ)

/-- The special case of the pairing integral in a set where the pairing is just the flip of the
scalar multiplication by `ℝ` on `F` and `f` is `F`-valued and `μ` is a signed measure.
The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)" in "s", "r:60:(scoped f => f)" ∂<•"μ:70 =>
  integral (VectorMeasure.restrict μ s) r (lsmul ℝ ℝ).flip

variable {μ ν B}

lemma integral_eq_setToFun : ∫ᵛ x, f x ∂[B; μ] = setToFun (μ.transpose B).variation (μ.transpose B)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f := by rfl

theorem integral_of_not_completeSpace (hG : ¬CompleteSpace G) :
    ∫ᵛ x, f x ∂[B; μ] = 0 := by
  simp [integral, setToFun, hG]

variable {f g : X → E} {μ ν : VectorMeasure X F} {B C : E →L[ℝ] F →L[ℝ] G}

@[simp]
theorem transpose_zero_cbm (μ : VectorMeasure X F) :
    μ.transpose (0 : E →L[ℝ] F →L[ℝ] G) = 0 := by
  ext
  simp [transpose]

@[simp]
theorem transpose_add_vectorMeasure (μ ν : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    (μ + ν).transpose B = μ.transpose B + ν.transpose B := by
  simp [transpose]

@[simp]
theorem transpose_add_cbm (μ : VectorMeasure X F) (B C : E →L[ℝ] F →L[ℝ] G) :
    μ.transpose (B + C) = μ.transpose B + μ.transpose C := by
  ext
  simp [transpose]

@[simp]
theorem transpose_finsetSum_vectorMeasure (μ : ι → VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G)
    (s : Finset ι) :
    (∑ i ∈ s, μ i).transpose B = ∑ i ∈ s, (μ i).transpose B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih => simp [Finset.sum_insert, his, ih]

@[simp]
theorem transpose_finsetSum_cbm (μ : VectorMeasure X F) (B : ι → E →L[ℝ] F →L[ℝ] G) (s : Finset ι) :
    μ.transpose (∑ i ∈ s, B i) = ∑ i ∈ s, μ.transpose (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih => simp [Finset.sum_insert, his, ih]

@[simp]
theorem transpose_neg_vectorMeasure (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    (-μ).transpose B = - (μ.transpose B) := by
  ext
  simp [transpose]

@[simp]
theorem transpose_neg_cbm (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    μ.transpose (-B) = - (μ.transpose B) := by
  ext
  simp [transpose]

@[simp]
theorem transpose_sub_vectorMeasure (μ ν : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    (μ - ν).transpose B = μ.transpose B - ν.transpose B := by
  ext
  simp [transpose]

@[simp]
theorem transpose_sub_cbm (μ : VectorMeasure X F) (B C : E →L[ℝ] F →L[ℝ] G) :
    μ.transpose (B - C) = μ.transpose B - μ.transpose C := by
  ext
  simp [transpose]

section Function

theorem integral_undef (h : ¬ μ.Integrable f B) :
    ∫ᵛ x, f x ∂[B; μ] = 0 := by
  simp [integral, setToFun_undef _ h]

@[simp]
theorem integral_zero : ∫ᵛ _, 0 ∂[B; μ] = 0 :=
  setToFun_zero _

theorem integral_congr_ae (h : f =ᵐ[(μ.transpose B).variation] g) :
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ] :=
  setToFun_congr_ae _ h

theorem integral_eq_zero_of_ae (hf : f =ᵐ[(μ.transpose B).variation] 0) :
    ∫ᵛ x, f x ∂[B; μ] = 0 := by
  simp [integral_congr_ae hf]

theorem integral_fun_add (hf : μ.Integrable f B) (hg : μ.Integrable g B) :
    ∫ᵛ x, f x + g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ] :=
  setToFun_add _ hf hg

theorem integral_add (hf : μ.Integrable f B) (hg : μ.Integrable g B) :
    ∫ᵛ x, (f + g) x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ] := integral_fun_add hf hg

theorem integral_finsetSum (s : Finset ι) {f : ι → X → E}
    (hf : ∀ i ∈ s, μ.Integrable (f i) B) :
    ∫ᵛ x, ∑ i ∈ s, f i x ∂[B; μ] = ∑ i ∈ s, ∫ᵛ x, f i x ∂[B; μ] :=
  setToFun_finsetSum _ s hf

variable (f μ B) in
@[integral_simps]
theorem integral_fun_neg (f : X → E) :
    ∫ᵛ x, -f x ∂[B; μ]= -∫ᵛ x, f x ∂[B; μ] :=
  setToFun_neg _ f

variable (f μ B) in
@[integral_simps]
theorem integral_neg :
    ∫ᵛ x, (-f) x ∂[B; μ] = -∫ᵛ x, f x ∂[B; μ] := integral_fun_neg μ B f

theorem integral_fun_sub (hf : μ.Integrable f B) (hg : μ.Integrable g B) :
    ∫ᵛ x, f x - g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ] :=
  setToFun_sub _ hf hg

theorem integral_sub (hf : μ.Integrable f B) (hg : μ.Integrable g B) :
    ∫ᵛ x, (f - g) x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ] := integral_fun_sub hf hg

variable (f μ B) in
@[integral_simps]
theorem integral_fun_smul (c : ℝ) (f : X → E) :
    ∫ᵛ x, c • f x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] :=
  setToFun_smul _ (by simp) c f

variable (f μ B) in
@[integral_simps]
theorem integral_smul (c : ℝ) :
    ∫ᵛ x, (c • f) x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] := integral_fun_smul μ B c f

end Function

section VectorMeasure

/- `simpNF` complains that this lemma can be proved by `simp`, because the `simp`-generated lemma
unfolds the abbrev `VectorMeasure.Integrable`. TODO: fix `simp`. See lean4#13958. -/
@[nolint simpNF, simp]
lemma Integrable.zero_vectorMeasure : (0 : VectorMeasure X F).Integrable f B := by
  simp [VectorMeasure.Integrable]

lemma Integrable.add_vectorMeasure (hμ : μ.Integrable f B) (hν : ν.Integrable f B) :
    (μ + ν).Integrable f B := by
  apply Integrable.mono_measure (integrable_add_measure.2 ⟨hμ, hν⟩)
  grw [transpose_add, variation_add_le]

lemma Integrable.neg_vectorMeasure (hμ : μ.Integrable f B) :
    (-μ).Integrable f B :=
  Integrable.mono_measure hμ (by simp)

lemma Integrable.sub_vectorMeasure (hμ : μ.Integrable f B) (hν : ν.Integrable f B) :
    (μ - ν).Integrable f B := by
  convert hμ.add_vectorMeasure hν.neg_vectorMeasure using 1
  exact sub_eq_add_neg μ ν

lemma Integrable.smul_vectorMeasure (hμ : μ.Integrable f B) (c : ℝ) :
    (c • μ).Integrable f B := by
  apply Integrable.mono_measure (Integrable.smul_measure_nnreal hμ (c := ‖c‖₊))
  simp [transpose_smul, variation_smul]

lemma Integrable.finsetSum_vectorMeasure {ι : Type*} {μ : ι → VectorMeasure X F} {s : Finset ι}
    (h : ∀ i ∈ s, (μ i).Integrable f B) :
    (∑ i ∈ s, μ i).Integrable f B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
        Finset.sum_insert] at h ⊢
      exact h.1.add_vectorMeasure (ih h.2)

lemma Integrable.restrict (hf : μ.Integrable f B) {s : Set X} :
    (μ.restrict s).Integrable f B := by
  by_cases hs : MeasurableSet s
  · simpa [VectorMeasure.Integrable, transpose_restrict, variation_restrict hs] using
      MeasureTheory.Integrable.restrict hf
  · simp [restrict_not_measurable _ hs]

@[simp]
theorem integral_zero_vectorMeasure :
    ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0 := by simp [integral]

lemma integral_of_isEmpty [IsEmpty X] : ∫ᵛ x, f x ∂[B; μ] = 0 := by simp [eq_zero_of_isEmpty]

@[simp]
theorem integral_smul_vectorMeasure (f : X → E) (c : ℝ) :
    ∫ᵛ x, f x ∂[B; c • μ] = c • ∫ᵛ x, f x ∂[B; μ] := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, setToFun, hG]
  simp_rw [integral, ← setToFun_smul_left]
  have : ((c • μ).transpose B).variation = ‖c‖₊ • (μ.transpose B).variation := by
    simp [transpose, mapRange_smul, variation_smul]
  simp only [this, mul_one]
  have : DominatedFinMeasAdditive (μ.transpose B).variation ((c • μ).transpose B) ‖c‖ := by
    simp only [transpose_smul, coe_smul, Real.norm_eq_abs]
    simpa using! (dominatedFinMeasAdditive_cbmApplyMeasure μ B).smul c
  rw! [← setToFun_congr_smul_measure' _ this, transpose_smul]
  rfl

theorem integral_add_vectorMeasure (hμ : μ.Integrable f B) (hν : ν.Integrable f B) :
    ∫ᵛ x, f x ∂[B; μ + ν] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[B; ν] :=
  setToFun_add_left'' (by simp [transpose]) hμ hν (by grw [transpose_add, variation_add_le])
    zero_le_one zero_le_one zero_le_one

theorem integral_finsetSum_vectorMeasure {μ : ι → VectorMeasure X F}
    {s : Finset ι} (hf : ∀ i ∈ s, (μ i).Integrable f B) :
    ∫ᵛ x, f x ∂[B; ∑ i ∈ s, μ i] = ∑ i ∈ s, ∫ᵛ x, f x ∂[B; μ i] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
      Finset.sum_insert] at hf ⊢
    rw [integral_add_vectorMeasure hf.1 (Integrable.finsetSum_vectorMeasure hf.2), ih hf.2]

@[integral_simps]
theorem integral_neg_vectorMeasure :
    ∫ᵛ x, f x ∂[B; -μ] = -∫ᵛ x, f x ∂[B; μ] := by
  simp [integral, ← setToFun_neg']

theorem integral_sub_vectorMeasure (hμ : μ.Integrable f B) (hν : ν.Integrable f B) :
    ∫ᵛ x, f x ∂[B; μ - ν] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, f x ∂[B; ν] := by
  rw [sub_eq_add_neg, integral_add_vectorMeasure hμ hν.neg_vectorMeasure,
    integral_neg_vectorMeasure, ← sub_eq_add_neg]

end VectorMeasure

section cbm

/- `simpNF` complains that this lemma can be proved by `simp`, because the `simp`-generated lemma
unfolds the abbrev `VectorMeasure.Integrable`. TODO: fix `simp`. See lean4#13958. -/
@[nolint simpNF, simp]
lemma Integrable.zero_cbm : μ.Integrable f (0 : E →L[ℝ] F →L[ℝ] G) := by
  simp [VectorMeasure.Integrable]

lemma Integrable.add_cbm (hB : μ.Integrable f B) (hC : μ.Integrable f C) :
    μ.Integrable f (B + C) := by
  apply Integrable.mono_measure (integrable_add_measure.2 ⟨hB, hC⟩)
  grw [transpose_add_cbm, variation_add_le]

lemma Integrable.neg_cbm (hB : μ.Integrable f B) :
    μ.Integrable f (-B) := by
  apply Integrable.mono_measure hB
  simp

lemma Integrable.sub_cbm (hB : μ.Integrable f B) (hC : μ.Integrable f C) :
    μ.Integrable f (B - C) := by
  convert hB.add_cbm hC.neg_cbm using 1
  exact sub_eq_add_neg B C

lemma Integrable.finsetSum_cbm {ι : Type*} {B : ι → E →L[ℝ] F →L[ℝ] G} {s : Finset ι}
    (h : ∀ i ∈ s, μ.Integrable f (B i)) : μ.Integrable f (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
        Finset.sum_insert] at h ⊢
      exact h.1.add_cbm (ih h.2)

variable (f μ) in
@[simp]
theorem integral_zero_cbm :
    ∫ᵛ x, f x ∂[(0 : E →L[ℝ] F →L[ℝ] G); μ] = 0 := by
  simp [integral]

theorem integral_add_cbm (hB : μ.Integrable f B) (hC : μ.Integrable f C) :
    ∫ᵛ x, f x ∂[B + C; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[C; μ] :=
  setToFun_add_left'' (by simp [transpose]) hB hC (by simp [variation_add_le])
    zero_le_one zero_le_one zero_le_one

theorem integral_finsetSum_cbm {B : ι → E →L[ℝ] F →L[ℝ] G}
    {s : Finset ι} (hf : ∀ i ∈ s, μ.Integrable f (B i)) :
    ∫ᵛ x, f x ∂[∑ i ∈ s, B i; μ] = ∑ i ∈ s, ∫ᵛ x, f x ∂[B i; μ] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
      Finset.sum_insert] at hf ⊢
    rw [integral_add_cbm hf.1 (Integrable.finsetSum_cbm hf.2), ih hf.2]

@[integral_simps]
theorem integral_neg_cbm :
    ∫ᵛ x, f x ∂[-B; μ] = -∫ᵛ x, f x ∂[B; μ] := by
  simp [integral, ← setToFun_neg']

theorem integral_sub_cbm (hB : μ.Integrable f B) (hC : μ.Integrable f C) :
    ∫ᵛ x, f x ∂[B - C; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, f x ∂[C; μ] := by
  rw [sub_eq_add_neg, integral_add_cbm hB, integral_neg_cbm, ← sub_eq_add_neg]
  simpa [VectorMeasure.Integrable] using hC

end cbm

end VectorMeasure

end MeasureTheory
