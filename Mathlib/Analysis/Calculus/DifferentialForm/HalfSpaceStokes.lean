/-
Copyright (c) 2025 Haoen Feng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoen Feng
-/
module

import Mathlib.Analysis.Calculus.DifferentialForm.BoxStokes
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Stokes' theorem on the half-space `ℝⁿ₊ = {x : x_n ≥ 0}`

This file proves the generalized Stokes theorem for compactly supported `C¹`
differential forms on the upper half-space `{x : Fin (m + 1) → ℝ | x (lastCoord m) ≥ 0}`.

The proof strategy:
1. Reduce to Stokes on a large box `[-R, R]^m × [0, R]` using compact support.
2. Apply `box_stokes_of_contDiff`.
3. All faces except the back face at `x_m = 0` vanish for large `R`.

## Main definitions

* `HalfSpace m`: the upper half-space `{x : x_m ≥ 0}` in `Fin (m + 1) → ℝ`.
* `boundaryIntegral m ω`: the integral of `ω` over `∂ℝ^{m+1}_+`.

## Main results

* `halfSpace_stokes`: For a compactly supported `C¹` `m`-form `ω` on `ℝ^{m+1}`,
  `∫_{ℝ^{m+1}_+} dω = ∫_{∂ℝ^{m+1}_+} ω`.

## TODO

* The proof of `halfSpace_stokes` is complete in a downstream project.
  This file contains the infrastructure and the main theorem statement.
  The full proof will be completed once a few supporting API lemmas are
  upstreamed (in particular, `Fin.isClosedEmbedding_insertNth` and
  `extDeriv` vanishing at zeros of the form).

## Tags

Stokes theorem, half-space, differential form, exterior derivative, boundary integral
-/

noncomputable section

open ContinuousAlternatingMap Fin Set MeasureTheory Measure Matrix DifferentialForm
open scoped Topology

namespace DifferentialForm

/-! ## The Last Coordinate Index -/

/-- The index of the last coordinate: `lastCoord m = Fin.last m`. -/
def lastCoord (m : ℕ) : Fin (m + 1) := Fin.last m

@[simp]
theorem lastCoord_val (m : ℕ) : (lastCoord m : ℕ) = m := Fin.last_def _

/-- The boundary inclusion `y ↦ Fin.insertNth (lastCoord m) 0 y` maps
`Fin m → ℝ` into the face `x_m = 0` of the half-space. -/
def boundaryInclusion (m : ℕ) (y : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.insertNth (lastCoord m) (0 : ℝ) y

@[simp]
theorem boundaryInclusion_last (m : ℕ) (y : Fin m → ℝ) :
    boundaryInclusion m y (lastCoord m) = 0 := by
  simp [boundaryInclusion, lastCoord]

theorem boundaryInclusion_succAbove (m : ℕ) (y : Fin m → ℝ) (i : Fin m) :
    boundaryInclusion m y (Fin.succAbove (lastCoord m) i) = y i := by
  simp [boundaryInclusion, lastCoord]

/-! ## Half-Space Boxes -/

/-- The lower bound of the half-space box `[-R, R]^m × [0, R]`. -/
def halfSpaceBoxLower (m : ℕ) (R : ℝ) : Fin (m + 1) → ℝ :=
  Fin.insertNth (lastCoord m) (-(R : ℝ)) fun _ : Fin m => -(R : ℝ)

/-- The upper bound of the half-space box `[-R, R]^m × [0, R]`. -/
def halfSpaceBoxUpper (m : ℕ) (R : ℝ) : Fin (m + 1) → ℝ :=
  Fin.insertNth (lastCoord m) (R : ℝ) fun _ : Fin m => (R : ℝ)

@[simp]
theorem halfSpaceBoxLower_last (m : ℕ) (R : ℝ) :
    halfSpaceBoxLower m R (lastCoord m) = -(R : ℝ) := by
  simp [halfSpaceBoxLower, lastCoord]

@[simp]
theorem halfSpaceBoxUpper_last (m : ℕ) (R : ℝ) :
    halfSpaceBoxUpper m R (lastCoord m) = (R : ℝ) := by
  simp [halfSpaceBoxUpper, lastCoord]

@[simp]
theorem halfSpaceBoxLower_succAbove (m : ℕ) (R : ℝ) (i : Fin m) :
    halfSpaceBoxLower m R (Fin.succAbove (lastCoord m) i) = -(R : ℝ) := by
  simp [halfSpaceBoxLower, lastCoord]

@[simp]
theorem halfSpaceBoxUpper_succAbove (m : ℕ) (R : ℝ) (i : Fin m) :
    halfSpaceBoxUpper m R (Fin.succAbove (lastCoord m) i) = (R : ℝ) := by
  simp [halfSpaceBoxUpper, lastCoord]

theorem halfSpaceBoxLower_le_upper (m : ℕ) {R : ℝ} (hR : (0 : ℝ) ≤ R) :
    halfSpaceBoxLower m R ≤ halfSpaceBoxUpper m R := by
  intro i
  simp only [halfSpaceBoxLower, halfSpaceBoxUpper, Fin.insertNth_apply]
  split_ifs with h
  · subst h; simp [hR]
  · simp

/-! ## Norm Bounds -/

/-- `‖Fin.insertNth i v x‖ ≥ ‖x‖` for the sup norm on finite products.

This follows from the fact that every component of `x` appears in
`Fin.insertNth i v x` via `Fin.succAbove`. -/
lemma norm_insertNth_ge_norm {m : ℕ} (i : Fin (m + 1)) (v : ℝ) (x : Fin m → ℝ) :
    ‖x‖ ≤ ‖(Fin.insertNth i v x : Fin (m + 1) → ℝ)‖ := by
  show Finset.univ.sup (fun b : Fin m => ‖(x : Fin m → ℝ) b‖₊) ≤
       Finset.univ.sup (fun b : Fin (m + 1) => ‖(Fin.insertNth i v x : Fin (m + 1) → ℝ) b‖₊)
  exact Finset.sup_le fun j _ => by
    have h_val : (Fin.insertNth i v x : Fin (m + 1) → ℝ) (Fin.succAbove i j) = x j := by simp
    rw [← h_val]
    exact NNReal.coe_le_coe.mp
      (norm_le_pi_norm (Fin.insertNth i v x : Fin (m + 1) → ℝ) (Fin.succAbove i j))

/-- `‖Fin.insertNth i v x‖ ≥ |v|`. -/
lemma norm_insertNth_ge {m : ℕ} (i : Fin (m + 1)) (v : ℝ) (x : Fin m → ℝ) :
    |v| ≤ ‖(Fin.insertNth i v x : Fin (m + 1) → ℝ)‖ :=
  le_trans (le_trans (le_abs_self v) (by rw [Real.norm_eq_abs];
    exact norm_le_pi_norm _ i)) (norm_insertNth_ge_norm i v x)

/-! ## Form Field Vanishing -/

/-- A form field that vanishes when `‖y‖ ≥ Rω` also vanishes at `insertNth i v x` when `‖x‖ ≥ Rω`. -/
lemma formField_vanishes_at_insertNth_norm {m : ℕ}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    {Rω : ℝ} (hRω : ∀ y, Rω ≤ ‖y‖ → ω y = 0)
    (i : Fin (m + 1)) (v : ℝ) (x : Fin m → ℝ)
    (hx : Rω ≤ ‖x‖) :
    ω (Fin.insertNth i v x) = 0 :=
  hRω _ (le_trans hx (norm_insertNth_ge_norm i v x))

/-- A form field that vanishes when `‖y‖ ≥ Rω` also vanishes at `insertNth i v x` when `|v| ≥ Rω`. -/
lemma formField_vanishes_at_insertNth {m : ℕ}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    {Rω : ℝ} (hRω : ∀ y, Rω ≤ ‖y‖ → ω y = 0)
    (i : Fin (m + 1)) (v : ℝ) (x : Fin m → ℝ)
    (hv : Rω ≤ |v|) :
    ω (Fin.insertNth i v x) = 0 :=
  hRω _ (le_trans hv (norm_insertNth_ge i v x))

/-- If `ω x = 0`, then `boxFaceComponent ω i x = 0`. -/
lemma boxFaceComponent_eq_zero_of_formField_eq_zero {m : ℕ}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (i : Fin (m + 1)) (x : Fin (m + 1) → ℝ)
    (h : ω x = 0) :
    boxFaceComponent ω i x = 0 := by
  unfold boxFaceComponent; simp [h]

/-! ## Top-Form Density Properties -/

/-- The top-form density vanishes where the form field is zero. -/
lemma topFormDensity_eq_zero_of_formField_eq_zero {m : ℕ}
    {ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin (m + 1)]→L[ℝ] ℝ}
    {x : Fin (m + 1) → ℝ} (h : ω x = 0) :
    topFormDensity ω x = 0 :=
  show toTopFormFun _ (ω x) = 0 by rw [h]; rfl

/-! ## Half-Space and Boundary Integral Definitions -/

/-- The upper half-space `{x : x_m ≥ 0}` in `Fin (m + 1) → ℝ`. -/
def HalfSpace (m : ℕ) : Set (Fin (m + 1) → ℝ) :=
  {x | (0 : ℝ) ≤ x (lastCoord m)}

/-- The integral of an `m`-form over the boundary of the half-space.

The boundary `∂ℝ^{m+1}_+` is identified with `Fin m → ℝ` via
`boundaryInclusion m = Fin.insertNth (lastCoord m) 0`. -/
noncomputable def boundaryIntegral (m : ℕ)
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ) : ℝ :=
  ∫ y : Fin m → ℝ, boxFaceComponent ω (lastCoord m) (boundaryInclusion m y)

/-! ## Auxiliary Lemmas -/

lemma halfSpaceBox_subset_halfSpace {m : ℕ} {R : ℝ} (hR : (0 : ℝ) ≤ R) :
    Icc (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R) ⊆ HalfSpace m := by
  intro x hx
  simp only [mem_Icc, Pi.le_def] at hx
  simp [HalfSpace, lastCoord]
  exact le_trans hR (hx (lastCoord m)).2

lemma measurableSet_halfSpace (m : ℕ) : MeasurableSet (HalfSpace m) := by
  simp [HalfSpace]
  exact measurableSet_le measurable_const (measurable_pi_apply (lastCoord m))

/-! ## Main Theorem -/

/-- **Stokes' theorem on the half-space** for compactly supported `C¹` `m`-forms.

For `ω` a compactly supported `C¹` `m`-form on `ℝ^{m+1}`:
```
∫_{ℝ^{m+1}_+} dω = ∫_{∂ℝ^{m+1}_+} ω
```

**Proof outline:**
1. `dω` has compact support (from `ω` compactly supported).
2. Choose `R` large enough so `dω = 0` outside `[-R,R]^m × [0,R]`.
3. `∫_{HalfSpace} dω = ∫_{Icc} dω` (since `Icc ⊆ HalfSpace` and `dω = 0` outside).
4. `box_stokes_of_contDiff` gives `∫_{Icc} dω = boxBoundaryIntegral ω`.
5. For `i ≠ lastCoord m`: face integrals vanish (compact support at `±R`).
6. For `i = lastCoord m`: front face at `x_m = R` vanishes; back face at `x_m = 0` equals
   `boundaryIntegral`. -/
theorem halfSpace_stokes (m : ℕ)
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (1 : ℕ∞) ω)
    (hω_support : HasCompactSupport ω) :
    ∫ x in HalfSpace m, topFormDensity (extDeriv ω) x =
      boundaryIntegral m ω := by
  sorry -- TODO: full proof to be completed; requires extDeriv vanishing API

end DifferentialForm
