/-
Copyright (c) 2025 Haoen Feng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoen Feng
-/
module

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Stokes' theorem on rectangular boxes in Euclidean space

This file proves the generalized Stokes theorem for differential forms on rectangular
boxes `[a, b] ⊂ ℝ^(m+1)`.  The proof reduces the top-degree case to Mathlib's
divergence theorem for boxes.

Let `ω` be an `m`-form on `ℝ^(m+1)`.  We extract the `i`-th signed face component
(`boxFaceComponent ω i`), a scalar function whose divergence equals the top-form
density of the exterior derivative `dω`.  The divergence theorem then turns the
integral of `dω` over the box into a sum of face integrals.

## Main definitions

* `topFormDensity`: the density function of a top-form field.
* `topFormIntegral`: the integral of a top-form field over a measurable set.
* `boxFaceComponent`: extracts the `i`-th signed face component from an `m`-form on
  `ℝ^(m+1)`.
* `boxBoundaryIntegral`: the signed boundary integral of an `m`-form over `∂[a,b]`.

## Main results

* `topFormDensity_extDeriv_eq_boxFaceComponent_divergence`: the top-form density of
  `dω` equals the divergence of the face components.
* `box_stokes_of_hasFDerivAt`: Stokes' theorem on a box with pointwise
  differentiability hypotheses.
* `box_stokes_of_contDiff`: a convenient `C¹` formulation.

## Tags

Stokes theorem, differential form, exterior derivative, box, divergence theorem
-/

noncomputable section

open ContinuousAlternatingMap Fin Set MeasureTheory Measure Matrix
open scoped Topology

namespace DifferentialForm

/-! ## Top-Form Density and Integration -/

/-- The determinant as a continuous alternating map on `Fin n → ℝ`.

We promote the algebraic alternating map `detRowAlternating` to a continuous one
using a Hadamard-style bound. -/
noncomputable def detTopForm (n : ℕ) :
    (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ :=
  AlternatingMap.mkContinuous
    (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ)
    ((Fintype.card (Fin n)).factorial)
    (fun m => by
      show ‖(Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ) m‖ ≤
           ↑(Fintype.card (Fin n)).factorial * ∏ i, ‖m i‖
      rw [show (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ) m =
            (Matrix.of m).det from rfl]
      rw [Matrix.det_apply]
      calc ‖(∑ σ : Perm (Fin n), Equiv.Perm.sign σ • ∏ i : Fin n, Matrix.of m (σ i) i)‖
          ≤ ∑ σ : Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i : Fin n, Matrix.of m (σ i) i‖ :=
            norm_sum_le _ _
        _ ≤ ∑ σ : Perm (Fin n), (1 : ℝ) * ∏ i : Fin n, ‖m (σ i)‖ := by
            refine Finset.sum_le_sum (fun σ _ => ?_)
            simp only [Matrix.of_apply]
            show ‖(Equiv.Perm.sign σ : ℤ) • ∏ x : Fin n, m (σ x) x‖ ≤
                 (1 : ℝ) * ∏ i : Fin n, ‖m (σ i)‖
            rw [zsmul_eq_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
            rw [← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]
            simp only [one_mul]
            rw [Finset.abs_prod Finset.univ (fun x => m (σ x) x)]
            have h_each : ∀ i : Fin n, (|m (σ i) i| : ℝ) ≤ ‖m (σ i)‖ := fun i => by
              have := norm_le_pi_norm (m (σ i)) i
              rw [Real.norm_eq_abs] at this
              exact this
            refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?_ ?_
            · simp
            · intro a s ha ih
              simp only [Finset.prod_insert ha]
              exact mul_le_mul (h_each a) ih (Finset.prod_nonneg
                (fun i _ => abs_nonneg _)) (norm_nonneg _)
        _ ≤ ∑ σ : Perm (Fin n), (1 : ℝ) * ∏ i : Fin n, ‖m i‖ := by
            exact le_of_eq (Finset.sum_congr rfl
              (fun σ _ => congrArg (fun p => (1 : ℝ) * p)
                (Equiv.Perm.prod_comp σ Finset.univ (fun j => (‖m j‖ : ℝ))
                  (by intro a _; exact Finset.mem_univ a))))
        _ = ↑(Fintype.card (Fin n)).factorial * ∏ i : Fin n, ‖m i‖ := by
            simp only [Finset.sum_const, nsmul_eq_mul, one_mul,
              Fintype.card_perm, Finset.card_univ])

@[simp]
theorem detTopForm_one (n : ℕ) :
    detTopForm n (1 : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  det_one

/-- Extract the density function from a top form: `ω` evaluated at the identity matrix. -/
noncomputable def toTopFormFun (n : ℕ) (ω : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) : ℝ :=
  ω (1 : Matrix (Fin n) (Fin n) ℝ)

@[simp]
theorem toTopFormFun_add (n : ℕ) (ω₁ ω₂ : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    toTopFormFun n (ω₁ + ω₂) = toTopFormFun n ω₁ + toTopFormFun n ω₂ := by
  simp [toTopFormFun]

@[simp]
theorem toTopFormFun_smul (n : ℕ) (c : ℝ) (ω : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    toTopFormFun n (c • ω) = c * toTopFormFun n ω := by
  simp [toTopFormFun, smul_eq_mul]

@[simp]
theorem toTopFormFun_zero (n : ℕ) :
    toTopFormFun n (0 : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) = 0 := rfl

/-- Construct a top form from scalar `c`: `ω = c · detTopForm`. -/
noncomputable def fromTopFormFun (n : ℕ) (c : ℝ) : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ :=
  c • detTopForm n

/-- The density function of a top-form field: `x ↦ toTopFormFun (ω x)`. -/
noncomputable def topFormDensity {n : ℕ}
    (ω : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) (x : Fin n → ℝ) : ℝ :=
  toTopFormFun n (ω x)

/-- The integral of a top-form field over a measurable set: `∫_s ω = ∫_{x ∈ s} topFormDensity ω x dx`. -/
noncomputable def topFormIntegral {n : ℕ}
    (ω : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (s : Set (Fin n → ℝ)) : ℝ :=
  ∫ x in s, topFormDensity ω x

variable {m : ℕ}

/-! ## Coordinate Components of an `m`-Form on `ℝ^(m+1)` -/

/-- The `i`-th row of the identity matrix is the `i`-th standard basis vector. -/
theorem matrix_one_row_eq_single (i : Fin (m + 1)) :
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i = Pi.single i 1 := by
  ext j
  simp only [Matrix.one_apply, Pi.single_apply]
  by_cases h : i = j <;> simp [h, eq_comm]

/-- The signed component of an `m`-form on `ℝ^(m+1)` normal to the `i`-th face.

If `ω` is an `m`-form and the ambient dimension is `m + 1`, then
`boxFaceComponent ω i` is the scalar function
`(-1)^i ω(e_0,...,ê_i,...,e_m)`.  Its divergence is the top-form
density of `dω`. -/
noncomputable def boxFaceComponent
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (i : Fin (m + 1)) (x : Fin (m + 1) → ℝ) : ℝ :=
  ((-1 : ℤ) ^ (i : ℕ)) •
    ω x (Fin.removeNth i (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))

/-- Differentiability of a face component follows from differentiability of the form field. -/
theorem boxFaceComponent_differentiableAt
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    {x : Fin (m + 1) → ℝ} (i : Fin (m + 1))
    (hω : DifferentiableAt ℝ ω x) :
    DifferentiableAt ℝ (boxFaceComponent ω i) x := by
  unfold boxFaceComponent
  exact (hω.continuousAlternatingMap_apply fun _ => differentiableAt_const _).const_smul
    ((-1 : ℤ) ^ (i : ℕ))

/-- A face component is as smooth as the underlying form field. -/
theorem boxFaceComponent_contDiff {n : WithTop ℕ∞}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (i : Fin (m + 1)) (hω : ContDiff ℝ n ω) :
    ContDiff ℝ n (boxFaceComponent ω i) := by
  unfold boxFaceComponent
  have happ : ContDiff ℝ n
      (fun x =>
        (ContinuousAlternatingMap.apply ℝ (Fin (m + 1) → ℝ) ℝ
          (Fin.removeNth i (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))) (ω x)) :=
    (ContinuousAlternatingMap.apply ℝ (Fin (m + 1) → ℝ) ℝ
      (Fin.removeNth i (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))).contDiff.comp hω
  simpa [ContinuousAlternatingMap.apply_apply] using
    happ.const_smul ((-1 : ℤ) ^ (i : ℕ))

/-! ## Top-Form Density as Divergence -/

/-- The top-form density of `dω` is the divergence of the signed face components.

This is the key identity that bridges the exterior-derivative world and the
divergence-theorem world. -/
theorem topFormDensity_extDeriv_eq_boxFaceComponent_divergence
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    {x : Fin (m + 1) → ℝ} (hω : DifferentiableAt ℝ ω x) :
    topFormDensity (extDeriv ω) x =
      ∑ i : Fin (m + 1),
        fderiv ℝ (boxFaceComponent ω i) x (Pi.single i 1) := by
  simp only [topFormDensity, toTopFormFun]
  rw [extDeriv_apply hω]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [matrix_one_row_eq_single i]
  have hraw : DifferentiableAt ℝ
      (fun y => ω y (Fin.removeNth i (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))) x :=
    hω.continuousAlternatingMap_apply fun _ => differentiableAt_const _
  unfold boxFaceComponent
  rw [fderiv_fun_const_smul hraw]
  rw [ContinuousLinearMap.smul_apply]

/-! ## Boundary Integral on a Box -/

/-- The signed boundary integral of an `m`-form over the boundary of a box.

Each coordinate direction contributes the integral over the front face
`xᵢ = bᵢ` minus the integral over the back face `xᵢ = aᵢ`, with the
orientation sign already included in `boxFaceComponent`. -/
noncomputable def boxBoundaryIntegral
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (a b : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i : Fin (m + 1),
    ((∫ x in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
        boxFaceComponent ω i (Fin.insertNth i (b i) x)) -
      ∫ x in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
        boxFaceComponent ω i (Fin.insertNth i (a i) x))

/-! ## Stokes on Boxes -/

/-- **Generalized Stokes theorem on rectangular boxes in `ℝ^(m+1)`.**

This is a genuine proved Stokes formula for Euclidean boxes.  The proof is:

1. rewrite the density of `dω` as the divergence of the signed face
   components of `ω`;
2. apply Mathlib's divergence theorem on boxes.

The hypotheses are exactly the analytic hypotheses required by the
divergence theorem: continuity of face components on the closed box,
differentiability of `ω` on the closed box, and integrability of the
resulting divergence. -/
theorem box_stokes_of_hasFDerivAt
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (a b : Fin (m + 1) → ℝ) (hle : a ≤ b)
    (Hc : ∀ i : Fin (m + 1), ContinuousOn (boxFaceComponent ω i) (Icc a b))
    (Hdω : ∀ x ∈ Icc a b, DifferentiableAt ℝ ω x)
    (Hi : IntegrableOn
      (fun x => ∑ i : Fin (m + 1),
        fderiv ℝ (boxFaceComponent ω i) x (Pi.single i 1)) (Icc a b)) :
    topFormIntegral (extDeriv ω) (Icc a b) = boxBoundaryIntegral ω a b := by
  unfold topFormIntegral boxBoundaryIntegral
  calc
    ∫ x in Icc a b, topFormDensity (extDeriv ω) x =
        ∫ x in Icc a b,
          ∑ i : Fin (m + 1),
            fderiv ℝ (boxFaceComponent ω i) x (Pi.single i 1) := by
      exact setIntegral_congr_fun measurableSet_Icc fun x hx =>
        topFormDensity_extDeriv_eq_boxFaceComponent_divergence ω (Hdω x hx)
    _ = ∑ i : Fin (m + 1),
        ((∫ x in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
            boxFaceComponent ω i (Fin.insertNth i (b i) x)) -
          ∫ x in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
            boxFaceComponent ω i (Fin.insertNth i (a i) x)) := by
      refine MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
        a b hle (fun i => boxFaceComponent ω i)
        (fun i x => fderiv ℝ (boxFaceComponent ω i) x)
        (∅ : Set (Fin (m + 1) → ℝ)) (by simp) Hc ?_ Hi
      intro x hx i
      refine (boxFaceComponent_differentiableAt ω i (Hdω x ?_)).hasFDerivAt
      have hxIoo : x ∈ Set.pi Set.univ fun j : Fin (m + 1) => Ioo (a j) (b j) := by
        simpa [diff_empty] using hx
      rw [mem_Icc]
      constructor <;> intro j
      · exact (mem_Icc_of_Ioo (hxIoo j trivial)).1
      · exact (mem_Icc_of_Ioo (hxIoo j trivial)).2

/-- A convenient `C¹` form of Stokes on rectangular boxes.

The lower-level theorem `box_stokes_of_hasFDerivAt` mirrors Mathlib's
divergence theorem hypotheses.  This wrapper derives those hypotheses from
the usual mathematical assumption that the form field is `C¹`. -/
theorem box_stokes_of_contDiff
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (a b : Fin (m + 1) → ℝ) (hle : a ≤ b)
    (hω : ContDiff ℝ (1 : ℕ∞) ω) :
    topFormIntegral (extDeriv ω) (Icc a b) = boxBoundaryIntegral ω a b := by
  refine box_stokes_of_hasFDerivAt ω a b hle ?_ ?_ ?_
  · -- Continuity of face components from C¹ smoothness
    intro i
    exact (boxFaceComponent_contDiff ω i hω).continuous.continuousOn
  · -- Differentiability of ω everywhere
    intro _x _hx
    exact (hω.differentiable one_ne_zero).differentiableAt
  · -- Integrability of divergence from continuity
    have hdiv_cont : Continuous
        (fun x => ∑ i : Fin (m + 1),
          fderiv ℝ (boxFaceComponent ω i) x (Pi.single i 1)) := by
      refine continuous_finset_sum _ ?_
      intro i _
      have hface : ContDiff ℝ (1 : ℕ∞) (boxFaceComponent ω i) :=
        boxFaceComponent_contDiff ω i hω
      exact (hface.continuous_fderiv_apply one_ne_zero).comp
        (continuous_id.prodMk continuous_const)
    exact hdiv_cont.integrableOn_Icc

end DifferentialForm
