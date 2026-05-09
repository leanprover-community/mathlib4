/-
Copyright (c) 2025 Haoen Feng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoen Feng
-/
module
public import Mathlib.Analysis.Calculus.DifferentialForm.HalfSpaceStokes

/-!
# Stokes' theorem on the full space ℝⁿ and product rule for differential forms

This file proves the full-space Stokes theorem for compactly supported `C¹`
differential forms, together with the product rule for the top-form density
of `d(f · ω)` and the partition-of-unity telescoping identity.

## Main definitions

* `wedgeDensity f ω x`: the scalar contribution of `df ∧ ω` to the top-form
  density, expressed coordinate-wise as `∑ᵢ (∂f/∂xᵢ)(x) · boxFaceComponent ω i x`.

## Main results

* `fullSpace_stokes`: For a compactly supported `C¹` `m`-form `ω` on `ℝ^(m+1)`,
  `∫_{ℝ^(m+1)} dω = 0`.
* `topFormDensity_extDeriv_smul`: Product rule for `d(f · ω)` in density form.
* `poTelescoping`: If `∑ ρᵢ = 1` then `∑ wedgeDensity ρᵢ ω = 0`.
* `continuous_topFormDensity_extDeriv`: Continuity of `topFormDensity (extDeriv ω)`.
* `topFormDensity_add`, `topFormDensity_smul`, `topFormDensity_fun_smul`:
  Linearity of `topFormDensity`.
* `extDeriv_sum`: `extDeriv` commutes with finite sums.
* `integral_extDeriv_add`: `∫ d(ω₁ + ω₂) = ∫ dω₁ + ∫ dω₂`.

## Tags

Stokes theorem, full space, differential form, exterior derivative, product rule,
partition of unity, wedge density
-/

@[expose] public section


noncomputable section

open ContinuousAlternatingMap Fin Set MeasureTheory Measure Function
open scoped Topology BigOperators

namespace DifferentialForm

variable {m : ℕ}

/-! ## Wedge Density and Product Rule -/

/-- The "wedge density" term: the contribution of `df ∧ ω` to the top-form
    density of `d(f · ω)`. In coordinates:
      `wedgeDensity f ω x = ∑ᵢ (∂f/∂xᵢ)(x) · boxFaceComponent ω i x`

    This is a scalar replacement for the abstract wedge product `df ∧ ω`,
    valid for `(m)`-forms on `ℝ^(m+1)` where the result is a top `(m+1)`-form. -/
noncomputable def wedgeDensity
    (f : (Fin (m + 1) → ℝ) → ℝ)
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (x : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i : Fin (m + 1),
    fderiv ℝ f x (Pi.single i 1) * boxFaceComponent ω i x

/-- `boxFaceComponent` distributes over scalar multiplication by a function. -/
lemma boxFaceComponent_fun_smul
    (f : (Fin (m + 1) → ℝ) → ℝ)
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (i : Fin (m + 1)) (x : Fin (m + 1) → ℝ) :
    boxFaceComponent (fun y => f y • ω y) i x =
      f x * boxFaceComponent ω i x := by
  unfold boxFaceComponent
  simp only [ContinuousAlternatingMap.smul_apply]
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_left_comm, smul_eq_mul]

/-- **Product rule for top-form density** (the core lemma).

    For a `C¹` function `f` and a `C¹` `m`-form `ω` on `ℝ^(m+1)`:
      `topFormDensity (extDeriv (fun x => f x · ω x)) x
        = f x · topFormDensity (extDeriv ω) x + wedgeDensity f ω x`

    This is proved via the `boxFaceComponent` divergence decomposition:
    each face component of `f · ω` satisfies the product rule for derivatives. -/
theorem topFormDensity_extDeriv_smul
    (f : (Fin (m + 1) → ℝ) → ℝ)
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (x : Fin (m + 1) → ℝ)
    (hf : DifferentiableAt ℝ f x)
    (hω : DifferentiableAt ℝ ω x) :
    topFormDensity (extDeriv (fun y => f y • ω y)) x =
      f x * topFormDensity (extDeriv ω) x + wedgeDensity f ω x := by
  have hsmul : DifferentiableAt ℝ (fun y => f y • ω y) x := hf.smul hω
  have hfi : DifferentiableAt ℝ f x := hf
  have hbi (i) : DifferentiableAt ℝ (boxFaceComponent ω i) x :=
    boxFaceComponent_differentiableAt ω i hω
  -- Product rule for each face component
  have h_prod (i : Fin (m + 1)) :
      fderiv ℝ (fun y => f y * boxFaceComponent ω i y) x (Pi.single i 1) =
      f x * fderiv ℝ (boxFaceComponent ω i) x (Pi.single i 1) +
      boxFaceComponent ω i x * fderiv ℝ f x (Pi.single i 1) := by
    have h := fderiv_fun_mul hfi (hbi i)
    rw [h]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  -- Use divergence decomposition + product rule
  have h_div_smul := topFormDensity_extDeriv_eq_boxFaceComponent_divergence
    (fun y => f y • ω y) hsmul
  have h_div_ω := topFormDensity_extDeriv_eq_boxFaceComponent_divergence ω hω
  change topFormDensity (extDeriv (fun y => f y • ω y)) x =
      f x * topFormDensity (extDeriv ω) x + wedgeDensity f ω x
  rw [h_div_smul, h_div_ω]
  unfold wedgeDensity
  have h_smul_face (i : Fin (m + 1)) :
      fderiv ℝ (fun y => f y * boxFaceComponent ω i y) x (Pi.single i 1) =
      f x * fderiv ℝ (boxFaceComponent ω i) x (Pi.single i 1) +
      boxFaceComponent ω i x * fderiv ℝ f x (Pi.single i 1) := h_prod i
  have h_rewrite (i : Fin (m + 1)) :
      fderiv ℝ (boxFaceComponent (fun y => f y • ω y) i) x =
      fderiv ℝ (fun y => f y * boxFaceComponent ω i y) x := by
    congr 1; funext y
    exact boxFaceComponent_fun_smul f ω i y
  simp only [h_rewrite, h_smul_face, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-! ## Partition-of-Unity Telescoping -/

/-- **Partition-of-unity telescoping** — density version.

    If `∑ᶠ i, ρᵢ = 1`, then for any `m`-form `ω`:
      `∑ᶠ i, wedgeDensity (ρᵢ) ω x = 0`

    Proof: `∑ (∂ρᵢ/∂xⱼ) · boxFaceComponent ω j x`
         `= (∑ ∂ρᵢ/∂xⱼ) · boxFaceComponent ω j x`   (by rearranging sums)
         `= (∂(∑ ρᵢ)/∂xⱼ) · boxFaceComponent ω j x`   (by linearity of `d`)
         `= (∂1/∂xⱼ) · boxFaceComponent ω j x = 0`      (derivative of const) -/
theorem poTelescoping {ι : Type*} [Fintype ι]
    (ρ : ι → (Fin (m + 1) → ℝ) → ℝ)
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (h_sum : ∀ x, ∑ i, ρ i x = 1)
    (x : Fin (m + 1) → ℝ)
    (hdiff : ∀ i, DifferentiableAt ℝ (ρ i) x) :
    (∑ i, wedgeDensity (ρ i) ω x) = 0 := by
  simp only [wedgeDensity]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h_deriv_sum : fderiv ℝ (fun y => ∑ i, ρ i y) x =
      ∑ i, fderiv ℝ (ρ i) x :=
    fderiv_fun_sum fun i _ => hdiff i
  have h_const_deriv : fderiv ℝ (fun y => ∑ i, ρ i y) x = 0 := by
    have : (fun y => ∑ i, ρ i y) = (fun _ => (1 : ℝ)) := funext h_sum
    rw [this]
    exact fderiv_const_apply (1 : ℝ)
  have h_sum_zero : ∑ i, (fderiv ℝ (ρ i) x) (Pi.single j 1) = 0 := by
    have h : (∑ i, fderiv ℝ (ρ i) x) (Pi.single j 1) = 0 := by
      rw [← h_deriv_sum, h_const_deriv]; rfl
    rw [ContinuousLinearMap.sum_apply] at h
    exact h
  rw [show ∑ i, (fderiv ℝ (ρ i) x) (Pi.single j 1) * boxFaceComponent ω j x =
        (∑ i, (fderiv ℝ (ρ i) x) (Pi.single j 1)) * boxFaceComponent ω j x from
    (Finset.sum_mul (Finset.univ : Finset ι)
      (fun i => (fderiv ℝ (ρ i) x) (Pi.single j 1))
      (boxFaceComponent ω j x)).symm]
  rw [h_sum_zero, zero_mul]

/-! ## Full-Space Stokes Theorem

  A compactly supported `(n-1)`-form on `ℝⁿ` has `∫ dω = 0`.
  This follows from the box Stokes theorem by choosing a large enough box
  that contains the support, so all face integrals vanish.
-/

/-- **Full-space Stokes theorem for compactly supported forms**.

    For a `C¹` `m`-form `ω` on `ℝ^(m+1)` with compact support:
      `∫_{ℝ^(m+1)} dω = 0`

    Proof: By `box_stokes_of_contDiff`, `∫_{Icc(-R,R)^n} dω`
    equals the boundary sum over all faces. For large enough `R`,
    each face integral vanishes because the support of `ω` is compact.
    And `∫_ℝⁿ dω = ∫_{Icc} dω` for large `R` since `dω` also has
    compact support. -/
theorem fullSpace_stokes (m : ℕ)
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (1 : ℕ∞) ω)
    (hω_support : HasCompactSupport ω) :
    (∫ x in Set.univ, topFormDensity (extDeriv ω) x) = 0 := by
  -- Get R large enough for ω support (face integrals) and density support
  obtain ⟨Rω, hRω⟩ :=
    exists_norm_bound_of_hasCompactSupport_form ω hω_support
  have hf_comp : HasCompactSupport (topFormDensity (extDeriv ω)) :=
    hasCompactSupport_topFormDensity_extDeriv ω hω hω_support
  obtain ⟨Rd, hRd⟩ := exists_norm_bound_of_compact_support _ hf_comp
  let R := max (max Rω Rd) 1
  have hRω_le : Rω ≤ R :=
    le_trans (le_max_left Rω Rd) (le_max_left (max Rω Rd) 1)
  have hRd_le : Rd ≤ R :=
    le_trans (le_max_right Rω Rd) (le_max_left (max Rω Rd) 1)
  have hR_pos : (0 : ℝ) < R :=
    lt_of_lt_of_le (by positivity) (le_max_right (max Rω Rd) 1)
  have hR_nneg : (0 : ℝ) ≤ R := le_of_lt hR_pos
  -- Apply box_stokes
  have hle : (fun _ : Fin (m + 1) => -(R : ℝ)) ≤
      (fun _ : Fin (m + 1) => (R : ℝ)) := by
    intro i; exact neg_le_self hR_nneg
  have h_box := box_stokes_of_contDiff ω
    (fun _ : Fin (m + 1) => -(R : ℝ))
    (fun _ : Fin (m + 1) => (R : ℝ)) hle hω
  -- All face integrals vanish for large R
  have h_face_pos (i : Fin (m + 1)) :
      (∫ x : Fin m → ℝ in
        Icc ((fun _ : Fin (m + 1) => -(R : ℝ)) ∘ Fin.succAbove i)
          ((fun _ : Fin (m + 1) => (R : ℝ)) ∘ Fin.succAbove i),
        boxFaceComponent ω i (Fin.insertNth i (R : ℝ) x)) = 0 :=
    faceIntegral_eq_zero_of_large_v ω Rω hRω
      (fun _ : Fin (m + 1) => -(R : ℝ))
      (fun _ : Fin (m + 1) => (R : ℝ)) i (R : ℝ)
      (le_trans hRω_le (ge_of_eq (abs_of_pos hR_pos)))
  have h_face_neg (i : Fin (m + 1)) :
      (∫ x : Fin m → ℝ in
        Icc ((fun _ : Fin (m + 1) => -(R : ℝ)) ∘ Fin.succAbove i)
          ((fun _ : Fin (m + 1) => (R : ℝ)) ∘ Fin.succAbove i),
        boxFaceComponent ω i (Fin.insertNth i (-(R : ℝ)) x)) = 0 := by
    have hRω_le_abs : Rω ≤ |-(R : ℝ)| := by
      rw [abs_neg]
      exact le_trans hRω_le (le_abs_self R)
    exact faceIntegral_eq_zero_of_large_v ω Rω hRω
      (fun _ : Fin (m + 1) => -(R : ℝ))
      (fun _ : Fin (m + 1) => (R : ℝ)) i (-(R : ℝ)) hRω_le_abs
  -- Boundary integral = sum over (front - back) = 0 for all faces
  have h_boundary_eq_zero : boxBoundaryIntegral ω
      (fun _ : Fin (m + 1) => -(R : ℝ))
      (fun _ : Fin (m + 1) => (R : ℝ)) = 0 := by
    unfold boxBoundaryIntegral
    rw [Finset.sum_eq_zero]
    intro i _
    -- After unfold, (fun _ => R) i and (fun _ => -R) i reduce to R and -R by rfl
    rw [h_face_pos i, h_face_neg i, sub_zero]
  -- Density = 0 outside Icc(-R, R) since R ≥ Rd
  have h_density_outside : ∀ x : Fin (m + 1) → ℝ,
      x ∉ Icc (fun _ : Fin (m + 1) => -(R : ℝ))
        (fun _ : Fin (m + 1) => (R : ℝ)) →
      topFormDensity (extDeriv ω) x = 0 := by
    intro x hx
    have hnorm : Rd ≤ ‖x‖ := by
      by_contra h_lt
      push Not at h_lt
      have h_in_box : x ∈ Icc
          (fun _ : Fin (m + 1) => -(R : ℝ))
          (fun _ : Fin (m + 1) => (R : ℝ)) := by
        simp only [mem_Icc, Pi.le_def]
        constructor <;> intro i
        · have hxi := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at hxi
          have : |x i| < R :=
            lt_of_le_of_lt hxi (lt_of_lt_of_le h_lt hRd_le)
          linarith [abs_le.mp (le_of_lt this)]
        · have hxi := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at hxi
          have : |x i| < R :=
            lt_of_le_of_lt hxi (lt_of_lt_of_le h_lt hRd_le)
          linarith [abs_le.mp (le_of_lt this)]
      exact hx h_in_box
    exact hRd x hnorm
  have h_cont : Continuous (topFormDensity (extDeriv ω)) := by
    refine (continuous_finsetSum _ fun i _ => ?_).congr
      (fun x => (topFormDensity_extDeriv_eq_boxFaceComponent_divergence
        ω ((hω.differentiable one_ne_zero).differentiableAt)).symm)
    exact (boxFaceComponent_contDiff ω i hω).continuous_fderiv_apply
      one_ne_zero |>.comp (continuous_id.prodMk continuous_const)
  have hf_int : Integrable (topFormDensity (extDeriv ω)) :=
    h_cont.integrable_of_hasCompactSupport hf_comp
  have h_box_meas : MeasurableSet
      (Icc (fun _ : Fin (m + 1) => -(R : ℝ))
        (fun _ : Fin (m + 1) => (R : ℝ))) := measurableSet_Icc
  have h_univ_meas : MeasurableSet (Set.univ : Set (Fin (m + 1) → ℝ)) :=
    MeasurableSet.univ
  have h_box_subset :
      (Icc (fun _ : Fin (m + 1) => -(R : ℝ))
        (fun _ : Fin (m + 1) => (R : ℝ))) ⊆
      (Set.univ : Set (Fin (m + 1) → ℝ)) :=
    fun _ _ => Set.mem_univ _
  -- ∫_{ℝⁿ} f = ∫_{Icc} f since f = 0 on ℝⁿ \ Icc
  have h_eq : (∫ x in Set.univ, topFormDensity (extDeriv ω) x) =
      ∫ x in Icc (fun _ : Fin (m + 1) => -(R : ℝ))
        (fun _ : Fin (m + 1) => (R : ℝ)),
        topFormDensity (extDeriv ω) x :=
    setIntegral_eq_of_zero_on_diff (topFormDensity (extDeriv ω))
      h_box_meas h_univ_meas h_box_subset
      (by intro x ⟨_, hx⟩; exact h_density_outside x hx)
      hf_int.integrableOn
  rw [h_eq]
  have h_box' : (∫ x in Icc (fun _ : Fin (m + 1) => -(R : ℝ))
        (fun _ : Fin (m + 1) => (R : ℝ)),
        topFormDensity (extDeriv ω) x) =
      boxBoundaryIntegral ω
        (fun _ : Fin (m + 1) => -(R : ℝ))
        (fun _ : Fin (m + 1) => (R : ℝ)) := h_box
  rw [h_box', h_boundary_eq_zero]

/-! ## Continuity and Linearity Utilities -/

/-- Continuity of `topFormDensity (extDeriv ω)` when `ω` is `C¹`.
    Follows from the box face decomposition of the divergence. -/
theorem continuous_topFormDensity_extDeriv {m : ℕ}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (1 : ℕ∞) ω) :
    Continuous (topFormDensity (extDeriv ω)) := by
  refine (continuous_finsetSum Finset.univ fun i _ => ?_).congr
    (fun x => (topFormDensity_extDeriv_eq_boxFaceComponent_divergence
      ω ((hω.differentiable one_ne_zero).differentiableAt)).symm)
  exact (boxFaceComponent_contDiff ω i hω).continuous_fderiv_apply
    one_ne_zero |>.comp (continuous_id.prodMk continuous_const)

/-- **Interior chart lemma**: the integral of `dω` over `ℝⁿ` is zero
    when `ω` is compactly supported.

    This is the "no-boundary" case of Stokes' theorem.
    In the manifold PoU proof, this handles all interior charts. -/
theorem interiorChartZero (m : ℕ)
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (1 : ℕ∞) ω)
    (hω_support : HasCompactSupport ω) :
    (∫ x in Set.univ, topFormDensity (extDeriv ω) x) = 0 :=
  fullSpace_stokes m ω hω hω_support

/-! ### `topFormDensity` Linearity

  Basic properties of the top-form density under pointwise operations.
  These are needed to relate `d(∑ φᵢ · ω)` to `∑ d(φᵢ · ω)`.
-/

/-- `topFormDensity` distributes over pointwise addition for top forms. -/
lemma topFormDensity_add {n : ℕ}
    (ω₁ ω₂ : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    topFormDensity (fun x => ω₁ x + ω₂ x) =
      fun x => topFormDensity ω₁ x + topFormDensity ω₂ x := by
  unfold topFormDensity; funext x; simp [toTopFormFun_add]

/-- `topFormDensity` distributes over pointwise scalar multiplication
    for top forms. -/
lemma topFormDensity_smul {n : ℕ} (c : ℝ)
    (ω : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    topFormDensity (fun x => c • ω x) =
      fun x => c * topFormDensity ω x := by
  unfold topFormDensity; funext x; simp [toTopFormFun_smul]

/-- `topFormDensity` of a function-weighted top form:
    `topFormDensity (fun x => f x • ω x) = fun x => f x * topFormDensity ω x`. -/
lemma topFormDensity_fun_smul {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (ω : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    topFormDensity (fun x => f x • ω x) =
      fun x => f x * topFormDensity ω x := by
  unfold topFormDensity; funext x; simp [toTopFormFun_smul]

/-! ### `extDeriv` and Sums -/

/-- `extDeriv` of a sum of `m`-forms equals the sum of `extDeriv`'s
    (when all forms are everywhere differentiable). -/
theorem extDeriv_sum {m : ℕ} {ι : Type*} [Fintype ι]
    (ω : ι → (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (hdiff : ∀ i x, DifferentiableAt ℝ (ω i) x)
    (x : Fin (m + 1) → ℝ) :
    extDeriv (fun y => ∑ i, ω i y) x =
      ∑ i, extDeriv (ω i) x := by
  classical
  have h : ∀ (s : Finset ι),
      extDeriv (∑ i ∈ s, ω i) x = ∑ i ∈ s, extDeriv (ω i) x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      unfold extDeriv
      rw [fderiv_zero]
      exact map_zero (alternatizeUncurryFinCLM ℝ _ _)
    | insert j s' hj ih =>
      simp only [Finset.sum_insert hj]
      have hd_j := hdiff j x
      have hd_s : DifferentiableAt ℝ (∑ i ∈ s', ω i) x :=
        DifferentiableAt.sum (fun i (_ : i ∈ s') => hdiff i x)
      rw [extDeriv_add hd_j hd_s, ih]
  specialize h Finset.univ
  convert h using 2
  ext y
  simp [Finset.sum_apply]

/-! ### Integral Linearity for `extDeriv` -/

/-- The integral of `topFormDensity (extDeriv ω)` over `ℝⁿ` is additive
    when both forms are `C¹` with compact support.
    This follows from `extDeriv` linearity + integral linearity. -/
theorem integral_extDeriv_add {m : ℕ}
    (ω₁ ω₂ : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (h₁ : ContDiff ℝ (1 : ℕ∞) ω₁) (h₂ : ContDiff ℝ (1 : ℕ∞) ω₂)
    (hc₁ : HasCompactSupport ω₁) (hc₂ : HasCompactSupport ω₂) :
    (∫ x in Set.univ, topFormDensity
      (extDeriv (fun y => ω₁ y + ω₂ y)) x) =
      (∫ x in Set.univ, topFormDensity (extDeriv ω₁) x) +
      (∫ x in Set.univ, topFormDensity (extDeriv ω₂) x) := by
  have h₁d (x) := (h₁.differentiable one_ne_zero).differentiableAt (x := x)
  have h₂d (x) := (h₂.differentiable one_ne_zero).differentiableAt (x := x)
  have hden : ∀ x, topFormDensity (extDeriv (fun y => ω₁ y + ω₂ y)) x =
      topFormDensity (extDeriv ω₁) x + topFormDensity (extDeriv ω₂) x := by
    intro x
    have h := extDeriv_fun_add (h₁d x) (h₂d x)
    unfold topFormDensity at *
    rw [h]
    exact toTopFormFun_add (m + 1) (extDeriv ω₁ x) (extDeriv ω₂ x)
  conv_lhs => rw [funext hden]
  have hf₁ : Integrable (topFormDensity (extDeriv ω₁)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact continuous_topFormDensity_extDeriv ω₁ h₁
    · exact hasCompactSupport_topFormDensity_extDeriv ω₁ h₁ hc₁
  have hf₂ : Integrable (topFormDensity (extDeriv ω₂)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact continuous_topFormDensity_extDeriv ω₂ h₂
    · exact hasCompactSupport_topFormDensity_extDeriv ω₂ h₂ hc₂
  exact integral_add hf₁.integrableOn hf₂.integrableOn

end DifferentialForm
