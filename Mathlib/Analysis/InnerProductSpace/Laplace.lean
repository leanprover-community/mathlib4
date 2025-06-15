/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

/-!
# The Laplace Operator

This file defines the Laplace operator for functions `f : E → F` on real, finite-dimensional, inner
product spaces `E`. In essence, we define the Laplacian of `f` as the second derivative, applied to
the canonical covariant tensor of `E`, as defined and discussed in
`Mathlib.Analysis.InnerProductSpace.CanonicalTensor`.

We show that the Laplace operator is `ℂ`-linear on continuously differentiable functions, and
establish the standard formula for computing the Laplace operator in terms of orthonormal bases of
`E`.
-/

open InnerProductSpace TensorProduct Topology

section secondDerivativeAPI

/-!
## Supporting API

The definition of the Laplace Operator of a function `f : E → F` involves the notion of the second
derivative, which can be seen as a continous multilinear map `ContinuousMultilinearMap 𝕜 (fun (i :
Fin 2) ↦ E) F`, a bilinear map `E →ₗ[𝕜] E →ₗ[𝕜] F`, or a linear map on tensors
`E ⊗[𝕜] E →ₗ[𝕜] F`. This section provides convenience API to convert between these notions.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E` to bilinear maps
`E →ₗ[ℝ] E →ₗ[ℝ] ℝ
-/
noncomputable def bilinear_of_iteratedFDeriv_two (f : E → F) : E → E →ₗ[𝕜] E →ₗ[𝕜] F :=
  fun x ↦ (fderiv 𝕜 (fderiv 𝕜 f) x).toLinearMap₂

/--
Expression of `bilinear_of_iteratedFDeriv_two` in terms of `iteratedFDeriv`.
-/
lemma bilinear_of_iteratedFDeriv_two_eq_iteratedFDeriv (f : E → F) (e e₁ e₂ : E) :
    bilinear_of_iteratedFDeriv_two 𝕜 f e e₁ e₂ = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  simp [iteratedFDeriv_two_apply f e ![e₁, e₂], bilinear_of_iteratedFDeriv_two]

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E` to linear maps
`E ⊗[𝕜] E →ₗ[𝕜] F`.
-/
noncomputable def tensor_of_iteratedFDeriv_two (f : E → F) : E → E ⊗[𝕜] E →ₗ[𝕜] F :=
  fun e ↦ lift (bilinear_of_iteratedFDeriv_two 𝕜 f e)

/--
Expression of `tensor_of_iteratedFDeriv_two` in terms of `iteratedFDeriv`.
-/
lemma tensor_of_iteratedFDeriv_two_eq_iteratedFDeriv (f : E → F) (e e₁ e₂ : E) :
    tensor_of_iteratedFDeriv_two 𝕜 f e (e₁ ⊗ₜ[𝕜] e₂) = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  rw [← bilinear_of_iteratedFDeriv_two_eq_iteratedFDeriv, tensor_of_iteratedFDeriv_two]
  rfl

end secondDerivativeAPI

/-!
## Definition of the Laplace Operator
-/

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : E → F} {x : E}

variable (f) in
/--
Definition of the Laplace operator for functions on real inner product spaces.
-/
noncomputable def Real.Laplace : E → F :=
  fun x ↦ tensor_of_iteratedFDeriv_two ℝ f x (InnerProductSpace.canonicalCovariantTensor E)

/--
Introduce `Δ` as a notation for the Laplace operator.
-/
notation "Δ" => Real.Laplace

/-!
## Computation of Δ in Terms of Orthonormal Bases
-/

variable (f) in
/--
Standard formula, computing the Laplace operator from any orthonormal basis.
-/
theorem laplace_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℝ E) :
    Δ f = fun x ↦ ∑ i, iteratedFDeriv ℝ 2 f x ![v i, v i] := by
  ext x
  simp [Real.Laplace, canonicalCovariantTensor_eq_sum E v,
    tensor_of_iteratedFDeriv_two_eq_iteratedFDeriv]

variable (f) in
/--
Standard formula, computing the Laplace operator from the standard orthonormal basis of a real inner
product space.
-/
theorem laplace_eq_iteratedFDeriv_stdOrthonormalBasis :
    Δ f = fun x ↦
      ∑ i, iteratedFDeriv ℝ 2 f x ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] :=
  laplace_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)

/--
Special case of the standard formula for functions on `ℂ`, with the standard structure as a real
inner product space.
-/
theorem laplace_eq_iteratedFDeriv_complexPlane (f : ℂ → F) :
    Δ f = fun x ↦
      iteratedFDeriv ℝ 2 f x ![1, 1] + iteratedFDeriv ℝ 2 f x ![Complex.I, Complex.I] := by
  simp [laplace_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI]

/-!
## Congruence Lemma for Δ
-/

/--
If two functions agree in a neighborhood of a point, then so do their Laplacians.
-/
theorem laplace_congr_nhds (h : f₁ =ᶠ[𝓝 x] f₂) :
    Δ f₁ =ᶠ[𝓝 x] Δ f₂ := by
  filter_upwards [Filter.EventuallyEq.iteratedFDeriv ℝ h 2] with x hx
  simp [laplace_eq_iteratedFDeriv_stdOrthonormalBasis, hx]

/-!
## ℂ-Linearity of Δ on Continuously Differentiable Functions
-/

/-- The Laplace operator commutes with addition. -/
theorem ContDiffAt.laplace_add (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) x = (Δ f₁) x + (Δ f₂) x := by
  simp [laplace_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_add_distrib, iteratedFDeriv_add_apply h₁ h₂]

/-- The Laplace operator commutes with addition. -/
theorem ContDiffAt.laplace_add_nhd (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) =ᶠ[𝓝 x] (Δ f₁) + (Δ f₂):= by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplace_add h₂x

/-- The Laplace operator commutes with scalar multiplication. -/
theorem laplace_smul (v : ℝ) (hf : ContDiffAt ℝ 2 f x) : Δ (v • f) x = v • (Δ f) x := by
  simp [laplace_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_smul_apply hf,
    Finset.smul_sum]

/-!
## Commutativity of Δ with Linear Operators

This section establishes commutativity with linear operators, showing in particular that `Δ`
commutes with taking real and imaginary parts of complex-valued functions.
-/

/-- The Laplace operator commuted with left composition by continuous linear maps. -/
theorem ContDiffAt.laplace_CLM_comp_left {l : F →L[ℝ] G} (h : ContDiffAt ℝ 2 f x) :
    Δ (l ∘ f) x = (l ∘ (Δ f)) x := by
  simp [laplace_eq_iteratedFDeriv_stdOrthonormalBasis,
    l.iteratedFDeriv_comp_left h, (by rfl : (2 : ℕ∞) = (2 : ℕ))]

/-- The Laplace operator commuted with left composition by continuous linear equivalences. -/
theorem laplace_CLE_comp_left {l : F ≃L[ℝ] G} :
    Δ (l ∘ f) = l ∘ (Δ f) := by
  ext x
  simp [laplace_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left]
