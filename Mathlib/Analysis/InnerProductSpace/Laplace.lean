/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

/-!
# The Laplacian

This file defines the Laplacian for functions `f : E → F` on real, finite-dimensional, inner product
spaces `E`. In essence, we define the Laplacian of `f` as the second derivative, applied to the
canonical covariant tensor of `E`, as defined and discussed in
`Mathlib.Analysis.InnerProductSpace.CanonicalTensor`.

We show that the Laplacian is `ℂ`-linear on continuously differentiable functions, and establish the
standard formula for computing the Laplacian in terms of orthonormal bases of `E`.
-/

open Filter TensorProduct Topology

section secondDerivativeAPI

/-!
## Supporting API

The definition of the Laplacian of a function `f : E → F` involves the notion of the second
derivative, which can be seen as a continous multilinear map `ContinuousMultilinearMap 𝕜 (fun (i :
Fin 2) ↦ E) F`, a bilinear map `E →ₗ[𝕜] E →ₗ[𝕜] F`, or a linear map on tensors `E ⊗[𝕜] E →ₗ[𝕜]
F`. This section provides convenience API to convert between these notions.
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
noncomputable def bilinearIteratedFDerivTwo (f : E → F) : E → E →ₗ[𝕜] E →ₗ[𝕜] F :=
  fun x ↦ (fderiv 𝕜 (fderiv 𝕜 f) x).toLinearMap₂

/--
Expression of `bilinearIteratedFDerivTwo` in terms of `iteratedFDeriv`.
-/
lemma bilinearIteratedFDerivTwo_eq_iteratedFDeriv (f : E → F) (e e₁ e₂ : E) :
    bilinearIteratedFDerivTwo 𝕜 f e e₁ e₂ = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  simp [iteratedFDeriv_two_apply f e ![e₁, e₂], bilinearIteratedFDerivTwo]

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E` to linear maps
`E ⊗[𝕜] E →ₗ[𝕜] F`.
-/
noncomputable def tensorIteratedFDerivTwo (f : E → F) : E → E ⊗[𝕜] E →ₗ[𝕜] F :=
  fun e ↦ lift (bilinearIteratedFDerivTwo 𝕜 f e)

/--
Expression of `tensorIteratedFDerivTwo` in terms of `iteratedFDeriv`.
-/
lemma tensorIteratedFDerivTwo_eq_iteratedFDeriv (f : E → F) (e e₁ e₂ : E) :
    tensorIteratedFDerivTwo 𝕜 f e (e₁ ⊗ₜ[𝕜] e₂) = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv, tensorIteratedFDerivTwo]
  rfl

end secondDerivativeAPI

/-!
## Definition of the Laplacian
-/

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : E → F} {x : E}

namespace InnerProductSpace

variable (f) in
/--
Laplacian for functions on real inner product spaces. Use `open InnerProductSpace` to access the
notation `Δ` for `InnerProductSpace.Laplacian`.
-/
noncomputable def laplacian : E → F :=
  fun x ↦ tensorIteratedFDerivTwo ℝ f x (InnerProductSpace.canonicalCovariantTensor E)

@[inherit_doc]
scoped[InnerProductSpace] notation "Δ" => laplacian

/-!
## Computation of Δ in Terms of Orthonormal Bases
-/

variable (f) in
/--
Standard formula, computing the Laplacian from any orthonormal basis.
-/
theorem laplacian_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℝ E) :
    Δ f = fun x ↦ ∑ i, iteratedFDeriv ℝ 2 f x ![v i, v i] := by
  ext x
  simp [InnerProductSpace.laplacian, canonicalCovariantTensor_eq_sum E v,
    tensorIteratedFDerivTwo_eq_iteratedFDeriv]

variable (f) in
/--
Standard formula, computing the Laplacian from the standard orthonormal basis of a real inner
product space.
-/
theorem laplacian_eq_iteratedFDeriv_stdOrthonormalBasis :
    Δ f = fun x ↦
      ∑ i, iteratedFDeriv ℝ 2 f x ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] :=
  laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)

/--
Special case of the standard formula for functions on `ℂ`, with the standard real inner product
structure.
-/
theorem laplacian_eq_iteratedFDeriv_complexPlane (f : ℂ → F) :
    Δ f = fun x ↦
      iteratedFDeriv ℝ 2 f x ![1, 1] + iteratedFDeriv ℝ 2 f x ![Complex.I, Complex.I] := by
  simp [laplacian_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI]

/-!
## Congruence Lemma for Δ
-/

/--
If two functions agree in a neighborhood of a point, then so do their Laplacians.
-/
theorem laplacian_congr_nhds (h : f₁ =ᶠ[𝓝 x] f₂) :
    Δ f₁ =ᶠ[𝓝 x] Δ f₂ := by
  filter_upwards [EventuallyEq.iteratedFDeriv ℝ h 2] with x hx
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hx]

/-!
## ℝ-Linearity of Δ on Continuously Differentiable Functions
-/

/-- The Laplacian commutes with addition. -/
theorem _root_.ContDiffAt.laplacian_add (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) x = (Δ f₁) x + (Δ f₂) x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_add_distrib, iteratedFDeriv_add_apply h₁ h₂]

/-- The Laplacian commutes with addition. -/
theorem _root_.ContDiffAt.laplacian_add_nhd (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) =ᶠ[𝓝 x] (Δ f₁) + (Δ f₂):= by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_add h₂x

/-- The Laplacian commutes with scalar multiplication. -/
theorem laplacian_smul (v : ℝ) (hf : ContDiffAt ℝ 2 f x) : Δ (v • f) x = v • (Δ f) x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_smul_apply hf,
    Finset.smul_sum]

/-!
## Commutativity of Δ with Linear Operators

This section establishes commutativity with linear operators, showing in particular that `Δ`
commutes with taking real and imaginary parts of complex-valued functions.
-/

/-- The Laplacian commutes with left composition by continuous linear maps. -/
theorem _root_.ContDiffAt.laplacian_CLM_comp_left {l : F →L[ℝ] G} (h : ContDiffAt ℝ 2 f x) :
    Δ (l ∘ f) x = (l ∘ (Δ f)) x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    l.iteratedFDeriv_comp_left h, (by rfl : (2 : ℕ∞) = (2 : ℕ))]

/-- The Laplacian commutes with left composition by continuous linear equivalences. -/
theorem laplacian_CLE_comp_left {l : F ≃L[ℝ] G} :
    Δ (l ∘ f) = l ∘ (Δ f) := by
  ext x
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left]

end InnerProductSpace
