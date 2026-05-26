/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Distribution.DerivNotation
public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

/-!
# The Laplacian

This file defines the Laplacian for functions `f : E → F` on real, finite-dimensional, inner product
spaces `E`. In essence, we define the Laplacian of `f` as the second derivative, applied to the
canonical covariant tensor of `E`, as defined and discussed in
`Mathlib.Analysis.InnerProductSpace.CanonicalTensor`.

We show that the Laplacian is `ℝ`-linear on continuously differentiable functions, and establish the
standard formula for computing the Laplacian in terms of orthonormal bases of `E`.
-/

@[expose] public section

open Filter TensorProduct Topology

section secondDerivativeAPI

/-!
## Supporting API

The definition of the Laplacian of a function `f : E → F` involves the notion of the second
derivative, which can be seen as a continuous multilinear map `ContinuousMultilinearMap 𝕜 (fun (i :
Fin 2) ↦ E) F`, a bilinear map `E →ₗ[𝕜] E →ₗ[𝕜] F`, or a linear map on tensors `E ⊗[𝕜] E →ₗ[𝕜]
F`. This section provides convenience API to convert between these notions.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormMetric F] [AddCommGroup F] [IsNormedAddGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormMetric G] [AddCommGroup G] [IsNormedAddGroup G] [NormedSpace 𝕜 G]

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E` to bilinear maps
`E →ₗ[ℝ] E →ₗ[ℝ] ℝ`.
-/
noncomputable def bilinearIteratedFDerivWithinTwo (f : E → F) (s : Set E) : E → E →ₗ[𝕜] E →ₗ[𝕜] F :=
  fun x ↦ (fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x).toLinearMap₁₂

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E` to bilinear maps
`E →ₗ[ℝ] E →ₗ[ℝ] ℝ`.
-/
noncomputable def bilinearIteratedFDerivTwo (f : E → F) : E → E →ₗ[𝕜] E →ₗ[𝕜] F :=
  fun x ↦ (fderiv 𝕜 (fderiv 𝕜 f) x).toLinearMap₁₂

/--
Expression of `bilinearIteratedFDerivWithinTwo` in terms of `iteratedFDerivWithin`.
-/
lemma bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv {e : E} {s : Set E} (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s) (e₁ e₂ : E) :
    bilinearIteratedFDerivWithinTwo 𝕜 f s e e₁ e₂ = iteratedFDerivWithin 𝕜 2 f s e ![e₁, e₂] := by
  simp [iteratedFDerivWithin_two_apply f hs he ![e₁, e₂], bilinearIteratedFDerivWithinTwo]

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
noncomputable def tensorIteratedFDerivWithinTwo (f : E → F) (s : Set E) : E → E ⊗[𝕜] E →ₗ[𝕜] F :=
  fun e ↦ lift (bilinearIteratedFDerivWithinTwo 𝕜 f s e)

variable (𝕜) in
/--
Convenience reformulation of the second iterated derivative, as a map from `E` to linear maps
`E ⊗[𝕜] E →ₗ[𝕜] F`.
-/
noncomputable def tensorIteratedFDerivTwo (f : E → F) : E → E ⊗[𝕜] E →ₗ[𝕜] F :=
  fun e ↦ lift (bilinearIteratedFDerivTwo 𝕜 f e)

/--
Expression of `tensorIteratedFDerivTwo` in terms of `iteratedFDerivWithin`.
-/
lemma tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin {e : E} {s : Set E} (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (he : e ∈ s) (e₁ e₂ : E) :
    tensorIteratedFDerivWithinTwo 𝕜 f s e (e₁ ⊗ₜ[𝕜] e₂) =
      iteratedFDerivWithin 𝕜 2 f s e ![e₁, e₂] := by
  rw [← bilinearIteratedFDerivWithinTwo_eq_iteratedFDeriv f hs he, tensorIteratedFDerivWithinTwo,
    lift.tmul]

/--
Expression of `tensorIteratedFDerivTwo` in terms of `iteratedFDeriv`.
-/
lemma tensorIteratedFDerivTwo_eq_iteratedFDeriv (f : E → F) (e e₁ e₂ : E) :
    tensorIteratedFDerivTwo 𝕜 f e (e₁ ⊗ₜ[𝕜] e₂) = iteratedFDeriv 𝕜 2 f e ![e₁, e₂] := by
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv, tensorIteratedFDerivTwo, lift.tmul]

end secondDerivativeAPI

/-!
## Definition of the Laplacian
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {E : Type*} [NormMetric E] [AddCommGroup E] [IsNormedAddGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormMetric F] [AddCommGroup F] [IsNormedAddGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]
  {G : Type*} [NormMetric G] [AddCommGroup G] [IsNormedAddGroup G] [NormedSpace ℝ G]
  {f f₁ f₂ : E → F} {x : E} {s : Set E}

namespace InnerProductSpace

variable (f s) in
/--
Laplacian for functions on real inner product spaces, with respect to a set `s`. Use `open
InnerProductSpace` to access the notation `Δ[s]` for `InnerProductSpace.LaplacianWithin`.
-/
noncomputable def laplacianWithin : E → F :=
  fun x ↦ tensorIteratedFDerivWithinTwo ℝ f s x (InnerProductSpace.canonicalCovariantTensor E)

@[inherit_doc]
scoped[InnerProductSpace] notation "Δ[" s "] " f:60 => laplacianWithin f s

noncomputable
instance instLaplacian : Laplacian (E → F) (E → F) where
  laplacian f x := tensorIteratedFDerivTwo ℝ f x (InnerProductSpace.canonicalCovariantTensor E)

@[deprecated (since := "2025-12-31")]
alias InnerProduct.laplacian := _root_.Laplacian.laplacian

open Laplacian

/--
The Laplacian equals the Laplacian with respect to `Set.univ`.
-/
@[simp]
theorem laplacianWithin_univ :
    Δ[(Set.univ : Set E)] f = Δ f := by
  ext x
  simp [laplacian, tensorIteratedFDerivTwo, bilinearIteratedFDerivTwo,
    laplacianWithin, tensorIteratedFDerivWithinTwo, bilinearIteratedFDerivWithinTwo]

/-!
## Computation of Δ in Terms of Orthonormal Bases
-/

variable (f) in
/--
Standard formula, computing the Laplacian from any orthonormal basis.
-/
theorem laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis {ι : Type*} [Fintype ι] {e : E}
    (hs : UniqueDiffOn ℝ s) (he : e ∈ s) (v : OrthonormalBasis ι ℝ E) :
    (Δ[s] f) e = ∑ i, iteratedFDerivWithin ℝ 2 f s e ![v i, v i] := by
  simp [InnerProductSpace.laplacianWithin, canonicalCovariantTensor_eq_sum E v,
    tensorIteratedFDerivWithinTwo_eq_iteratedFDerivWithin f hs he]

variable (f) in
/--
Standard formula, computing the Laplacian from any orthonormal basis.
-/
theorem laplacian_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℝ E) :
    Δ f = fun x ↦ ∑ i, iteratedFDeriv ℝ 2 f x ![v i, v i] := by
  ext x
  simp [laplacian, canonicalCovariantTensor_eq_sum E v, tensorIteratedFDerivTwo_eq_iteratedFDeriv]

variable (f) in
/--
Standard formula, computing the Laplacian from the standard orthonormal basis of a real inner
product space.
-/
theorem laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis {e : E} (hs : UniqueDiffOn ℝ s)
    (he : e ∈ s) :
    (Δ[s] f) e = ∑ i, iteratedFDerivWithin ℝ 2 f s e
      ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] := by
  apply laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he (stdOrthonormalBasis ℝ E)

variable (f) in
/--
Standard formula, computing the Laplacian from the standard orthonormal basis of a real inner
product space.
-/
theorem laplacian_eq_iteratedFDeriv_stdOrthonormalBasis :
    Δ f = fun x ↦
      ∑ i, iteratedFDeriv ℝ 2 f x ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] :=
  laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)

/-- For a function on `ℝ`, the Laplacian is the second derivative: version within a set. -/
theorem laplacianWithin_eq_iteratedDerivWithin_real {e : ℝ} {s : Set ℝ} (f : ℝ → F)
    (hs : UniqueDiffOn ℝ s) (he : e ∈ s) :
    (Δ[s] f) e = iteratedDerivWithin 2 f s e := by
  simp only [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
        (OrthonormalBasis.singleton (Fin 1) ℝ),
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, OrthonormalBasis.singleton_apply,
    Finset.sum_const, Finset.card_singleton, one_smul, iteratedDerivWithin_eq_iteratedFDerivWithin]
  congr with i
  fin_cases i <;> simp

/-- For a function on `ℝ`, the Laplacian is the second derivative. -/
@[simp]
theorem laplacian_eq_iteratedDeriv_real {e : ℝ} (f : ℝ → F) :
    Δ f e = iteratedDeriv 2 f e := by
  rw [← laplacianWithin_univ, ← iteratedDerivWithin_univ,
    laplacianWithin_eq_iteratedDerivWithin_real _ (by simp) (by simp)]

/--
Special case of the standard formula for functions on `ℂ`, with the standard real inner product
structure.
-/
theorem laplacianWithin_eq_iteratedFDerivWithin_complexPlane {e : ℂ} {s : Set ℂ} (f : ℂ → F)
    (hs : UniqueDiffOn ℝ s) (he : e ∈ s) :
    (Δ[s] f) e = iteratedFDerivWithin ℝ 2 f s e ![1, 1]
      + iteratedFDerivWithin ℝ 2 f s e ![Complex.I, Complex.I] := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
    Complex.orthonormalBasisOneI]

/--
Special case of the standard formula for functions on `ℂ`, with the standard real inner product
structure.
-/
theorem laplacian_eq_iteratedFDeriv_complexPlane (f : ℂ → F) :
    Δ f = fun x ↦
      iteratedFDeriv ℝ 2 f x ![1, 1] + iteratedFDeriv ℝ 2 f x ![Complex.I, Complex.I] := by
  simp [laplacian_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI]

/--
The Laplacian of a constant function is zero.
-/
@[simp] theorem laplacian_const {c : F} :
    Laplacian.laplacian (fun (_ : E) ↦ c) = 0 := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_of_ne two_ne_zero,
    Pi.zero_def]

/-!
## Congruence Lemmata for Δ
-/

/--
If two functions agree in a neighborhood of a point, then so do their Laplacians.
-/
theorem laplacianWithin_congr_nhdsWithin (h : f₁ =ᶠ[𝓝[s] x] f₂) (hs : UniqueDiffOn ℝ s) :
    Δ[s] f₁ =ᶠ[𝓝[s] x] Δ[s] f₂ := by
  filter_upwards [EventuallyEq.iteratedFDerivWithin (𝕜 := ℝ) h 2,
    eventually_mem_nhdsWithin] with x h₁x h₂x
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs h₂x, h₁x]

/--
If two functions agree in a neighborhood of a point, then so do their Laplacians.
-/
theorem laplacian_congr_nhds (h : f₁ =ᶠ[𝓝 x] f₂) :
    Δ f₁ =ᶠ[𝓝 x] Δ f₂ := by
  filter_upwards [EventuallyEq.iteratedFDeriv ℝ h 2] with x hx
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hx]

/-!
## 𝕜-Linearity of Δ on Continuously Differentiable Functions
-/

/-- The Laplacian commutes with addition. -/
theorem _root_.ContDiffWithinAt.laplacianWithin_add (h₁ : ContDiffWithinAt ℝ 2 f₁ s x)
    (h₂ : ContDiffWithinAt ℝ 2 f₂ s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    (Δ[s] (f₁ + f₂)) x = (Δ[s] f₁) x + (Δ[s] f₂) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    ← Finset.sum_add_distrib, iteratedFDerivWithin_add_apply h₁ h₂ hs hx]

/-- The Laplacian commutes with addition. -/
theorem _root_.ContDiffAt.laplacian_add (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) x = Δ f₁ x + Δ f₂ x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_add_distrib, iteratedFDeriv_add_apply h₁ h₂]

/-- The Laplacian commutes with addition. -/
theorem _root_.ContDiffAt.laplacianWithin_add_nhdsWithin (h₁ : ContDiffWithinAt ℝ 2 f₁ s x)
    (h₂ : ContDiffWithinAt ℝ 2 f₂ s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    Δ[s] (f₁ + f₂) =ᶠ[𝓝[s] x] (Δ[s] f₁) + Δ[s] f₂ := by
  nth_rw 1 [← s.insert_eq_of_mem hx]
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp),
    eventually_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [s.insert_eq_of_mem hx] at h₃y
  simp [h₁y.laplacianWithin_add h₂y hs h₃y]

/-- The Laplacian commutes with addition. -/
theorem _root_.ContDiffAt.laplacian_add_nhds (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ + f₂) =ᶠ[𝓝 x] (Δ f₁) + (Δ f₂) := by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_add h₂x

/-- The Laplacian commutes with negation. -/
theorem laplacianWithin_neg (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    (Δ[s] (-f)) x = -(Δ[s] f) x := by
  simp only [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx]
  rw [iteratedFDerivWithin_neg_apply hs hx]
  aesop

/-- The Laplacian commutes with negation. -/
theorem laplacian_neg :
    Δ (-f) = -(Δ f) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_neg]
  aesop

/-- The Laplacian commutes with subtraction. -/
theorem _root_.ContDiffWithinAt.laplacianWithin_sub (h₁ : ContDiffWithinAt ℝ 2 f₁ s x)
    (h₂ : ContDiffWithinAt ℝ 2 f₂ s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    (Δ[s] (f₁ - f₂)) x = (Δ[s] f₁) x - (Δ[s] f₂) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    ← Finset.sum_sub_distrib, iteratedFDerivWithin_sub_apply h₁ h₂ hs hx]

/-- The Laplacian commutes with subtraction. -/
theorem _root_.ContDiffAt.laplacian_sub (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ - f₂) x = Δ f₁ x - Δ f₂ x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    ← Finset.sum_sub_distrib, iteratedFDeriv_sub_apply h₁ h₂]

/-- The Laplacian commutes with subtraction. -/
theorem _root_.ContDiffAt.laplacianWithin_sub_nhdsWithin (h₁ : ContDiffWithinAt ℝ 2 f₁ s x)
    (h₂ : ContDiffWithinAt ℝ 2 f₂ s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    Δ[s] (f₁ - f₂) =ᶠ[𝓝[s] x] (Δ[s] f₁) - Δ[s] f₂ := by
  nth_rw 1 [← s.insert_eq_of_mem hx]
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp),
    eventually_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [s.insert_eq_of_mem hx] at h₃y
  simp [h₁y.laplacianWithin_sub h₂y hs h₃y]

/-- The Laplacian commutes with subtraction. -/
theorem _root_.ContDiffAt.laplacian_sub_nhds (h₁ : ContDiffAt ℝ 2 f₁ x) (h₂ : ContDiffAt ℝ 2 f₂ x) :
    Δ (f₁ - f₂) =ᶠ[𝓝 x] (Δ f₁) - (Δ f₂) := by
  filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with x h₁x h₂x
  exact h₁x.laplacian_sub h₂x

/-- The Laplacian commutes with scalar multiplication. -/
theorem laplacianWithin_smul (v : 𝕜) (hf : ContDiffWithinAt ℝ 2 f s x) (hs : UniqueDiffOn ℝ s)
    (hx : x ∈ s) :
    (Δ[s] (v • f)) x = v • (Δ[s] f) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    iteratedFDerivWithin_const_smul_apply hf hs hx,
    Finset.smul_sum]

/-- The Laplacian commutes with scalar multiplication. -/
theorem laplacian_smul (v : 𝕜) (hf : ContDiffAt ℝ 2 f x) : Δ (v • f) x = v • (Δ f) x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_smul_apply hf,
    Finset.smul_sum]

/-- The Laplacian commutes with scalar multiplication. -/
theorem laplacianWithin_smul_nhds
    (v : 𝕜) (hf : ContDiffWithinAt ℝ 2 f s x) (hs : UniqueDiffOn ℝ s) :
    Δ[s] (v • f) =ᶠ[𝓝[s] x] v • (Δ[s] f) := by
  filter_upwards [(hf.eventually (by simp)).filter_mono (nhdsWithin_mono _ (Set.subset_insert ..)),
    eventually_mem_nhdsWithin] with a h₁a using laplacianWithin_smul v h₁a hs

/-- The Laplacian commutes with scalar multiplication. -/
theorem laplacian_smul_nhds (v : 𝕜) (h : ContDiffAt ℝ 2 f x) :
    Δ (v • f) =ᶠ[𝓝 x] v • (Δ f) := by
  filter_upwards [h.eventually (by simp)] with a ha
  simp [laplacian_smul v ha]

/-!
## Commutativity of Δ with Linear Operators

This section establishes commutativity with linear operators, showing in particular that `Δ`
commutes with taking real and imaginary parts of complex-valued functions.
-/

/-- The Laplacian commutes with left composition by continuous linear maps. -/
theorem _root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left {l : F →L[ℝ] G}
    (h : ContDiffWithinAt ℝ 2 f s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    (Δ[s] (l ∘ f)) x = (l ∘ (Δ[s] f)) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    l.iteratedFDerivWithin_comp_left h hs hx]

/-- The Laplacian commutes with left composition by continuous linear maps. -/
theorem _root_.ContDiffAt.laplacian_CLM_comp_left {l : F →L[ℝ] G} (h : ContDiffAt ℝ 2 f x) :
    Δ (l ∘ f) x = (l ∘ (Δ f)) x := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left h]

/-- The Laplacian commutes with left composition by continuous linear maps. -/
theorem _root_.ContDiffWithinAt.laplacianWithin_CLM_comp_left_nhds {l : F →L[ℝ] G}
    (h : ContDiffWithinAt ℝ 2 f s x) (hs : UniqueDiffOn ℝ s) :
    Δ[s] (l ∘ f) =ᶠ[𝓝[s] x] l ∘ Δ[s] f := by
  filter_upwards [(h.eventually (by simp)).filter_mono (nhdsWithin_mono _ (Set.subset_insert ..)),
    eventually_mem_nhdsWithin] with a h₁a using h₁a.laplacianWithin_CLM_comp_left hs

/-- The Laplacian commutes with left composition by continuous linear maps. -/
theorem _root_.ContDiffAt.laplacian_CLM_comp_left_nhds {l : F →L[ℝ] G} (h : ContDiffAt ℝ 2 f x) :
    Δ (l ∘ f) =ᶠ[𝓝 x] l ∘ (Δ f) := by
  filter_upwards [h.eventually (by simp)] with a ha
  rw [ha.laplacian_CLM_comp_left]

/-- The Laplacian commutes with left composition by continuous linear equivalences. -/
theorem laplacianWithin_CLE_comp_left {l : F ≃L[ℝ] G} (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    (Δ[s] (l ∘ f)) x = (l ∘ (Δ[s] f)) x := by
  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
    l.iteratedFDerivWithin_comp_left _ hs hx]

/-- The Laplacian commutes with left composition by continuous linear equivalences. -/
theorem laplacian_CLE_comp_left {l : F ≃L[ℝ] G} :
    Δ (l ∘ f) = l ∘ (Δ f) := by
  ext x
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, l.iteratedFDeriv_comp_left]

end InnerProductSpace
