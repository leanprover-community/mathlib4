/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.Stochastic

/-!
# Spectrum and Perron–Frobenius for matrices

Spectrum, eigenvalue, and positivity lemmas for real and complex matrices used in the
Perron–Frobenius development.

## Main definitions

* `Matrix.supportFinset`, `Matrix.kernelFinset`: the indices at which a vector is strictly
  positive, resp. zero.

## Main results

* `Matrix.hasEigenvalue_toLin'_iff_det_sub_eq_zero`: `μ` is an eigenvalue of `A` iff
  `det (μ • 1 - A) = 0`.
* `Matrix.spectralRadius_finite`, `Matrix.spectralRadius_le_opNorm`: the spectral radius of a
  matrix is finite and bounded by the operator norm.
* `Matrix.spectralRadius_stochastic_le_one`: the spectral radius of a row-stochastic matrix is
  at most `1`.

## References

* [E. Seneta, *Non-negative Matrices and Markov Chains*][seneta2006]

## Tags

Perron–Frobenius theorem, matrix spectrum, irreducible matrix, primitive matrix
-/

@[expose] public section

namespace Matrix
open LinearMap Polynomial Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
## Spectral Properties of Matrices
-/

/-- The determinant of `μ • 1 - A` is the characteristic polynomial of `A` at `μ`. -/
lemma det_smul_sub_eq_eval_charpoly {R : Type*} [CommRing R] (A : Matrix n n R) (μ : R) :
    det (μ • 1 - A) = A.charpoly.eval μ := by
  rw [eval_charpoly, scalar_apply, smul_one_eq_diagonal]

/-!
## Determinant, kernel, and invertibility
-/

section
variable {K V : Type*} [CommRing K] [IsDomain K] [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V] {f : V →ₗ[K] V}

/-- If a non-zero vector `v` is in the kernel of a linear map `f`, then `det f` must be zero. -/
lemma det_eq_zero_of_exists_mem_ker (h : ∃ v, v ≠ 0 ∧ f v = 0) : LinearMap.det f = 0 :=
  LinearMap.det_eq_zero_iff_ker_ne_bot.mpr <|
    (Submodule.ne_bot_iff _).mpr <| h.imp fun _ hv => ⟨hv.2, hv.1⟩

/-- If a linear endomorphism of a finite free module over a domain is not injective,
then its determinant is zero. -/
lemma det_eq_zero_of_not_injective (h : ¬Function.Injective f) : LinearMap.det f = 0 :=
  LinearMap.det_eq_zero_iff_ker_ne_bot.mpr (mt LinearMap.ker_eq_bot.mp h)

end

omit [Fintype n] [DecidableEq n] in
/-- If the determinant is zero, the linear map is not injective. -/
lemma not_injective_of_det_eq_zero [Finite n] {f : (n → ℝ) →ₗ[ℝ] (n → ℝ)} (h : f.det = 0) :
    ¬Function.Injective f := fun hf => det_eq_zero_iff_ker_ne_bot.mp h (ker_eq_bot.mpr hf)

/-- For a matrix `A`, the associated linear map `toLin' A` has a non-trivial kernel
if and only if the determinant of `A` is zero. -/
lemma ker_toLin'_ne_bot_iff_det_eq_zero (A : Matrix n n ℝ) : ker (toLin' A) ≠ ⊥ ↔ det A = 0 := by
  rw [← det_toLin', det_eq_zero_iff_ker_ne_bot]

/-- A real number `μ` is an eigenvalue of a matrix `A` if and only if `det(μ • 1 - A) = 0`. -/
lemma hasEigenvalue_toLin'_iff_det_sub_eq_zero (A : Matrix n n ℝ) (μ : ℝ) :
    Module.End.HasEigenvalue (toLin' A) μ ↔ det (μ • 1 - A) = 0 := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, spectrum_toLin', mem_spectrum_iff_isRoot_charpoly,
    Polynomial.IsRoot.def, det_smul_sub_eq_eval_charpoly]

/-! ## Spectral Radius Theory for Matrices -/

/-- A linear endomorphism is bijective iff its kernel is trivial and its range is everything. -/
lemma LinearMap.bijective_iff_ker_eq_bot_and_range_eq_top {R : Type*} [Ring R] {M : Type*}
    [AddCommGroup M] [Module R M] (f : M →ₗ[R] M) :
    Function.Bijective f ↔ ker f = ⊥ ∧ range f = ⊤ :=
  and_congr ker_eq_bot.symm range_eq_top.symm

/-- For finite dimensions, injective endomorphisms are bijective. -/
lemma injective_iff_bijective_toLin' {K : Type*} [Field K] (A : Matrix n n K) :
    Function.Injective (Matrix.toLin' A) ↔ Function.Bijective (Matrix.toLin' A) :=
  ⟨fun h => ⟨h, LinearMap.injective_iff_surjective.mp h⟩, And.left⟩

/-- If the determinant of `toLin' A` is non-zero, then `toLin' A` is a unit. -/
lemma isUnit_of_det_ne_zero {K : Type*} [Field K] (A : Matrix n n K)
    (h_det_ne_zero : LinearMap.det (toLin' A) ≠ 0) : IsUnit (toLin' A) :=
  (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h_det_ne_zero)

/-- An eigenvalue of a real matrix is bounded in norm by the operator norm of the associated
continuous linear map. -/
lemma spectralRadius_le_nnnorm_of_mem_spectrum {A : Matrix n n ℝ} {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ A) : ‖μ‖₊ ≤ ‖(Matrix.toLin' A).toContinuousLinearMap‖₊ := by
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    (show μ ∈ spectrum ℝ (toLin' A) by rwa [spectrum_toLin'])).exists_hasEigenvector
  have h := ContinuousLinearMap.le_opNorm (Matrix.toLin' A).toContinuousLinearMap v
  rw [LinearMap.coe_toContinuousLinearMap', hv.apply_eq_smul, norm_smul] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hv.2)

/-- The spectral radius of a real matrix is finite. -/
lemma spectralRadius_lt_top {A : Matrix n n ℝ} : spectralRadius ℝ A < ⊤ :=
  lt_of_le_of_lt (iSup₂_le fun _ hμ =>
    ENNReal.coe_le_coe.mpr (spectralRadius_le_nnnorm_of_mem_spectrum hμ)) ENNReal.coe_lt_top

omit [DecidableEq n] in
/-- Multiplying by a matrix on the right is multiplying by its transpose on the left. -/
lemma vecMul_eq_mulVec_transpose {α : Type*} [NonUnitalCommSemiring α] (A : Matrix n n α)
    (v : n → α) : v ᵥ* A = Aᵀ *ᵥ v :=
  (A.mulVec_transpose v).symm

/-- Dot products are monotone in the right argument along a nonnegative left argument. -/
lemma dotProduct_le_dotProduct_of_nonneg_left' {R n : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] [Fintype n] {u x y : n → R} (hu_nonneg : ∀ i, 0 ≤ u i) (h_le : x ≤ y) :
    u ⬝ᵥ x ≤ u ⬝ᵥ y :=
  dotProduct_le_dotProduct_of_nonneg_left h_le hu_nonneg

/-- A nonnegative vector whose dot product with a strictly positive vector vanishes is zero. -/
lemma eq_zero_of_nonneg_of_dotProduct_eq_zero {R n : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] [NoZeroDivisors R] [Fintype n] {u z : n → R} (hu_pos : ∀ i, 0 < u i)
    (hz_nonneg : ∀ i, 0 ≤ z i) (h_dot : u ⬝ᵥ z = 0) : z = 0 :=
  funext fun i => (mul_eq_zero.mp (congr_fun ((Fintype.sum_eq_zero_iff_of_nonneg fun j =>
    mul_nonneg (hu_pos j).le (hz_nonneg j)).mp h_dot) i)).resolve_left (hu_pos i).ne'

/-- A scalar in the spectrum of an endomorphism of a finite-dimensional space admits an
eigenvector. -/
lemma Module.End.exists_eigenvector_of_mem_spectrum {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {f : V →ₗ[K] V} {μ : K} (h_is_eigenvalue : μ ∈ spectrum K f) :
    ∃ v, v ≠ 0 ∧ f v = μ • v :=
  (End.HasEigenvalue.of_mem_spectrum h_is_eigenvalue).exists_hasEigenvector.imp fun _ hv =>
    ⟨hv.2, End.mem_eigenspace_iff.1 hv.1⟩

/-- The spectral radius of `toLin' A` is bounded by the operator norm. -/
lemma spectralRadius_le_opNorm (A : Matrix n n ℝ) :
    spectralRadius ℝ (Matrix.toLin' A) ≤ ↑‖(Matrix.toLin' A).toContinuousLinearMap‖₊ :=
  iSup₂_le fun _ hμ => ENNReal.coe_le_coe.2 <|
    spectralRadius_le_nnnorm_of_mem_spectrum <| spectrum_toLin' A ▸ hμ

/-- The spectral radius of `toLin' A` is finite. -/
lemma spectralRadius_finite (A : Matrix n n ℝ) :
    spectralRadius ℝ (Matrix.toLin' A) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_opNorm A)

/-- The spectral radius of a row-stochastic matrix with non-negative entries is at most 1. -/
theorem spectralRadius_stochastic_le_one {A : Matrix n n ℝ}
    (h_stochastic : ∀ i, ∑ j, A i j = 1) (h_nonneg : ∀ i j, 0 ≤ A i j) :
    spectralRadius ℝ (Matrix.toLin' A) ≤ 1 :=
  (spectralRadius_le_opNorm A).trans <| ENNReal.coe_le_one_iff.2 <|
    ContinuousLinearMap.opNNNorm_le_bound _ 1 fun v => by
      simpa [← NNReal.coe_le_coe] using norm_mulVec_le_of_row_sum h_stochastic h_nonneg v

/-! ## Core Perron-Frobenius Theory -/

/-- Indices `i` with strictly positive entry `v i`. -/
noncomputable def supportFinset (v : n → ℝ) : Finset n :=
  Finset.univ.filter (fun i => v i > 0)

/-- Indices `i` with zero entry `v i`. -/
noncomputable def kernelFinset (v : n → ℝ) : Finset n :=
  Finset.univ.filter (fun i => v i = 0)

omit [DecidableEq n] in
/-- The support and the zero set of a vector are disjoint. -/
lemma disjoint_kernel_support {v : n → ℝ} :
    Disjoint (supportFinset v) (kernelFinset v) :=
  Finset.disjoint_filter.2 fun _ _ hi h0 => hi.ne' h0

omit [DecidableEq n] in
/-- A non-zero non-negative vector has non-empty support. -/
lemma support_nonempty_of_ne_zero {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    (supportFinset v).Nonempty :=
  let ⟨i, hi⟩ := Function.ne_iff.1 hv_ne_zero
  ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, (hv_nonneg i).lt_of_ne' hi⟩⟩

/-- If a finite sum of non-negative terms is positive, at least one term must be positive. -/
lemma exists_pos_of_sum_pos {ι : Type*} [Fintype ι] {f : ι → ℝ} (h_nonneg : ∀ i, 0 ≤ f i)
    (h_sum_pos : 0 < ∑ i, f i) : ∃ i, 0 < f i :=
  not_not.1 fun h => h_sum_pos.ne' <|
    Finset.sum_eq_zero fun i _ => le_antisymm (not_lt.1 fun hi => h ⟨i, hi⟩) (h_nonneg i)

/-- For a non-negative `a`, `a * b` is positive iff both `a` and `b` are positive. -/
lemma mul_pos_iff_of_nonneg_left {a b : ℝ} (ha_nonneg : 0 ≤ a) :
    0 < a * b ↔ 0 < a ∧ 0 < b :=
  mul_pos_iff.trans <| or_iff_left fun h => absurd h.1 (not_lt.2 ha_nonneg)

/-- If a scalar `μ` is an eigenvalue of a matrix `A`, then it is a root of its
characteristic polynomial. -/
lemma isRoot_of_hasEigenvalue {A : Matrix n n ℝ} {μ : ℝ}
    (h_eig : Module.End.HasEigenvalue (toLin' A) μ) : (charpoly A).IsRoot μ :=
  mem_spectrum_iff_isRoot_charpoly.1 <| spectrum_toLin' A ▸ h_eig.mem_spectrum

/-- If `v` is an eigenvector of `f` for `μ`, then `μ` belongs to the spectrum of `f`. -/
lemma Module.End.mem_spectrum_of_hasEigenvector {K V : Type*} [CommRing K] [AddCommGroup V]
    [Module K V] {f : V →ₗ[K] V} {μ : K} {v : V}
    (h : Module.End.HasEigenvector f μ v) : μ ∈ spectrum K f :=
  (End.hasEigenvalue_of_hasEigenvector h).mem_spectrum

end Matrix
