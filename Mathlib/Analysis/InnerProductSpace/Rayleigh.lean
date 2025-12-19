/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis, Wanli Ma,Yunfei Zhang
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.EuclideanDomain.Basic

/-!
# The Rayleigh quotient

The Rayleigh quotient of a self-adjoint operator `T` on an inner product space `E` is the function
`fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2`.

The main results of this file are `IsSelfAdjoint.hasEigenvector_of_isMaxOn` and
`IsSelfAdjoint.hasEigenvector_of_isMinOn`, which state that if `E` is complete, and if the
Rayleigh quotient attains its global maximum/minimum over some sphere at the point `x₀`, then `x₀`
is an eigenvector of `T`, and the `iSup`/`iInf` of `fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2` is the corresponding
eigenvalue.

The corollaries `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and
`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` state that if `E` is
finite-dimensional and nontrivial, then `T` has some (nonzero) eigenvectors with eigenvalue the
`iSup`/`iInf` of `fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2`.

## TODO

A slightly more elaborate corollary is that if `E` is complete and `T` is a compact operator, then
`T` has some (nonzero) eigenvector with eigenvalue either `⨆ x, ⟪T x, x⟫ / ‖x‖ ^ 2` or
`⨅ x, ⟪T x, x⟫ / ‖x‖ ^ 2` (not necessarily both).

-/

@[expose] public section


variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped NNReal

open Module.End Metric

namespace ContinuousLinearMap

variable (T : E →L[𝕜] E)

/-- The *Rayleigh quotient* of a continuous linear map `T` (over `ℝ` or `ℂ`) at a vector `x` is
the quantity `re ⟪T x, x⟫ / ‖x‖ ^ 2`. -/
noncomputable abbrev rayleighQuotient (x : E) := T.reApplyInnerSelf x / ‖(x : E)‖ ^ 2

theorem rayleigh_smul (x : E) {c : 𝕜} (hc : c ≠ 0) :
    rayleighQuotient T (c • x) = rayleighQuotient T x := by
  by_cases hx : x = 0
  · simp [hx]
  simp [field, norm_smul, T.reApplyInnerSelf_smul]

theorem image_rayleigh_eq_image_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
    rayleighQuotient T '' {0}ᶜ = rayleighQuotient T '' sphere 0 r := by
  ext a
  constructor
  · rintro ⟨x, hx : x ≠ 0, hxT⟩
    let c : 𝕜 := ↑‖x‖⁻¹ * r
    have : c ≠ 0 := by simp [c, hx, hr.ne']
    refine ⟨c • x, ?_, ?_⟩
    · simp [field, c, norm_smul, abs_of_pos hr]
    · rw [T.rayleigh_smul x this]
      exact hxT
  · rintro ⟨x, hx, hxT⟩
    exact ⟨x, ne_zero_of_mem_sphere hr.ne' ⟨x, hx⟩, hxT⟩

theorem iSup_rayleigh_eq_iSup_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
    ⨆ x : { x : E // x ≠ 0 }, rayleighQuotient T x =
      ⨆ x : sphere (0 : E) r, rayleighQuotient T x :=
  show ⨆ x : ({0}ᶜ : Set E), rayleighQuotient T x = _ by
    simp only [← @sSup_image' _ _ _ _ (rayleighQuotient T),
      T.image_rayleigh_eq_image_rayleigh_sphere hr]

theorem iInf_rayleigh_eq_iInf_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
    ⨅ x : { x : E // x ≠ 0 }, rayleighQuotient T x =
      ⨅ x : sphere (0 : E) r, rayleighQuotient T x :=
  show ⨅ x : ({0}ᶜ : Set E), rayleighQuotient T x = _ by
    simp only [← @sInf_image' _ _ _ _ (rayleighQuotient T),
      T.image_rayleigh_eq_image_rayleigh_sphere hr]

section RayleighGeneral

variable {x : E} {T : E →L[𝕜] E}

/-!
### General lemmas
theorem
`ContinuousLinearMap.rayleighQuotient_mem_Icc_of_mem_span_orthonormal_eigenvectors`:
For a continuous linear operator `T` with an orthonormal family of eigenvectors
`v j` with real eigenvalues `u j`, the Rayleigh quotient of a unit vector in the span
of `{v j | j ∈ s}` lies between the minimum and maximum eigenvalues `u j` for `j ∈ s`.

theorem
`ContinuousLinearMap.rayleighQuotient_mem_Icc_of_mem_span_orthonormal_eigenvectors_nonzero`:
Non-normalized version of the above.
-/

/-- The Rayleigh quotient is additive in the operator: the Rayleigh quotient of the sum of two
operators equals the sum of their individual Rayleigh quotients. This property is useful for
decomposing operators into simpler components. -/
@[simp]
theorem rayleighQuotient_add {S : E →L[𝕜] E} :
    (T + S).rayleighQuotient x = T.rayleighQuotient x + S.rayleighQuotient x := by
  simp [rayleighQuotient, reApplyInnerSelf_apply, inner_add_left, add_div]


variable {ι : Type*} {v : ι → E} {u : ι → ℝ} {s : Finset ι}


/-- Rayleigh quotient expressed using coefficients in an orthonormal eigenbasis.
If `v` is an orthonormal family of eigenvectors of a continuous linear operator `T` with
real eigenvalues `u`, and `x` is a linear combination of `v j` for `j ∈ s` with coefficients
`c j`, then the Rayleigh quotient of `x` is the weighted average of the corresponding
eigenvalues with weights `‖c j‖²`. -/
lemma rayleighQuotient_eq_sum_sqNorm_mul_eigenvalues {c : s → 𝕜} (hv : Orthonormal 𝕜 v)
    (h_eigen : ∀ j : ι, T (v j) = (u j : 𝕜) • v j) (hx : x = ∑ j, c j • v j) :
    T.rayleighQuotient x = (∑ j, ‖c j‖ ^ 2 * u j) / ‖x‖ ^ 2 := by
  have hv' : Orthonormal 𝕜 (fun j : s => v j) :=
    ⟨fun j => hv.1 j, fun i j hij => hv.2 (Subtype.coe_ne_coe.mpr hij)⟩
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, hx]
  congr 1
  simp only [map_sum, map_smul, h_eigen, smul_smul, Orthonormal.inner_sum hv']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mul, RCLike.conj_ofReal, mul_right_comm, mul_comm (starRingEnd 𝕜 (c i)),
    RCLike.mul_conj]
  simp


variable [LinearOrder ι]


/-- **Rayleigh quotient bounds for a unit vector** in the span of an orthonormal family
of eigenvectors, indexed by a finite set.
Assume the eigenvalues `u` are indexed in nonincreasing order with respect to the index
(order-preserving indices correspond to nonincreasing eigenvalues). For a unit vector in
the span of `{v j | j ∈ s}`, its Rayleigh quotient lies between the minimal and maximal
eigenvalues among `u j` for `j ∈ s`. -/
theorem rayleighQuotient_mem_Icc_of_mem_span_orthonormal_eigenvectors
    (hv : Orthonormal 𝕜 v)
    (h_eigen : ∀ j : ι, T (v j) = (u j : 𝕜) • v j)
    (hs : s.Nonempty) (h_norm : ‖x‖ = 1)
    (h_in_span : x ∈ Submodule.span 𝕜 (Set.range fun j : s => v j))
    (h_sorted : Antitone u) :
    u (s.max' hs) ≤ T.rayleighQuotient x ∧
    T.rayleighQuotient x ≤ u (s.min' hs) := by
  have ⟨c, hc⟩ : ∃ (c : s → 𝕜), x = ∑ j, c j • v j := by
    rw [Submodule.mem_span_range_iff_exists_fun] at h_in_span
    exact ⟨h_in_span.choose, h_in_span.choose_spec.symm⟩
  have hv' : Orthonormal 𝕜 (fun j : s => v j) :=
    ⟨fun j => hv.1 j, fun i j hij => hv.2 (Subtype.coe_ne_coe.mpr hij)⟩
  have hsum : ∑ j, ‖c j‖ ^ 2 = 1 := by
    have : OrthogonalFamily 𝕜 (fun _ : s => 𝕜)
        (fun j : s => LinearIsometry.toSpanSingleton 𝕜 E (hv'.1 j)) := by
      intro i j hij v w
      simp only [LinearIsometry.toSpanSingleton_apply, inner_smul_left, inner_smul_right,
        hv'.2 hij, mul_zero]
    have parseval := OrthogonalFamily.norm_sum this c  (Finset.univ : Finset s)
    simp only [LinearIsometry.toSpanSingleton_apply, Finset.univ_eq_attach] at parseval
    calc ∑ j, ‖c j‖ ^ 2
        = ‖∑ j, c j • v j‖ ^ 2 := parseval.symm
      _ = ‖x‖ ^ 2 := by rw [hc]
      _ = 1 := by rw [h_norm]; ring
  rw [rayleighQuotient_eq_sum_sqNorm_mul_eigenvalues hv h_eigen hc]
  simp only [h_norm, one_pow, div_one]
  constructor
  · calc u (s.max' hs) = u (s.max' hs) * ∑ j : s, ‖c j‖ ^ 2 := by rw [hsum]; ring
      _ = ∑ j : s, u (s.max' hs) * ‖c j‖ ^ 2 := by rw [← Finset.mul_sum]
      _ ≤ ∑ j : s, u ↑j * ‖c j‖ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_right
            (h_sorted (Finset.le_max' s (↑j) j.2)) (sq_nonneg _)
      _ = ∑ j : s, ‖c j‖ ^ 2 * u ↑j := by
          refine Finset.sum_congr rfl fun j _ => mul_comm _ _
  · calc ∑ j : s, ‖c j‖ ^ 2 * u ↑j
        = ∑ j : s, u ↑j * ‖c j‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ ≤ ∑ j : s, u (s.min' hs) * ‖c j‖ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_right
            (h_sorted (Finset.min'_le s (↑j) j.2)) (sq_nonneg _)
      _ = u (s.min' hs) * ∑ j : s, ‖c j‖ ^ 2 := by rw [← Finset.mul_sum]
      _ = u (s.min' hs) := by rw [hsum]; ring


/-- **Rayleigh quotient bounds for a nonzero vector** in the span of an orthonormal family
of eigenvectors, indexed by a finite set.
This is the non-normalized version of
`ContinuousLinearMap.rayleighQuotient_mem_Icc_of_mem_span_orthonormal_eigenvectors`, obtained by
normalizing the vector and using the fact that the Rayleigh quotient is invariant
under nonzero scalar multiples. -/
theorem rayleighQuotient_mem_Icc_of_mem_span_orthonormal_eigenvectors_nonzero
    (hv : Orthonormal 𝕜 v)
    (h_eigen : ∀ j : ι, T (v j) = (u j : 𝕜) • v j)
    (hs : s.Nonempty) (h_nz : x ≠ 0)
    (h_in_span : x ∈ Submodule.span 𝕜 (Set.range fun j : s => v j))
    (h_sorted : Antitone u) :
    u (s.max' hs) ≤ T.rayleighQuotient x ∧
    T.rayleighQuotient x ≤ u (s.min' hs) := by
  by_cases h_unit : ‖x‖ = 1
  · exact rayleighQuotient_mem_Icc_of_mem_span_orthonormal_eigenvectors
        hv h_eigen  hs  h_unit h_in_span h_sorted
  · have h_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr h_nz
    set a : 𝕜 := ((‖x‖ : ℝ)⁻¹ : 𝕜) with ha
    set t := a • x with ht
    have h_t_norm : ‖t‖ = 1 := by
      rw [ht, norm_smul]; simp [ha, h_norm_pos.ne']
    have h_t_mem : t ∈ Submodule.span 𝕜 (Set.range fun j : s => v j) :=
      Submodule.smul_mem _ _ h_in_span
    have ha_ne : a ≠ 0 := by simp [ha, h_norm_pos.ne']
    rw [show T.rayleighQuotient x = T.rayleighQuotient t from
      (ht ▸ (ContinuousLinearMap.rayleigh_smul T x ha_ne).symm)]
    exact rayleighQuotient_mem_Icc_of_mem_span_orthonormal_eigenvectors
        hv h_eigen hs  h_t_norm h_t_mem h_sorted

end RayleighGeneral

end ContinuousLinearMap



namespace IsSelfAdjoint

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem _root_.LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf {T : F →L[ℝ] F}
    (hT : (T : F →ₗ[ℝ] F).IsSymmetric) (x₀ : F) :
    HasStrictFDerivAt T.reApplyInnerSelf (2 • (innerSL ℝ (T x₀))) x₀ := by
  convert T.hasStrictFDerivAt.inner ℝ (hasStrictFDerivAt_id x₀) using 1
  ext y
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, innerSL_apply_apply, id, ContinuousLinearMap.id_apply,
    hT.apply_clm x₀ y, real_inner_comm _ x₀, two_smul]

variable [CompleteSpace F] {T : F →L[ℝ] F}

theorem linearly_dependent_of_isLocalExtrOn (hT : IsSelfAdjoint T) {x₀ : F}
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : F) ‖x₀‖) x₀) :
    ∃ a b : ℝ, (a, b) ≠ 0 ∧ a • x₀ + b • T x₀ = 0 := by
  have H : IsLocalExtrOn T.reApplyInnerSelf {x : F | ‖x‖ ^ 2 = ‖x₀‖ ^ 2} x₀ := by
    convert hextr
    ext x
    simp
  -- find Lagrange multipliers for the function `T.re_apply_inner_self` and the
  -- hypersurface-defining function `fun x ↦ ‖x‖ ^ 2`
  obtain ⟨a, b, h₁, h₂⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d H (hasStrictFDerivAt_norm_sq x₀)
      (hT.isSymmetric.hasStrictFDerivAt_reApplyInnerSelf x₀)
  refine ⟨a, b, h₁, ?_⟩
  apply (InnerProductSpace.toDualMap ℝ F).injective
  simp only [LinearIsometry.map_add, LinearIsometry.map_zero]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
  simp only [map_smulₛₗ _, RCLike.conj_to_real]
  change a • innerSL ℝ x₀ + b • innerSL ℝ (T x₀) = 0
  apply smul_right_injective (F →L[ℝ] ℝ) (two_ne_zero : (2 : ℝ) ≠ 0)
  simpa only [two_smul, smul_add, add_smul, add_zero] using h₂

-- Non-terminal simp, used to be field_simp
set_option linter.flexible false in
open scoped InnerProductSpace in
theorem eq_smul_self_of_isLocalExtrOn_real (hT : IsSelfAdjoint T) {x₀ : F}
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : F) ‖x₀‖) x₀) :
    T x₀ = T.rayleighQuotient x₀ • x₀ := by
  obtain ⟨a, b, h₁, h₂⟩ := hT.linearly_dependent_of_isLocalExtrOn hextr
  by_cases hx₀ : x₀ = 0
  · simp [hx₀]
  by_cases hb : b = 0
  · have : a ≠ 0 := by simpa [hb] using h₁
    refine absurd ?_ hx₀
    apply smul_right_injective F this
    simpa [hb] using h₂
  have hc : T x₀ = (-b⁻¹ * a) • x₀ := by
    linear_combination (norm := match_scalars <;> field) b⁻¹ • h₂
  set c : ℝ := -b⁻¹ * a
  convert hc
  have := congr_arg (fun x => ⟪x, x₀⟫_ℝ) hc
  simp [field, inner_smul_left, mul_comm a] at this ⊢
  exact this

end Real

section CompleteSpace

variable [CompleteSpace E] {T : E →L[𝕜] E}

theorem eq_smul_self_of_isLocalExtrOn (hT : IsSelfAdjoint T) {x₀ : E}
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    T x₀ = (↑(T.rayleighQuotient x₀) : 𝕜) • x₀ := by
  letI := InnerProductSpace.rclikeToReal 𝕜 E
  let hSA := hT.isSymmetric.restrictScalars.toSelfAdjoint.prop
  exact hSA.eq_smul_self_of_isLocalExtrOn_real hextr

/-- For a self-adjoint operator `T`, a local extremum of the Rayleigh quotient of `T` on a sphere
centred at the origin is an eigenvector of `T`. -/
theorem hasEigenvector_of_isLocalExtrOn (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ ≠ 0)
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    HasEigenvector (T : E →ₗ[𝕜] E) (↑(T.rayleighQuotient x₀)) x₀ := by
  refine ⟨?_, hx₀⟩
  rw [Module.End.mem_eigenspace_iff]
  exact hT.eq_smul_self_of_isLocalExtrOn hextr

/-- For a self-adjoint operator `T`, a maximum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global supremum of the Rayleigh
quotient. -/
theorem hasEigenvector_of_isMaxOn (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ ≠ 0)
    (hextr : IsMaxOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    HasEigenvector (T : E →ₗ[𝕜] E) (↑(⨆ x : { x : E // x ≠ 0 }, T.rayleighQuotient x)) x₀ := by
  convert hT.hasEigenvector_of_isLocalExtrOn hx₀ (Or.inr hextr.localize)
  have hx₀' : 0 < ‖x₀‖ := by simp [hx₀]
  have hx₀'' : x₀ ∈ sphere (0 : E) ‖x₀‖ := by simp
  rw [T.iSup_rayleigh_eq_iSup_rayleigh_sphere hx₀']
  refine IsMaxOn.iSup_eq hx₀'' ?_
  intro x hx
  dsimp
  have : ‖x‖ = ‖x₀‖ := by simpa using hx
  simp only [ContinuousLinearMap.rayleighQuotient]
  rw [this]
  gcongr
  exact hextr hx

/-- For a self-adjoint operator `T`, a minimum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global infimum of the Rayleigh
quotient. -/
theorem hasEigenvector_of_isMinOn (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ ≠ 0)
    (hextr : IsMinOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    HasEigenvector (T : E →ₗ[𝕜] E) (↑(⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x)) x₀ := by
  convert hT.hasEigenvector_of_isLocalExtrOn hx₀ (Or.inl hextr.localize)
  have hx₀' : 0 < ‖x₀‖ := by simp [hx₀]
  have hx₀'' : x₀ ∈ sphere (0 : E) ‖x₀‖ := by simp
  rw [T.iInf_rayleigh_eq_iInf_rayleigh_sphere hx₀']
  refine IsMinOn.iInf_eq hx₀'' ?_
  intro x hx
  dsimp
  have : ‖x‖ = ‖x₀‖ := by simpa using hx
  simp only [ContinuousLinearMap.rayleighQuotient]
  rw [this]
  gcongr
  exact hextr hx

end CompleteSpace

end IsSelfAdjoint

section FiniteDimensional

variable [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}

namespace LinearMap

namespace IsSymmetric

/-- The supremum of the Rayleigh quotient of a symmetric operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
theorem hasEigenvalue_iSup_of_finiteDimensional [Nontrivial E] (hT : T.IsSymmetric) :
    HasEigenvalue T ↑(⨆ x : { x : E // x ≠ 0 }, RCLike.re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 : ℝ) := by
  haveI := FiniteDimensional.proper_rclike 𝕜 E
  let T' := hT.toSelfAdjoint
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
  have H₁ : IsCompact (sphere (0 : E) ‖x‖) := isCompact_sphere _ _
  have H₂ : (sphere (0 : E) ‖x‖).Nonempty := ⟨x, by simp⟩
  -- key point: in finite dimension, a continuous function on the sphere has a max
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_isMaxOn H₂ T'.val.reApplyInnerSelf_continuous.continuousOn
  have hx₀ : ‖x₀‖ = ‖x‖ := by simpa using hx₀'
  have : IsMaxOn T'.val.reApplyInnerSelf (sphere 0 ‖x₀‖) x₀ := by simpa only [← hx₀] using hTx₀
  have hx₀_ne : x₀ ≠ 0 := by
    have : ‖x₀‖ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, Ne, not_false_iff]
    simpa [← norm_eq_zero, Ne]
  exact hasEigenvalue_of_hasEigenvector (T'.prop.hasEigenvector_of_isMaxOn hx₀_ne this)

/-- The infimum of the Rayleigh quotient of a symmetric operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
theorem hasEigenvalue_iInf_of_finiteDimensional [Nontrivial E] (hT : T.IsSymmetric) :
    HasEigenvalue T ↑(⨅ x : { x : E // x ≠ 0 }, RCLike.re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 : ℝ) := by
  haveI := FiniteDimensional.proper_rclike 𝕜 E
  let T' := hT.toSelfAdjoint
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
  have H₁ : IsCompact (sphere (0 : E) ‖x‖) := isCompact_sphere _ _
  have H₂ : (sphere (0 : E) ‖x‖).Nonempty := ⟨x, by simp⟩
  -- key point: in finite dimension, a continuous function on the sphere has a min
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_isMinOn H₂ T'.val.reApplyInnerSelf_continuous.continuousOn
  have hx₀ : ‖x₀‖ = ‖x‖ := by simpa using hx₀'
  have : IsMinOn T'.val.reApplyInnerSelf (sphere 0 ‖x₀‖) x₀ := by simpa only [← hx₀] using hTx₀
  have hx₀_ne : x₀ ≠ 0 := by
    have : ‖x₀‖ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, Ne, not_false_iff]
    simpa [← norm_eq_zero, Ne]
  exact hasEigenvalue_of_hasEigenvector (T'.prop.hasEigenvector_of_isMinOn hx₀_ne this)

theorem subsingleton_of_no_eigenvalue_finiteDimensional (hT : T.IsSymmetric)
    (hT' : ∀ μ : 𝕜, Module.End.eigenspace (T : E →ₗ[𝕜] E) μ = ⊥) : Subsingleton E :=
  (subsingleton_or_nontrivial E).resolve_right fun _h =>
    absurd (hT' _) hT.hasEigenvalue_iSup_of_finiteDimensional

end IsSymmetric

end LinearMap

end FiniteDimensional
