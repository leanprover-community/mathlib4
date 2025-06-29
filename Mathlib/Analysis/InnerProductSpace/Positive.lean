/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Positive operators

In this file we define when an operator in a Hilbert space is positive. We follow Bourbaki's choice
of requiring self adjointness in the definition.

## Main definitions

* `LinearMap.IsPositive` : a linear map is positive if it is self adjoint and
  `∀ x, 0 ≤ re ⟪T x, x⟫`.
* `ContinuousLinearMap.IsPositive` : a continuous linear map is positive if it is self adjoint and
  `∀ x, 0 ≤ re ⟪T x, x⟫`.

## Main statements

* `ContinuousLinearMap.IsPositive.conj_adjoint` : if `T : E →L[𝕜] E` is positive,
  then for any `S : E →L[𝕜] F`, `S ∘L T ∘L S†` is also positive.
* `ContinuousLinearMap.isPositive_iff_complex` : in a ***complex*** Hilbert space,
  checking that `⟪T x, x⟫` is a nonnegative real number for all `x` suffices to prove that
  `T` is positive.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

Positive operator
-/

open InnerProductSpace RCLike LinearMap ContinuousLinearMap

open scoped InnerProduct ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]

/-- A continuous linear endomorphism `T` of a Hilbert space is **positive** if it is self adjoint
  and `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
def IsPositive (T : E →L[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x

theorem IsPositive.isSelfAdjoint {T : E →L[𝕜] E} (hT : IsPositive T) : IsSelfAdjoint T :=
  hT.1

theorem IsPositive.inner_left_eq_inner_right {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    ⟪T x, x⟫ = ⟪x, T x⟫ := by
  rw [← adjoint_inner_left, hT.isSelfAdjoint.adjoint_eq]

theorem IsPositive.re_inner_nonneg_left {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ re ⟪T x, x⟫ :=
  hT.2 x

theorem IsPositive.re_inner_nonneg_right {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ re ⟪x, T x⟫ := by rw [inner_re_symm]; exact hT.re_inner_nonneg_left x

open ComplexOrder in
theorem isPositive_iff (T : E →L[𝕜] E) :
    IsPositive T ↔ IsSelfAdjoint T ∧ ∀ x, 0 ≤ ⟪T x, x⟫ := by
  simp_rw [IsPositive, and_congr_right_iff, ← RCLike.ofReal_nonneg (K := 𝕜), reApplyInnerSelf_apply]
  intro hT
  have := hT.isSymmetric.coe_re_inner_apply_self
  simp_all

open ComplexOrder in
theorem IsPositive.inner_nonneg_left {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ ⟪T x, x⟫ :=
  ((isPositive_iff T).mp hT).right x

open ComplexOrder in
theorem IsPositive.inner_nonneg_right {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ ⟪x, T x⟫ := by
  rw [← hT.inner_left_eq_inner_right]
  exact inner_nonneg_left hT x

@[simp]
theorem isPositive_zero : IsPositive (0 : E →L[𝕜] E) := by
  refine ⟨.zero _, fun x => ?_⟩
  simp [reApplyInnerSelf_apply]

@[simp]
theorem isPositive_one : IsPositive (1 : E →L[𝕜] E) :=
  ⟨.one _, fun _ => inner_self_nonneg⟩

@[simp]
theorem isPositive_natCast {n : ℕ} : IsPositive (n : E →L[𝕜] E) := by
  refine ⟨IsSelfAdjoint.natCast n, ?_⟩
  intro x
  simpa [reApplyInnerSelf_apply, ← Nat.cast_smul_eq_nsmul 𝕜, inner_smul_left] using
    mul_nonneg n.cast_nonneg' inner_self_nonneg

@[simp]
theorem isPositive_ofNat {n : ℕ} [n.AtLeastTwo] : IsPositive (ofNat(n) : E →L[𝕜] E) :=
  isPositive_natCast

@[aesop safe apply]
theorem IsPositive.add {T S : E →L[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
    (T + S).IsPositive := by
  refine ⟨hT.isSelfAdjoint.add hS.isSelfAdjoint, fun x => ?_⟩
  rw [reApplyInnerSelf, add_apply, inner_add_left, map_add]
  exact add_nonneg (hT.re_inner_nonneg_left x) (hS.re_inner_nonneg_left x)

open ComplexOrder in
theorem IsPositive.smul_of_zero_le {T : E →L[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 ≤ c) :
    (c • T).IsPositive := by
  have hc' : starRingEnd 𝕜 c = c := by
    simp [conj_eq_iff_im, ← (le_iff_re_im.mp hc).right]
  apply And.intro
  · exact IsSelfAdjoint.smul hc' hT.left
  · intro x
    rw [reApplyInnerSelf, smul_apply, inner_smul_left, hc', mul_re, conj_eq_iff_im.mp hc', zero_mul,
      sub_zero]
    exact mul_nonneg ((re_nonneg_of_nonneg hc').mpr hc) (re_inner_nonneg_left hT x)

@[aesop safe apply]
theorem IsPositive.conj_adjoint {T : E →L[𝕜] E} (hT : T.IsPositive) (S : E →L[𝕜] F) :
    (S ∘L T ∘L S†).IsPositive := by
  refine ⟨hT.isSelfAdjoint.conj_adjoint S, fun x => ?_⟩
  rw [reApplyInnerSelf, comp_apply, ← adjoint_inner_right]
  exact hT.re_inner_nonneg_left _

@[aesop safe apply]
theorem IsPositive.adjoint_conj {T : E →L[𝕜] E} (hT : T.IsPositive) (S : F →L[𝕜] E) :
    (S† ∘L T ∘L S).IsPositive := by
  convert hT.conj_adjoint (S†)
  rw [adjoint_adjoint]

theorem IsPositive.conj_orthogonalProjection (U : Submodule 𝕜 E) {T : E →L[𝕜] E} (hT : T.IsPositive)
    [CompleteSpace U] :
    (U.subtypeL ∘L
        U.orthogonalProjection ∘L T ∘L U.subtypeL ∘L U.orthogonalProjection).IsPositive := by
  have := hT.conj_adjoint (U.subtypeL ∘L U.orthogonalProjection)
  rwa [(orthogonalProjection_isSelfAdjoint U).adjoint_eq] at this

theorem IsPositive.orthogonalProjection_comp {T : E →L[𝕜] E} (hT : T.IsPositive) (U : Submodule 𝕜 E)
    [CompleteSpace U] : (U.orthogonalProjection ∘L T ∘L U.subtypeL).IsPositive := by
  have := hT.conj_adjoint (U.orthogonalProjection : E →L[𝕜] U)
  rwa [U.adjoint_orthogonalProjection] at this

open scoped NNReal

lemma antilipschitz_of_forall_le_inner_map {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (f : H →L[𝕜] H) {c : ℝ≥0} (hc : 0 < c)
    (h : ∀ x, ‖x‖ ^ 2 * c ≤ ‖⟪f x, x⟫_𝕜‖) : AntilipschitzWith c⁻¹ f := by
  refine f.antilipschitz_of_bound (K := c⁻¹) fun x ↦ ?_
  rw [NNReal.coe_inv, inv_mul_eq_div, le_div_iff₀ (by exact_mod_cast hc)]
  simp_rw [sq, mul_assoc] at h
  by_cases hx0 : x = 0
  · simp [hx0]
  · apply (map_le_map_iff <| OrderIso.mulLeft₀ ‖x‖ (norm_pos_iff.mpr hx0)).mp
    exact (h x).trans <| (norm_inner_le_norm _ _).trans <| (mul_comm _ _).le

lemma isUnit_of_forall_le_norm_inner_map (f : E →L[𝕜] E) {c : ℝ≥0} (hc : 0 < c)
    (h : ∀ x, ‖x‖ ^ 2 * c ≤ ‖⟪f x, x⟫_𝕜‖) : IsUnit f := by
  rw [isUnit_iff_bijective, bijective_iff_dense_range_and_antilipschitz]
  have h_anti : AntilipschitzWith c⁻¹ f := antilipschitz_of_forall_le_inner_map f hc h
  refine ⟨?_, ⟨_, h_anti⟩⟩
  have _inst := h_anti.completeSpace_range_clm
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro x hx
  have : ‖x‖ ^ 2 * c = 0 := le_antisymm (by simpa only [hx (f x) ⟨x, rfl⟩, norm_zero] using h x)
    (by positivity)
  aesop

section Complex

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

theorem isPositive_iff_complex (T : E' →L[ℂ] E') :
    IsPositive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ := by
  simp_rw [IsPositive, forall_and, isSelfAdjoint_iff_isSymmetric,
    LinearMap.isSymmetric_iff_inner_map_self_real, conj_eq_iff_re]
  rfl

end Complex

section PartialOrder

/-- The (Loewner) partial order on continuous linear maps on a Hilbert space determined by
`f ≤ g` if and only if `g - f` is a positive linear map (in the sense of
`ContinuousLinearMap.IsPositive`). With this partial order, the continuous linear maps form a
`StarOrderedRing`. -/
instance instLoewnerPartialOrder : PartialOrder (E →L[𝕜] E) where
  le f g := (g - f).IsPositive
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm f₁ f₂ h₁ h₂ := by
    rw [← sub_eq_zero]
    have h_isSymm := isSelfAdjoint_iff_isSymmetric.mp <| IsPositive.isSelfAdjoint h₂
    exact_mod_cast h_isSymm.inner_map_self_eq_zero.mp fun x ↦ by
      open scoped ComplexOrder in
      refine le_antisymm ?_ (h₂.inner_nonneg_left x)
      rw [← neg_nonneg, ← inner_neg_left]
      simpa using h₁.inner_nonneg_left x

lemma le_def (f g : E →L[𝕜] E) : f ≤ g ↔ (g - f).IsPositive := Iff.rfl

lemma nonneg_iff_isPositive (f : E →L[𝕜] E) : 0 ≤ f ↔ f.IsPositive := by
  simpa using le_def 0 f

end PartialOrder

end ContinuousLinearMap

namespace LinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- A linear map `T` of a Hilbert space is **positive** if it is self adjoint and
  `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
def IsPositive (T : E →ₗ[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, 0 ≤ re ⟪T x, x⟫

theorem IsPositive.isSelfAdjoint {T : E →ₗ[𝕜] E} (hT : IsPositive T) :
    IsSelfAdjoint T := hT.1

theorem IsPositive.re_inner_nonneg_left {T : E →ₗ[𝕜] E} (hT : IsPositive T)
    (x : E) : 0 ≤ re ⟪T x, x⟫ :=
  hT.2 x

theorem IsPositive.re_inner_nonneg_right {T : E →ₗ[𝕜] E} (hT : IsPositive T)
    (x : E) : 0 ≤ re ⟪x, T x⟫ := by
  rw [inner_re_symm]
  exact hT.re_inner_nonneg_left x

lemma isPositive_toContinuousLinearMap_iff [CompleteSpace E] (T : E →ₗ[𝕜] E) :
    T.toContinuousLinearMap.IsPositive ↔ T.IsPositive := by
  simp [ContinuousLinearMap.IsPositive, IsPositive, isSelfAdjoint_toContinuousLinearMap_iff T,
    ContinuousLinearMap.reApplyInnerSelf]

lemma _root_.ContinuousLinearMap.isPositive_toLinearMap_iff [CompleteSpace E] (T : E →L[𝕜] E) :
    (T : E →ₗ[𝕜] E).IsPositive ↔ T.IsPositive := by
  simp [ContinuousLinearMap.IsPositive, IsPositive, isSelfAdjoint_toLinearMap_iff T,
    ContinuousLinearMap.reApplyInnerSelf]

section Complex

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']

theorem isPositive_iff_complex (T : E' →ₗ[ℂ] E') :
    IsPositive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ := by
  simp_rw [IsPositive, forall_and, ← isSymmetric_iff_isSelfAdjoint,
    LinearMap.isSymmetric_iff_inner_map_self_real, conj_eq_iff_re, re_to_complex,
    Complex.coe_algebraMap]

end Complex

theorem IsPositive.isSymmetric {T : E →ₗ[𝕜] E} (hT : IsPositive T) :
    IsSymmetric T := (isSymmetric_iff_isSelfAdjoint T).mpr hT.isSelfAdjoint

open ComplexOrder in
theorem isPositive_iff (T : E →ₗ[𝕜] E) :
    IsPositive T ↔ IsSelfAdjoint T ∧ ∀ x, 0 ≤ ⟪T x, x⟫ := by
  simp_rw [IsPositive, and_congr_right_iff, ← RCLike.ofReal_nonneg (K := 𝕜)]
  intro hT
  simp [isSymmetric_iff_isSelfAdjoint _ |>.mpr hT]

open ComplexOrder in
theorem IsPositive.inner_nonneg_left {T : E →ₗ[𝕜] E} (hT : IsPositive T) (x : E) : 0 ≤ ⟪T x, x⟫ :=
  ((isPositive_iff T).mp hT).right x

open ComplexOrder in
theorem IsPositive.inner_nonneg_right {T : E →ₗ[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ ⟪x, T x⟫ := by
  rw [← hT.isSymmetric]
  exact hT.inner_nonneg_left x

@[simp]
theorem isPositive_zero : IsPositive (0 : E →ₗ[𝕜] E) := ⟨.zero _, by simp⟩

@[simp]
theorem isPositive_one : IsPositive (1 : E →ₗ[𝕜] E) := ⟨.one _, fun _ => inner_self_nonneg⟩

@[simp]
theorem isPositive_natCast {n : ℕ} : IsPositive (n : E →ₗ[𝕜] E) := by
  refine ⟨IsSelfAdjoint.natCast n, ?_⟩
  intro x
  simp only [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul 𝕜, inner_smul_left, map_natCast,
    mul_re, natCast_re, inner_self_im, mul_zero, sub_zero]
  exact mul_nonneg n.cast_nonneg' inner_self_nonneg

@[simp]
theorem isPositive_ofNat {n : ℕ} [n.AtLeastTwo] : IsPositive (ofNat(n) : E →ₗ[𝕜] E) :=
  isPositive_natCast

@[aesop safe apply]
theorem IsPositive.add {T S : E →ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
    (T + S).IsPositive := by
  refine ⟨hT.isSelfAdjoint.add hS.isSelfAdjoint, fun x => ?_⟩
  rw [add_apply, inner_add_left, map_add]
  exact add_nonneg (hT.re_inner_nonneg_left x) (hS.re_inner_nonneg_left x)

open ComplexOrder in
theorem IsPositive.smul_of_zero_le {T : E →ₗ[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 ≤ c) :
    (c • T).IsPositive := by
  have hc' : starRingEnd 𝕜 c = c := by
    simp [conj_eq_iff_im, ← (le_iff_re_im.mp hc).right]
  apply And.intro
  · exact IsSelfAdjoint.smul hc' hT.left
  · intro x
    rw [smul_apply, inner_smul_left, hc', mul_re, conj_eq_iff_im.mp hc', zero_mul, sub_zero]
    exact mul_nonneg ((re_nonneg_of_nonneg hc').mpr hc) (re_inner_nonneg_left hT x)

@[aesop safe apply]
theorem IsPositive.conj_adjoint {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (S : E →ₗ[𝕜] F) :
    (S ∘ₗ T ∘ₗ S.adjoint).IsPositive := by
  refine And.intro ?_ ?_
  · rw [isSelfAdjoint_iff', adjoint_comp, adjoint_comp, adjoint_adjoint, ← star_eq_adjoint, hT.1,
      comp_assoc]
  · intro x
    rw [comp_apply, ← adjoint_inner_right]
    exact hT.re_inner_nonneg_left _

@[aesop safe apply]
theorem IsPositive.adjoint_conj {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (S : F →ₗ[𝕜] E) :
    (S.adjoint ∘ₗ T ∘ₗ S).IsPositive := by
  convert hT.conj_adjoint S.adjoint
  rw [adjoint_adjoint]

theorem IsPositive.nonneg_eigenvalues {T : E →ₗ[𝕜] E} {n : ℕ} (hT : T.IsPositive)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) : 0 ≤ hT.isSymmetric.eigenvalues hn i := by
  have h := hT.right (hT.isSymmetric.eigenvectorBasis hn i)
  rw [hT.isSymmetric.apply_eigenvectorBasis, inner_smul_real_left, RCLike.smul_re,
    inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow, mul_one] at h
  exact h

section PartialOrder

/-- The (Loewner) partial order on linear maps on a Hilbert space determined by `f ≤ g`
if and only if `g - f` is a positive linear map (in the sense of `LinearMap.IsPositive`). -/
instance instLoewnerPartialOrder : PartialOrder (E →ₗ[𝕜] E) where
  le f g := (g - f).IsPositive
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm f₁ f₂ h₁ h₂ := by
    rw [← sub_eq_zero]
    have h_isSymm := (isSymmetric_iff_isSelfAdjoint (f₁ - f₂)).mpr h₂.isSelfAdjoint
    exact h_isSymm.inner_map_self_eq_zero.mp fun x ↦ by
      open scoped ComplexOrder in
      refine le_antisymm ?_ (h₂.inner_nonneg_left x)
      rw [← neg_nonneg, ← inner_neg_left]
      simpa using h₁.inner_nonneg_left x

lemma le_def (f g : E →ₗ[𝕜] E) : f ≤ g ↔ (g - f).IsPositive := Iff.rfl

lemma nonneg_iff_isPositive (f : E →ₗ[𝕜] E) : 0 ≤ f ↔ f.IsPositive := by
  simpa using le_def 0 f

end PartialOrder

end LinearMap
