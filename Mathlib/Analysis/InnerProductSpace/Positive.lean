/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive operators

In this file we define when an operator in a Hilbert space is positive. We follow Bourbaki's choice
of requiring self adjointness in the definition.

## Main definitions

* `LinearMap.IsPositive` : a linear map is positive if it is symmetric and
  `∀ x, 0 ≤ re ⟪T x, x⟫`.
* `ContinuousLinearMap.IsPositive` : a continuous linear map is positive if it is symmetric and
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

namespace LinearMap

/-- A linear operator `T` on a Hilbert space is **positive** if it is symmetric and
  `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
def IsPositive (T : E →ₗ[𝕜] E) : Prop :=
  IsSymmetric T ∧ ∀ x, 0 ≤ re ⟪T x, x⟫

theorem IsPositive.isSymmetric {T : E →ₗ[𝕜] E} (hT : IsPositive T) :
    IsSymmetric T := hT.1

theorem IsPositive.re_inner_nonneg_left {T : E →ₗ[𝕜] E} (hT : IsPositive T)
    (x : E) : 0 ≤ re ⟪T x, x⟫ :=
  hT.2 x

theorem IsPositive.re_inner_nonneg_right {T : E →ₗ[𝕜] E} (hT : IsPositive T)
    (x : E) : 0 ≤ re ⟪x, T x⟫ :=
  inner_re_symm (𝕜 := 𝕜) _ x ▸ hT.re_inner_nonneg_left x

section Complex

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']

theorem isPositive_iff_complex (T : E' →ₗ[ℂ] E') :
    IsPositive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ := by
  simp_rw [IsPositive, forall_and, isSymmetric_iff_inner_map_self_real,
    conj_eq_iff_re, re_to_complex, Complex.coe_algebraMap]

end Complex

theorem IsPositive.isSelfAdjoint [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : IsPositive T) :
    IsSelfAdjoint T := (isSymmetric_iff_isSelfAdjoint _).mp hT.isSymmetric

theorem IsPositive.adjoint_eq [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : IsPositive T) :
    T.adjoint = T := hT.isSelfAdjoint

open ComplexOrder in
theorem isPositive_iff (T : E →ₗ[𝕜] E) :
    IsPositive T ↔ IsSymmetric T ∧ ∀ x, 0 ≤ ⟪T x, x⟫ := by
  simp_rw [IsPositive, and_congr_right_iff, ← RCLike.ofReal_nonneg (K := 𝕜)]
  intro hT
  simp [hT]

open ComplexOrder in
theorem IsPositive.inner_nonneg_left {T : E →ₗ[𝕜] E} (hT : IsPositive T) (x : E) : 0 ≤ ⟪T x, x⟫ :=
  (T.isPositive_iff.mp hT).right x

open ComplexOrder in
theorem IsPositive.inner_nonneg_right {T : E →ₗ[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ ⟪x, T x⟫ :=
  hT.isSymmetric _ _ ▸ hT.inner_nonneg_left x

@[simp]
theorem isPositive_zero : IsPositive (0 : E →ₗ[𝕜] E) := ⟨.zero, by simp⟩

@[simp]
theorem isPositive_one : IsPositive (1 : E →ₗ[𝕜] E) := ⟨.id, fun _ => inner_self_nonneg⟩

@[simp]
theorem isPositive_id : IsPositive (id : E →ₗ[𝕜] E) := isPositive_one

@[simp]
theorem isPositive_natCast {n : ℕ} : IsPositive (n : E →ₗ[𝕜] E) := by
  refine ⟨IsSymmetric.natCast n, fun x => ?_⟩
  simp only [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul 𝕜, inner_smul_left, map_natCast,
    mul_re, natCast_re, inner_self_im, mul_zero, sub_zero]
  exact mul_nonneg n.cast_nonneg' inner_self_nonneg

@[simp]
theorem isPositive_ofNat {n : ℕ} [n.AtLeastTwo] : IsPositive (ofNat(n) : E →ₗ[𝕜] E) :=
  isPositive_natCast

@[aesop safe apply]
theorem IsPositive.add {T S : E →ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
    (T + S).IsPositive := by
  refine ⟨hT.isSymmetric.add hS.isSymmetric, fun x => ?_⟩
  rw [add_apply, inner_add_left, map_add]
  exact add_nonneg (hT.re_inner_nonneg_left x) (hS.re_inner_nonneg_left x)

open ComplexOrder in
@[aesop safe apply]
theorem IsPositive.smul_of_nonneg {T : E →ₗ[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 ≤ c) :
    (c • T).IsPositive := by
  have hc' : starRingEnd 𝕜 c = c := by
    simp [conj_eq_iff_im, ← (le_iff_re_im.mp hc).right]
  refine ⟨hT.left.smul hc', fun x => ?_⟩
  rw [smul_apply, inner_smul_left, hc', mul_re, conj_eq_iff_im.mp hc', zero_mul, sub_zero]
  exact mul_nonneg ((re_nonneg_of_nonneg hc').mpr hc) (re_inner_nonneg_left hT x)

theorem IsPositive.nonneg_eigenvalues [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} {n : ℕ} (hT : T.IsPositive)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) : 0 ≤ hT.isSymmetric.eigenvalues hn i := by
  simpa only [hT.isSymmetric.apply_eigenvectorBasis, inner_smul_real_left, RCLike.smul_re,
    inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow, mul_one]
      using hT.right (hT.isSymmetric.eigenvectorBasis hn i)

section PartialOrder

/-- The (Loewner) partial order on linear maps on a Hilbert space determined by `f ≤ g`
if and only if `g - f` is a positive linear map (in the sense of `LinearMap.IsPositive`). -/
instance instLoewnerPartialOrder : PartialOrder (E →ₗ[𝕜] E) where
  le f g := (g - f).IsPositive
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm f₁ f₂ h₁ h₂ := by
    rw [← sub_eq_zero, ← h₂.isSymmetric.inner_map_self_eq_zero]
    intro x
    have hba2 := h₁.2 x
    rw [← neg_le_neg_iff, ← map_neg, ← inner_neg_left, ← neg_apply, neg_sub, neg_zero] at hba2
    rw [← h₂.isSymmetric.coe_re_inner_apply_self, RCLike.ofReal_eq_zero]
    exact le_antisymm hba2 (h₂.2 _)

lemma le_def (f g : E →ₗ[𝕜] E) : f ≤ g ↔ (g - f).IsPositive := Iff.rfl

lemma nonneg_iff_isPositive (f : E →ₗ[𝕜] E) : 0 ≤ f ↔ f.IsPositive := by
  simpa using le_def 0 f

end PartialOrder

/-- An idempotent linear map is positive iff it is symmetric. -/
theorem IsIdempotentElem.isPositive_iff_isSymmetric {T : E →ₗ[𝕜] E} (hT : IsIdempotentElem T) :
    T.IsPositive ↔ T.IsSymmetric := by
  refine ⟨fun h => h.isSymmetric, fun h => ⟨h, fun x => ?_⟩⟩
  rw [← hT.eq, Module.End.mul_apply, h]
  exact inner_self_nonneg

theorem isPositive_linearIsometryEquiv_conj_iff {T : E →ₗ[𝕜] E} (f : E ≃ₗᵢ[𝕜] F) :
    IsPositive (f.toLinearMap ∘ₗ T ∘ₗ f.symm.toLinearMap) ↔ IsPositive T := by
  simp_rw [IsPositive, isSymmetric_linearIsometryEquiv_conj_iff, and_congr_right_iff,
    LinearIsometryEquiv.toLinearEquiv_symm, coe_comp, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.coe_symm_toLinearEquiv,
    Function.comp_apply, LinearIsometryEquiv.inner_map_eq_flip]
  exact fun _ => ⟨fun h x => by simpa using h (f x), fun h x => h _⟩

open scoped ComplexOrder in
/-- `A.toEuclideanLin` is positive if and only if `A` is positive semi-definite. -/
@[simp] theorem _root_.Matrix.isPositive_toEuclideanLin_iff {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} : A.toEuclideanLin.IsPositive ↔ A.PosSemidef := by
  simp_rw [LinearMap.IsPositive, ← Matrix.isHermitian_iff_isSymmetric, inner_re_symm,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply,
    dotProduct_comm (A.mulVec _), Matrix.PosSemidef, and_congr_right_iff,
    RCLike.nonneg_iff (K := 𝕜)]
  refine fun hA ↦ (EuclideanSpace.equiv n 𝕜).forall_congr' fun x ↦ ?_
  simp [hA.im_star_dotProduct_mulVec_self]

open ComplexOrder in
/-- `A.toMatrix` is positive semi-definite if and only if `A` is positive. -/
@[simp] theorem posSemidef_toMatrix_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : E →ₗ[𝕜] E} (b : OrthonormalBasis ι 𝕜 E) :
    (A.toMatrix b.toBasis b.toBasis).PosSemidef ↔ A.IsPositive := by
  rw [← Matrix.isPositive_toEuclideanLin_iff, (by exact Matrix.toLin'_toMatrix' _ :
    (A.toMatrix b.toBasis b.toBasis).toEuclideanLin =
      b.repr.toLinearMap ∘ₗ A ∘ₗ b.repr.symm.toLinearMap), isPositive_linearIsometryEquiv_conj_iff]

/-- A symmetric projection is positive. -/
@[aesop 10% apply, grind →]
theorem IsPositive.of_isSymmetricProjection {p : E →ₗ[𝕜] E} (hp : p.IsSymmetricProjection) :
    p.IsPositive :=
  hp.isIdempotentElem.isPositive_iff_isSymmetric.mpr hp.isSymmetric

/-- A star projection operator is positive. -/
@[deprecated (since := "19-08-2025")]
alias IsPositive.of_isStarProjection := IsPositive.of_isSymmetricProjection

end LinearMap

namespace ContinuousLinearMap

/-- A continuous linear endomorphism `T` of a Hilbert space is **positive** if it is symmetric
  and `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
def IsPositive (T : E →L[𝕜] E) : Prop :=
  T.IsSymmetric ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x

theorem isPositive_def {T : E →L[𝕜] E} :
    T.IsPositive ↔ T.IsSymmetric ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x := Iff.rfl

/-- In a complete space, a continuous linear endomorphism `T` is **positive** if it is
symmetric and `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
theorem isPositive_def' [CompleteSpace E] {T : E →L[𝕜] E} :
    T.IsPositive ↔ IsSelfAdjoint T ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x := by
  simp [IsPositive, isSelfAdjoint_iff_isSymmetric, LinearMap.IsSymmetric]

theorem IsPositive.isSymmetric {T : E →L[𝕜] E} (hT : T.IsPositive) :
    T.IsSymmetric := hT.1

theorem IsPositive.isSelfAdjoint [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsPositive T) :
    IsSelfAdjoint T := hT.isSymmetric.isSelfAdjoint

theorem IsPositive.inner_left_eq_inner_right {T : E →L[𝕜] E} (hT : IsPositive T) (x y : E) :
    ⟪T x, y⟫ = ⟪x, T y⟫ := hT.isSymmetric _ _

theorem IsPositive.re_inner_nonneg_left {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ re ⟪T x, x⟫ := hT.2 x

lemma _root_.LinearMap.isPositive_toContinuousLinearMap_iff
    [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    T.toContinuousLinearMap.IsPositive ↔ T.IsPositive := Iff.rfl

lemma isPositive_toLinearMap_iff (T : E →L[𝕜] E) :
    (T : E →ₗ[𝕜] E).IsPositive ↔ T.IsPositive := Iff.rfl

alias ⟨_, IsPositive.toLinearMap⟩ := isPositive_toLinearMap_iff

theorem IsPositive.re_inner_nonneg_right {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ re ⟪x, T x⟫ := hT.toLinearMap.re_inner_nonneg_right x

open ComplexOrder in
/-- An operator is positive iff it is symmetric and `0 ≤ ⟪T x, x⟫`.

For the version with `IsSelfAdjoint` instead of `IsSymmetric`, see
`ContinuousLinearMap.isPositive_iff'`. -/
theorem isPositive_iff (T : E →L[𝕜] E) :
    IsPositive T ↔ T.IsSymmetric ∧ ∀ x, 0 ≤ ⟪T x, x⟫ := LinearMap.isPositive_iff _

open ComplexOrder in
/-- An operator is positive iff it is self-adjoint and `0 ≤ ⟪T x, x⟫`.

For the version with `IsSymmetric` instead of `IsSelfAdjoint`, see
`ContinuousLinearMap.isPositive_iff`. -/
theorem isPositive_iff' [CompleteSpace E] (T : E →L[𝕜] E) :
    IsPositive T ↔ IsSelfAdjoint T ∧ ∀ x, 0 ≤ ⟪T x, x⟫ := by
  simp [isSelfAdjoint_iff_isSymmetric, isPositive_iff]

open ComplexOrder in
theorem IsPositive.inner_nonneg_left {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ ⟪T x, x⟫ := hT.toLinearMap.inner_nonneg_left x

open ComplexOrder in
theorem IsPositive.inner_nonneg_right {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ ⟪x, T x⟫ := hT.toLinearMap.inner_nonneg_right x

@[simp]
theorem isPositive_zero : IsPositive (0 : E →L[𝕜] E) := LinearMap.isPositive_zero

@[simp]
theorem isPositive_id : IsPositive (.id 𝕜 E : E →L[𝕜] E) := LinearMap.isPositive_id

@[simp]
theorem isPositive_one : IsPositive (1 : E →L[𝕜] E) := LinearMap.isPositive_one

@[simp]
theorem isPositive_natCast {n : ℕ} : IsPositive (n : E →L[𝕜] E) :=
  (isPositive_toLinearMap_iff _).mp LinearMap.isPositive_natCast

@[simp]
theorem isPositive_ofNat {n : ℕ} [n.AtLeastTwo] : IsPositive (ofNat(n) : E →L[𝕜] E) :=
  isPositive_natCast

@[aesop safe apply]
theorem IsPositive.add {T S : E →L[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
    (T + S).IsPositive :=
  (isPositive_toLinearMap_iff _).mp (hT.toLinearMap.add hS.toLinearMap)

open ComplexOrder in
@[aesop safe apply]
theorem IsPositive.smul_of_nonneg {T : E →L[𝕜] E} (hT : T.IsPositive) {c : 𝕜} (hc : 0 ≤ c) :
    (c • T).IsPositive :=
  (isPositive_toLinearMap_iff _).mp (hT.toLinearMap.smul_of_nonneg hc)

@[aesop safe apply]
theorem IsPositive.conj_adjoint [CompleteSpace E] [CompleteSpace F] {T : E →L[𝕜] E}
    (hT : T.IsPositive) (S : E →L[𝕜] F) : (S ∘L T ∘L S†).IsPositive := by
  refine isPositive_def'.mpr ⟨hT.isSelfAdjoint.conj_adjoint S, fun x => ?_⟩
  rw [reApplyInnerSelf, comp_apply, ← adjoint_inner_right]
  exact hT.re_inner_nonneg_left _

theorem isPositive_self_comp_adjoint [CompleteSpace E] [CompleteSpace F] (S : E →L[𝕜] F) :
    (S ∘L S†).IsPositive := by
  simpa using isPositive_one.conj_adjoint S

@[aesop safe apply]
theorem IsPositive.adjoint_conj [CompleteSpace E] [CompleteSpace F] {T : E →L[𝕜] E}
    (hT : T.IsPositive) (S : F →L[𝕜] E) : (S† ∘L T ∘L S).IsPositive := by
  convert hT.conj_adjoint (S†)
  rw [adjoint_adjoint]

theorem isPositive_adjoint_comp_self [CompleteSpace E] [CompleteSpace F] (S : E →L[𝕜] F) :
    (S† ∘L S).IsPositive := by
  simpa using isPositive_one.adjoint_conj S

section LinearMap
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

@[aesop safe apply]
theorem _root_.LinearMap.IsPositive.conj_adjoint {T : E →ₗ[𝕜] E}
    (hT : T.IsPositive) (S : E →ₗ[𝕜] F) : (S ∘ₗ T ∘ₗ S.adjoint).IsPositive := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa [← isPositive_toContinuousLinearMap_iff] using
    ((T.isPositive_toContinuousLinearMap_iff.mpr hT).conj_adjoint S.toContinuousLinearMap)

theorem _root_.LinearMap.isPositive_self_comp_adjoint (S : E →ₗ[𝕜] F) :
    (S ∘ₗ S.adjoint).IsPositive := by
  simpa using LinearMap.isPositive_one.conj_adjoint S

@[aesop safe apply]
theorem _root_.LinearMap.IsPositive.adjoint_conj {T : E →ₗ[𝕜] E}
    (hT : T.IsPositive) (S : F →ₗ[𝕜] E) : (S.adjoint ∘ₗ T ∘ₗ S).IsPositive := by
  convert hT.conj_adjoint S.adjoint
  rw [LinearMap.adjoint_adjoint]

theorem _root_.LinearMap.isPositive_adjoint_comp_self (S : E →ₗ[𝕜] F) :
    (S.adjoint ∘ₗ S).IsPositive := by
  simpa using LinearMap.isPositive_one.adjoint_conj S

end LinearMap

theorem IsPositive.conj_starProjection (U : Submodule 𝕜 E) {T : E →L[𝕜] E} (hT : T.IsPositive)
    [U.HasOrthogonalProjection] :
    (U.starProjection ∘L T ∘L U.starProjection).IsPositive := by
  simp only [isPositive_iff, IsSymmetric, coe_comp, LinearMap.coe_comp, coe_coe,
    Function.comp_apply, coe_comp']
  simp_rw [← coe_coe, U.starProjection_isSymmetric _ , hT.isSymmetric _,
    U.starProjection_isSymmetric _, ← U.starProjection_isSymmetric _, coe_coe,
    hT.inner_nonneg_right, implies_true, and_self]

theorem IsPositive.orthogonalProjection_comp {T : E →L[𝕜] E} (hT : T.IsPositive) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : (U.orthogonalProjection ∘L T ∘L U.subtypeL).IsPositive := by
  simp only [isPositive_iff, IsSymmetric, coe_comp, LinearMap.coe_comp, coe_coe,
    Function.comp_apply, coe_comp']
  simp_rw [U.inner_orthogonalProjection_eq_of_mem_right, Submodule.subtypeL_apply,
    U.inner_orthogonalProjection_eq_of_mem_left, ← coe_coe, hT.isSymmetric _, coe_coe,
    hT.inner_nonneg_right, implies_true, and_self]

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

lemma isUnit_of_forall_le_norm_inner_map [CompleteSpace E] (f : E →L[𝕜] E) {c : ℝ≥0} (hc : 0 < c)
    (h : ∀ x, ‖x‖ ^ 2 * c ≤ ‖⟪f x, x⟫_𝕜‖) : IsUnit f := by
  rw [isUnit_iff_bijective, bijective_iff_dense_range_and_antilipschitz]
  have h_anti : AntilipschitzWith c⁻¹ f := antilipschitz_of_forall_le_inner_map f hc h
  refine ⟨?_, ⟨_, h_anti⟩⟩
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro x hx
  have : ‖x‖ ^ 2 * c = 0 := le_antisymm (by simpa only [hx (f x) ⟨x, rfl⟩, norm_zero] using h x)
    (by positivity)
  aesop

section Complex
variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']

theorem isPositive_iff_complex (T : E' →L[ℂ] E') :
    IsPositive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ := by
  simp [← isPositive_toLinearMap_iff, LinearMap.isPositive_iff_complex]

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
  le_antisymm _ _ h₁ h₂ := coe_inj.mp (le_antisymm h₁.toLinearMap h₂.toLinearMap)

lemma le_def (f g : E →L[𝕜] E) : f ≤ g ↔ (g - f).IsPositive := Iff.rfl

lemma coe_le_coe_iff (f g : E →L[𝕜] E) :
    (f : E →ₗ[𝕜] E) ≤ g ↔ f ≤ g :=
  isPositive_toLinearMap_iff (g - f)

lemma nonneg_iff_isPositive (f : E →L[𝕜] E) : 0 ≤ f ↔ f.IsPositive := by
  simpa using le_def 0 f

end PartialOrder

/-- An idempotent operator is positive if and only if it is self-adjoint. -/
@[grind →]
theorem IsIdempotentElem.isPositive_iff_isSelfAdjoint [CompleteSpace E]
    {p : E →L[𝕜] E} (hp : IsIdempotentElem p) : p.IsPositive ↔ IsSelfAdjoint p := by
  rw [← isPositive_toLinearMap_iff, IsIdempotentElem.isPositive_iff_isSymmetric hp.toLinearMap]
  exact isSelfAdjoint_iff_isSymmetric.symm

/-- A star projection operator is positive.

The proof of this will soon be simplified to `IsStarProjection.nonneg` when we
have `StarOrderedRing (E →L[𝕜] E)`. -/
@[aesop 10% apply, grind →]
theorem IsPositive.of_isStarProjection [CompleteSpace E] {p : E →L[𝕜] E}
    (hp : IsStarProjection p) : p.IsPositive :=
  hp.isIdempotentElem.isPositive_iff_isSelfAdjoint.mpr hp.isSelfAdjoint

/-- For an idempotent operator `p`, TFAE:
* `(range p)ᗮ = ker p`
* `p` is normal
* `p` is self-adjoint
* `p` is positive -/
theorem IsIdempotentElem.TFAE [CompleteSpace E] {p : E →L[𝕜] E} (hp : IsIdempotentElem p) :
    [(LinearMap.range p)ᗮ = LinearMap.ker p,
      IsStarNormal p,
      IsSelfAdjoint p,
      p.IsPositive].TFAE := by
  tfae_have 2 ↔ 3 := hp.isSelfAdjoint_iff_isStarNormal.symm
  tfae_have 3 ↔ 4 := hp.isPositive_iff_isSelfAdjoint.symm
  tfae_have 3 ↔ 1 := p.isSelfAdjoint_iff_isSymmetric.eq ▸
    (ContinuousLinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range hp)
  tfae_finish

end ContinuousLinearMap
