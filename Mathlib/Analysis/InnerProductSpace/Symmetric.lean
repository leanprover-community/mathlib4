/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.SesquilinearForm

/-!
# Symmetric linear maps in an inner product space

This file defines and proves basic theorems about symmetric **not necessarily bounded** operators
on an inner product space, i.e linear maps `T : E → E` such that `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.

In comparison to `IsSelfAdjoint`, this definition works for non-continuous linear maps, and
doesn't rely on the definition of the adjoint, which allows it to be stated in non-complete space.

## Main definitions

* `LinearMap.IsSymmetric`: a (not necessarily bounded) operator on an inner product space is
symmetric, if for all `x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`

## Main statements

* `IsSymmetric.continuous`: if a symmetric operator is defined on a complete space, then
  it is automatically continuous.

## Tags

self-adjoint, symmetric
-/


open RCLike

open ComplexConjugate

section Seminormed

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

/-! ### Symmetric operators -/


/-- A (not necessarily bounded) operator on an inner product space is symmetric, if for all
`x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`. -/
def IsSymmetric (T : E →ₗ[𝕜] E) : Prop :=
  ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫

section Real

/-- An operator `T` on an inner product space is symmetric if and only if it is
`LinearMap.IsSelfAdjoint` with respect to the sesquilinear form given by the inner product. -/
theorem isSymmetric_iff_sesqForm (T : E →ₗ[𝕜] E) :
    T.IsSymmetric ↔ LinearMap.IsSelfAdjoint (R := 𝕜) (M := E) sesqFormOfInner T :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

end Real

theorem IsSymmetric.conj_inner_sym {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) (x y : E) :
    conj ⟪T x, y⟫ = ⟪T y, x⟫ := by rw [hT x y, inner_conj_symm]

@[simp]
theorem IsSymmetric.apply_clm {T : E →L[𝕜] E} (hT : IsSymmetric (T : E →ₗ[𝕜] E)) (x y : E) :
    ⟪T x, y⟫ = ⟪x, T y⟫ :=
  hT x y

@[simp]
protected theorem IsSymmetric.zero : (0 : E →ₗ[𝕜] E).IsSymmetric := fun x y =>
  (inner_zero_right x : ⟪x, 0⟫ = 0).symm ▸ (inner_zero_left y : ⟪0, y⟫ = 0)

@[simp]
protected theorem IsSymmetric.id : (LinearMap.id : E →ₗ[𝕜] E).IsSymmetric := fun _ _ => rfl

@[aesop safe apply]
theorem IsSymmetric.add {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
    (T + S).IsSymmetric := by
  intro x y
  rw [add_apply, inner_add_left, hT x y, hS x y, ← inner_add_right, add_apply]

@[aesop safe apply]
theorem IsSymmetric.sub {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
    (T - S).IsSymmetric := by
  intro x y
  rw [sub_apply, inner_sub_left, hT x y, hS x y, ← inner_sub_right, sub_apply]

@[aesop safe apply]
theorem IsSymmetric.smul {c : 𝕜} (hc : conj c = c) {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    c • T |>.IsSymmetric := by
  intro x y
  simp only [smul_apply, inner_smul_left, hc, hT x y, inner_smul_right]

@[aesop 30% apply]
lemma IsSymmetric.mul_of_commute {S T : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hST : Commute S T) : (S * T).IsSymmetric :=
  fun _ _ ↦ by rw [Module.End.mul_apply, hS, hT, hST, Module.End.mul_apply]

@[aesop safe apply]
lemma IsSymmetric.pow {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (n : ℕ) : (T ^ n).IsSymmetric := by
  refine Nat.le_induction (by simp [Module.End.one_eq_id]) (fun k _ ih ↦ ?_) n n.zero_le
  rw [Module.End.iterate_succ, ← Module.End.mul_eq_comp]
  exact ih.mul_of_commute hT <| .pow_left rfl k

/-- For a symmetric operator `T`, the function `fun x ↦ ⟪T x, x⟫` is real-valued. -/
@[simp]
theorem IsSymmetric.coe_reApplyInnerSelf_apply {T : E →L[𝕜] E} (hT : IsSymmetric (T : E →ₗ[𝕜] E))
    (x : E) : (T.reApplyInnerSelf x : 𝕜) = ⟪T x, x⟫ := by
  rsuffices ⟨r, hr⟩ : ∃ r : ℝ, ⟪T x, x⟫ = r
  · simp [hr, T.reApplyInnerSelf_apply]
  rw [← conj_eq_iff_real]
  exact hT.conj_inner_sym x x

/-- For a symmetric linear map `T`, the function `fun x ↦ ⟪T x, x⟫` is real-valued. -/
@[simp]
theorem IsSymmetric.reApplyInnerSelf_apply {T : E →ₗ[𝕜] E} (hT : IsSymmetric T)
    (x : E) : (T.reApplyInnerSelf x : 𝕜) = ⟪T x, x⟫ := by
  rsuffices ⟨r, hr⟩ : ∃ r : ℝ, ⟪T x, x⟫ = r
  · simp [hr, T.reApplyInnerSelf_apply]
  rw [← conj_eq_iff_real]
  exact hT.conj_inner_sym x x

/-- If a symmetric operator preserves a submodule, its restriction to that submodule is
symmetric. -/
theorem IsSymmetric.restrict_invariant {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) {V : Submodule 𝕜 E}
    (hV : ∀ v ∈ V, T v ∈ V) : IsSymmetric (T.restrict hV) := fun v w => hT v w

theorem IsSymmetric.restrictScalars {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    letI := InnerProductSpace.rclikeToReal 𝕜 E
    letI : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower _ _ _
    (T.restrictScalars ℝ).IsSymmetric :=
  fun x y => by simp [hT x y, real_inner_eq_re_inner, LinearMap.coe_restrictScalars ℝ]

section Complex

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

attribute [local simp] map_ofNat in -- use `ofNat` simp theorem with bad keys
open scoped InnerProductSpace in
/-- A linear operator on a complex inner product space is symmetric precisely when
`⟪T v, v⟫_ℂ` is real for all v. -/
theorem isSymmetric_iff_inner_map_self_real (T : V →ₗ[ℂ] V) :
    IsSymmetric T ↔ ∀ v : V, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ := by
  constructor
  · intro hT v
    apply IsSymmetric.conj_inner_sym hT
  · intro h x y
    rw [← inner_conj_symm x (T y)]
    rw [inner_map_polarization T x y]
    simp only [starRingEnd_apply, star_div₀, star_sub, star_add, star_mul]
    simp only [← starRingEnd_apply]
    rw [h (x + y), h (x - y), h (x + Complex.I • y), h (x - Complex.I • y)]
    simp only [Complex.conj_I]
    rw [inner_map_polarization']
    norm_num
    ring

end Complex

/-- Polarization identity for symmetric linear maps.
See `inner_map_polarization` for the complex version without the symmetric assumption. -/
theorem IsSymmetric.inner_map_polarization {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (x y : E) :
    ⟪T x, y⟫ =
      (⟪T (x + y), x + y⟫ - ⟪T (x - y), x - y⟫ - I * ⟪T (x + (I : 𝕜) • y), x + (I : 𝕜) • y⟫ +
          I * ⟪T (x - (I : 𝕜) • y), x - (I : 𝕜) • y⟫) /
        4 := by
  rcases@I_mul_I_ax 𝕜 _ with (h | h)
  · simp_rw [h, zero_mul, sub_zero, add_zero, map_add, map_sub, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right, hT x, ← inner_conj_symm x (T y)]
    suffices (re ⟪T y, x⟫ : 𝕜) = ⟪T y, x⟫ by
      rw [conj_eq_iff_re.mpr this]
      ring
    rw [← re_add_im ⟪T y, x⟫]
    simp_rw [h, mul_zero, add_zero]
    norm_cast
  · simp_rw [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      LinearMap.map_smul, inner_smul_left, inner_smul_right, RCLike.conj_I, mul_add, mul_sub,
      sub_sub, ← mul_assoc, mul_neg, h, neg_neg, one_mul, neg_one_mul]
    ring

end LinearMap

end Seminormed

section Normed

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

/-- The **Hellinger--Toeplitz theorem**: if a symmetric operator is defined on a complete space,
  then it is automatically continuous. -/
theorem IsSymmetric.continuous [CompleteSpace E] {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) :
    Continuous T := by
  -- We prove it by using the closed graph theorem
  refine T.continuous_of_seq_closed_graph fun u x y hu hTu => ?_
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜]
  have hlhs : ∀ k : ℕ, ⟪T (u k) - T x, y - T x⟫ = ⟪u k - x, T (y - T x)⟫ := by
    intro k
    rw [← T.map_sub, hT]
  refine tendsto_nhds_unique ((hTu.sub_const _).inner tendsto_const_nhds) ?_
  simp_rw [Function.comp_apply, hlhs]
  rw [← inner_zero_left (T (y - T x))]
  refine Filter.Tendsto.inner ?_ tendsto_const_nhds
  rw [← sub_self x]
  exact hu.sub_const _

/-- A symmetric linear map `T` is zero if and only if `⟪T x, x⟫_ℝ = 0` for all `x`.
See `inner_map_self_eq_zero` for the complex version without the symmetric assumption. -/
theorem IsSymmetric.inner_map_self_eq_zero {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    (∀ x, ⟪T x, x⟫ = 0) ↔ T = 0 := by
  simp_rw [LinearMap.ext_iff, zero_apply]
  refine ⟨fun h x => ?_, fun h => by simp_rw [h, inner_zero_left, forall_const]⟩
  rw [← @inner_self_eq_zero 𝕜, hT.inner_map_polarization]
  simp_rw [h _]
  ring

end LinearMap

end Normed
