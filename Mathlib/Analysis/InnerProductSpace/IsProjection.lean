/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
# `IsProjection` and `IsOrthogonalProjection` as predicates on linear maps

This files defines when a linear map is a projection and when it is an orthogonal projection.

## Main definitions

* `LinearMap.IsProjection`: We call a linear map `T` a projection when `T ∘ₗ T = T`.
* `LinearMap.IsOrthogonalProjection`: We call a linear map `T` an orthogonal projection when it is a
projection and it is self-adjoint.

-/

namespace LinearMap

section IsProjection

variable {R E : Type*}
variable [Semiring R] [AddCommMonoid E] [Module R E]

/-- When a linear map is a projection. -/
def IsProjection (T : E →ₗ[R] E) : Prop :=
  T ∘ₗ T = T

lemma IsProjection.app_range {T : E →ₗ[R] E} (hT : T.IsProjection) {x : E} (hx : x ∈ range T) :
    T x = x := by
  obtain ⟨y, hy⟩ := hx
  rw [← hy, ← comp_apply, hT]

lemma IsProjection.zero : (0 : E →ₗ[R] E).IsProjection :=
  rfl

lemma IsProjection.one : (1 : E →ₗ[R] E).IsProjection :=
  rfl

end IsProjection

section IsOrthogonalProjection

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- When a linear map is an orthogonal projection. -/
structure IsOrthogonalProjection (T : E →ₗ[𝕜] E) : Prop where
  isProjection : T.IsProjection
  isSelfAdjoint : IsSelfAdjoint T

lemma IsOrthogonalProjection.isSymmetric {T : E →ₗ[𝕜] E} (hT : T.IsOrthogonalProjection) :
    T.IsSymmetric := (isSymmetric_iff_isSelfAdjoint T).mpr hT.isSelfAdjoint

lemma IsOrthogonalProjection.isPositive {T : E →ₗ[𝕜] E} (hT : T.IsOrthogonalProjection) :
    T.IsPositive := by
  apply And.intro hT.isSelfAdjoint
  intro x
  rw [← hT.isProjection, comp_apply, hT.isSymmetric]
  exact inner_self_nonneg

lemma IsOrthogonalProjection.range_eq_orthogonal_ker {T : E →ₗ[𝕜] E}
    (hT : T.IsOrthogonalProjection) : range T = (ker T)ᗮ := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [← hT.isProjection.app_range hx, ← (isSymmetric_iff_isSelfAdjoint T).mpr hT.isSelfAdjoint,
      hu]
    exact inner_zero_left x
  · rw [Nat.eq_sub_of_add_eq' (ker T).finrank_add_finrank_orthogonal,
      eq_tsub_iff_add_eq_of_le (ker T).finrank_le]
    exact finrank_range_add_finrank_ker T

/-- Get a linear map from a submodule. See `Submodule.toOrthogonalProjection_valid` for the proof
that it actually satisfies `LinearMap.IsOrthogonalProjection`. -/
noncomputable def Submodule.toOrthogonalProjection (K : Submodule 𝕜 E) : E →ₗ[𝕜] E :=
  K.subtype ∘ₗ K.orthogonalProjection

lemma Submodule.toOrthogonalProjection_eq (K : Submodule 𝕜 E) (x : E) :
    toOrthogonalProjection K x = K.orthogonalProjection x := rfl

lemma Submodule.toOrthogonalProjection_valid (K : Submodule 𝕜 E) :
    (toOrthogonalProjection K).IsOrthogonalProjection := by
  constructor
  · ext
    simp [toOrthogonalProjection]
  · rw [← isSymmetric_iff_isSelfAdjoint]
    intro x y
    unfold toOrthogonalProjection
    simp only [coe_comp]
    exact K.inner_orthogonalProjection_left_eq_right x y

lemma Submodule.range_toOrthogonalProjection_eq (K : Submodule 𝕜 E) :
    range (toOrthogonalProjection K) = K := by
  rw [(toOrthogonalProjection_valid K).range_eq_orthogonal_ker]
  unfold toOrthogonalProjection
  rw [← Submodule.orthogonalComplement_eq_orthogonalComplement,
    Submodule.orthogonal_orthogonal]
  ext x
  rw [mem_ker, ← Submodule.orthogonalProjection_eq_zero_iff]
  simp

lemma IsOrthogonalProjection.toOrthogonalProjection_range_eq (T : E →ₗ[𝕜] E)
    (hT : T.IsOrthogonalProjection) : Submodule.toOrthogonalProjection (range T) = T := by
  ext x
  rw [hT.range_eq_orthogonal_ker]
  have hx := Submodule.exists_add_mem_mem_orthogonal (ker T) x
  obtain ⟨y, hy, z, hz, hxyz⟩ := hx
  rw [hxyz]
  repeat rw [map_add, Submodule.toOrthogonalProjection_eq,
    Submodule.orthogonalProjection_orthogonal_val]
  apply Mathlib.Tactic.LinearCombination.add_eq_eq
  · rw [Submodule.orthogonalProjection_eq_self_iff.mpr hy, sub_self, hy]
  · rw [Submodule.orthogonalProjection_eq_zero_iff.mpr hz,
      ZeroMemClass.coe_zero, sub_zero]
    have hz' : z ∈ range T := by
      rw [hT.range_eq_orthogonal_ker]
      exact hz
    exact (hT.isProjection.app_range hz').symm

theorem IsOrthogonalProjection.eq_iff_range_eq {T S : E →ₗ[𝕜] E} (hT : T.IsOrthogonalProjection)
    (hS : S.IsOrthogonalProjection) : T = S ↔ range T = range S := by
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    rw [← hT.toOrthogonalProjection_range_eq, ← hS.toOrthogonalProjection_range_eq, h]

lemma IsOrthogonalProjection.zero : (0 : E →ₗ[𝕜] E).IsOrthogonalProjection :=
  ⟨IsProjection.zero, IsSelfAdjoint.zero (E →ₗ[𝕜] E)⟩

lemma IsOrthogonalProjection.one : (1 : E →ₗ[𝕜] E).IsOrthogonalProjection :=
  ⟨IsProjection.one, IsSelfAdjoint.one (E →ₗ[𝕜] E)⟩

lemma Submodule.toOrthogonalProjection_bot :
    toOrthogonalProjection (⊥ : Submodule 𝕜 E) = (0 : E →ₗ[𝕜] E) := by
  ext x
  simp [toOrthogonalProjection_eq, Submodule.orthogonalProjection_bot]

lemma Submodule.toOrthogonalProjection_top :
    toOrthogonalProjection (⊤ : Submodule 𝕜 E) = (1 : E →ₗ[𝕜] E) := by
  ext x
  simp [toOrthogonalProjection_eq, Submodule.orthogonalProjection_eq_self_iff]

end IsOrthogonalProjection

end LinearMap
