/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-!

# Bipolar Theorem

## Main definitions

- `LinearMap.rightDualEquiv`: When `B` is right-separating, `F` is linearly equivalent to the
  strong dual of `E` with the weak topology.
- `LinearMap.leftDualEquiv`: When `B` is left-separating, `E` is linearly equivalent to the
  strong dual of `F` with the weak topology.

## Main statements

- `LinearMap.flip_polar_polar_eq`: The Bipolar Theorem: The bipolar of a set coincides with its
  closed absolutely convex hull.

## References

* [Conway, *A course in functional analysis*][conway1990]

## Tags

bipolar, locally convex space
-/

variable {𝕜 E F : Type*}

namespace LinearMap

section NormedField

variable [NormedField 𝕜] [NormedSpace ℝ 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (s : Set E)

variable [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [IsScalarTower ℝ 𝕜 𝕜]

theorem polar_AbsConvex : AbsConvex 𝕜 (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact AbsConvex.iInter₂ fun i hi =>
    ⟨balanced_closedBall_zero.mulActionHom_preimage (f := (B i : (F →ₑ[(RingHom.id 𝕜)] 𝕜))),
      (convex_closedBall _ _).linear_preimage (B i)⟩

end NormedField

section

variable [NontriviallyNormedField 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (s : Set E)

lemma closureOperator_polar_gc_empty_of_separatingLeft (h : SeparatingLeft B) :
    B.polar_gc.closureOperator (∅ : Set E) = {0} := by
  simp only [GaloisConnection.closureOperator_apply, Function.comp_apply, polar_empty,
    OrderDual.ofDual_toDual, (B.flip.polar_univ h)]

end


section RCLike

variable [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

/- The Bipolar Theorem: The bipolar of a set coincides with its closed absolutely convex hull. -/
open scoped ComplexConjugate
theorem flip_polar_polar_eq {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {s : Set E} [Nonempty s] :
    B.flip.polar (B.polar s) = closedAbsConvexHull (E := WeakBilin B) 𝕜 s := by
  refine le_antisymm ?_ <| closedAbsConvexHull_min
    (subset_bipolar B s) (polar_AbsConvex _) (polar_isClosed B.flip _)
  simp only [Set.le_eq_subset]
  rw [← Set.compl_subset_compl]
  intro x hx
  obtain ⟨f, ⟨u, ⟨hf₁, hf₂⟩⟩⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) (E := WeakBilin B)
      absConvex_convexClosedHull.2 isClosed_closedAbsConvexHull hx
  have e3 : RCLike.re (f 0) < u :=
    (hf₁ 0) (absConvexHull_subset_closedAbsConvexHull zero_mem_absConvexHull)
  rw [map_zero, map_zero] at e3
  set g := (1/u : ℝ) • f with fg
  have fg2 : u • g = f := by
    rw [fg, one_div, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ (ne_of_lt e3).symm, one_smul]
  have hg₁ {a : _} (ha : a ∈ (closedAbsConvexHull (E := WeakBilin B) 𝕜) s) :
    RCLike.re (g a) < 1 := by
    rw [fg, ContinuousLinearMap.coe_smul', Pi.smul_apply, RCLike.smul_re, one_div,
      ← (inv_mul_cancel₀ (lt_iff_le_and_ne.mp e3).2.symm)]
    exact mul_lt_mul_of_pos_left ((hf₁ _) ha) (inv_pos_of_pos e3)
  obtain ⟨f₀, hf₀⟩ := B.dualEmbedding_surjective g
  have hg₃ : f₀ ∈ (B.polar (E := WeakBilin B) s) := by
    simp [← hf₀, WeakBilin.eval] at hg₁
    intro x₂ hx₂
    let l := conj (B x₂ f₀) / ‖B x₂ f₀‖
    have lnorm : ‖l‖ ≤ 1 := by
      rw [norm_div, RCLike.norm_conj, norm_algebraMap', norm_norm]
      exact div_self_le_one _
    have i1 : RCLike.re ((B.flip f₀) (l • x₂)) ≤ 1 := le_of_lt <| hg₁
      <| balanced_iff_smul_mem.mp absConvex_convexClosedHull.1 lnorm
        (subset_closedAbsConvexHull hx₂)
    rwa [CompatibleSMul.map_smul, smul_eq_mul, mul_comm, ← mul_div_assoc, LinearMap.flip_apply,
      RCLike.mul_conj, sq, mul_self_div_self, RCLike.ofReal_re] at i1
  have one_lt_x_f₀ : 1 < RCLike.re (B x f₀) := by
    rw [← one_lt_inv_mul₀ e3] at hf₂
    suffices u⁻¹ * RCLike.re (f x) = RCLike.re ((B x) f₀) by exact lt_of_lt_of_eq hf₂ this
    rw [← RCLike.re_ofReal_mul]
    congr
    simp [map_inv₀, ← fg2, ← hf₀, WeakBilin.eval]
    rw [← smul_eq_mul, ← smul_assoc]
    norm_cast
    have unz : u ≠ 0 := (ne_of_lt e3).symm
    aesop
  by_contra hc
  rw [Set.mem_compl_iff, not_not] at hc
  exact ((lt_iff_le_not_ge.mp one_lt_x_f₀).2)
    (Preorder.le_trans (RCLike.re ((B x) f₀)) ‖(B x) f₀‖ 1
      (RCLike.re_le_norm ((B x) f₀)) (hc f₀ hg₃))

/-
This fails when `s` is empty. Indeed, `closedAbsConvexHull (E := WeakBilin B) 𝕜 s` is the empty set,
but `B.polar_gc.closureOperator s` equals `{0}` when `B` is left separating.
-/
lemma closureOperator_polar_gc_nonempty {s : Set E} [Nonempty s] :
    B.polar_gc.closureOperator s = closedAbsConvexHull (E := WeakBilin B) 𝕜 s := by
  simp [flip_polar_polar_eq]

end RCLike

end LinearMap
