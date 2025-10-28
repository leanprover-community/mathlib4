/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.RCLike.Lemmas

/-!

# Bipolar Theorem

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

section

variable [NontriviallyNormedField 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (s : Set E)

/-
When `B` is left-separating, the closure of the empty set is the singleton `{0}`. This is in
contrast to the closed absolutely convex hull of the empty set, which is again the empty set.
c.f. `closureOperator_polar_gc_nonempty` below.
-/
example (h : SeparatingLeft B) : B.polar_gc.closureOperator (∅ : Set E) = {0} := by
  simp only [GaloisConnection.closureOperator_apply, Function.comp_apply, polar_empty,
    OrderDual.ofDual_toDual, (B.flip.polar_univ h)]

end

section NormedField

variable [RCLike 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F] [IsScalarTower ℝ 𝕜 𝕜]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (s : Set E)

open scoped ComplexOrder
theorem polar_absConvex : AbsConvex 𝕜 (B.polar s) :=
  polar_eq_biInter_preimage B s ▸ AbsConvex.iInter₂ fun i _ =>
    ⟨balanced_closedBall_zero.mulActionHom_preimage (f := (B i : (F →ₑ[(RingHom.id 𝕜)] 𝕜))),
      (convex_RCLike_iff_convex_real.mpr (convex_closedBall _ _)).linear_preimage (B i)⟩

end NormedField



section RCLike

variable [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜}

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

/-
The Bipolar Theorem: The bipolar of a set coincides with its closed absolutely convex hull.
[Conway, *A course in functional analysis*, Chapter V. 1.8][conway1990]
-/
open scoped ComplexConjugate
open scoped ComplexOrder
theorem flip_polar_polar_eq {s : Set E} [Nonempty s] :
    B.flip.polar (B.polar s) = closedAbsConvexHull (E := WeakBilin B) 𝕜 s := by
  refine subset_antisymm ?_ <| closedAbsConvexHull_min (E := WeakBilin B)
    (subset_bipolar B s) (polar_absConvex _) (polar_isClosed B.flip _)
  rw [← Set.compl_subset_compl]
  -- Let `x` be an element not in `(closedAbsConvexHull 𝕜) s`
  intro x hx
  -- Use the Geometric Hahn-Banach theorem to obtain a function `f` and a constant `u` separating
  -- `(closedAbsConvexHull 𝕜) s` and `x`
  obtain ⟨f, ⟨u, ⟨hf₁, hf₂⟩⟩⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) (E := WeakBilin B)
      absConvex_convexClosedHull.2 isClosed_closedAbsConvexHull hx
  -- `0` is in `(closedAbsConvexHull 𝕜) s` so `u` must be strictly positive
  have f_zero_lt_u : RCLike.re (f 0) < u :=
    (hf₁ 0) (absConvexHull_subset_closedAbsConvexHull zero_mem_absConvexHull)
  rw [map_zero, map_zero] at f_zero_lt_u
  -- Rescale `f` as `g` in order that for all `a` in `(closedAbsConvexHull 𝕜) s` `Re (g a) < 1`
  set g := (1/u : ℝ) • f with fg
  have u_smul_g_eq_f : u • g = f := by
    rw [fg, one_div, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ (ne_of_lt f_zero_lt_u).symm,
      one_smul]
  have re_g_a_lt_one {a : _} (ha : a ∈ (closedAbsConvexHull (E := WeakBilin B) 𝕜) s) :
    RCLike.re (g a) < 1 := by
    rw [fg, ContinuousLinearMap.coe_smul', Pi.smul_apply, RCLike.smul_re, one_div,
      ← (inv_mul_cancel₀ (lt_iff_le_and_ne.mp f_zero_lt_u).2.symm)]
    exact mul_lt_mul_of_pos_left ((hf₁ _) ha) (inv_pos_of_pos f_zero_lt_u)
  -- The dual embedding is surjective, let `f₀` be the element of `F` corresponding to `g`
  obtain ⟨f₀, hf₀⟩ := B.dualEmbedding_surjective g
  -- Then, by construction, `f₀` is in the polar of `s`
  have mem_polar : f₀ ∈ (B.polar (E := WeakBilin B) s) := by
    simp only [← hf₀, WeakBilin.eval, coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_mk']
      at re_g_a_lt_one
    intro x₂ hx₂
    let l := conj (B x₂ f₀) / ‖B x₂ f₀‖
    have lnorm : ‖l‖ ≤ 1 := by
      rw [norm_div, RCLike.norm_conj, norm_algebraMap', norm_norm]
      exact div_self_le_one _
    have i1 : RCLike.re ((B.flip f₀) (l • x₂)) ≤ 1 := le_of_lt <| re_g_a_lt_one
      <| balanced_iff_smul_mem.mp absConvex_convexClosedHull.1 lnorm
        (subset_closedAbsConvexHull hx₂)
    rwa [CompatibleSMul.map_smul, smul_eq_mul, mul_comm, ← mul_div_assoc, LinearMap.flip_apply,
      RCLike.mul_conj, sq, mul_self_div_self, RCLike.ofReal_re] at i1
  -- and `1 < Re (B x f₀)`
  have one_lt_x_f₀ : 1 < RCLike.re (B x f₀) := by
    rw [← one_lt_inv_mul₀ f_zero_lt_u] at hf₂
    suffices u⁻¹ * RCLike.re (f x) = RCLike.re ((B x) f₀) by exact lt_of_lt_of_eq hf₂ this
    rw [← RCLike.re_ofReal_mul]
    congr
    simp only [map_inv₀, ← u_smul_g_eq_f, ← hf₀, WeakBilin.eval, coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_mk', Pi.smul_apply,
      Algebra.mul_smul_comm]
    rw [← smul_eq_mul, ← smul_assoc]
    norm_cast
    have unz : u ≠ 0 := (ne_of_lt f_zero_lt_u).symm
    simp_all only [nonempty_subtype, Set.mem_compl_iff, one_div, ne_eq, not_false_eq_true,
      smul_inv_smul₀, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, mul_inv_cancel₀,
      map_one, one_mul]
    rfl
  -- From which it follows that `x` can't be in the bipolar of `s`
  exact fun hc ↦ ((lt_iff_le_not_ge.mp one_lt_x_f₀).2)
    (Preorder.le_trans (RCLike.re ((B x) f₀)) ‖(B x) f₀‖ 1
      (RCLike.re_le_norm ((B x) f₀)) (hc f₀ mem_polar))

/-
This fails when `s` is empty. Indeed, `closedAbsConvexHull (E := WeakBilin B) 𝕜 s` is the empty set,
but `B.polar_gc.closureOperator s` equals `{0}` when `B` is left separating (see example above).
-/
lemma closureOperator_polar_gc_nonempty {s : Set E} [Nonempty s] :
    B.polar_gc.closureOperator s = closedAbsConvexHull (E := WeakBilin B) 𝕜 s := by
  simp [flip_polar_polar_eq]

end RCLike

end LinearMap
