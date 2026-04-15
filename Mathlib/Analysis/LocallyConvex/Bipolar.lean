/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.LocallyConvex.Separation

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

public section

namespace WeakBilin

variable {𝕜 E F : Type*} [CommSemiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- The canonical linear equivalence between `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` and `E`. -/
noncomputable def linearEquiv : WeakBilin B ≃ₗ[𝕜] E :=
  LinearEquiv.refl ..

/-- The dual pairing between `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` and `F`. In order to avoid abuse
of the definitional equality between `E` and `WeakBilin B`, it is necessary to use this pairing
instead of `B` itself when considering statements involving the weak topology induced by the
pairing, such as the bipolar theorem. -/
noncomputable def pairing : WeakBilin B →ₗ[𝕜] F →ₗ[𝕜] 𝕜 :=
  (linearEquiv B).symm.arrowCongr (.refl _ _) B

end WeakBilin

namespace LinearMap

open WeakBilin

lemma isClosed_polar {𝕜 E F : Type*} [NormedCommRing 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (s : Set E) :
    IsClosed ((pairing B.flip).flip.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact isClosed_biInter
    fun _ _ ↦ Metric.isClosed_closedBall.preimage (WeakBilin.eval_continuous B.flip _)

end LinearMap

open scoped ComplexOrder

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


section RCLike

variable [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜}

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E]


open WeakBilin
/-
The Bipolar Theorem: The bipolar of a set coincides with its closed absolutely convex hull.
[Conway, *A course in functional analysis*, Chapter V. 1.8][conway1990]
-/
set_option backward.isDefEq.respectTransparency false in
open scoped ComplexConjugate ComplexOrder in
theorem pairing_flip_polar_polar {s : Set (WeakBilin B)} [Nonempty s] :
    (pairing B).flip.polar ((pairing B).polar s) = closedAbsConvexHull 𝕜 s := by
  apply subset_antisymm ?h1 <| closedAbsConvexHull_min (subset_bipolar (pairing B) s)
      (absConvex_polar _) (B.flip.isClosed_polar _)
  rw [← Set.compl_subset_compl]
  -- Let `x` be an element not in `(closedAbsConvexHull 𝕜) s`
  intro x hx
  obtain ⟨f, ⟨u, ⟨hf₁, hf₂⟩⟩⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
      (by rw [← convex_RCLike_iff_convex_real (K := 𝕜)]; exact absConvex_convexClosedHull.2)
      isClosed_closedAbsConvexHull hx
  -- `0` is in `(closedAbsConvexHull 𝕜) s` so `u` must be strictly positive
  have f_zero_lt_u : RCLike.re (f 0) < u :=
    (hf₁ 0) (absConvexHull_subset_closedAbsConvexHull zero_mem_absConvexHull)
  rw [map_zero, map_zero] at f_zero_lt_u
  -- Rescale `f` as `g` in order that for all `a` in `(closedAbsConvexHull 𝕜) s` `Re (g a) < 1`
  set g := (1/u : ℝ) • f with fg
  have u_smul_g_eq_f : u • g = f := by
    rw [fg, one_div, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ (ne_of_lt f_zero_lt_u).symm,
      one_smul]
  have re_g_a_lt_one {a : _} (ha : a ∈ closedAbsConvexHull 𝕜 s) :
    RCLike.re (g a) < 1 := by
    rw [fg, ContinuousLinearMap.coe_smul', Pi.smul_apply, RCLike.smul_re, one_div,
      ← (inv_mul_cancel₀ (lt_iff_le_and_ne.mp f_zero_lt_u).2.symm)]
    exact mul_lt_mul_of_pos_left ((hf₁ _) ha) (inv_pos_of_pos f_zero_lt_u)
  -- The dual embedding is surjective, let `f₀` be the element of `F` corresponding to `g`
  obtain ⟨f₀, hf₀⟩ := (pairing B).dualEmbedding_surjective g
  -- Then, by construction, `f₀` is in the polar of `s`
  have mem_polar : f₀ ∈ (pairing B).polar s := by
    simp only [← hf₀, WeakBilin.eval, coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_mk']
      at re_g_a_lt_one
    intro x₂ hx₂
    let l := conj (pairing B x₂ f₀) / ‖pairing B x₂ f₀‖
    have lnorm : ‖l‖ ≤ 1 := by
      rw [norm_div, RCLike.norm_conj, norm_algebraMap', norm_norm]
      exact div_self_le_one _
    have i1 : RCLike.re (((pairing B).flip f₀) (l • x₂)) ≤ 1 := le_of_lt <| re_g_a_lt_one
      <| balanced_iff_smul_mem.mp absConvex_convexClosedHull.1 lnorm
        (subset_closedAbsConvexHull hx₂)
    rwa [CompatibleSMul.map_smul, smul_eq_mul, mul_comm, ← mul_div_assoc, LinearMap.flip_apply,
      RCLike.mul_conj, sq, mul_self_div_self, RCLike.ofReal_re] at i1
  -- and `1 < Re (B x f₀)`
  have one_lt_x_f₀ : 1 < RCLike.re (pairing B x f₀) := by
    rw [← one_lt_inv_mul₀ f_zero_lt_u] at hf₂
    suffices u⁻¹ * RCLike.re (f x) = RCLike.re ((pairing B x) f₀) by exact lt_of_lt_of_eq hf₂ this
    rw [← RCLike.re_ofReal_mul]
    congr
    simp only [map_inv₀, ← u_smul_g_eq_f, ← hf₀, WeakBilin.eval, coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_mk', Pi.smul_apply,
      Algebra.mul_smul_comm]
    rw [← smul_eq_mul, ← smul_assoc]
    norm_cast
    simp only [smul_eq_mul, mul_inv_cancel₀ (ne_of_lt f_zero_lt_u).symm, map_one, one_mul]
    exact flip_apply ..
  -- From which it follows that `x` can't be in the bipolar of `s`
  exact fun hc ↦ ((lt_iff_le_not_ge.mp one_lt_x_f₀).2)
    (Preorder.le_trans (RCLike.re ((pairing B x) f₀)) ‖(pairing B x) f₀‖ 1
      (RCLike.re_le_norm ((pairing B x) f₀)) (hc f₀ mem_polar))

/-
This fails when `s` is empty. Indeed, `closedAbsConvexHull (E := WeakBilin B) 𝕜 s` is the empty set,
but `B.polar_gc.closureOperator s` equals `{0}` when `B` is left separating (see example above).
-/
lemma closureOperator_polar_gc_nonempty {s : Set (WeakBilin B)} [Nonempty s] :
    (pairing B).polar_gc.closureOperator s = closedAbsConvexHull (E := WeakBilin B) 𝕜 s := by
  simp [pairing_flip_polar_polar]

end RCLike

end LinearMap
