/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Holomorphicity of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are holomorphic on the upper half plane, which is stated as being
MDifferentiable.
-/

public section

noncomputable section

open UpperHalfPlane Filter Function Complex Manifold CongruenceSubgroup

namespace EisensteinSeries

/-- Auxiliary lemma showing that for any `k : ℤ` the function `z → 1/(c*z+d)^k` is
differentiable on `{z : ℂ | 0 < z.im}`. -/
lemma div_linear_zpow_differentiableOn (k : ℤ) (a : Fin 2 → ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => (a 0 * z + a 1) ^ (-k)) {z : ℂ | 0 < z.im} := by
  rcases ne_or_eq a 0 with ha | rfl
  · apply DifferentiableOn.zpow
    · fun_prop
    · left
      exact fun z hz ↦ linear_ne_zero ⟨z, hz⟩
        ((comp_ne_zero_iff _ Int.cast_injective Int.cast_zero).mpr ha)
  · simp only [Pi.zero_apply, Int.cast_zero, zero_mul, add_zero]
    apply differentiableOn_const

/-- Auxiliary lemma showing that for any `k : ℤ` and `(a : Fin 2 → ℤ)`
the extension of `eisSummand` is differentiable on `{z : ℂ | 0 < z.im}`. -/
lemma eisSummand_extension_differentiableOn (k : ℤ) (a : Fin 2 → ℤ) :
    DifferentiableOn ℂ (↑ₕeisSummand k a) {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.congr (div_linear_zpow_differentiableOn k a)
  intro z hz
  lift z to ℍ using hz
  apply comp_ofComplex

/-- Eisenstein series are MDifferentiable (i.e. holomorphic functions from `ℍ → ℂ`). -/
theorem eisensteinSeries_SIF_MDifferentiable {k : ℤ} {N : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    MDiff (eisensteinSeries_SIF a k) := by
  intro τ
  suffices DifferentiableAt ℂ (↑ₕeisensteinSeries_SIF a k) τ.1 by
    convert MDifferentiableAt.comp τ (DifferentiableAt.mdifferentiableAt this) τ.mdifferentiable_coe
    exact funext fun z ↦ (comp_ofComplex (eisensteinSeries_SIF a k) z).symm
  refine DifferentiableOn.differentiableAt ?_ (isOpen_upperHalfPlaneSet.mem_nhds τ.2)
  exact (eisensteinSeries_tendstoLocallyUniformlyOn hk a).differentiableOn
    (Eventually.of_forall fun s ↦ DifferentiableOn.fun_sum
    fun _ _ ↦ eisSummand_extension_differentiableOn _ _) isOpen_upperHalfPlaneSet

end EisensteinSeries
