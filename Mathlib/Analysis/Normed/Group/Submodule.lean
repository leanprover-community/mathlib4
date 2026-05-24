/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Analysis.Normed.Group.Basic

/-! # Submodules of normed groups -/

public section

variable {𝕜 E : Type*}

namespace Submodule

/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.
-/
instance instIsNormedAddGroup [Ring 𝕜] [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E] [Module 𝕜 E]
    (s : Submodule 𝕜 E) : IsNormedAddGroup s :=
  IsNormedAddGroup.induced _ _ s.subtype.toAddMonoidHom

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `s` is equal to its
norm in `E`. -/
theorem coe_norm [Ring 𝕜] [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

This is a reversed version of the `simp` lemma `Submodule.coe_norm` for use by `norm_cast`. -/
theorem norm_coe [Ring 𝕜] [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl

end Submodule

@[continuity, fun_prop]
theorem LinearMap.continuous_domRestrict {R R' M M' : Type*} [Semiring R] [Semiring R']
    [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R' M'] {σ₁₂ : R →+* R'}
    (f : M →ₛₗ[σ₁₂] M') [TopologicalSpace M] [TopologicalSpace M'] (hf : Continuous f)
    (p : Submodule R M) : Continuous (f.domRestrict p) := by
  rw [coe_domRestrict]
  fun_prop
