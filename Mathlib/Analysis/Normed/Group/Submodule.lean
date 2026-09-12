/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-! # Submodules of normed groups -/

public section

variable {𝕜 E : Type*}

namespace Submodule

/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.
-/
instance seminormedAddCommGroup [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]
    (s : Submodule 𝕜 E) : SeminormedAddCommGroup s :=
  fast_instance% SeminormedAddCommGroup.induced _ _ s.subtype.toAddMonoidHom

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `s` is equal to its
norm in `E`. -/
@[deprecated "use `norm_coe`" (since := "2026-08-25")]
theorem coe_norm [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`. -/
@[simp ←, norm_cast]
theorem norm_coe [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl

/-- A submodule of a normed group is also a normed group, with the restriction of the norm. -/
instance normedAddCommGroup [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    (s : Submodule 𝕜 E) : NormedAddCommGroup s :=
  { Submodule.seminormedAddCommGroup s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

end Submodule

namespace ClosedSubmodule

/-- A closed submodule of a seminormed group is also a seminormed group, with the restriction of the
norm. -/
instance seminormedAddCommGroup [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]
    (s : ClosedSubmodule 𝕜 E) : SeminormedAddCommGroup s :=
  fast_instance% s.toSubmodule.seminormedAddCommGroup

/-- If `x` is an element of a closed submodule `s` of a normed group `E`, its norm in `s` is equal
to its norm in `E`. -/
@[simp ←, norm_cast]
theorem norm_coe [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : ClosedSubmodule 𝕜 E}
    (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl

/-- A closed submodule of a normed group is also a normed group, with the restriction of the norm.
-/
instance normedAddCommGroup [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    (s : ClosedSubmodule 𝕜 E) : NormedAddCommGroup s :=
  fast_instance% s.toSubmodule.normedAddCommGroup

end ClosedSubmodule

@[continuity, fun_prop]
theorem LinearMap.continuous_domRestrict {R R' M M' : Type*} [Semiring R] [Semiring R']
    [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R' M'] {σ₁₂ : R →+* R'}
    (f : M →ₛₗ[σ₁₂] M') [TopologicalSpace M] [TopologicalSpace M'] (hf : Continuous f)
    (p : Submodule R M) : Continuous (f.domRestrict p) := by
  rw [coe_domRestrict]
  fun_prop
