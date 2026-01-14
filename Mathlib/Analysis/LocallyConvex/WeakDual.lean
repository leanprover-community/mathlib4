/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.WeakBilin

/-!
# Weak Dual in Topological Vector Spaces

We prove that the weak topology induced by a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is locally
convex and we explicitly give a neighborhood basis in terms of the family of seminorms
`fun x => ‖B x y‖` for `y : F`.

## Main definitions

* `LinearMap.toSeminorm`: turn a linear form `f : E →ₗ[𝕜] 𝕜` into a seminorm `fun x => ‖f x‖`.
* `LinearMap.toSeminormFamily`: turn a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` into a map
  `F → Seminorm 𝕜 E`.

## Main statements

* `LinearMap.hasBasis_weakBilin`: the seminorm balls of `B.toSeminormFamily` form a
  neighborhood basis of `0` in the weak topology.
* `LinearMap.toSeminormFamily.withSeminorms`: the topology of a weak space is induced by the
  family of seminorms `B.toSeminormFamily`.
* `WeakBilin.locallyConvexSpace`: a space endowed with a weak topology is locally convex.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

weak dual, seminorm
-/


variable {𝕜 E F : Type*}

open Topology

section BilinForm

namespace LinearMap

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- Construct a seminorm from a linear form `f : E →ₗ[𝕜] 𝕜` over a normed field `𝕜` by
`fun x => ‖f x‖` -/
def toSeminorm (f : E →ₗ[𝕜] 𝕜) : Seminorm 𝕜 E :=
  (normSeminorm 𝕜 𝕜).comp f

theorem coe_toSeminorm {f : E →ₗ[𝕜] 𝕜} : ⇑f.toSeminorm = fun x => ‖f x‖ :=
  rfl

@[simp]
theorem toSeminorm_apply {f : E →ₗ[𝕜] 𝕜} {x : E} : f.toSeminorm x = ‖f x‖ :=
  rfl

theorem toSeminorm_ball_zero {f : E →ₗ[𝕜] 𝕜} {r : ℝ} :
    Seminorm.ball f.toSeminorm 0 r = { x : E | ‖f x‖ < r } := by
  simp only [Seminorm.ball_zero_eq, toSeminorm_apply]

theorem toSeminorm_comp (f : F →ₗ[𝕜] 𝕜) (g : E →ₗ[𝕜] F) :
    f.toSeminorm.comp g = (f.comp g).toSeminorm := by
  ext
  simp only [Seminorm.comp_apply, toSeminorm_apply, coe_comp, Function.comp_apply]

/-- Construct a family of seminorms from a bilinear form. -/
def toSeminormFamily (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : SeminormFamily 𝕜 E F := fun y =>
  (B.flip y).toSeminorm

@[simp]
theorem toSeminormFamily_apply {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {x y} : (B.toSeminormFamily y) x = ‖B x y‖ :=
  rfl

end LinearMap

end BilinForm

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

theorem LinearMap.weakBilin_withSeminorms (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    WithSeminorms (LinearMap.toSeminormFamily B : F → Seminorm 𝕜 (WeakBilin B)) :=
  let e : F ≃ (Σ _ : F, Fin 1) := .symm <| .sigmaUnique _ _
  withSeminorms_induced (withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜 𝕜))
    (LinearMap.ltoFun 𝕜 F 𝕜 ∘ₗ B : (WeakBilin B) →ₗ[𝕜] (F → 𝕜)) |>.congr_equiv e

theorem LinearMap.hasBasis_weakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    (𝓝 (0 : WeakBilin B)).HasBasis B.toSeminormFamily.basisSets _root_.id :=
  LinearMap.weakBilin_withSeminorms B |>.hasBasis

end Topology

section LocallyConvex

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [NormedSpace ℝ 𝕜] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

instance WeakBilin.locallyConvexSpace {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} :
    LocallyConvexSpace ℝ (WeakBilin B) :=
  B.weakBilin_withSeminorms.toLocallyConvexSpace

end LocallyConvex
