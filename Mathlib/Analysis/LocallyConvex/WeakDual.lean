/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Data.Finsupp.Order
import Mathlib.LinearAlgebra.Dual.Lemmas

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
* [Rudin, *Functional Analysis*][rudin1991]

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

variable {ι 𝕜 E F : Type*}

open Topology TopologicalSpace
open scoped NNReal

section

section TopologicalRing

variable [Finite ι] [Field 𝕜] [t𝕜 : TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [T0Space 𝕜]

theorem mem_span_iff_continuous_of_finite {f : ι → E →ₗ[𝕜] 𝕜} (φ : E →ₗ[𝕜] 𝕜) :
    φ ∈ Submodule.span 𝕜 (Set.range f) ↔
    Continuous[⨅ i, induced (f i) t𝕜, t𝕜] φ := by
  let _ := ⨅ i, induced (f i) t𝕜
  constructor
  · exact Submodule.span_induction
      (Set.forall_mem_range.mpr fun i ↦ continuous_iInf_dom continuous_induced_dom) continuous_zero
      (fun _ _ _ _ ↦ .add) (fun c _ _ h ↦ h.const_smul c)
  · intro φ_cont
    refine mem_span_of_iInf_ker_le_ker fun x hx ↦ ?_
    simp_rw [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    have : Inseparable x 0 := by
      -- Maybe missing lemmas about `Inseparable`?
      simp_rw [Inseparable, nhds_iInf, nhds_induced, hx, map_zero]
    simpa only [map_zero] using (this.map φ_cont).eq

end TopologicalRing

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem mem_span_iff_continuous {f : ι → E →ₗ[𝕜] 𝕜} (φ : E →ₗ[𝕜] 𝕜) :
    φ ∈ Submodule.span 𝕜 (Set.range f) ↔
    Continuous[⨅ i, induced (f i) inferInstance, inferInstance] φ := by
  letI t𝕜 : TopologicalSpace 𝕜 := inferInstance
  let t := ⨅ i, induced (f i) t𝕜
  constructor
  -- TODO: is it worth factoring the first implication with `mem_span_iff_continuous_of_finite`?
  · exact Submodule.span_induction
      (Set.forall_mem_range.mpr fun i ↦ continuous_iInf_dom continuous_induced_dom) continuous_zero
      (fun _ _ _ _ ↦ .add) (fun c _ _ h ↦ h.const_smul c)
  · intro φ_cont
    obtain ⟨s, hs⟩ : ∃ s : Finset ι, Continuous[⨅ i : s, induced (f i) t𝕜, t𝕜] φ := by
      -- The following should be golfable by using/developping better API
      have : φ ⁻¹' (Metric.ball 0 1) ∈ 𝓝 0 :=
        φ_cont.continuousAt.tendsto (map_zero φ ▸ Metric.ball_mem_nhds (0 : 𝕜) one_pos)
      rw [nhds_iInf, Filter.mem_iInf_finite] at this
      rcases this with ⟨s, hs⟩
      use s
      let t' := ⨅ i : s, induced (f i) t𝕜
      have : IsTopologicalAddGroup E :=
        topologicalAddGroup_iInf fun _ ↦ topologicalAddGroup_induced _
      have : ContinuousSMul 𝕜 E :=
        continuousSMul_iInf fun _ ↦ continuousSMul_induced _
      rw [Seminorm.continuous_iff_continuous_comp (norm_withSeminorms 𝕜 𝕜), forall_const]
      refine Seminorm.continuous (r := 1) ?_
      rwa [nhds_iInf, Seminorm.ball_comp, ball_normSeminorm, iInf_subtype, map_zero]
    rw [← LinearMap.mem_span_iff_continuous_of_finite] at hs
    exact Submodule.span_mono (Set.range_comp_subset_range _ _) hs

theorem mem_span_iff_bound [Nonempty ι] {f : ι → E →ₗ[𝕜] 𝕜} (φ : E →ₗ[𝕜] 𝕜) :
    φ ∈ Submodule.span 𝕜 (Set.range f) ↔
    ∃ s : Finset ι, ∃ c : ℝ≥0, (normSeminorm 𝕜 𝕜).comp φ ≤
      c • (s.sup fun i ↦ (normSeminorm 𝕜 𝕜).comp (f i)) := by
  letI t𝕜 : TopologicalSpace 𝕜 := inferInstance
  let t := ⨅ i, induced (f i) t𝕜
  have : IsTopologicalAddGroup E := topologicalAddGroup_iInf fun _ ↦ topologicalAddGroup_induced _
  have : WithSeminorms (fun i ↦ (normSeminorm 𝕜 𝕜).comp (f i)) := by
    simp_rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, nhds_iInf, nhds_induced, map_zero,
      ← comap_norm_nhds_zero (E := 𝕜), Filter.comap_comap]
    rfl
  rw [LinearMap.mem_span_iff_continuous]
  constructor <;> intro H
  · rw [Seminorm.continuous_iff_continuous_comp (norm_withSeminorms 𝕜 𝕜), forall_const] at H
    rcases Seminorm.bound_of_continuous this _ H with ⟨s, C, -, hC⟩
    exact ⟨s, C, hC⟩
  · exact Seminorm.cont_withSeminorms_normedSpace _ this _ H

example [AddCommGroup F] [Module 𝕜 F] {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (f : E →ₗ[𝕜] 𝕜) :
    f ∈ Submodule.span 𝕜 (Set.range (B.flip)) ↔
    ∃ s : Finset F, ∃ (γ : NNReal), f.toSeminorm ≤ γ • (s.sup B.toSeminormFamily) := by
  apply mem_span_iff_bound f

end NontriviallyNormedField

end

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
