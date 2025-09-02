/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.NormedSpace.RCLike
/-!
# Finite dimensional topological vector spaces over `ℝ` satisfy the Tietze extension property

There are two main results here:

- `RCLike.instTietzeExtensionTVS`: finite dimensional topological vector spaces over `ℝ` (or `ℂ`)
  have the Tietze extension property.
- `BoundedContinuousFunction.exists_norm_eq_restrict_eq`: when mapping into a finite dimensional
  normed vector space over `ℝ` (or `ℂ`), the extension can be chosen to preserve the norm of the
  bounded continuous function it extends.

-/

universe u u₁ v w

-- this is not an instance because Lean cannot determine `𝕜`.
theorem TietzeExtension.of_tvs (𝕜 : Type v) [NontriviallyNormedField 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    [TietzeExtension.{u, v} 𝕜] : TietzeExtension.{u, w} E :=
  Module.Basis.ofVectorSpace 𝕜 E |>.equivFun.toContinuousLinearEquiv.toHomeomorph |> .of_homeo

instance Complex.instTietzeExtension : TietzeExtension ℂ :=
  TietzeExtension.of_tvs ℝ

instance (priority := 900) RCLike.instTietzeExtension {𝕜 : Type*} [RCLike 𝕜] :
    TietzeExtension 𝕜 := TietzeExtension.of_tvs ℝ

instance RCLike.instTietzeExtensionTVS {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} E :=
  TietzeExtension.of_tvs 𝕜

instance Set.instTietzeExtensionUnitBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} (Metric.ball (0 : E) 1) :=
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  .of_homeo Homeomorph.unitBall.symm

instance Set.instTietzeExtensionUnitClosedBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} (Metric.closedBall (0 : E) 1) := by
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := Real.isScalarTower
  -- I didn't find this retract in Mathlib.
  let g : E → E := fun x ↦ ‖x‖⁻¹ • x
  classical
  suffices this : Continuous (piecewise (Metric.closedBall 0 1) id g) by
    refine .of_retract ⟨Subtype.val, by fun_prop⟩ ⟨_, this.codRestrict fun x ↦ ?_⟩ ?_
    · by_cases hx : x ∈ Metric.closedBall 0 1
      · simpa [piecewise_eq_of_mem (hi := hx)] using hx
      · simp only [g, piecewise_eq_of_notMem (hi := hx), RCLike.real_smul_eq_coe_smul (K := 𝕜)]
        by_cases hx' : x = 0 <;> simp [hx']
    · ext x
      simp
  refine continuous_piecewise (fun x hx ↦ ?_) continuousOn_id ?_
  · replace hx : ‖x‖ = 1 := by simpa [frontier_closedBall (0 : E) one_ne_zero] using hx
    simp [g, hx]
  · refine continuousOn_id.norm.inv₀ ?_ |>.smul continuousOn_id
    simp only [closure_compl, interior_closedBall (0 : E) one_ne_zero, mem_compl_iff,
      Metric.mem_ball, dist_zero_right, not_lt, id_eq, ne_eq, norm_eq_zero]
    exact fun x hx ↦ norm_pos_iff.mp <| one_pos.trans_le hx

theorem Metric.instTietzeExtensionBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {r : ℝ} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.ball (0 : E) r) :=
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  .of_homeo <| show (Metric.ball (0 : E) r) ≃ₜ (Metric.ball (0 : E) 1) from
    PartialHomeomorph.unitBallBall (0 : E) r hr |>.toHomeomorphSourceTarget.symm

theorem Metric.instTietzeExtensionClosedBall (𝕜 : Type v) [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (y : E) {r : ℝ} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.closedBall y r) :=
  .of_homeo <| by
    change (Metric.closedBall y r) ≃ₜ (Metric.closedBall (0 : E) 1)
    symm
    apply (DilationEquiv.smulTorsor y (k := (r : 𝕜)) <| by exact_mod_cast hr.ne').toHomeomorph.sets
    ext x
    simp only [mem_closedBall, dist_zero_right, DilationEquiv.coe_toHomeomorph, Set.mem_preimage,
      DilationEquiv.smulTorsor_apply, vadd_eq_add, dist_add_self_left, norm_smul,
      RCLike.norm_ofReal, abs_of_nonneg hr.le]
    exact (mul_le_iff_le_one_right hr).symm

variable {X : Type u} [TopologicalSpace X] [NormalSpace X] {s : Set X} (hs : IsClosed s)
variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace BoundedContinuousFunction

include 𝕜 hs in
/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and bundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
theorem exists_norm_eq_restrict_eq (f : s →ᵇ E) :
    ∃ g : X →ᵇ E, ‖g‖ = ‖f‖ ∧ g.restrict s = f := by
  by_cases hf : ‖f‖ = 0; · exact ⟨0, by aesop⟩
  have := Metric.instTietzeExtensionClosedBall.{u, v} 𝕜 (0 : E) (by simp_all : 0 < ‖f‖)
  have hf' x : f x ∈ Metric.closedBall 0 ‖f‖ := by simpa using f.norm_coe_le_norm x
  obtain ⟨g, hg_mem, hg⟩ := (f : C(s, E)).exists_forall_mem_restrict_eq hs hf'
  simp only [Metric.mem_closedBall, dist_zero_right] at hg_mem
  let g' : X →ᵇ E := .ofNormedAddCommGroup g (map_continuous g) ‖f‖ hg_mem
  refine ⟨g', ?_, by ext x; congrm($(hg) x)⟩
  apply le_antisymm ((g'.norm_le <| by positivity).mpr hg_mem)
  refine (f.norm_le <| by positivity).mpr fun x ↦ ?_
  have hx : f x = g' x := by simpa using congr($(hg) x).symm
  rw [hx]
  exact g'.norm_le (norm_nonneg g') |>.mp le_rfl x

end BoundedContinuousFunction
