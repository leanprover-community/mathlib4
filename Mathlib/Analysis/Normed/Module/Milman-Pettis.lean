/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Topology.Algebra.Module.LinearMap

open scoped Topology NNReal

section opNorm

namespace ContinuousLinearMap

-- **TODO** Open PR moving these two, and removing `exists_lt_apply_of_lt_opNorm` away from `NNNorm`
variable {𝕜 𝕜' E F : Type*}
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [DenselyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NontriviallyNormedField 𝕜']
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜' F] {σ₁₂ : 𝕜 →+* 𝕜'} [RingHomIsometric σ₁₂]


theorem exists_nnorm_eq_one_lt_apply_of_lt_opNorm (f : E →SL[σ₁₂] F) {r : ℝ} (hr₀ : 0 ≤ r)
    (hr : r < ‖f‖) : ∃ x : E, ‖x‖ = 1 ∧ r < ‖f x‖ := by
  obtain ⟨x, hlt, hr⟩ := exists_lt_apply_of_lt_opNorm f hr
  obtain rfl | hx0 := eq_zero_or_norm_pos x
  · simp only [map_zero, norm_zero] at hr
    exact (not_lt_of_ge hr₀ hr).elim
  use algebraMap ℝ 𝕜 ‖x‖⁻¹ • x
  suffices r < ‖x‖⁻¹ * ‖f x‖ by simpa [norm_smul, inv_mul_cancel₀ hx0.ne'] using this
  calc
    r < 1⁻¹ * ‖f x‖ := by simpa
    _ < ‖x‖⁻¹ * ‖f x‖ := by
      gcongr; exact lt_of_le_of_lt hr₀ hr

theorem exists_nnorm_eq_one_lt_apply_of_lt_opNorm' [Nontrivial E]
    (f : E →SL[σ₁₂] F) {r : ℝ} (hr : r < ‖f‖) :
    ∃ x : E, ‖x‖ = 1 ∧ r < ‖f x‖ := by
  by_cases hr₀ : r < 0
  · obtain ⟨y, hy⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
    refine ⟨algebraMap ℝ 𝕜 ‖y‖⁻¹ • y, ?_, lt_of_lt_of_le hr₀ <| norm_nonneg _⟩
    calc ‖algebraMap ℝ 𝕜 ‖y‖⁻¹ • y‖ = ‖algebraMap ℝ 𝕜 ‖y‖⁻¹‖ * ‖y‖ := by rw [norm_smul]
                                  _ = ‖y‖⁻¹ * ‖y‖ := by simp_all [norm_inv]
                                  _ = 1 := by rw [inv_mul_cancel₀]; rwa [norm_ne_zero_iff]
  obtain ⟨x, hlt, hr⟩ := exists_lt_apply_of_lt_opNorm f hr
  obtain rfl | hx0 := eq_zero_or_norm_pos x
  · simp only [map_zero, norm_zero] at hr
    exact (hr₀ hr).elim
  use algebraMap ℝ 𝕜 ‖x‖⁻¹ • x
  suffices r < ‖x‖⁻¹ * ‖f x‖ by simpa [norm_smul, inv_mul_cancel₀ hx0.ne'] using this
  calc
    r < 1⁻¹ * ‖f x‖ := by simpa
    _ < ‖x‖⁻¹ * ‖f x‖ := by
      gcongr; exact lt_of_le_of_lt (le_of_not_gt hr₀) hr

end ContinuousLinearMap

end opNorm

variable {𝕜 𝕜₁ 𝕜₂ E E₁ E₂ : Type*} [RCLike 𝕜₂] [NontriviallyNormedField 𝕜] [NormedField 𝕜₁]
[NormedAddCommGroup E] [NormedSpace 𝕜 E] [Module ℝ E]
[SeminormedAddCommGroup E₁] [NormedSpace 𝕜₁ E₁]
[NormedAddCommGroup E₂] [NormedSpace 𝕜₂ E₂]

open Metric NormedSpace Function ContinuousLinearMap Pointwise

local notation3 "E**" => StrongDual 𝕜 (StrongDual 𝕜 E)
local notation3 "𝒰" => (inclusionInDoubleDual 𝕜₂ E₂) '' closedBall 0 1

-- **TODO**: Change name, generalise to every radious/centre, align assumptions with
-- `double_dual_bound`
-- lemma image_closedBall_subset_closedBall : 𝒰 ⊆ closedBall 0 1 := by
--   intro _ ⟨_, _, hxa⟩
--   grw [← hxa, mem_closedBall_zero_iff, double_dual_bound, ← mem_closedBall_zero_iff]
--   assumption

-- **FAE** serve RCLike, not-Semi(Normed)
lemma IsClosed_image_ball [CompleteSpace E₂] : IsClosed 𝒰 :=
    (inclusionInDoubleDualLi 𝕜₂ E₂).isometry.isClosedEmbedding.isClosedMap _ isClosed_closedBall

-- **FAE** serve Nontriviallynormed, basta SeminormedAddGroup
lemma WeakClosure_subset_closedBall {s : Set E**} {c : E**} {ε : ℝ} (hs : s ⊆ closedBall c ε) :
    letI 𝒯 : TopologicalSpace (WeakDual 𝕜 (StrongDual 𝕜 E)) := inferInstance
    (closure[𝒯] s) ⊆ closedBall (α := E**) c ε :=
  closure_minimal hs (WeakDual.isClosed_closedBall ..)


-- **TODO** Check not in Mathlib, miminise assumptions, golf proof.
lemma surjective_iff_sphere_subset_range [Algebra ℝ 𝕜₁]
    {F : Type*} [NormedAddCommGroup F] [Module 𝕜₁ F]
    [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜₁ F] [Module ℝ E₁] [IsScalarTower ℝ 𝕜₁ E₁]
    (f : E₁ →L[𝕜₁] F) : Surjective f ↔ ∃ ρ > 0, sphere 0 ρ ⊆ Set.range f := by
  refine ⟨fun _ ↦ ⟨1, by simp_all⟩, fun ⟨ρ, ρ_pos, sphere_le⟩ z ↦ ?_⟩
  by_cases hz : z = 0
  · exact ⟨0, by simp_all⟩
  set α := ‖z‖
  have hα : α ≠ 0 := by rwa [norm_ne_zero_iff]
  have h_mem : (ρ * α⁻¹) • z ∈ sphere 0 ρ := by
    simp only [mem_sphere_iff_norm, sub_zero]
    calc  ‖(ρ * α⁻¹) • z‖ = |ρ * α⁻¹| * |α| := by rw [norm_smul, Real.norm_eq_abs, abs_mul,
      abs_norm]
           _ = ρ := by simpa [← abs_mul, mul_assoc, inv_mul_cancel₀ hα] using le_of_lt ρ_pos
  obtain ⟨x, hx⟩ := sphere_le h_mem
  use (ρ⁻¹ * α) • x
  simp [hx, ← smul_assoc, show (ρ⁻¹ * α * (ρ * α⁻¹)) = 1 by grind]

lemma surjective_iff_closedBall_subset_range [Algebra ℝ 𝕜₁]
    {F : Type*} [NormedAddCommGroup F] [Module 𝕜₁ F]
    [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜₁ F] [Module ℝ E₁] [IsScalarTower ℝ 𝕜₁ E₁]
    (f : E₁ →L[𝕜₁] F) : Surjective f ↔ ∃ ρ > 0, closedBall 0 ρ ⊆ Set.range f :=
  ⟨fun _ ↦ ⟨1, by simp_all⟩,
  fun ⟨_, ρ_pos, sphere_le⟩ ↦ (surjective_iff_sphere_subset_range f).mpr ⟨_, ρ_pos, fun _ hx ↦
    sphere_le (sphere_subset_closedBall hx)⟩⟩

/-- Goldstine lemma (see Brezis, Chapter § 3.5, Lemma 3.4) says that the unit ball in the double
dual of a Banach space (**FAE: I suspect completeness is not needed) ** is the closure, with respect
to the weak topology `σ(E**, E*)` induced by the canonical pairing `E** × E* → ℝ`, of the image of
the unit ball in  `E`. Observe that, for any topological `𝕜`-module `M`, `strongDualPairing 𝕜 M` is
the pairing whose *first* variable is in `M*` and the second is in `M`. -/
axiom goldstine : closure (X := (WeakBilin (topDualPairing ℝ (StrongDual ℝ E))))
  (inclusionInDoubleDual ℝ E '' (closedBall 0 1)) = closedBall (0 : E**) 1-- := by sorry
-- **use**
-- theorem polar_flip_polar_eq {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {s : Set E} [Nonempty s] :
--     B.flip.polar (B.polar s) = closedAbsConvexHull (E := WeakBilin B) 𝕜 s := by


lemma exists_functional_sub_one_lt {ξ : E**} {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (h : ‖ξ‖ = 1) :
    ∃ φ : StrongDual ℝ E, ‖φ‖ = 1 ∧ |ξ φ - 1| < δ := by
  obtain ⟨φ, hφ_eq, hφ_lt⟩ := exists_nnorm_eq_one_lt_apply_of_lt_opNorm
    (f := ξ) (r := 1 - δ) (by grind) (by grind)
  replace hφ_lt : 1 - δ < |ξ φ| := by rwa [Real.norm_eq_abs] at hφ_lt
  wlog h_pos : 0 ≤ ξ φ generalizing φ
  · exact this (-φ) (by rw [opNorm_neg, hφ_eq]) (by simpa)
      (by simpa only [map_neg, Left.nonneg_neg_iff] using le_of_not_ge h_pos)
  have : ξ φ ≤ 1 := by
    apply le_of_abs_le
    grw [← Real.norm_eq_abs, le_opNorm ξ φ, h, hφ_eq, one_mul]
  refine ⟨φ, hφ_eq, ?_⟩
  rw [← abs_neg, neg_sub]
  rw [abs_eq_self.mpr (by grind)] at ⊢ hφ_lt
  rwa [sub_lt_comm]

lemma exists_ball_lt [UniformConvexSpace E] {ξ : E**} {ε : ℝ} (hε : 0 < ε)
    (hξ : ξ ∈ sphere 0 1) :
    letI 𝒯 : TopologicalSpace (WeakDual ℝ (StrongDual ℝ E)) := inferInstance
    ∃ W : Set E**, IsOpen[𝒯] W ∧ ξ ∈ W ∧ ∃ c, (W ∩ 𝒰) ⊆ closedBall c ε := by
  letI 𝒯 : TopologicalSpace (WeakDual ℝ (StrongDual ℝ E)) := inferInstance
  obtain ⟨δ', hδ₀, h_UniformConvex⟩ := exists_forall_closedBall_dist_lt E hε
  have hξ_norm : ‖ξ‖ = 1 := by rwa [← mem_sphere_zero_iff_norm]
  set δ := min δ' (1/2) with δ_def
  have hδ₀ : 0 < δ/2 := by positivity
  have hδ₁ : δ/2 < 1 := by
    calc δ/2 ≤ δ := by linarith
          _ =  min δ' (1/2) := by rfl
          _ ≤ (1/2) := min_le_right ..
          _ < 1 := by linarith
  obtain ⟨φ, hφ_norm, hφ_lt⟩ := exists_functional_sub_one_lt hδ₀ hδ₁ hξ_norm
  replace hφ_lt : |ξ φ - 1| < δ'/2 := by
    apply lt_of_lt_of_le hφ_lt
    rw [div_le_div_iff_of_pos_right (zero_lt_two), δ_def]
    exact min_le_left ..
  set V := {x : E** | |x φ - 1| < δ'/2} with hV_def
  have hξ_mem {V : Set _} (hV_mem : ξ ∈ V) (hV : IsOpen[𝒯] V) : ξ ∈ closure[𝒯] (V ∩ 𝒰) := by
    apply hV.inter_closure <| Set.mem_inter hV_mem _
    rw [goldstine]
    apply sphere_subset_closedBall hξ
  have hV_open : IsOpen[𝒯] V := by
    convert @Continuous.isOpen_preimage (X := WeakDual ℝ (StrongDual ℝ E)) (Y := ℝ) _ _
      (fun x : E** ↦ |x φ - 1|) (s := ball 0 (δ'/2)) _ isOpen_ball
    · ext
      simp_all
    · exact Continuous.comp (X := WeakDual ℝ (StrongDual ℝ E)) (g := fun (x : ℝ) ↦ |x - 1|)
        (by fun_prop) <| WeakBilin.eval_continuous (strongDualPairing ℝ (StrongDual ℝ E)) _
  refine ⟨V, hV_open, by simpa, ?_⟩
  obtain ⟨ϖ, hϖ⟩ : (V ∩ 𝒰).Nonempty := by
    rw [← closure_nonempty_iff (X := WeakDual ℝ (StrongDual ℝ E))]
    exact ⟨ξ, hξ_mem hφ_lt hV_open⟩
  use ϖ
  intro ζ hζ
  have {θ : E**} (hθ : θ ∈ V) : θ φ > 1 - δ'/2 := by
    rw [hV_def, Set.mem_setOf_eq, abs_sub_lt_iff] at hθ
    linarith
  rw [mem_closedBall_iff_norm]
  apply le_of_lt
  obtain ⟨z, hz_norm, hzζ⟩ := hζ.2
  obtain ⟨y, hy_norm, hyϖ⟩ := hϖ.2
  rw [← hzζ, ← hyϖ, ← map_sub, double_dual_norm_eq]
  apply h_UniformConvex (by rwa [← mem_closedBall_zero_iff]) (by rwa [← mem_closedBall_zero_iff])
  rw [← double_dual_norm_eq ℝ, map_add, hzζ, hyϖ]
  calc ‖ζ + ϖ‖ ≥ ‖(ζ + ϖ) φ‖ := by grw [(le_opNorm (f := ζ + ϖ) φ), hφ_norm, mul_one]
             _ = |ζ φ + ϖ φ| := by simp
             _ ≥ ζ φ + ϖ φ := le_abs_self ..
             _ > 1 - δ'/2 + 1 - δ'/2 := by linarith [this hζ.1, this hϖ.1]
             _ = 2 - δ' := by linarith


lemma sphere_subset_closure [Module ℝ E] [UniformConvexSpace E] : sphere 0 1 ⊆ closure 𝒰 := by
  let 𝒯 : TopologicalSpace <| WeakDual ℝ (StrongDual ℝ E) := inferInstance
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨W, hW, x_mem, c, hW_sub⟩ := exists_ball_lt (ε := ε/3) (by positivity) hx
  have hx_mem : x ∈ closure[𝒯] (W ∩ 𝒰) := by
    apply hW.inter_closure <| Set.mem_inter x_mem _
    rw [goldstine]
    exact sphere_subset_closedBall (α := E**) hx
  obtain ⟨y, hy_mem⟩ : (W ∩ 𝒰).Nonempty := by
    rw [← closure_nonempty_iff (X := WeakDual ℝ (StrongDual ℝ E))]
    use x
  refine ⟨y, hy_mem.2, ?_⟩
  suffices x ∈ closedBall c (ε/2) by
    apply lt_of_le_of_lt
    apply dist_triangle  (y := c)
    simp at this
    grw [hW_sub] at hy_mem
    simp only [mem_closedBall, dist_comm] at hy_mem
    grw [hy_mem, this]
    linarith
  apply WeakClosure_subset_closedBall _ hx_mem
  apply subset_trans hW_sub <| closedBall_subset_closedBall (by linarith)

lemma sphere_subset_image [CompleteSpace E] [UniformConvexSpace E] : sphere 0 1 ⊆ 𝒰 := by
  grw [sphere_subset_closure, IsClosed.closure_eq]
  exact IsClosed_image_ball

variable (E) [CompleteSpace E] [UniformConvexSpace E]

/- Milman-Pettis theorem: every uniformly convex Banach (**FAE: Complete Needed?**) space is
reflexive, stated as the surjectivity of `inclusionInDoubleDual`. For the version proving
this is a linear isometric equivalence, see `LinearIsometryEquiv_of_uniformConvexSpace`. -/
theorem surjective_of_uniformConvexSpace : Surjective (inclusionInDoubleDual ℝ E) :=
  (surjective_iff_sphere_subset_range _).mpr
    ⟨_, zero_lt_one, sphere_subset_image.trans <| Set.image_subset_range ..⟩

/-- Milman-Pettis theorem: every uniformly convex Banach (**FAE: Complete Needed?**) space is
reflexive. For a version proving only surjectivity, see `surjective_of_uniformConvexSpace`. -/
noncomputable
def LinearIsometryEquiv_of_uniformConvexSpace : E ≃ₗᵢ[ℝ] E** where
    __ := inclusionInDoubleDualLi ℝ E
    invFun := sorry
    left_inv := sorry
    right_inv := sorry

instance : Module.IsReflexive ℝ E where
  bijective_dual_eval' := by
    convert (LinearIsometryEquiv_of_uniformConvexSpace E).bijective
    sorry

-- alias milman_pettis := surjective_of_uniformConvexSpace
alias milman_pettis := LinearIsometryEquiv_of_uniformConvexSpace
