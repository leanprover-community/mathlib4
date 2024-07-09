/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Analysis.LocallyConvex.Polar

#align_import analysis.normed_space.dual from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# The topological dual of a normed space

In this file we define the topological dual `NormedSpace.Dual` of a normed space, and the
continuous linear map `NormedSpace.inclusionInDoubleDual` from a normed space into its double
dual.

For base field `𝕜 = ℝ` or `𝕜 = ℂ`, this map is actually an isometric embedding; we provide a
version `NormedSpace.inclusionInDoubleDualLi` of the map which is of type a bundled linear
isometric embedding, `E →ₗᵢ[𝕜] (Dual 𝕜 (Dual 𝕜 E))`.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `SeminormedAddCommGroup` and we specialize to `NormedAddCommGroup` when needed.

## Main definitions

* `inclusionInDoubleDual` and `inclusionInDoubleDualLi` are the inclusion of a normed space
  in its double dual, considered as a bounded linear map and as a linear isometry, respectively.
* `polar 𝕜 s` is the subset of `Dual 𝕜 E` consisting of those functionals `x'` for which
  `‖x' z‖ ≤ 1` for every `z ∈ s`.

## Tags

dual
-/


noncomputable section

open scoped Classical
open Topology Bornology

universe u v

namespace NormedSpace

section General

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The topological dual of a seminormed space `E`. -/
abbrev Dual : Type _ := E →L[𝕜] 𝕜
#align normed_space.dual NormedSpace.Dual

-- TODO: helper instance for elaboration of inclusionInDoubleDual_norm_eq until
-- leanprover/lean4#2522 is resolved; remove once fixed
instance : NormedSpace 𝕜 (Dual 𝕜 E) := inferInstance

-- TODO: helper instance for elaboration of inclusionInDoubleDual_norm_le until
-- leanprover/lean4#2522 is resolved; remove once fixed
instance : SeminormedAddCommGroup (Dual 𝕜 E) := inferInstance

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusionInDoubleDual : E →L[𝕜] Dual 𝕜 (Dual 𝕜 E) :=
  ContinuousLinearMap.apply 𝕜 𝕜
#align normed_space.inclusion_in_double_dual NormedSpace.inclusionInDoubleDual

@[simp]
theorem dual_def (x : E) (f : Dual 𝕜 E) : inclusionInDoubleDual 𝕜 E x f = f x :=
  rfl
#align normed_space.dual_def NormedSpace.dual_def

theorem inclusionInDoubleDual_norm_eq :
    ‖inclusionInDoubleDual 𝕜 E‖ = ‖ContinuousLinearMap.id 𝕜 (Dual 𝕜 E)‖ :=
  ContinuousLinearMap.opNorm_flip _
#align normed_space.inclusion_in_double_dual_norm_eq NormedSpace.inclusionInDoubleDual_norm_eq

theorem inclusionInDoubleDual_norm_le : ‖inclusionInDoubleDual 𝕜 E‖ ≤ 1 := by
  rw [inclusionInDoubleDual_norm_eq]
  exact ContinuousLinearMap.norm_id_le
#align normed_space.inclusion_in_double_dual_norm_le NormedSpace.inclusionInDoubleDual_norm_le

theorem double_dual_bound (x : E) : ‖(inclusionInDoubleDual 𝕜 E) x‖ ≤ ‖x‖ := by
  simpa using ContinuousLinearMap.le_of_opNorm_le _ (inclusionInDoubleDual_norm_le 𝕜 E) x
#align normed_space.double_dual_bound NormedSpace.double_dual_bound

/-- The dual pairing as a bilinear form. -/
def dualPairing : Dual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜
#align normed_space.dual_pairing NormedSpace.dualPairing

@[simp]
theorem dualPairing_apply {v : Dual 𝕜 E} {x : E} : dualPairing 𝕜 E v x = v x :=
  rfl
#align normed_space.dual_pairing_apply NormedSpace.dualPairing_apply

theorem dualPairing_separatingLeft : (dualPairing 𝕜 E).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective
#align normed_space.dual_pairing_separating_left NormedSpace.dualPairing_separatingLeft

end General

section BidualIsometry

variable (𝕜 : Type v) [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `ContinuousLinearMap.opNorm_le_bound`. -/
theorem norm_le_dual_bound (x : E) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ f : Dual 𝕜 E, ‖f x‖ ≤ M * ‖f‖) :
    ‖x‖ ≤ M := by
  classical
    by_cases h : x = 0
    · simp only [h, hMp, norm_zero]
    · obtain ⟨f, hf₁, hfx⟩ : ∃ f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x = ‖x‖ := exists_dual_vector 𝕜 x h
      calc
        ‖x‖ = ‖(‖x‖ : 𝕜)‖ := RCLike.norm_coe_norm.symm
        _ = ‖f x‖ := by rw [hfx]
        _ ≤ M * ‖f‖ := hM f
        _ = M := by rw [hf₁, mul_one]
#align normed_space.norm_le_dual_bound NormedSpace.norm_le_dual_bound

theorem eq_zero_of_forall_dual_eq_zero {x : E} (h : ∀ f : Dual 𝕜 E, f x = (0 : 𝕜)) : x = 0 :=
  norm_le_zero_iff.mp (norm_le_dual_bound 𝕜 x le_rfl fun f => by simp [h f])
#align normed_space.eq_zero_of_forall_dual_eq_zero NormedSpace.eq_zero_of_forall_dual_eq_zero

theorem eq_zero_iff_forall_dual_eq_zero (x : E) : x = 0 ↔ ∀ g : Dual 𝕜 E, g x = 0 :=
  ⟨fun hx => by simp [hx], fun h => eq_zero_of_forall_dual_eq_zero 𝕜 h⟩
#align normed_space.eq_zero_iff_forall_dual_eq_zero NormedSpace.eq_zero_iff_forall_dual_eq_zero

/-- See also `geometric_hahn_banach_point_point`. -/
theorem eq_iff_forall_dual_eq {x y : E} : x = y ↔ ∀ g : Dual 𝕜 E, g x = g y := by
  rw [← sub_eq_zero, eq_zero_iff_forall_dual_eq_zero 𝕜 (x - y)]
  simp [sub_eq_zero]
#align normed_space.eq_iff_forall_dual_eq NormedSpace.eq_iff_forall_dual_eq

/-- The inclusion of a normed space in its double dual is an isometry onto its image. -/
def inclusionInDoubleDualLi : E →ₗᵢ[𝕜] Dual 𝕜 (Dual 𝕜 E) :=
  { inclusionInDoubleDual 𝕜 E with
    norm_map' := by
      intro x
      apply le_antisymm
      · exact double_dual_bound 𝕜 E x
      rw [ContinuousLinearMap.norm_def]
      refine le_csInf ContinuousLinearMap.bounds_nonempty ?_
      rintro c ⟨hc1, hc2⟩
      exact norm_le_dual_bound 𝕜 x hc1 hc2 }
#align normed_space.inclusion_in_double_dual_li NormedSpace.inclusionInDoubleDualLi

end BidualIsometry

section PolarSets

open Metric Set NormedSpace

/-- Given a subset `s` in a normed space `E` (over a field `𝕜`), the polar
`polar 𝕜 s` is the subset of `Dual 𝕜 E` consisting of those functionals which
evaluate to something of norm at most one at all points `z ∈ s`. -/
def polar (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] : Set E → Set (Dual 𝕜 E) :=
  (dualPairing 𝕜 E).flip.polar
#align normed_space.polar NormedSpace.polar

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem mem_polar_iff {x' : Dual 𝕜 E} (s : Set E) : x' ∈ polar 𝕜 s ↔ ∀ z ∈ s, ‖x' z‖ ≤ 1 :=
  Iff.rfl
#align normed_space.mem_polar_iff NormedSpace.mem_polar_iff

@[simp]
theorem polar_univ : polar 𝕜 (univ : Set E) = {(0 : Dual 𝕜 E)} :=
  (dualPairing 𝕜 E).flip.polar_univ
    (LinearMap.flip_separatingRight.mpr (dualPairing_separatingLeft 𝕜 E))
#align normed_space.polar_univ NormedSpace.polar_univ

theorem isClosed_polar (s : Set E) : IsClosed (polar 𝕜 s) := by
  dsimp only [NormedSpace.polar]
  simp only [LinearMap.polar_eq_iInter, LinearMap.flip_apply]
  refine isClosed_biInter fun z _ => ?_
  exact isClosed_Iic.preimage (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous.norm
#align normed_space.is_closed_polar NormedSpace.isClosed_polar

@[simp]
theorem polar_closure (s : Set E) : polar 𝕜 (closure s) = polar 𝕜 s :=
  ((dualPairing 𝕜 E).flip.polar_antitone subset_closure).antisymm <|
    (dualPairing 𝕜 E).flip.polar_gc.l_le <|
      closure_minimal ((dualPairing 𝕜 E).flip.polar_gc.le_u_l s) <| by
        simpa [LinearMap.flip_flip] using
          (isClosed_polar _ _).preimage (inclusionInDoubleDual 𝕜 E).continuous
#align normed_space.polar_closure NormedSpace.polar_closure

variable {𝕜}

/-- If `x'` is a dual element such that the norms `‖x' z‖` are bounded for `z ∈ s`, then a
small scalar multiple of `x'` is in `polar 𝕜 s`. -/
theorem smul_mem_polar {s : Set E} {x' : Dual 𝕜 E} {c : 𝕜} (hc : ∀ z, z ∈ s → ‖x' z‖ ≤ ‖c‖) :
    c⁻¹ • x' ∈ polar 𝕜 s := by
  by_cases c_zero : c = 0
  · simp only [c_zero, inv_zero, zero_smul]
    exact (dualPairing 𝕜 E).flip.zero_mem_polar _
  have eq : ∀ z, ‖c⁻¹ • x' z‖ = ‖c⁻¹‖ * ‖x' z‖ := fun z => norm_smul c⁻¹ _
  have le : ∀ z, z ∈ s → ‖c⁻¹ • x' z‖ ≤ ‖c⁻¹‖ * ‖c‖ := by
    intro z hzs
    rw [eq z]
    apply mul_le_mul (le_of_eq rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _)
  have cancel : ‖c⁻¹‖ * ‖c‖ = 1 := by
    simp only [c_zero, norm_eq_zero, Ne, not_false_iff, inv_mul_cancel, norm_inv]
  rwa [cancel] at le
#align normed_space.smul_mem_polar NormedSpace.smul_mem_polar

theorem polar_ball_subset_closedBall_div {c : 𝕜} (hc : 1 < ‖c‖) {r : ℝ} (hr : 0 < r) :
    polar 𝕜 (ball (0 : E) r) ⊆ closedBall (0 : Dual 𝕜 E) (‖c‖ / r) := by
  intro x' hx'
  rw [mem_polar_iff] at hx'
  simp only [polar, mem_setOf, mem_closedBall_zero_iff, mem_ball_zero_iff] at *
  have hcr : 0 < ‖c‖ / r := div_pos (zero_lt_one.trans hc) hr
  refine ContinuousLinearMap.opNorm_le_of_shell hr hcr.le hc fun x h₁ h₂ => ?_
  calc
    ‖x' x‖ ≤ 1 := hx' _ h₂
    _ ≤ ‖c‖ / r * ‖x‖ := (inv_pos_le_iff_one_le_mul' hcr).1 (by rwa [inv_div])
#align normed_space.polar_ball_subset_closed_ball_div NormedSpace.polar_ball_subset_closedBall_div

variable (𝕜)

theorem closedBall_inv_subset_polar_closedBall {r : ℝ} :
    closedBall (0 : Dual 𝕜 E) r⁻¹ ⊆ polar 𝕜 (closedBall (0 : E) r) := fun x' hx' x hx =>
  calc
    ‖x' x‖ ≤ ‖x'‖ * ‖x‖ := x'.le_opNorm x
    _ ≤ r⁻¹ * r :=
      (mul_le_mul (mem_closedBall_zero_iff.1 hx') (mem_closedBall_zero_iff.1 hx) (norm_nonneg _)
        (dist_nonneg.trans hx'))
    _ = r / r := inv_mul_eq_div _ _
    _ ≤ 1 := div_self_le_one r
#align normed_space.closed_ball_inv_subset_polar_closed_ball NormedSpace.closedBall_inv_subset_polar_closedBall

/-- The `polar` of closed ball in a normed space `E` is the closed ball of the dual with
inverse radius. -/
theorem polar_closedBall {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}
    (hr : 0 < r) : polar 𝕜 (closedBall (0 : E) r) = closedBall (0 : Dual 𝕜 E) r⁻¹ := by
  refine Subset.antisymm ?_ (closedBall_inv_subset_polar_closedBall 𝕜)
  intro x' h
  simp only [mem_closedBall_zero_iff]
  refine ContinuousLinearMap.opNorm_le_of_ball hr (inv_nonneg.mpr hr.le) fun z _ => ?_
  simpa only [one_div] using LinearMap.bound_of_ball_bound' hr 1 x'.toLinearMap h z
#align normed_space.polar_closed_ball NormedSpace.polar_closedBall

/-- Given a neighborhood `s` of the origin in a normed space `E`, the dual norms
of all elements of the polar `polar 𝕜 s` are bounded by a constant. -/
theorem isBounded_polar_of_mem_nhds_zero {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
    IsBounded (polar 𝕜 s) := by
  obtain ⟨a, ha⟩ : ∃ a : 𝕜, 1 < ‖a‖ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, r_pos, r_ball⟩ : ∃ r : ℝ, 0 < r ∧ ball 0 r ⊆ s := Metric.mem_nhds_iff.1 s_nhd
  exact isBounded_closedBall.subset
    (((dualPairing 𝕜 E).flip.polar_antitone r_ball).trans <|
      polar_ball_subset_closedBall_div ha r_pos)
#align normed_space.bounded_polar_of_mem_nhds_zero NormedSpace.isBounded_polar_of_mem_nhds_zero

end PolarSets

end NormedSpace
