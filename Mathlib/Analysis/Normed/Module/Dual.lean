/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Data.Set.Finite.Lemmas

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

## References

* [Conway, John B., A course in functional analysis][conway1990]

## Tags

dual, polar
-/


noncomputable section

open Topology Bornology

universe u v

namespace NormedSpace

section General

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The topological dual of a seminormed space `E`. -/
abbrev Dual : Type _ := E →L[𝕜] 𝕜

-- TODO: helper instance for elaboration of inclusionInDoubleDual_norm_eq until
-- https://github.com/leanprover/lean4/issues/2522 is resolved; remove once fixed
instance : NormedSpace 𝕜 (Dual 𝕜 E) := inferInstance

-- TODO: helper instance for elaboration of inclusionInDoubleDual_norm_le until
-- https://github.com/leanprover/lean4/issues/2522 is resolved; remove once fixed
instance : SeminormedAddCommGroup (Dual 𝕜 E) := inferInstance

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusionInDoubleDual : E →L[𝕜] Dual 𝕜 (Dual 𝕜 E) :=
  ContinuousLinearMap.apply 𝕜 𝕜

@[simp]
theorem dual_def (x : E) (f : Dual 𝕜 E) : inclusionInDoubleDual 𝕜 E x f = f x :=
  rfl

theorem inclusionInDoubleDual_norm_eq :
    ‖inclusionInDoubleDual 𝕜 E‖ = ‖ContinuousLinearMap.id 𝕜 (Dual 𝕜 E)‖ :=
  ContinuousLinearMap.opNorm_flip _

theorem inclusionInDoubleDual_norm_le : ‖inclusionInDoubleDual 𝕜 E‖ ≤ 1 := by
  rw [inclusionInDoubleDual_norm_eq]
  exact ContinuousLinearMap.norm_id_le

theorem double_dual_bound (x : E) : ‖(inclusionInDoubleDual 𝕜 E) x‖ ≤ ‖x‖ := by
  simpa using ContinuousLinearMap.le_of_opNorm_le _ (inclusionInDoubleDual_norm_le 𝕜 E) x

/-- The dual pairing as a bilinear form. -/
def dualPairing : Dual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜

@[simp]
theorem dualPairing_apply {v : Dual 𝕜 E} {x : E} : dualPairing 𝕜 E v x = v x :=
  rfl

theorem dualPairing_separatingLeft : (dualPairing 𝕜 E).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective

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

theorem eq_zero_of_forall_dual_eq_zero {x : E} (h : ∀ f : Dual 𝕜 E, f x = (0 : 𝕜)) : x = 0 :=
  norm_le_zero_iff.mp (norm_le_dual_bound 𝕜 x le_rfl fun f => by simp [h f])

theorem eq_zero_iff_forall_dual_eq_zero (x : E) : x = 0 ↔ ∀ g : Dual 𝕜 E, g x = 0 :=
  ⟨fun hx => by simp [hx], fun h => eq_zero_of_forall_dual_eq_zero 𝕜 h⟩

/-- See also `geometric_hahn_banach_point_point`. -/
theorem eq_iff_forall_dual_eq {x y : E} : x = y ↔ ∀ g : Dual 𝕜 E, g x = g y := by
  rw [← sub_eq_zero, eq_zero_iff_forall_dual_eq_zero 𝕜 (x - y)]
  simp [sub_eq_zero]

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

end BidualIsometry

section PolarSets

open Metric Set NormedSpace

/-- Given a subset `s` in a normed space `E` (over a field `𝕜`), the polar
`polar 𝕜 s` is the subset of `Dual 𝕜 E` consisting of those functionals which
evaluate to something of norm at most one at all points `z ∈ s`. -/
def polar (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] : Set E → Set (Dual 𝕜 E) :=
  (dualPairing 𝕜 E).flip.polar

/-- Given a subset `s` in a normed space `E` (over a field `𝕜`) closed under scalar multiplication,
 the polar `polarSubmodule 𝕜 s` is the submodule of `Dual 𝕜 E` consisting of those functionals which
evaluate to zero at all points `z ∈ s`. -/
def polarSubmodule (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    Submodule 𝕜 (Dual 𝕜 E) := (dualPairing 𝕜 E).flip.polarSubmodule m

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma polarSubmodule_eq_polar (m : SubMulAction 𝕜 E) :
    (polarSubmodule 𝕜 m : Set (Dual 𝕜 E)) = polar 𝕜 m := rfl

theorem mem_polar_iff {x' : Dual 𝕜 E} (s : Set E) : x' ∈ polar 𝕜 s ↔ ∀ z ∈ s, ‖x' z‖ ≤ 1 :=
  Iff.rfl

lemma polarSubmodule_eq_setOf {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    polarSubmodule 𝕜 m = { y : Dual 𝕜 E | ∀ x ∈ m, y x = 0 } :=
  (dualPairing 𝕜 E).flip.polar_subMulAction _

lemma mem_polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) (y : Dual 𝕜 E) :
    y ∈ polarSubmodule 𝕜 m ↔ ∀ x ∈ m, y x = 0 := by
  have := polarSubmodule_eq_setOf 𝕜 m
  apply_fun (y ∈ ·) at this
  rwa [propext_iff] at this

@[simp]
theorem zero_mem_polar (s : Set E) : (0 : Dual 𝕜 E) ∈ polar 𝕜 s :=
  LinearMap.zero_mem_polar _ s

theorem polar_nonempty (s : Set E) : Set.Nonempty (polar 𝕜 s) :=
  LinearMap.polar_nonempty _ _

@[simp]
theorem polar_univ : polar 𝕜 (univ : Set E) = {(0 : Dual 𝕜 E)} :=
  (dualPairing 𝕜 E).flip.polar_univ
    (LinearMap.flip_separatingRight.mpr (dualPairing_separatingLeft 𝕜 E))

theorem isClosed_polar (s : Set E) : IsClosed (polar 𝕜 s) := by
  dsimp only [NormedSpace.polar]
  simp only [LinearMap.polar_eq_iInter, LinearMap.flip_apply]
  refine isClosed_biInter fun z _ => ?_
  exact isClosed_Iic.preimage (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous.norm

@[simp]
theorem polar_closure (s : Set E) : polar 𝕜 (closure s) = polar 𝕜 s :=
  ((dualPairing 𝕜 E).flip.polar_antitone subset_closure).antisymm <|
    (dualPairing 𝕜 E).flip.polar_gc.l_le <|
      closure_minimal ((dualPairing 𝕜 E).flip.polar_gc.le_u_l s) <| by
        simpa [LinearMap.flip_flip] using
          (isClosed_polar _ _).preimage (inclusionInDoubleDual 𝕜 E).continuous

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
    simp only [c_zero, norm_eq_zero, Ne, not_false_iff, inv_mul_cancel₀, norm_inv]
  rwa [cancel] at le

theorem polar_ball_subset_closedBall_div {c : 𝕜} (hc : 1 < ‖c‖) {r : ℝ} (hr : 0 < r) :
    polar 𝕜 (ball (0 : E) r) ⊆ closedBall (0 : Dual 𝕜 E) (‖c‖ / r) := by
  intro x' hx'
  rw [mem_polar_iff] at hx'
  simp only [polar, mem_setOf, mem_closedBall_zero_iff, mem_ball_zero_iff] at *
  have hcr : 0 < ‖c‖ / r := div_pos (zero_lt_one.trans hc) hr
  refine ContinuousLinearMap.opNorm_le_of_shell hr hcr.le hc fun x h₁ h₂ => ?_
  calc
    ‖x' x‖ ≤ 1 := hx' _ h₂
    _ ≤ ‖c‖ / r * ‖x‖ := (inv_le_iff_one_le_mul₀' hcr).1 (by rwa [inv_div])

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

/-- The `polar` of closed ball in a normed space `E` is the closed ball of the dual with
inverse radius. -/
theorem polar_closedBall {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}
    (hr : 0 < r) : polar 𝕜 (closedBall (0 : E) r) = closedBall (0 : Dual 𝕜 E) r⁻¹ := by
  refine Subset.antisymm ?_ (closedBall_inv_subset_polar_closedBall 𝕜)
  intro x' h
  simp only [mem_closedBall_zero_iff]
  refine ContinuousLinearMap.opNorm_le_of_ball hr (inv_nonneg.mpr hr.le) fun z _ => ?_
  simpa only [one_div] using LinearMap.bound_of_ball_bound' hr 1 x'.toLinearMap h z

theorem polar_ball {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}
    (hr : 0 < r) : polar 𝕜 (ball (0 : E) r) = closedBall (0 : Dual 𝕜 E) r⁻¹ := by
  apply le_antisymm
  · intro x hx
    rw [mem_closedBall_zero_iff]
    apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    rw [← mem_closedBall_zero_iff, ← (mul_div_cancel_left₀ a (Ne.symm (ne_of_lt hr)))]
    rw [← RCLike.norm_of_nonneg (K := 𝕜) (le_trans zero_le_one
      (le_of_lt ((inv_lt_iff_one_lt_mul₀' hr).mp ha)))]
    apply polar_ball_subset_closedBall_div _ hr hx
    rw [RCLike.norm_of_nonneg (K := 𝕜) (le_trans zero_le_one
      (le_of_lt ((inv_lt_iff_one_lt_mul₀' hr).mp ha)))]
    exact (inv_lt_iff_one_lt_mul₀' hr).mp ha
  · rw [← polar_closedBall hr]
    exact LinearMap.polar_antitone _ ball_subset_closedBall

/-- Given a neighborhood `s` of the origin in a normed space `E`, the dual norms
of all elements of the polar `polar 𝕜 s` are bounded by a constant. -/
theorem isBounded_polar_of_mem_nhds_zero {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
    IsBounded (polar 𝕜 s) := by
  obtain ⟨a, ha⟩ : ∃ a : 𝕜, 1 < ‖a‖ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, r_pos, r_ball⟩ : ∃ r : ℝ, 0 < r ∧ ball 0 r ⊆ s := Metric.mem_nhds_iff.1 s_nhd
  exact isBounded_closedBall.subset
    (((dualPairing 𝕜 E).flip.polar_antitone r_ball).trans <|
      polar_ball_subset_closedBall_div ha r_pos)

@[simp]
theorem polar_empty : polar 𝕜 (∅ : Set E) = Set.univ :=
  LinearMap.polar_empty _

@[simp]
theorem polar_singleton {a : E} : polar 𝕜 {a} = { x | ‖x a‖ ≤ 1 } := by
  simp only [polar, LinearMap.polar_singleton, LinearMap.flip_apply, dualPairing_apply]

theorem mem_polar_singleton {a : E} (y : Dual 𝕜 E) : y ∈ polar 𝕜 {a} ↔ ‖y a‖ ≤ 1 := by
  simp only [polar_singleton, mem_setOf_eq]

theorem polar_union {s t : Set E} : polar 𝕜 (s ∪ t) = polar 𝕜 s ∩ polar 𝕜 t :=
  (dualPairing 𝕜 E).flip.polar_union

theorem polar_iUnion {ι} {s : ι → Set E} : polar 𝕜 (⋃ i, s i) = ⋂ i, polar 𝕜 (s i) :=
  (dualPairing 𝕜 E).flip.polar_iUnion
theorem polar_zero : polar 𝕜 ({0} : Set E) = Set.univ :=
  LinearMap.polar_zero _

theorem sInter_polar_eq_closedBall {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {r : ℝ} (hr : 0 < r) :
    ⋂₀ (polar 𝕜 '' { F | F.Finite ∧ F ⊆ closedBall (0 : E) r⁻¹ }) = closedBall 0 r := by
  conv_rhs => rw [← inv_inv r]
  rw [← polar_closedBall (inv_pos_of_pos hr), polar,
    (dualPairing 𝕜 E).flip.sInter_polar_finite_subset_eq_polar (closedBall (0 : E) r⁻¹)]

end PolarSets

end NormedSpace
