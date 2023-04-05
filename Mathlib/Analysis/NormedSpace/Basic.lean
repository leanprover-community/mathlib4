/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module analysis.normed_space.basic
! leanprover-community/mathlib commit d3af0609f6db8691dffdc3e1fb7feb7da72698f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Pi
import Mathbin.Algebra.Algebra.RestrictScalars
import Mathbin.Analysis.Normed.Field.Basic
import Mathbin.Data.Real.Sqrt
import Mathbin.Topology.Algebra.Module.Basic

/-!
# Normed spaces

In this file we define (semi)normed spaces and algebras. We also prove some theorems
about these definitions.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {ι : Type _}

open Filter Metric Function Set

open Topology BigOperators NNReal ENNReal uniformity Pointwise

section SeminormedAddCommGroup

section Prio

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option extends_priority -/
set_option extends_priority 920

-- Here, we set a rather high priority for the instance `[normed_space α β] : module α β`
-- to take precedence over `semiring.to_module` as this leads to instance paths with better
-- unification properties.
/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `‖c • x‖ = ‖c‖ ‖x‖`. We require only `‖c • x‖ ≤ ‖c‖ ‖x‖` in the definition, then prove
`‖c • x‖ = ‖c‖ ‖x‖` in `norm_smul`.

Note that since this requires `seminormed_add_comm_group` and not `normed_add_comm_group`, this
typeclass can be used for "semi normed spaces" too, just as `module` can be used for
"semi modules". -/
class NormedSpace (α : Type _) (β : Type _) [NormedField α] [SeminormedAddCommGroup β] extends
  Module α β where
  norm_smul_le : ∀ (a : α) (b : β), ‖a • b‖ ≤ ‖a‖ * ‖b‖
#align normed_space NormedSpace

end Prio

variable [NormedField α] [SeminormedAddCommGroup β]

-- note: while these are currently strictly weaker than the versions without `le`, they will cease
-- to be if we eventually generalize `normed_space` from `normed_field α` to `normed_ring α`.
section Le

theorem norm_smul_le [NormedSpace α β] (r : α) (x : β) : ‖r • x‖ ≤ ‖r‖ * ‖x‖ :=
  NormedSpace.norm_smul_le _ _
#align norm_smul_le norm_smul_le

theorem nnnorm_smul_le [NormedSpace α β] (s : α) (x : β) : ‖s • x‖₊ ≤ ‖s‖₊ * ‖x‖₊ :=
  norm_smul_le s x
#align nnnorm_smul_le nnnorm_smul_le

theorem dist_smul_le [NormedSpace α β] (s : α) (x y : β) : dist (s • x) (s • y) ≤ ‖s‖ * dist x y :=
  by simpa only [dist_eq_norm, ← smul_sub] using norm_smul_le _ _
#align dist_smul_le dist_smul_le

theorem nndist_smul_le [NormedSpace α β] (s : α) (x y : β) :
    nndist (s • x) (s • y) ≤ ‖s‖₊ * nndist x y :=
  dist_smul_le s x y
#align nndist_smul_le nndist_smul_le

end Le

-- see Note [lower instance priority]
instance (priority := 100) NormedSpace.boundedSMul [NormedSpace α β] : BoundedSMul α β
    where
  dist_smul_pair' x y₁ y₂ := by simpa [dist_eq_norm, smul_sub] using norm_smul_le x (y₁ - y₂)
  dist_pair_smul' x₁ x₂ y := by simpa [dist_eq_norm, sub_smul] using norm_smul_le (x₁ - x₂) y
#align normed_space.has_bounded_smul NormedSpace.boundedSMul

-- Shortcut instance, as otherwise this will be found by `normed_space.to_module` and be
-- noncomputable.
instance : Module ℝ ℝ := by infer_instance

instance NormedField.toNormedSpace : NormedSpace α α where norm_smul_le a b := norm_mul_le a b
#align normed_field.to_normed_space NormedField.toNormedSpace

theorem norm_smul [NormedSpace α β] (s : α) (x : β) : ‖s • x‖ = ‖s‖ * ‖x‖ :=
  by
  by_cases h : s = 0
  · simp [h]
  · refine' le_antisymm (norm_smul_le s x) _
    calc
      ‖s‖ * ‖x‖ = ‖s‖ * ‖s⁻¹ • s • x‖ := by rw [inv_smul_smul₀ h]
      _ ≤ ‖s‖ * (‖s⁻¹‖ * ‖s • x‖) := (mul_le_mul_of_nonneg_left (norm_smul_le _ _) (norm_nonneg _))
      _ = ‖s • x‖ := by rw [norm_inv, ← mul_assoc, mul_inv_cancel (mt norm_eq_zero.1 h), one_mul]
      
#align norm_smul norm_smul

theorem norm_zsmul (α) [NormedField α] [NormedSpace α β] (n : ℤ) (x : β) :
    ‖n • x‖ = ‖(n : α)‖ * ‖x‖ := by rw [← norm_smul, ← Int.smul_one_eq_coe, smul_assoc, one_smul]
#align norm_zsmul norm_zsmul

@[simp]
theorem abs_norm_eq_norm (z : β) : |‖z‖| = ‖z‖ :=
  (abs_eq (norm_nonneg z)).mpr (Or.inl rfl)
#align abs_norm_eq_norm abs_norm_eq_norm

theorem inv_norm_smul_mem_closed_unit_ball [NormedSpace ℝ β] (x : β) :
    ‖x‖⁻¹ • x ∈ closedBall (0 : β) 1 := by
  simp only [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul,
    div_self_le_one]
#align inv_norm_smul_mem_closed_unit_ball inv_norm_smul_mem_closed_unit_ball

theorem dist_smul₀ [NormedSpace α β] (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * dist x y := by
  simp only [dist_eq_norm, (norm_smul _ _).symm, smul_sub]
#align dist_smul₀ dist_smul₀

theorem nnnorm_smul [NormedSpace α β] (s : α) (x : β) : ‖s • x‖₊ = ‖s‖₊ * ‖x‖₊ :=
  NNReal.eq <| norm_smul s x
#align nnnorm_smul nnnorm_smul

theorem nndist_smul₀ [NormedSpace α β] (s : α) (x y : β) :
    nndist (s • x) (s • y) = ‖s‖₊ * nndist x y :=
  NNReal.eq <| dist_smul₀ s x y
#align nndist_smul₀ nndist_smul₀

theorem lipschitzWith_smul [NormedSpace α β] (s : α) : LipschitzWith ‖s‖₊ ((· • ·) s : β → β) :=
  lipschitzWith_iff_dist_le_mul.2 fun x y => by rw [dist_smul₀, coe_nnnorm]
#align lipschitz_with_smul lipschitzWith_smul

theorem norm_smul_of_nonneg [NormedSpace ℝ β] {t : ℝ} (ht : 0 ≤ t) (x : β) : ‖t • x‖ = t * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
#align norm_smul_of_nonneg norm_smul_of_nonneg

variable {E : Type _} [SeminormedAddCommGroup E] [NormedSpace α E]

variable {F : Type _} [SeminormedAddCommGroup F] [NormedSpace α F]

theorem eventually_nhds_norm_smul_sub_lt (c : α) (x : E) {ε : ℝ} (h : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ‖c • (y - x)‖ < ε :=
  have : Tendsto (fun y => ‖c • (y - x)‖) (𝓝 x) (𝓝 0) :=
    ((continuous_id.sub continuous_const).const_smul _).norm.tendsto' _ _ (by simp)
  this.Eventually (gt_mem_nhds h)
#align eventually_nhds_norm_smul_sub_lt eventually_nhds_norm_smul_sub_lt

theorem Filter.Tendsto.zero_smul_isBoundedUnder_le {f : ι → α} {g : ι → E} {l : Filter ι}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l (norm ∘ g)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· • ·) norm_smul_le
#align filter.tendsto.zero_smul_is_bounded_under_le Filter.Tendsto.zero_smul_isBoundedUnder_le

theorem Filter.IsBoundedUnder.smul_tendsto_zero {f : ι → α} {g : ι → E} {l : Filter ι}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· • ·)) fun x y =>
    (norm_smul_le y x).trans_eq (mul_comm _ _)
#align filter.is_bounded_under.smul_tendsto_zero Filter.IsBoundedUnder.smul_tendsto_zero

theorem closure_ball [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    closure (ball x r) = closedBall x r :=
  by
  refine' subset.antisymm closure_ball_subset_closed_ball fun y hy => _
  have : ContinuousWithinAt (fun c : ℝ => c • (y - x) + x) (Ico 0 1) 1 :=
    ((continuous_id.smul continuous_const).add continuous_const).ContinuousWithinAt
  convert this.mem_closure _ _
  · rw [one_smul, sub_add_cancel]
  · simp [closure_Ico zero_ne_one, zero_le_one]
  · rintro c ⟨hc0, hc1⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0,
      mul_comm, ← mul_one r]
    rw [mem_closed_ball, dist_eq_norm] at hy
    replace hr : 0 < r
    exact ((norm_nonneg _).trans hy).lt_of_ne hr.symm
    apply mul_lt_mul' <;> assumption
#align closure_ball closure_ball

theorem frontier_ball [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    frontier (ball x r) = sphere x r :=
  by
  rw [frontier, closure_ball x hr, is_open_ball.interior_eq]
  ext x; exact (@eq_iff_le_not_lt ℝ _ _ _).symm
#align frontier_ball frontier_ball

theorem interior_closedBall [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    interior (closedBall x r) = ball x r :=
  by
  cases' hr.lt_or_lt with hr hr
  · rw [closed_ball_eq_empty.2 hr, ball_eq_empty.2 hr.le, interior_empty]
  refine' subset.antisymm _ ball_subset_interior_closed_ball
  intro y hy
  rcases(mem_closed_ball.1 <| interior_subset hy).lt_or_eq with (hr | rfl)
  · exact hr
  set f : ℝ → E := fun c : ℝ => c • (y - x) + x
  suffices f ⁻¹' closed_ball x (dist y x) ⊆ Icc (-1) 1
    by
    have hfc : Continuous f := (continuous_id.smul continuous_const).add continuous_const
    have hf1 : (1 : ℝ) ∈ f ⁻¹' interior (closed_ball x <| dist y x) := by simpa [f]
    have h1 : (1 : ℝ) ∈ interior (Icc (-1 : ℝ) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage hfc hf1)
    contrapose h1
    simp
  intro c hc
  rw [mem_Icc, ← abs_le, ← Real.norm_eq_abs, ← mul_le_mul_right hr]
  simpa [f, dist_eq_norm, norm_smul] using hc
#align interior_closed_ball interior_closedBall

theorem frontier_closedBall [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    frontier (closedBall x r) = sphere x r := by
  rw [frontier, closure_closed_ball, interior_closedBall x hr, closed_ball_diff_ball]
#align frontier_closed_ball frontier_closedBall

instance {E : Type _} [NormedAddCommGroup E] [NormedSpace ℚ E] (e : E) :
    DiscreteTopology <| AddSubgroup.zmultiples e :=
  by
  rcases eq_or_ne e 0 with (rfl | he)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    infer_instance
  · rw [discreteTopology_iff_open_singleton_zero, isOpen_induced_iff]
    refine' ⟨Metric.ball 0 ‖e‖, Metric.isOpen_ball, _⟩
    ext ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := add_subgroup.mem_zmultiples_iff.mp hx
    rw [mem_preimage, mem_ball_zero_iff, AddSubgroup.coe_mk, mem_singleton_iff, Subtype.ext_iff,
      AddSubgroup.coe_mk, AddSubgroup.coe_zero, norm_zsmul ℚ k e, Int.norm_cast_rat,
      Int.norm_eq_abs, ← Int.cast_abs, mul_lt_iff_lt_one_left (norm_pos_iff.mpr he), ←
      @Int.cast_one ℝ _, Int.cast_lt, Int.abs_lt_one_iff, smul_eq_zero, or_iff_left he]

/-- A (semi) normed real vector space is homeomorphic to the unit ball in the same space.
This homeomorphism sends `x : E` to `(1 + ‖x‖²)^(- ½) • x`.

In many cases the actual implementation is not important, so we don't mark the projection lemmas
`homeomorph_unit_ball_apply_coe` and `homeomorph_unit_ball_symm_apply` as `@[simp]`.

See also `cont_diff_homeomorph_unit_ball` and `cont_diff_on_homeomorph_unit_ball_symm` for
smoothness properties that hold when `E` is an inner-product space. -/
@[simps (config := { attrs := [] })]
noncomputable def homeomorphUnitBall [NormedSpace ℝ E] : E ≃ₜ ball (0 : E) 1
    where
  toFun x :=
    ⟨(1 + ‖x‖ ^ 2).sqrt⁻¹ • x, by
      have : 0 < 1 + ‖x‖ ^ 2 := by positivity
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, ← div_eq_inv_mul,
        div_lt_one (abs_pos.mpr <| real.sqrt_ne_zero'.mpr this), ← abs_norm_eq_norm x, ← sq_lt_sq,
        abs_norm_eq_norm, Real.sq_sqrt this.le]
      exact lt_one_add _⟩
  invFun y := (1 - ‖(y : E)‖ ^ 2).sqrt⁻¹ • (y : E)
  left_inv x := by
    field_simp [norm_smul, smul_smul, (zero_lt_one_add_norm_sq x).ne',
      Real.sq_sqrt (zero_lt_one_add_norm_sq x).le, ← Real.sqrt_div (zero_lt_one_add_norm_sq x).le]
  right_inv y :=
    by
    have : 0 < 1 - ‖(y : E)‖ ^ 2 := by
      nlinarith [norm_nonneg (y : E), (mem_ball_zero_iff.1 y.2 : ‖(y : E)‖ < 1)]
    field_simp [norm_smul, smul_smul, this.ne', Real.sq_sqrt this.le, ← Real.sqrt_div this.le]
  continuous_toFun := by
    suffices : Continuous fun x => (1 + ‖x‖ ^ 2).sqrt⁻¹;
    exact (this.smul continuous_id).subtype_mk _
    refine' Continuous.inv₀ _ fun x => real.sqrt_ne_zero'.mpr (by positivity)
    continuity
  continuous_invFun :=
    by
    suffices ∀ y : ball (0 : E) 1, (1 - ‖(y : E)‖ ^ 2).sqrt ≠ 0 by continuity
    intro y
    rw [Real.sqrt_ne_zero']
    nlinarith [norm_nonneg (y : E), (mem_ball_zero_iff.1 y.2 : ‖(y : E)‖ < 1)]
#align homeomorph_unit_ball homeomorphUnitBall

@[simp]
theorem coe_homeomorphUnitBall_apply_zero [NormedSpace ℝ E] :
    (homeomorphUnitBall (0 : E) : E) = 0 := by simp [homeomorphUnitBall]
#align coe_homeomorph_unit_ball_apply_zero coe_homeomorphUnitBall_apply_zero

open NormedField

instance : NormedSpace α (ULift E) :=
  { ULift.normedAddCommGroup, ULift.module' with
    norm_smul_le := fun s x => (norm_smul_le s x.down : _) }

/-- The product of two normed spaces is a normed space, with the sup norm. -/
instance Prod.normedSpace : NormedSpace α (E × F) :=
  { Prod.normedAddCommGroup, Prod.module with
    norm_smul_le := fun s x => by simp [Prod.norm_def, norm_smul_le, mul_max_of_nonneg] }
#align prod.normed_space Prod.normedSpace

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance Pi.normedSpace {E : ι → Type _} [Fintype ι] [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace α (E i)] : NormedSpace α (∀ i, E i)
    where norm_smul_le a f :=
    by
    simp_rw [← coe_nnnorm, ← NNReal.coe_mul, NNReal.coe_le_coe, Pi.nnnorm_def,
      NNReal.mul_finset_sup]
    exact Finset.sup_mono_fun fun _ _ => norm_smul_le _ _
#align pi.normed_space Pi.normedSpace

instance MulOpposite.normedSpace : NormedSpace α Eᵐᵒᵖ :=
  { MulOpposite.normedAddCommGroup, MulOpposite.module _ with
    norm_smul_le := fun s x => norm_smul_le s x.unop }
#align mul_opposite.normed_space MulOpposite.normedSpace

/-- A subspace of a normed space is also a normed space, with the restriction of the norm. -/
instance Submodule.normedSpace {𝕜 R : Type _} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] {E : Type _}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E]
    (s : Submodule R E) : NormedSpace 𝕜 s where norm_smul_le c x := norm_smul_le c (x : E)
#align submodule.normed_space Submodule.normedSpace

/-- If there is a scalar `c` with `‖c‖>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
theorem rescale_to_shell_semi_normed_zpow {c : α} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E}
    (hx : ‖x‖ ≠ 0) :
    ∃ n : ℤ, c ^ n ≠ 0 ∧ ‖c ^ n • x‖ < ε ∧ ε / ‖c‖ ≤ ‖c ^ n • x‖ ∧ ‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖ :=
  by
  have xεpos : 0 < ‖x‖ / ε := div_pos ((Ne.symm hx).le_iff_lt.1 (norm_nonneg x)) εpos
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩
  have cpos : 0 < ‖c‖ := lt_trans (zero_lt_one : (0 : ℝ) < 1) hc
  have cnpos : 0 < ‖c ^ (n + 1)‖ := by
    rw [norm_zpow]
    exact lt_trans xεpos hn.2
  refine' ⟨-(n + 1), _, _, _, _⟩
  show c ^ (-(n + 1)) ≠ 0; exact zpow_ne_zero _ (norm_pos_iff.1 cpos)
  show ‖c ^ (-(n + 1)) • x‖ < ε
  · rw [norm_smul, zpow_neg, norm_inv, ← div_eq_inv_mul, div_lt_iff cnpos, mul_comm, norm_zpow]
    exact (div_lt_iff εpos).1 hn.2
  show ε / ‖c‖ ≤ ‖c ^ (-(n + 1)) • x‖
  · rw [zpow_neg, div_le_iff cpos, norm_smul, norm_inv, norm_zpow, zpow_add₀ (ne_of_gt cpos),
      zpow_one, mul_inv_rev, mul_comm, ← mul_assoc, ← mul_assoc, mul_inv_cancel (ne_of_gt cpos),
      one_mul, ← div_eq_inv_mul, le_div_iff (zpow_pos_of_pos cpos _), mul_comm]
    exact (le_div_iff εpos).1 hn.1
  show ‖c ^ (-(n + 1))‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖
  · rw [zpow_neg, norm_inv, inv_inv, norm_zpow, zpow_add₀ cpos.ne', zpow_one, mul_right_comm, ←
      div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right hn.1 (norm_nonneg _)
#align rescale_to_shell_semi_normed_zpow rescale_to_shell_semi_normed_zpow

/-- If there is a scalar `c` with `‖c‖>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
theorem rescale_to_shell_semi_normed {c : α} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E}
    (hx : ‖x‖ ≠ 0) : ∃ d : α, d ≠ 0 ∧ ‖d • x‖ < ε ∧ ε / ‖c‖ ≤ ‖d • x‖ ∧ ‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖ :=
  let ⟨n, hn⟩ := rescale_to_shell_semi_normed_zpow hc εpos hx
  ⟨_, hn⟩
#align rescale_to_shell_semi_normed rescale_to_shell_semi_normed

end SeminormedAddCommGroup

/-- A linear map from a `module` to a `normed_space` induces a `normed_space` structure on the
domain, using the `seminormed_add_comm_group.induced` norm.

See note [reducible non-instances] -/
@[reducible]
def NormedSpace.induced {F : Type _} (α β γ : Type _) [NormedField α] [AddCommGroup β] [Module α β]
    [SeminormedAddCommGroup γ] [NormedSpace α γ] [LinearMapClass F α β γ] (f : F) :
    @NormedSpace α β _ (SeminormedAddCommGroup.induced β γ f)
    where norm_smul_le a b := by
    unfold norm
    exact (map_smul f a b).symm ▸ norm_smul_le a (f b)
#align normed_space.induced NormedSpace.induced

section NormedAddCommGroup

variable [NormedField α]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace α E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace α F]

open NormedField

/-- While this may appear identical to `normed_space.to_module`, it contains an implicit argument
involving `normed_add_comm_group.to_seminormed_add_comm_group` that typeclass inference has trouble
inferring.

Specifically, the following instance cannot be found without this `normed_space.to_module'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [normed_field 𝕜] [Π i, normed_add_comm_group (E i)] [Π i, normed_space 𝕜 (E i)] :
  Π i, module 𝕜 (E i) := by apply_instance
```

[This Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/245151099)
gives some more context. -/
instance (priority := 100) NormedSpace.toModule' : Module α F :=
  NormedSpace.toModule
#align normed_space.to_module' NormedSpace.toModule'

section Surj

variable (E) [NormedSpace ℝ E] [Nontrivial E]

theorem exists_norm_eq {c : ℝ} (hc : 0 ≤ c) : ∃ x : E, ‖x‖ = c :=
  by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rw [← norm_ne_zero_iff] at hx
  use c • ‖x‖⁻¹ • x
  simp [norm_smul, Real.norm_of_nonneg hc, hx]
#align exists_norm_eq exists_norm_eq

@[simp]
theorem range_norm : range (norm : E → ℝ) = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 norm_nonneg) fun _ => exists_norm_eq E
#align range_norm range_norm

theorem nnnorm_surjective : Surjective (nnnorm : E → ℝ≥0) := fun c =>
  (exists_norm_eq E c.coe_nonneg).imp fun x h => NNReal.eq h
#align nnnorm_surjective nnnorm_surjective

@[simp]
theorem range_nnnorm : range (nnnorm : E → ℝ≥0) = univ :=
  (nnnorm_surjective E).range_eq
#align range_nnnorm range_nnnorm

end Surj

/-- If `E` is a nontrivial topological module over `ℝ`, then `E` has no isolated points.
This is a particular case of `module.punctured_nhds_ne_bot`. -/
instance Real.punctured_nhds_module_neBot {E : Type _} [AddCommGroup E] [TopologicalSpace E]
    [ContinuousAdd E] [Nontrivial E] [Module ℝ E] [ContinuousSMul ℝ E] (x : E) : NeBot (𝓝[≠] x) :=
  Module.punctured_nhds_neBot ℝ E x
#align real.punctured_nhds_module_ne_bot Real.punctured_nhds_module_neBot

theorem interior_closed_ball' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
    interior (closedBall x r) = ball x r :=
  by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closed_ball_zero, ball_zero, interior_singleton]
  · exact interior_closedBall x hr
#align interior_closed_ball' interior_closed_ball'

theorem frontier_closed_ball' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
    frontier (closedBall x r) = sphere x r := by
  rw [frontier, closure_closed_ball, interior_closed_ball' x r, closed_ball_diff_ball]
#align frontier_closed_ball' frontier_closed_ball'

variable {α}

theorem rescale_to_shell_zpow {c : α} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : x ≠ 0) :
    ∃ n : ℤ, c ^ n ≠ 0 ∧ ‖c ^ n • x‖ < ε ∧ ε / ‖c‖ ≤ ‖c ^ n • x‖ ∧ ‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖ :=
  rescale_to_shell_semi_normed_zpow hc εpos (mt norm_eq_zero.1 hx)
#align rescale_to_shell_zpow rescale_to_shell_zpow

/-- If there is a scalar `c` with `‖c‖>1`, then any element can be moved by scalar multiplication to
any shell of width `‖c‖`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
theorem rescale_to_shell {c : α} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : x ≠ 0) :
    ∃ d : α, d ≠ 0 ∧ ‖d • x‖ < ε ∧ ε / ‖c‖ ≤ ‖d • x‖ ∧ ‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖ :=
  rescale_to_shell_semi_normed hc εpos (mt norm_eq_zero.1 hx)
#align rescale_to_shell rescale_to_shell

end NormedAddCommGroup

section NontriviallyNormedSpace

variable (𝕜 E : Type _) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Nontrivial E]

include 𝕜

/-- If `E` is a nontrivial normed space over a nontrivially normed field `𝕜`, then `E` is unbounded:
for any `c : ℝ`, there exists a vector `x : E` with norm strictly greater than `c`. -/
theorem NormedSpace.exists_lt_norm (c : ℝ) : ∃ x : E, c < ‖x‖ :=
  by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rcases NormedField.exists_lt_norm 𝕜 (c / ‖x‖) with ⟨r, hr⟩
  use r • x
  rwa [norm_smul, ← div_lt_iff]
  rwa [norm_pos_iff]
#align normed_space.exists_lt_norm NormedSpace.exists_lt_norm

protected theorem NormedSpace.unbounded_univ : ¬Bounded (univ : Set E) := fun h =>
  let ⟨R, hR⟩ := bounded_iff_forall_norm_le.1 h
  let ⟨x, hx⟩ := NormedSpace.exists_lt_norm 𝕜 E R
  hx.not_le (hR x trivial)
#align normed_space.unbounded_univ NormedSpace.unbounded_univ

/-- A normed vector space over a nontrivially normed field is a noncompact space. This cannot be
an instance because in order to apply it, Lean would have to search for `normed_space 𝕜 E` with
unknown `𝕜`. We register this as an instance in two cases: `𝕜 = E` and `𝕜 = ℝ`. -/
protected theorem NormedSpace.noncompactSpace : NoncompactSpace E :=
  ⟨fun h => NormedSpace.unbounded_univ 𝕜 _ h.Bounded⟩
#align normed_space.noncompact_space NormedSpace.noncompactSpace

instance (priority := 100) NontriviallyNormedField.noncompactSpace : NoncompactSpace 𝕜 :=
  NormedSpace.noncompactSpace 𝕜 𝕜
#align nontrivially_normed_field.noncompact_space NontriviallyNormedField.noncompactSpace

omit 𝕜

instance (priority := 100) RealNormedSpace.noncompactSpace [NormedSpace ℝ E] : NoncompactSpace E :=
  NormedSpace.noncompactSpace ℝ E
#align real_normed_space.noncompact_space RealNormedSpace.noncompactSpace

end NontriviallyNormedSpace

section NormedAlgebra

/-- A normed algebra `𝕜'` over `𝕜` is normed module that is also an algebra.

See the implementation notes for `algebra` for a discussion about non-unital algebras. Following
the strategy there, a non-unital *normed* algebra can be written as:
```lean
variables [normed_field 𝕜] [non_unital_semi_normed_ring 𝕜']
variables [normed_module 𝕜 𝕜'] [smul_comm_class 𝕜 𝕜' 𝕜'] [is_scalar_tower 𝕜 𝕜' 𝕜']
```
-/
class NormedAlgebra (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [SeminormedRing 𝕜'] extends
  Algebra 𝕜 𝕜' where
  norm_smul_le : ∀ (r : 𝕜) (x : 𝕜'), ‖r • x‖ ≤ ‖r‖ * ‖x‖
#align normed_algebra NormedAlgebra

variable {𝕜 : Type _} (𝕜' : Type _) [NormedField 𝕜] [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']

instance (priority := 100) NormedAlgebra.toNormedSpace : NormedSpace 𝕜 𝕜'
    where norm_smul_le := NormedAlgebra.norm_smul_le
#align normed_algebra.to_normed_space NormedAlgebra.toNormedSpace

/-- While this may appear identical to `normed_algebra.to_normed_space`, it contains an implicit
argument involving `normed_ring.to_semi_normed_ring` that typeclass inference has trouble inferring.

Specifically, the following instance cannot be found without this `normed_space.to_module'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [normed_field 𝕜] [Π i, normed_ring (E i)] [Π i, normed_algebra 𝕜 (E i)] :
  Π i, module 𝕜 (E i) := by apply_instance
```

See `normed_space.to_module'` for a similar situation. -/
instance (priority := 100) NormedAlgebra.toNormedSpace' {𝕜'} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] :
    NormedSpace 𝕜 𝕜' := by infer_instance
#align normed_algebra.to_normed_space' NormedAlgebra.toNormedSpace'

theorem norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖(1 : 𝕜')‖ :=
  by
  rw [Algebra.algebraMap_eq_smul_one]
  exact norm_smul _ _
#align norm_algebra_map norm_algebraMap

theorem nnnorm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ * ‖(1 : 𝕜')‖₊ :=
  Subtype.ext <| norm_algebraMap 𝕜' x
#align nnnorm_algebra_map nnnorm_algebraMap

@[simp]
theorem norm_algebra_map' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ := by
  rw [norm_algebraMap, norm_one, mul_one]
#align norm_algebra_map' norm_algebra_map'

@[simp]
theorem nnnorm_algebra_map' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ :=
  Subtype.ext <| norm_algebra_map' _ _
#align nnnorm_algebra_map' nnnorm_algebra_map'

section NNReal

variable [NormOneClass 𝕜'] [NormedAlgebra ℝ 𝕜']

@[simp]
theorem norm_algebraMap_nNReal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖ = x :=
  (norm_algebra_map' 𝕜' (x : ℝ)).symm ▸ Real.norm_of_nonneg x.Prop
#align norm_algebra_map_nnreal norm_algebraMap_nNReal

@[simp]
theorem nnnorm_algebraMap_nNReal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖₊ = x :=
  Subtype.ext <| norm_algebraMap_nNReal 𝕜' x
#align nnnorm_algebra_map_nnreal nnnorm_algebraMap_nNReal

end NNReal

variable (𝕜 𝕜')

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
theorem algebraMap_isometry [NormOneClass 𝕜'] : Isometry (algebraMap 𝕜 𝕜') :=
  by
  refine' Isometry.of_dist_eq fun x y => _
  rw [dist_eq_norm, dist_eq_norm, ← RingHom.map_sub, norm_algebra_map']
#align algebra_map_isometry algebraMap_isometry

instance NormedAlgebra.id : NormedAlgebra 𝕜 𝕜 :=
  { NormedField.toNormedSpace, Algebra.id 𝕜 with }
#align normed_algebra.id NormedAlgebra.id

/-- Any normed characteristic-zero division ring that is a normed_algebra over the reals is also a
normed algebra over the rationals.

Phrased another way, if `𝕜` is a normed algebra over the reals, then `algebra_rat` respects that
norm. -/
instance normedAlgebraRat {𝕜} [NormedDivisionRing 𝕜] [CharZero 𝕜] [NormedAlgebra ℝ 𝕜] :
    NormedAlgebra ℚ 𝕜
    where norm_smul_le q x := by
    rw [← smul_one_smul ℝ q x, Rat.smul_one_eq_coe, norm_smul, Rat.norm_cast_real]
#align normed_algebra_rat normedAlgebraRat

instance PUnit.normedAlgebra : NormedAlgebra 𝕜 PUnit
    where norm_smul_le q x := by simp only [PUnit.norm_eq_zero, MulZeroClass.mul_zero]
#align punit.normed_algebra PUnit.normedAlgebra

instance : NormedAlgebra 𝕜 (ULift 𝕜') :=
  { ULift.normedSpace with }

/-- The product of two normed algebras is a normed algebra, with the sup norm. -/
instance Prod.normedAlgebra {E F : Type _} [SeminormedRing E] [SeminormedRing F] [NormedAlgebra 𝕜 E]
    [NormedAlgebra 𝕜 F] : NormedAlgebra 𝕜 (E × F) :=
  { Prod.normedSpace with }
#align prod.normed_algebra Prod.normedAlgebra

/-- The product of finitely many normed algebras is a normed algebra, with the sup norm. -/
instance Pi.normedAlgebra {E : ι → Type _} [Fintype ι] [∀ i, SeminormedRing (E i)]
    [∀ i, NormedAlgebra 𝕜 (E i)] : NormedAlgebra 𝕜 (∀ i, E i) :=
  { Pi.normedSpace, Pi.algebra _ E with }
#align pi.normed_algebra Pi.normedAlgebra

instance MulOpposite.normedAlgebra {E : Type _} [SeminormedRing E] [NormedAlgebra 𝕜 E] :
    NormedAlgebra 𝕜 Eᵐᵒᵖ :=
  { MulOpposite.normedSpace with }
#align mul_opposite.normed_algebra MulOpposite.normedAlgebra

end NormedAlgebra

/-- A non-unital algebra homomorphism from an `algebra` to a `normed_algebra` induces a
`normed_algebra` structure on the domain, using the `semi_normed_ring.induced` norm.

See note [reducible non-instances] -/
@[reducible]
def NormedAlgebra.induced {F : Type _} (α β γ : Type _) [NormedField α] [Ring β] [Algebra α β]
    [SeminormedRing γ] [NormedAlgebra α γ] [NonUnitalAlgHomClass F α β γ] (f : F) :
    @NormedAlgebra α β _ (SeminormedRing.induced β γ f)
    where norm_smul_le a b := by
    unfold norm
    exact (map_smul f a b).symm ▸ norm_smul_le a (f b)
#align normed_algebra.induced NormedAlgebra.induced

instance Subalgebra.toNormedAlgebra {𝕜 A : Type _} [SeminormedRing A] [NormedField 𝕜]
    [NormedAlgebra 𝕜 A] (S : Subalgebra 𝕜 A) : NormedAlgebra 𝕜 S :=
  @NormedAlgebra.induced _ 𝕜 S A _ (SubringClass.toRing S) S.Algebra _ _ _ S.val
#align subalgebra.to_normed_algebra Subalgebra.toNormedAlgebra

section RestrictScalars

variable (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  (E : Type _) [SeminormedAddCommGroup E] [NormedSpace 𝕜' E]

instance {𝕜 : Type _} {𝕜' : Type _} {E : Type _} [I : SeminormedAddCommGroup E] :
    SeminormedAddCommGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

instance {𝕜 : Type _} {𝕜' : Type _} {E : Type _} [I : NormedAddCommGroup E] :
    NormedAddCommGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

/-- If `E` is a normed space over `𝕜'` and `𝕜` is a normed algebra over `𝕜'`, then
`restrict_scalars.module` is additionally a `normed_space`. -/
instance : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  { RestrictScalars.module 𝕜 𝕜' E with
    norm_smul_le := fun c x =>
      (norm_smul_le (algebraMap 𝕜 𝕜' c) (_ : E)).trans_eq <| by rw [norm_algebra_map'] }

-- If you think you need this, consider instead reproducing `restrict_scalars.lsmul`
-- appropriately modified here.
/-- The action of the original normed_field on `restrict_scalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `restrict_scalars`.
-/
def Module.RestrictScalars.normedSpaceOrig {𝕜 : Type _} {𝕜' : Type _} {E : Type _} [NormedField 𝕜']
    [SeminormedAddCommGroup E] [I : NormedSpace 𝕜' E] : NormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I
#align module.restrict_scalars.normed_space_orig Module.RestrictScalars.normedSpaceOrig

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` and/or `restrict_scalars 𝕜 𝕜' E` instead.

This definition allows the `restrict_scalars.normed_space` instance to be put directly on `E`
rather on `restrict_scalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.
-/
def NormedSpace.restrictScalars : NormedSpace 𝕜 E :=
  RestrictScalars.normedSpace _ 𝕜' _
#align normed_space.restrict_scalars NormedSpace.restrictScalars

end RestrictScalars

