/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module analysis.normed_space.basic
! leanprover-community/mathlib commit d3af0609f6db8691dffdc3e1fb7feb7da72698f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Normed spaces

In this file we define (semi)normed spaces and algebras. We also prove some theorems
about these definitions.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {ι : Type _}

open Filter Metric Function Set Topology BigOperators NNReal ENNReal uniformity Pointwise

section SeminormedAddCommGroup

section Prio

-- set_option extends_priority 920 -- Porting note: option unsupported

-- Here, we set a rather high priority for the instance `[NormedSpace α β] : Module α β`
-- to take precedence over `Semiring.toModule` as this leads to instance paths with better
-- unification properties.
/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `‖c • x‖ = ‖c‖ ‖x‖`. We require only `‖c • x‖ ≤ ‖c‖ ‖x‖` in the definition, then prove
`‖c • x‖ = ‖c‖ ‖x‖` in `norm_smul`.

Note that since this requires `SeminormedAddCommGroup` and not `NormedAddCommGroup`, this
typeclass can be used for "semi normed spaces" too, just as `Module` can be used for
"semi modules". -/
class NormedSpace (α : Type _) (β : Type _) [NormedField α] [SeminormedAddCommGroup β] extends
  Module α β where
  norm_smul_le : ∀ (a : α) (b : β), ‖a • b‖ ≤ ‖a‖ * ‖b‖
#align normed_space NormedSpace

attribute [inherit_doc NormedSpace] NormedSpace.norm_smul_le

end Prio

variable [NormedField α] [SeminormedAddCommGroup β]

-- note: while these are currently strictly weaker than the versions without `le`, they will cease
-- to be if we eventually generalize `NormedSpace` from `NormedField α` to `NormedRing α`.
section LE

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

end LE

-- see Note [lower instance priority]
instance (priority := 100) NormedSpace.boundedSMul [NormedSpace α β] : BoundedSMul α β where
  dist_smul_pair' x y₁ y₂ := by simpa [dist_eq_norm, smul_sub] using norm_smul_le x (y₁ - y₂)
  dist_pair_smul' x₁ x₂ y := by simpa [dist_eq_norm, sub_smul] using norm_smul_le (x₁ - x₂) y
#align normed_space.has_bounded_smul NormedSpace.boundedSMul

-- Shortcut instance, as otherwise this will be found by `NormedSpace.toModule` and be
-- noncomputable.
instance : Module ℝ ℝ := by infer_instance

instance NormedField.toNormedSpace : NormedSpace α α where norm_smul_le a b := norm_mul_le a b
#align normed_field.to_normed_space NormedField.toNormedSpace

theorem norm_smul [NormedSpace α β] (s : α) (x : β) : ‖s • x‖ = ‖s‖ * ‖x‖ := by
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
  simp only [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, ← _root_.div_eq_inv_mul,
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
  this.eventually (gt_mem_nhds h)
#align eventually_nhds_norm_smul_sub_lt eventually_nhds_norm_smul_sub_lt

theorem Filter.Tendsto.zero_smul_isBoundedUnder_le {f : ι → α} {g : ι → E} {l : Filter ι}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l (Norm.norm ∘ g)) :
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
    closure (ball x r) = closedBall x r := by
  refine' Subset.antisymm closure_ball_subset_closedBall fun y hy => _
  have : ContinuousWithinAt (fun c : ℝ => c • (y - x) + x) (Ico 0 1) 1 :=
    ((continuous_id.smul continuous_const).add continuous_const).continuousWithinAt
  convert this.mem_closure _ _
  · rw [one_smul, sub_add_cancel]
  · simp [closure_Ico zero_ne_one, zero_le_one]
  · rintro c ⟨hc0, hc1⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0,
      mul_comm, ← mul_one r]
    rw [mem_closedBall, dist_eq_norm] at hy
    replace hr : 0 < r := ((norm_nonneg _).trans hy).lt_of_ne hr.symm
    apply mul_lt_mul' <;> assumption
#align closure_ball closure_ball

theorem frontier_ball [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    frontier (ball x r) = sphere x r := by
  rw [frontier, closure_ball x hr, isOpen_ball.interior_eq, closedBall_diff_ball]
#align frontier_ball frontier_ball

theorem interior_closedBall [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    interior (closedBall x r) = ball x r := by
  cases' hr.lt_or_lt with hr hr
  · rw [closedBall_eq_empty.2 hr, ball_eq_empty.2 hr.le, interior_empty]
  refine' Subset.antisymm _ ball_subset_interior_closedBall
  intro y hy
  rcases (mem_closedBall.1 <| interior_subset hy).lt_or_eq with (hr | rfl)
  · exact hr
  set f : ℝ → E := fun c : ℝ => c • (y - x) + x
  suffices f ⁻¹' closedBall x (dist y x) ⊆ Icc (-1) 1 by
    have hfc : Continuous f := (continuous_id.smul continuous_const).add continuous_const
    have hf1 : (1 : ℝ) ∈ f ⁻¹' interior (closedBall x <| dist y x) := by simpa
    have h1 : (1 : ℝ) ∈ interior (Icc (-1 : ℝ) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage hfc hf1)
    contrapose h1
    simp
  intro c hc
  rw [mem_Icc, ← abs_le, ← Real.norm_eq_abs, ← mul_le_mul_right hr]
  simpa [dist_eq_norm, norm_smul] using hc
#align interior_closed_ball interior_closedBall

theorem frontier_closedBall [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    frontier (closedBall x r) = sphere x r := by
  rw [frontier, closure_closedBall, interior_closedBall x hr, closedBall_diff_ball]
#align frontier_closed_ball frontier_closedBall

instance {E : Type _} [NormedAddCommGroup E] [NormedSpace ℚ E] (e : E) :
    DiscreteTopology <| AddSubgroup.zmultiples e := by
  rcases eq_or_ne e 0 with (rfl | he)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    refine Subsingleton.discreteTopology (α := ↑(⊥ : Subspace ℚ E))
  · rw [discreteTopology_iff_open_singleton_zero, isOpen_induced_iff]
    refine' ⟨Metric.ball 0 ‖e‖, Metric.isOpen_ball, _⟩
    ext ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [mem_preimage, mem_ball_zero_iff, AddSubgroup.coe_mk, mem_singleton_iff, Subtype.ext_iff,
      AddSubgroup.coe_mk, AddSubgroup.coe_zero, norm_zsmul ℚ k e, Int.norm_cast_rat,
      Int.norm_eq_abs, mul_lt_iff_lt_one_left (norm_pos_iff.mpr he), ←
      @Int.cast_one ℝ _, Int.cast_lt, Int.abs_lt_one_iff, smul_eq_zero, or_iff_left he]

/-- A (semi) normed real vector space is homeomorphic to the unit ball in the same space.
This homeomorphism sends `x : E` to `(1 + ‖x‖²)^(- ½) • x`.

In many cases the actual implementation is not important, so we don't mark the projection lemmas
`homeomorphUnitBall_apply_coe` and `homeomorphUnitBall_symm_apply` as `@[simp]`.

See also `contDiff_homeomorphUnitBall` and `contDiffOn_homeomorphUnitBall_symm` for
smoothness properties that hold when `E` is an inner-product space. -/
@[simps (config := { attrs := [] })]
noncomputable def homeomorphUnitBall [NormedSpace ℝ E] : E ≃ₜ ball (0 : E) 1 where
  toFun x :=
    ⟨(1 + ‖x‖ ^ 2).sqrt⁻¹ • x, by
      have : 0 < 1 + ‖x‖ ^ 2 := by positivity
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, ← _root_.div_eq_inv_mul,
        div_lt_one (abs_pos.mpr <| Real.sqrt_ne_zero'.mpr this), ← abs_norm_eq_norm x, ← sq_lt_sq,
        abs_norm_eq_norm, Real.sq_sqrt this.le]
      exact lt_one_add _⟩
  invFun y := (1 - ‖(y : E)‖ ^ 2).sqrt⁻¹ • (y : E)
  left_inv x := by
    field_simp [norm_smul, smul_smul, (zero_lt_one_add_norm_sq x).ne', sq_abs,
      Real.sq_sqrt (zero_lt_one_add_norm_sq x).le, ← Real.sqrt_div (zero_lt_one_add_norm_sq x).le]
  right_inv y := by
    have : 0 < 1 - ‖(y : E)‖ ^ 2 := by
      nlinarith [norm_nonneg (y : E), (mem_ball_zero_iff.1 y.2 : ‖(y : E)‖ < 1)]
    field_simp [norm_smul, smul_smul, this.ne', sq_abs, Real.sq_sqrt this.le,
      ← Real.sqrt_div this.le]
  continuous_toFun := by
    suffices : Continuous fun (x:E) => (1 + ‖x‖ ^ 2).sqrt⁻¹;
    exact (this.smul continuous_id).subtype_mk _
    refine' Continuous.inv₀ _ fun x => Real.sqrt_ne_zero'.mpr (by positivity)
    continuity
  continuous_invFun := by
    suffices ∀ y : ball (0 : E) 1, (1 - ‖(y : E)‖ ^ 2).sqrt ≠ 0 by
      apply Continuous.smul (Continuous.inv₀
        (continuous_const.sub ?_).sqrt this) continuous_induced_dom
      continuity -- Porting note: was just this tactic for `suffices`
    intro y
    rw [Real.sqrt_ne_zero']
    nlinarith [norm_nonneg (y : E), (mem_ball_zero_iff.1 y.2 : ‖(y : E)‖ < 1)]
#align homeomorph_unit_ball homeomorphUnitBall

-- Porting note: simp can prove this; removed simp
theorem coe_homeomorphUnitBall_apply_zero [NormedSpace ℝ E] :
    (homeomorphUnitBall (0 : E) : E) = 0 := by simp
#align coe_homeomorph_unit_ball_apply_zero coe_homeomorphUnitBall_apply_zero

open NormedField

instance ULift.normedSpace : NormedSpace α (ULift E) :=
  { ULift.seminormedAddCommGroup (E := E), ULift.module' with
    norm_smul_le := fun s x => (norm_smul_le s x.down : _) }

/-- The product of two normed spaces is a normed space, with the sup norm. -/
instance Prod.normedSpace : NormedSpace α (E × F) :=
  { Prod.seminormedAddCommGroup (E := E) (F := F), Prod.module with
    norm_smul_le := fun s x => by
      simp only [norm_smul, Prod.norm_def, Prod.smul_snd, Prod.smul_fst,
        mul_max_of_nonneg, norm_nonneg, le_rfl] }
#align prod.normed_space Prod.normedSpace

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance Pi.normedSpace {E : ι → Type _} [Fintype ι] [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace α (E i)] : NormedSpace α (∀ i, E i) where
  norm_smul_le a f := by
    simp_rw [← coe_nnnorm, ← NNReal.coe_mul, NNReal.coe_le_coe, Pi.nnnorm_def,
      NNReal.mul_finset_sup]
    exact Finset.sup_mono_fun fun _ _ => norm_smul_le _ _
#align pi.normed_space Pi.normedSpace

instance MulOpposite.normedSpace : NormedSpace α Eᵐᵒᵖ :=
  { MulOpposite.seminormedAddCommGroup (E := Eᵐᵒᵖ), MulOpposite.module _ with
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
    ∃ n : ℤ, c ^ n ≠ 0 ∧ ‖c ^ n • x‖ < ε ∧ ε / ‖c‖ ≤ ‖c ^ n • x‖ ∧ ‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖ := by
  have xεpos : 0 < ‖x‖ / ε := div_pos ((Ne.symm hx).le_iff_lt.1 (norm_nonneg x)) εpos
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩
  have cpos : 0 < ‖c‖ := lt_trans (zero_lt_one : (0 : ℝ) < 1) hc
  have cnpos : 0 < ‖c ^ (n + 1)‖ := by
    rw [norm_zpow]
    exact lt_trans xεpos hn.2
  refine' ⟨-(n + 1), _, _, _, _⟩
  show c ^ (-(n + 1)) ≠ 0; exact zpow_ne_zero _ (norm_pos_iff.1 cpos)
  show ‖c ^ (-(n + 1)) • x‖ < ε
  · rw [norm_smul, zpow_neg, norm_inv, ← _root_.div_eq_inv_mul, div_lt_iff cnpos, mul_comm,
      norm_zpow]
    exact (div_lt_iff εpos).1 hn.2
  show ε / ‖c‖ ≤ ‖c ^ (-(n + 1)) • x‖
  · rw [zpow_neg, div_le_iff cpos, norm_smul, norm_inv, norm_zpow, zpow_add₀ (ne_of_gt cpos),
      zpow_one, mul_inv_rev, mul_comm, ← mul_assoc, ← mul_assoc, mul_inv_cancel (ne_of_gt cpos),
      one_mul, ← _root_.div_eq_inv_mul, le_div_iff (zpow_pos_of_pos cpos _), mul_comm]
    exact (le_div_iff εpos).1 hn.1
  show ‖c ^ (-(n + 1))‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖
  · rw [zpow_neg, norm_inv, inv_inv, norm_zpow, zpow_add₀ cpos.ne', zpow_one, mul_right_comm, ←
      _root_.div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right hn.1 (norm_nonneg _)
#align rescale_to_shell_semi_normed_zpow rescale_to_shell_semi_normed_zpow

/-- If there is a scalar `c` with `‖c‖>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
theorem rescale_to_shell_semi_normed {c : α} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E}
    (hx : ‖x‖ ≠ 0) : ∃ d : α, d ≠ 0 ∧ ‖d • x‖ < ε ∧ ε / ‖c‖ ≤ ‖d • x‖ ∧ ‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖ :=
  let ⟨_, hn⟩ := rescale_to_shell_semi_normed_zpow hc εpos hx
  ⟨_, hn⟩
#align rescale_to_shell_semi_normed rescale_to_shell_semi_normed

end SeminormedAddCommGroup

/-- A linear map from a `Module` to a `NormedSpace` induces a `NormedSpace` structure on the
domain, using the `SeminormedAddCommGroup.induced` norm.

See note [reducible non-instances] -/
@[reducible]
def NormedSpace.induced {F : Type _} (α β γ : Type _) [NormedField α] [AddCommGroup β] [Module α β]
    [SeminormedAddCommGroup γ] [NormedSpace α γ] [LinearMapClass F α β γ] (f : F) :
    @NormedSpace α β _ (SeminormedAddCommGroup.induced β γ f) := by
  -- Porting note: trouble inferring SeminormedAddCommGroup β and Module α β
  -- unfolding the induced semi-norm is fiddly
  refine @NormedSpace.mk (α := α) (β := β) _ ?_ ?_ ?_
  · infer_instance
  · intro a b
    change ‖(⇑f) (a • b)‖ ≤ ‖a‖ * ‖(⇑f) b‖
    exact (map_smul f a b).symm ▸ norm_smul_le a (f b)
#align normed_space.induced NormedSpace.induced

section NormedAddCommGroup

variable [NormedField α]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace α E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace α F]

open NormedField

/-- While this may appear identical to `NormedSpace.toModule`, it contains an implicit argument
involving `NormedAddCommGroup.toSeminormedAddCommGroup` that typeclass inference has trouble
inferring.

Specifically, the following instance cannot be found without this `NormedSpace.toModule'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [NormedField 𝕜] [Π i, NormedAddCommGroup (E i)] [Π i, NormedSpace 𝕜 (E i)] :
  Π i, Module 𝕜 (E i) := by apply_instance
```

[This Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/245151099)
gives some more context. -/
instance (priority := 100) NormedSpace.toModule' : Module α F :=
  NormedSpace.toModule
#align normed_space.to_module' NormedSpace.toModule'

section Surj

variable (E)

variable [NormedSpace ℝ E] [Nontrivial E]

theorem exists_norm_eq {c : ℝ} (hc : 0 ≤ c) : ∃ x : E, ‖x‖ = c := by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rw [← norm_ne_zero_iff] at hx
  use c • ‖x‖⁻¹ • x
  simp [norm_smul, Real.norm_of_nonneg hc, abs_of_nonneg hc, inv_mul_cancel hx]
#align exists_norm_eq exists_norm_eq

@[simp]
theorem range_norm : range (norm : E → ℝ) = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 norm_nonneg) fun _ => exists_norm_eq E
#align range_norm range_norm

theorem nnnorm_surjective : Surjective (nnnorm : E → ℝ≥0) := fun c =>
  (exists_norm_eq E c.coe_nonneg).imp fun _ h => NNReal.eq h
#align nnnorm_surjective nnnorm_surjective

@[simp]
theorem range_nnnorm : range (nnnorm : E → ℝ≥0) = univ :=
  (nnnorm_surjective E).range_eq
#align range_nnnorm range_nnnorm

end Surj

/-- If `E` is a nontrivial topological module over `ℝ`, then `E` has no isolated points.
This is a particular case of `Module.punctured_nhds_neBot`. -/
instance Real.punctured_nhds_module_neBot {E : Type _} [AddCommGroup E] [TopologicalSpace E]
    [ContinuousAdd E] [Nontrivial E] [Module ℝ E] [ContinuousSMul ℝ E] (x : E) : NeBot (𝓝[≠] x) :=
  Module.punctured_nhds_neBot ℝ E x
#align real.punctured_nhds_module_ne_bot Real.punctured_nhds_module_neBot

theorem interior_closedBall' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
    interior (closedBall x r) = ball x r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, ball_zero, interior_singleton]
  · exact interior_closedBall x hr
#align interior_closed_ball' interior_closedBall'

theorem frontier_closedBall' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
    frontier (closedBall x r) = sphere x r := by
  rw [frontier, closure_closedBall, interior_closedBall' x r, closedBall_diff_ball]
#align frontier_closed_ball' frontier_closedBall'

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

/-- If `E` is a nontrivial normed space over a nontrivially normed field `𝕜`, then `E` is unbounded:
for any `c : ℝ`, there exists a vector `x : E` with norm strictly greater than `c`. -/
theorem NormedSpace.exists_lt_norm (c : ℝ) : ∃ x : E, c < ‖x‖ := by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rcases NormedField.exists_lt_norm 𝕜 (c / ‖x‖) with ⟨r, hr⟩
  use r • x
  rwa [norm_smul, ← _root_.div_lt_iff]
  rwa [norm_pos_iff]
#align normed_space.exists_lt_norm NormedSpace.exists_lt_norm

protected theorem NormedSpace.unbounded_univ : ¬Bounded (univ : Set E) := fun h =>
  let ⟨R, hR⟩ := bounded_iff_forall_norm_le.1 h
  let ⟨x, hx⟩ := NormedSpace.exists_lt_norm 𝕜 E R
  hx.not_le (hR x trivial)
#align normed_space.unbounded_univ NormedSpace.unbounded_univ

/-- A normed vector space over a nontrivially normed field is a noncompact space. This cannot be
an instance because in order to apply it, Lean would have to search for `NormedSpace 𝕜 E` with
unknown `𝕜`. We register this as an instance in two cases: `𝕜 = E` and `𝕜 = ℝ`. -/
protected theorem NormedSpace.noncompactSpace : NoncompactSpace E :=
  ⟨fun h => NormedSpace.unbounded_univ 𝕜 _ h.bounded⟩
#align normed_space.noncompact_space NormedSpace.noncompactSpace

instance (priority := 100) NontriviallyNormedField.noncompactSpace : NoncompactSpace 𝕜 :=
  NormedSpace.noncompactSpace 𝕜 𝕜
#align nontrivially_normed_field.noncompact_space NontriviallyNormedField.noncompactSpace

instance (priority := 100) RealNormedSpace.noncompactSpace [NormedSpace ℝ E] : NoncompactSpace E :=
  NormedSpace.noncompactSpace ℝ E
#align real_normed_space.noncompact_space RealNormedSpace.noncompactSpace

end NontriviallyNormedSpace

section NormedAlgebra

/-- A normed algebra `𝕜'` over `𝕜` is normed module that is also an algebra.

See the implementation notes for `Algebra` for a discussion about non-unital algebras. Following
the strategy there, a non-unital *normed* algebra can be written as:
```lean
variables [NormedField 𝕜] [NonunitalSeminormedRing 𝕜']
variables [NormedModule 𝕜 𝕜'] [SMulCommClass 𝕜 𝕜' 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜']
```
-/
class NormedAlgebra (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [SeminormedRing 𝕜'] extends
  Algebra 𝕜 𝕜' where
  norm_smul_le : ∀ (r : 𝕜) (x : 𝕜'), ‖r • x‖ ≤ ‖r‖ * ‖x‖
#align normed_algebra NormedAlgebra

attribute [inherit_doc NormedAlgebra] NormedAlgebra.norm_smul_le

variable {𝕜 : Type _} (𝕜' : Type _) [NormedField 𝕜] [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']

instance (priority := 100) NormedAlgebra.toNormedSpace : NormedSpace 𝕜 𝕜' :=
  -- Porting note: previous Lean could figure out what we were extending
  { NormedAlgebra.toAlgebra.toModule with
  norm_smul_le := NormedAlgebra.norm_smul_le }
#align normed_algebra.to_normed_space NormedAlgebra.toNormedSpace

/-- While this may appear identical to `NormedAlgebra.toNormedSpace`, it contains an implicit
argument involving `NormedRing.toSeminormedRing` that typeclass inference has trouble inferring.

Specifically, the following instance cannot be found without this `NormedSpace.toModule'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [NormedField 𝕜] [Π i, NormedRing (E i)] [Π i, NormedAlgebra 𝕜 (E i)] :
  Π i, Module 𝕜 (E i) := by apply_instance
```

See `NormedSpace.toModule'` for a similar situation. -/
instance (priority := 100) NormedAlgebra.toNormedSpace' {𝕜'} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] :
    NormedSpace 𝕜 𝕜' := by infer_instance
#align normed_algebra.to_normed_space' NormedAlgebra.toNormedSpace'

theorem norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖(1 : 𝕜')‖ := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact norm_smul _ _
#align norm_algebra_map norm_algebraMap

theorem nnnorm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ * ‖(1 : 𝕜')‖₊ :=
  Subtype.ext <| norm_algebraMap 𝕜' x
#align nnnorm_algebra_map nnnorm_algebraMap

@[simp]
theorem norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ := by
  rw [norm_algebraMap, norm_one, mul_one]
#align norm_algebra_map' norm_algebraMap'

@[simp]
theorem nnnorm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ :=
  Subtype.ext <| norm_algebraMap' _ _
#align nnnorm_algebra_map' nnnorm_algebraMap'

section NNReal

variable [NormOneClass 𝕜'] [NormedAlgebra ℝ 𝕜']

@[simp]
theorem norm_algebraMap_nNReal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖ = x :=
  (norm_algebraMap' 𝕜' (x : ℝ)).symm ▸ Real.norm_of_nonneg x.prop
#align norm_algebra_map_nnreal norm_algebraMap_nNReal

@[simp]
theorem nnnorm_algebraMap_nNReal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖₊ = x :=
  Subtype.ext <| norm_algebraMap_nNReal 𝕜' x
#align nnnorm_algebra_map_nnreal nnnorm_algebraMap_nNReal

end NNReal

variable (𝕜)

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
theorem algebraMap_isometry [NormOneClass 𝕜'] : Isometry (algebraMap 𝕜 𝕜') := by
  refine' Isometry.of_dist_eq fun x y => _
  rw [dist_eq_norm, dist_eq_norm, ← RingHom.map_sub, norm_algebraMap']
#align algebra_map_isometry algebraMap_isometry

instance NormedAlgebra.id : NormedAlgebra 𝕜 𝕜 :=
  { NormedField.toNormedSpace, Algebra.id 𝕜 with }
#align normed_algebra.id NormedAlgebra.id

-- Porting note: cannot synth scalar tower ℚ ℝ k
set_option synthInstance.etaExperiment true in
/-- Any normed characteristic-zero division ring that is a normed algebra over the reals is also a
normed algebra over the rationals.

Phrased another way, if `𝕜` is a normed algebra over the reals, then `AlgebraRat` respects that
norm. -/
instance normedAlgebraRat {𝕜} [NormedDivisionRing 𝕜] [CharZero 𝕜] [NormedAlgebra ℝ 𝕜] :
    NormedAlgebra ℚ 𝕜 where
  norm_smul_le q x := by
    rw [← smul_one_smul ℝ q x]
    -- Porting note: broken notation class seems to cause a problem here
    conv_lhs => change ‖(SMul.smul q (1:ℝ)) • x‖; rw [Rat.smul_one_eq_coe q]
    rw [norm_smul, Rat.norm_cast_real]
#align normed_algebra_rat normedAlgebraRat

instance PUnit.normedAlgebra : NormedAlgebra 𝕜 PUnit where
  norm_smul_le q _ := by simp only [norm_eq_zero, mul_zero, le_refl]
#align punit.normed_algebra PUnit.normedAlgebra

instance : NormedAlgebra 𝕜 (ULift 𝕜') :=
  { ULift.normedSpace, ULift.algebra with }

/-- The product of two normed algebras is a normed algebra, with the sup norm. -/
instance Prod.normedAlgebra {E F : Type _} [SeminormedRing E] [SeminormedRing F] [NormedAlgebra 𝕜 E]
    [NormedAlgebra 𝕜 F] : NormedAlgebra 𝕜 (E × F) :=
  { Prod.normedSpace, Prod.algebra 𝕜 E F with }
#align prod.normed_algebra Prod.normedAlgebra

-- Porting note: Lean 3 could synth the algebra instances for Pi Pr
/-- The product of finitely many normed algebras is a normed algebra, with the sup norm. -/
instance Pi.normedAlgebra {E : ι → Type _} [Fintype ι] [∀ i, SeminormedRing (E i)]
    [∀ i, NormedAlgebra 𝕜 (E i)] : NormedAlgebra 𝕜 (∀ i, E i) :=
  { Pi.normedSpace, Pi.algebra _ E with }
#align pi.normed_algebra Pi.normedAlgebra

variable {E : Type _} [SeminormedRing E] [NormedAlgebra 𝕜 E]

instance MulOpposite.normedAlgebra {E : Type _} [SeminormedRing E] [NormedAlgebra 𝕜 E] :
    NormedAlgebra 𝕜 Eᵐᵒᵖ :=
  { MulOpposite.normedSpace, MulOpposite.instAlgebraMulOppositeSemiring with }
#align mul_opposite.normed_algebra MulOpposite.normedAlgebra

end NormedAlgebra

set_option synthInstance.etaExperiment true in -- Porting note: gets around lean4#2074
/-- A non-unital algebra homomorphism from an `Algebra` to a `NormedAlgebra` induces a
`NormedAlgebra` structure on the domain, using the `SeminormedRing.induced` norm.

See note [reducible non-instances] -/
@[reducible]
def NormedAlgebra.induced {F : Type _} (α β γ : Type _) [NormedField α] [Ring β] [Algebra α β]
    [SeminormedRing γ] [NormedAlgebra α γ] [NonUnitalAlgHomClass F α β γ] (f : F) :
    @NormedAlgebra α β _ (SeminormedRing.induced β γ f) := by
  -- Porting note: trouble with SeminormedRing β, Algebra α β, and unfolding seminorm
  refine @NormedAlgebra.mk (𝕜 := α) (𝕜' := β) _ ?_ ?_ ?_
  · infer_instance
  · intro a b
    change ‖(⇑f) (a • b)‖ ≤ ‖a‖ * ‖(⇑f) b‖
    exact (map_smul f a b).symm ▸ norm_smul_le a (f b)
#align normed_algebra.induced NormedAlgebra.induced

-- Porting note: failed to synth NonunitalAlgHomClass
set_option synthInstance.etaExperiment true in
instance Subalgebra.toNormedAlgebra {𝕜 A : Type _} [SeminormedRing A] [NormedField 𝕜]
    [NormedAlgebra 𝕜 A] (S : Subalgebra 𝕜 A) : NormedAlgebra 𝕜 S :=
  @NormedAlgebra.induced _ 𝕜 S A _ (SubringClass.toRing S) _ _ _ _ S.val
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
`RestrictScalars.module` is additionally a `NormedSpace`. -/
instance RestrictScalars.normedSpace : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  { RestrictScalars.module 𝕜 𝕜' E with
    norm_smul_le := fun c x =>
      (norm_smul_le (algebraMap 𝕜 𝕜' c) (_ : E)).trans_eq <| by rw [norm_algebraMap'] }

-- If you think you need this, consider instead reproducing `RestrictScalars.lsmul`
-- appropriately modified here.
/-- The action of the original normed_field on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScalars`.
-/
def Module.RestrictScalars.normedSpaceOrig {𝕜 : Type _} {𝕜' : Type _} {E : Type _} [NormedField 𝕜']
    [SeminormedAddCommGroup E] [I : NormedSpace 𝕜' E] : NormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I
#align module.restrict_scalars.normed_space_orig Module.RestrictScalars.normedSpaceOrig

/-- Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` and/or `RestrictScalars 𝕜 𝕜' E` instead.

This definition allows the `RestrictScalars.normedSpace` instance to be put directly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.
-/
def NormedSpace.restrictScalars : NormedSpace 𝕜 E :=
  RestrictScalars.normedSpace _ 𝕜' _
#align normed_space.restrict_scalars NormedSpace.restrictScalars

end RestrictScalars
