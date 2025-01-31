/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-!
# Uniformly convex spaces

This file defines uniformly convex spaces, which are real normed vector spaces in which for all
strictly positive `ε`, there exists some strictly positive `δ` such that `ε ≤ ‖x - y‖` implies
`‖x + y‖ ≤ 2 - δ` for all `x` and `y` of norm at most than `1`. This means that the triangle
inequality is strict with a uniform bound, as opposed to strictly convex spaces where the triangle
inequality is strict but not necessarily uniformly (`‖x + y‖ < ‖x‖ + ‖y‖` for all `x` and `y` not in
the same ray).

## Main declarations

`UniformConvexSpace E` means that `E` is a uniformly convex space.

## TODO

* Milman-Pettis
* Hanner's inequalities

## Tags

convex, uniformly convex
-/


open Set Metric Filter Topology Uniformity

open Convex Pointwise

theorem norm_tendsto_of_norm_add_of_le {ι E : Type*} [SeminormedAddCommGroup E]
    {a : ℝ} {𝓕 : Filter ι} {f g : ι → E}
    (norm_f : ∀ᶠ i in 𝓕, ‖f i‖ ≤ a)
    (norm_g : ∀ᶠ i in 𝓕, ‖g i‖ ≤ a)
    (norm_add : Tendsto (fun i ↦ ‖f i + g i‖) 𝓕 (𝓝 (a+a))) :
    Tendsto (fun i ↦ ‖f i‖) 𝓕 (𝓝 a) := by
  have : ∀ᶠ i in 𝓕, ‖f i + g i‖ - a ≤ ‖f i‖ := by
    filter_upwards [norm_g] with i hgi
    rw [sub_le_iff_le_add]
    exact norm_add_le _ _ |>.trans (add_le_add_left hgi _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ tendsto_const_nhds this norm_f
  simpa only [add_sub_cancel_right a a] using norm_add.sub_const a

theorem normalize_tendsto_uniformity_of_norm_tendsto {ι E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} {𝓕 : Filter ι} {f : ι → E} (ha : a ≠ 0)
    (norm_f : Tendsto (fun i ↦ ‖f i‖) 𝓕 (𝓝 a)) :
    Tendsto (fun i ↦ (‖f i‖⁻¹ • f i, a⁻¹ • f i)) 𝓕 (𝓤 E) := by
  simp_rw [uniformity_eq_comap_nhds_zero, tendsto_comap_iff, Function.comp_def, ← sub_smul]
  have : Tendsto (fun i ↦ a⁻¹ - ‖f i‖⁻¹) 𝓕 (𝓝 0) := by
    simpa using (norm_f.inv₀ ha).const_sub a⁻¹
  exact this.zero_smul_isBoundedUnder_le norm_f.isBoundedUnder_le

/-- A *uniformly convex space* is a real normed space where `‖x - y‖` tends to `0` when
`‖x+y‖` tends to `2` and `‖x‖` and `‖y‖` tend to `1`. This is a strenghtening of strict convexity,
which says that `‖x - y‖ = 0` when `‖x‖ = ‖y‖ = 1` and `‖x + y‖ = 2`.

A more concrete characterization is given by
`uniformConvexSpace_iff_exists_forall_sphere_norm_add_le_add_sub` : a normed space is
uniformly convex if and only if, over the `x` and `y` of norm `1`,
`‖x + y‖` is uniformly bounded above by a constant `< 2` when `‖x - y‖` is uniformly bounded below
by a positive constant. -/
@[mk_iff uniformConvexSpace_iff_comap_norm_add_le_uniformity]
class UniformConvexSpace (E : Type*) [SeminormedAddCommGroup E] : Prop where
  protected comap_norm_add_le_uniformity : ∀ a : ℝ, 0 < a →
    comap (fun xy ↦ ⟨‖xy.1‖, ‖xy.2‖, ‖xy.1 + xy.2‖⟩ : E × E → ℝ × ℝ × ℝ) (𝓝 ⟨a, a, a+a⟩) ≤ 𝓤 E

variable {E : Type*}

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup E]

theorem uniformConvexSpace_iff_le_uniformity_of_norm_add' :
    UniformConvexSpace E ↔ ∀ a : ℝ, 0 < a → ∀ 𝓕 : Filter (E × E),
      Tendsto (fun xy ↦ ‖xy.1‖) 𝓕 (𝓝 a) →
      Tendsto (fun xy ↦ ‖xy.2‖) 𝓕 (𝓝 a) →
      Tendsto (fun xy ↦ ‖xy.1 + xy.2‖) 𝓕 (𝓝 (a+a)) →
      𝓕 ≤ 𝓤 E := by
  rw [uniformConvexSpace_iff_comap_norm_add_le_uniformity]
  congrm ∀ a a_pos, ?_
  rw [← forall_le_iff_le]
  congrm ∀ 𝓕, ?_
  simp_rw [← tendsto_iff_comap, nhds_prod_eq, tendsto_prod_iff', and_imp]

theorem tendsto_uniformity_of_norm_add {ι : Type*} [H : UniformConvexSpace E]
    {a : ℝ} {𝓕 : Filter ι} {f g : ι → E} (norm_f : Tendsto (fun i ↦ ‖f i‖) 𝓕 (𝓝 a))
    (norm_g : Tendsto (fun i ↦ ‖g i‖) 𝓕 (𝓝 a))
    (norm_add : Tendsto (fun i ↦ ‖f i + g i‖) 𝓕 (𝓝 (a+a))) :
    Tendsto (fun i ↦ (f i, g i)) 𝓕 (𝓤 E) := by
  rcases lt_trichotomy a 0 with (ha|rfl|ha)
  · have : 𝓕 = ⊥ := by
      rw [← eventually_false_iff_eq_bot]
      filter_upwards [norm_f.eventually_lt_const ha] using fun i ↦ norm_nonneg _ |>.not_lt
    exact this ▸ tendsto_bot
  · rw [← tendsto_zero_iff_norm_tendsto_zero] at norm_f norm_g
    exact le_trans (Filter.le_prod.mpr ⟨norm_f, norm_g⟩)
      (nhds_prod_eq (X := E) (Y := E) ▸ nhds_le_uniformity (0 : E))
  · apply uniformConvexSpace_iff_le_uniformity_of_norm_add'.mp H a ha (map (fun i ↦ (f i, g i)) 𝓕)
      <;> rwa [tendsto_map'_iff]

theorem tendsto_uniformity_of_norm_add_of_closedBall {ι : Type*}
    [UniformConvexSpace E] {a : ℝ} {𝓕 : Filter ι} {f g : ι → E}
    (norm_f : ∀ᶠ i in 𝓕, ‖f i‖ ≤ a)
    (norm_g : ∀ᶠ i in 𝓕, ‖g i‖ ≤ a)
    (norm_add : Tendsto (fun i ↦ ‖f i + g i‖) 𝓕 (𝓝 (a+a))) :
    Tendsto (fun i ↦ (f i, g i)) 𝓕 (𝓤 E) :=
  tendsto_uniformity_of_norm_add
    (norm_tendsto_of_norm_add_of_le norm_f norm_g norm_add)
    (norm_tendsto_of_norm_add_of_le norm_g norm_f (by simpa [add_comm] using norm_add)) norm_add

theorem tendsto_uniformity_of_norm_add_of_sphere {ι : Type*}
    [UniformConvexSpace E] {a : ℝ} {𝓕 : Filter ι} {f g : ι → E}
    (norm_f : ∀ᶠ i in 𝓕, ‖f i‖ = a)
    (norm_g : ∀ᶠ i in 𝓕, ‖g i‖ = a)
    (norm_add : Tendsto (fun i ↦ ‖f i + g i‖) 𝓕 (𝓝 (a+a))) :
    Tendsto (fun i ↦ (f i, g i)) 𝓕 (𝓤 E) :=
  tendsto_uniformity_of_norm_add_of_closedBall
    (norm_f.mono fun _ ↦ Eq.le) (norm_g.mono fun _ ↦ Eq.le) norm_add

variable (E) in
theorem exists_forall_closedBall_norm_add_le_add_sub [UniformConvexSpace E]
    (a : ℝ) {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ δ > 0, ∀ ⦃x : E⦄, ‖x‖ ≤ a → ∀ ⦃y⦄, ‖y‖ ≤ a → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ (a + a) - δ := by
  set 𝓕 : Filter (E × E) :=
    comap (fun xy ↦ ‖xy.1 + xy.2‖) (𝓝 (a+a)) ⊓ 𝓟 {xy | ‖xy.1‖ ≤ a ∧ ‖xy.2‖ ≤ a}
  have := tendsto_uniformity_of_norm_add_of_closedBall (E := E) (𝓕 := 𝓕)
    (mem_inf_of_right fun _ ↦ And.left) (mem_inf_of_right fun _ ↦ And.right)
    (tendsto_inf_left tendsto_comap) |>.eventually (dist_mem_uniformity ε_pos)
  simp_rw [𝓕, eventually_inf_principal, nhds_basis_ball.comap _ |>.eventually_iff,
    Prod.forall, Real.ball_eq_Ioo, dist_eq_norm] at this
  rcases this with ⟨δ, δ_pos, hδ⟩
  exact ⟨δ, δ_pos, fun _ hxa _ hyb ↦ le_imp_le_of_lt_imp_lt fun hxy ↦ hδ _ _
    ⟨hxy, lt_add_of_le_of_pos (norm_add_le_of_le hxa hyb) δ_pos⟩ ⟨hxa, hyb⟩⟩

variable (E) in
theorem exists_forall_closedBall_norm_add_le_two_sub [UniformConvexSpace E]
    {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ δ > 0, ∀ ⦃x : E⦄, ‖x‖ ≤ 1 → ∀ ⦃y⦄, ‖y‖ ≤ 1 → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ := by
  simpa only [one_add_one_eq_two] using exists_forall_closedBall_norm_add_le_add_sub E 1 ε_pos

variable (E) in
theorem exists_forall_sphere_norm_add_le_add_sub [UniformConvexSpace E]
    (a : ℝ) {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ δ > 0, ∀ ⦃x : E⦄, ‖x‖ = a → ∀ ⦃y⦄, ‖y‖ = a → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ (a + a) - δ :=
  exists_forall_closedBall_norm_add_le_add_sub (a := a) (E := E) ε_pos |>.imp
    fun _ ⟨δ_pos, hδ⟩ ↦ ⟨δ_pos, fun _ hx _ hy ↦ hδ hx.le hy.le⟩

variable (E) in
theorem exists_forall_sphere_norm_add_le_two_sub [UniformConvexSpace E]
    {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ δ > 0, ∀ ⦃x : E⦄, ‖x‖ = 1 → ∀ ⦃y⦄, ‖y‖ = 1 → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ := by
  simpa only [one_add_one_eq_two] using exists_forall_sphere_norm_add_le_add_sub E 1 ε_pos

theorem uniformConvexSpace_iff_le_uniformity_of_norm_add_of_sphere
    [NormedSpace ℝ E] {a : ℝ} (a_pos : a > 0) :
    UniformConvexSpace E ↔ ∀ 𝓕 : Filter (E × E),
      (∀ᶠ xy in 𝓕, ‖xy.1‖ = a) →
      (∀ᶠ xy in 𝓕, ‖xy.2‖ = a) →
      Tendsto (fun xy ↦ ‖xy.1 + xy.2‖) 𝓕 (𝓝 (a+a)) →
      𝓕 ≤ 𝓤 E := by
  refine ⟨fun H 𝓕 ↦ tendsto_uniformity_of_norm_add_of_sphere,
    fun H ↦ uniformConvexSpace_iff_le_uniformity_of_norm_add'.mpr
      fun b b_pos 𝓕 norm_fst norm_snd norm_add ↦ ?_⟩
  change Tendsto id 𝓕 (𝓤 E)
  rw [← smul_tendsto_smul_iff₀ (inv_ne_zero b_pos.ne'), smul_uniformity₀ (inv_ne_zero b_pos.ne')]
  have key_fst := normalize_tendsto_uniformity_of_norm_tendsto b_pos.ne' norm_fst
  have key_snd := normalize_tendsto_uniformity_of_norm_tendsto b_pos.ne' norm_snd
  have key_add : Tendsto (fun xy ↦ ‖‖xy.1‖⁻¹ • xy.1 + ‖xy.2‖⁻¹ • xy.2‖) 𝓕 (𝓝 (1 + 1)) := by
    have := Tendsto.comp uniformContinuous_norm (key_fst.uniformity_add key_snd)
    refine .congr_uniformity ?_ this.uniformity_symm
    simpa [← smul_add, norm_smul_of_nonneg (inv_pos.mpr b_pos).le, mul_add, b_pos.ne'] using
      norm_add.const_mul b⁻¹
  refine key_fst.uniformity_symm.uniformity_trans ?_ |>.uniformity_trans key_snd
  rw [← smul_tendsto_smul_iff₀ a_pos.ne', smul_uniformity₀ a_pos.ne']
  refine H _ ?_ ?_ ?_
  · rw [eventually_map]
    filter_upwards [norm_fst.eventually_ne b_pos.ne'] with xy hx
    simpa [norm_smul, hx] using a_pos.le
  · rw [eventually_map]
    filter_upwards [norm_snd.eventually_ne b_pos.ne'] with xy hy
    simpa [norm_smul, hy] using a_pos.le
  · rw [tendsto_map'_iff]
    simpa [Function.comp_def, ← smul_add, norm_smul_of_nonneg a_pos.le, mul_add]
      using key_add.const_mul a

theorem uniformConvexSpace_iff_le_uniformity_of_norm_add_of_closedBall
    [NormedSpace ℝ E] {a : ℝ} (a_pos : a > 0) :
    UniformConvexSpace E ↔ ∀ 𝓕 : Filter (E × E),
      (∀ᶠ xy in 𝓕, ‖xy.1‖ ≤ a) →
      (∀ᶠ xy in 𝓕, ‖xy.2‖ ≤ a) →
      Tendsto (fun xy ↦ ‖xy.1 + xy.2‖) 𝓕 (𝓝 (a+a)) →
      𝓕 ≤ 𝓤 E := by
  constructor <;> intro H
  · exact fun 𝓕 ↦ tendsto_uniformity_of_norm_add_of_closedBall
  · rw [uniformConvexSpace_iff_le_uniformity_of_norm_add_of_sphere a_pos]
    exact fun 𝓕 norm_fst norm_snd ↦ H 𝓕 (norm_fst.mono fun _ ↦ Eq.le) (norm_snd.mono fun _ ↦ Eq.le)

theorem uniformConvexSpace_iff_le_uniformity_of_norm_add [NormedSpace ℝ E] {a : ℝ}
    (a_pos : 0 < a) :
    UniformConvexSpace E ↔ ∀ 𝓕 : Filter (E × E),
      Tendsto (fun xy ↦ ‖xy.1‖) 𝓕 (𝓝 a) →
      Tendsto (fun xy ↦ ‖xy.2‖) 𝓕 (𝓝 a) →
      Tendsto (fun xy ↦ ‖xy.1 + xy.2‖) 𝓕 (𝓝 (a+a)) →
      𝓕 ≤ 𝓤 E := by
  constructor <;> intro H
  · exact fun 𝓕 ↦ tendsto_uniformity_of_norm_add
  · rw [uniformConvexSpace_iff_le_uniformity_of_norm_add_of_sphere a_pos]
    exact fun 𝓕 norm_fst norm_snd ↦ H 𝓕
      (EventuallyEq.tendsto norm_fst) (EventuallyEq.tendsto norm_snd)

theorem uniformConvexSpace_iff_exists_forall_sphere_norm_add_le_add_sub [NormedSpace ℝ E]
    {a : ℝ} (a_pos : 0 < a) :
    UniformConvexSpace E ↔ ∀ ε > 0,
      ∃ δ > 0, ∀ ⦃x : E⦄, ‖x‖ = a → ∀ ⦃y⦄, ‖y‖ = a → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ (a + a) - δ := by
  constructor <;> intro H
  · exact fun ε ↦ exists_forall_sphere_norm_add_le_add_sub E a
  · simp_rw [uniformConvexSpace_iff_le_uniformity_of_norm_add_of_sphere a_pos]
    intro 𝓕 norm_fst norm_snd norm_add
    refine uniformity_basis_dist.ge_iff.mpr fun ε ε_pos ↦ ?_
    rcases H ε ε_pos with ⟨δ, δ_pos, hδ⟩
    filter_upwards [norm_fst, norm_snd, norm_add.eventually_const_lt
      (show a + a - δ < a + a by linarith)] with p norm_p_fst norm_p_snd
    exact le_imp_le_iff_lt_imp_lt.mp <| dist_eq_norm p.1 p.2 ▸ hδ norm_p_fst norm_p_snd

theorem uniformConvexSpace_iff_exists_forall_closedBall_norm_add_le_add_sub [NormedSpace ℝ E]
    {a : ℝ} (a_pos : 0 < a) :
    UniformConvexSpace E ↔ ∀ ε > 0,
      ∃ δ > 0, ∀ ⦃x : E⦄, ‖x‖ ≤ a → ∀ ⦃y⦄, ‖y‖ ≤ a → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ (a + a) - δ := by
  constructor <;> intro H
  · exact fun ε ↦ exists_forall_closedBall_norm_add_le_add_sub E a
  · rw [uniformConvexSpace_iff_exists_forall_sphere_norm_add_le_add_sub a_pos]
    exact fun ε ε_pos ↦ (H ε ε_pos).imp fun δ ⟨δ_pos, hδ⟩ ↦ ⟨δ_pos, fun _ hx _ hy ↦ hδ hx.le hy.le⟩

end SeminormedAddCommGroup

variable [NormedAddCommGroup E] [UniformConvexSpace E]

-- See note [lower instance priority]
instance (priority := 100) UniformConvexSpace.toStrictConvexSpace [NormedSpace ℝ E] :
    StrictConvexSpace ℝ E :=
  StrictConvexSpace.of_norm_add_ne_two fun _ _ hx hy hxy =>
    let ⟨_, hδ, h⟩ := exists_forall_closedBall_norm_add_le_two_sub E (norm_sub_pos_iff.2 hxy)
    ((h hx.le hy.le le_rfl).trans_lt <| sub_lt_self _ hδ).ne

/-- In a uniformly convex space over `ℝ` or `ℂ`, the only obstruction for weak convergence to imply
convergence is the potential loss of mass. More explicitly, if `f i` converges to `x` weakly
and `‖f i‖` converges to `‖x‖`, then `f i` converges to `x` in norm. -/
theorem tendsto_iff_forall_dual_and_norm {𝕜 ι : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    {𝓕 : Filter ι} {f : ι → E} {x : E} :
    Tendsto f 𝓕 (𝓝 x) ↔
      (∀ l : E →L[𝕜] 𝕜, Tendsto (l ∘ f) 𝓕 (𝓝 (l x))) ∧ Tendsto (‖f ·‖) 𝓕 (𝓝 ‖x‖) := by
  -- The forward direction is obvious
  refine ⟨fun H ↦ ⟨fun l ↦ l.continuous.tendsto _ |>.comp H, H.norm⟩, fun ⟨Hdual, Hnorm⟩ ↦ ?_⟩
  -- For the backward direction, the case `x = 0` is trivial.
  rcases eq_or_ne x 0 with (rfl|x_nz)
  · rwa [norm_zero, ← tendsto_zero_iff_norm_tendsto_zero] at Hnorm
  -- If `x ≠ 0`, pick a linear form `l` with `‖l‖ = 1` and `l x = ‖x‖`
  · rcases exists_dual_vector 𝕜 x x_nz with ⟨l, norm_l, l_x⟩
    rw [Uniform.tendsto_nhds_left]
  -- By uniform convexity and since `‖f i‖` tends to `‖x‖`,
  -- it suffices to show that `‖f i + x‖` tends to `2 * ‖x‖`.
    refine tendsto_uniformity_of_norm_add Hnorm tendsto_const_nhds ?_
  -- This follows from `‖l (f i + x)‖ ≤ ‖f i + x‖ ≤ ‖f i‖ + ‖x‖`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun i ↦ ‖l (f i + x)‖)
      ?_ (Hnorm.add tendsto_const_nhds) (fun i ↦ ?_) (fun i ↦ norm_add_le _ _)
    · simpa [l_x, ← two_smul ℝ] using (Hdual l |>.add <| tendsto_const_nhds (x := l x)).norm
    · simpa using l.le_of_opNorm_le norm_l.le (f i + x)
