/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

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

theorem tendsto_smul_sub_smul_zero_iff_tendsto_sub (𝕜 : Type*) {ι E : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {𝓕 : Filter ι} {a b : ι → 𝕜}
    {x y : ι → E} (hab : Tendsto (a - b) 𝓕 (𝓝 0)) (hau : 𝓕.IsBoundedUnder (· ≤ ·) (‖a ·‖))
    (had : ∃ m > 0, ∀ᶠ x in 𝓕, m ≤ ‖a x‖) (hy : 𝓕.IsBoundedUnder (· ≤ ·) (‖y ·‖)) :
    Tendsto (a • x - b • y) 𝓕 (𝓝 0) ↔ Tendsto (x - y) 𝓕 (𝓝 0) := by
  rcases had with ⟨m, m_pos, hm⟩
  have had' : 𝓕.IsBoundedUnder (· ≤ ·) (‖a⁻¹ ·‖) := by
    refine Filter.isBoundedUnder_of_eventually_le (a := m⁻¹) ?_
    filter_upwards [hm] with i hi
    simpa only [Pi.inv_apply, norm_inv] using inv_anti₀ m_pos hi
  have eq : a • x - b • y = a • (x - y) + (a - b) • y := by module
  have lim : Tendsto ((a - b) • y) 𝓕 (𝓝 0) := hab.zero_smul_isBoundedUnder_le hy
  have scale : Tendsto (a • (x - y)) 𝓕 (𝓝 0) ↔ Tendsto (x - y) 𝓕 (𝓝 0) := by
    refine ⟨fun H ↦ (had'.smul_tendsto_zero H).congr' ?_, fun H ↦ hau.smul_tendsto_zero H⟩
    filter_upwards [hm] with i hi
    rw [Pi.smul_apply', Pi.inv_apply, smul_smul, inv_mul_cancel₀
      (ne_zero_of_norm_ne_zero (m_pos.trans_le hi).ne'), one_smul]
  rw [eq, ← scale]
  exact ⟨fun H ↦ by simpa using H.sub lim, fun H ↦ by simpa using H.add lim⟩

theorem tendsto_smul_inv_norm_uniformity_iff_of_norm {ι E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {𝓕 : Filter ι} {x y : ι → E}
    {l : ℝ} (l_pos : 0 < l) (normx : Tendsto (‖x ·‖) 𝓕 (𝓝 l)) (normy : Tendsto (‖y ·‖) 𝓕 (𝓝 l)) :
    Tendsto ((‖x ·‖⁻¹) • x - (‖y ·‖⁻¹) • y) 𝓕 (𝓝 0) ↔ Tendsto (x - y) 𝓕 (𝓝 0) := by
  apply tendsto_smul_sub_smul_zero_iff_tendsto_sub ℝ
  · simpa using (normx.inv₀ l_pos.ne').sub (normy.inv₀ l_pos.ne')
  · exact normx.inv₀ l_pos.ne' |>.norm.isBoundedUnder_le
  · rcases exists_gt l with ⟨M, hM⟩
    use M⁻¹, inv_pos.mpr (l_pos.trans hM)
    filter_upwards [eventually_le_of_tendsto_lt hM normx, eventually_gt_of_tendsto_gt l_pos normx]
    exact fun i hiM hi0 ↦ (Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (x i)))).symm ▸
      inv_anti₀ hi0 hiM
  · exact normy.isBoundedUnder_le

--theorem dist_div_norm_self_div_norm_self_le {E : Type*} [SeminormedAddCommGroup E]
--    [NormedSpace ℝ E] {x y : E} (hx : ‖x‖ ≠ 0) (hy : ‖y‖ ≠ 0) :
--    dist (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) ≤ ‖x‖⁻¹ * dist x y + (‖y‖ - ‖x‖) :=
--  calc dist (‖x‖⁻¹ • x) (‖y‖⁻¹ • y)
--    _ = ‖(‖x‖⁻¹ • x - ‖x‖⁻¹ • y) + (‖x‖⁻¹ • y - ‖y‖⁻¹ • y)‖ := by
--        simp_rw [dist_eq_norm, sub_add_sub_cancel]
--    _ ≤ ‖‖x‖⁻¹ • x - ‖x‖⁻¹ • y‖ + ‖‖x‖⁻¹ • y - ‖y‖⁻¹ • y‖ := norm_add_le _ _
--    _ = ‖x‖⁻¹ * ‖x - y‖ + ‖‖x‖⁻¹ • y - ‖y‖⁻¹ • y‖ := norm_add_le _ _
--    _ ≤ ‖x‖⁻¹ * dist x y + (‖y‖ - ‖x‖) := sorry

-- This can probably stay here
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

/-- A *uniformly convex space* is a real normed space where the triangle inequality is strict with a
uniform bound. Namely, over the `x` and `y` of norm `1`, `‖x + y‖` is uniformly bounded above
by a constant `< 2` when `‖x - y‖` is uniformly bounded below by a positive constant. -/
@[mk_iff uniformConvexSpace_iff_comap_norm_add_le_uniformity]
class UniformConvexSpace (E : Type*) [SeminormedAddCommGroup E] : Prop where
  protected comap_norm_add_le_uniformity : ∀ a : ℝ, 0 < a →
    comap (fun xy ↦ ⟨‖xy.1‖, ‖xy.2‖, ‖xy.1 + xy.2‖⟩ : E × E → ℝ × ℝ × ℝ) (𝓝 ⟨a, a, a+a⟩) ≤ 𝓤 E

/-- A *uniformly convex space* is a real normed space where the triangle inequality is strict with a
uniform bound. Namely, over the `x` and `y` of norm `1`, `‖x + y‖` is uniformly bounded above
by a constant `< 2` when `‖x - y‖` is uniformly bounded below by a positive constant. -/
@[mk_iff]
class UniformConvexSpace' (E : Type*) [SeminormedAddCommGroup E] : Prop where
  uniform_convex : ∀ ⦃ε : ℝ⦄,
    0 < ε → ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ = 1 → ∀ ⦃y⦄, ‖y‖ = 1 → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ

variable {E : Type*}

section SeminormedAddCommGroup

variable {E : Type*} [SeminormedAddCommGroup E]

theorem uniformConvexSpace_iff_le_uniformity_of_norm_add :
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
  -- This is ugly
  rcases lt_trichotomy a 0 with (ha|rfl|ha)
  · replace norm_f := eventually_le_of_tendsto_lt ha norm_f
    replace norm_g := eventually_le_of_tendsto_lt ha norm_g
    refine tendsto_uniformity_iff_dist_tendsto_zero.mpr <| tendsto_const_nhds.congr' ?_
    filter_upwards [norm_f, norm_g] with a hf hg
    refine .symm <| Inseparable.dist_eq_zero <| .trans (y := 0) ?_ <| .symm ?_ <;>
    exact inseparable_zero_iff_norm.mpr (le_antisymm (by assumption) (norm_nonneg _))
  · rw [← tendsto_zero_iff_norm_tendsto_zero] at norm_f norm_g
    exact le_trans (Filter.le_prod.mpr ⟨norm_f, norm_g⟩)
      (nhds_prod_eq (X := E) (Y := E) ▸ nhds_le_uniformity (0 : E))
  · apply uniformConvexSpace_iff_le_uniformity_of_norm_add.mp H a ha (map (fun i ↦ (f i, g i)) 𝓕)
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
    (EventuallyEq.le norm_f) (EventuallyEq.le norm_g) norm_add

theorem exists_forall_closedBall_norm_add_le_add_sub [UniformConvexSpace E]
    {a ε : ℝ} (ε_pos : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ ≤ a → ∀ ⦃y⦄, ‖y‖ ≤ a → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ (a + a) - δ := by
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

theorem uniformConvexSpace_iff_tendsto_uniformity_of_norm_add_of_unit_sphere
    [NormedSpace ℝ E] :
    UniformConvexSpace E ↔ ∀ 𝓕 : Filter (E × E),
      (∀ᶠ xy in 𝓕, ‖xy.1‖ = 1) →
      (∀ᶠ xy in 𝓕, ‖xy.2‖ = 1) →
      Tendsto (fun xy ↦ ‖xy.1 + xy.2‖) 𝓕 (𝓝 2) →
      𝓕 ≤ 𝓤 E := by
  refine ⟨fun H 𝓕 ↦ one_add_one_eq_two (R := ℝ) ▸ tendsto_uniformity_of_norm_add_of_sphere,
    fun H ↦ uniformConvexSpace_iff_le_uniformity_of_norm_add.mpr
      fun a' ha' 𝓕 norm_fst norm_snd norm_add ↦ ?_⟩
  simp_rw [Metric.uniformity_eq_comap_nhds_zero, ← tendsto_iff_comap, dist_eq_norm_sub,
    ← tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_smul_inv_norm_uniformity_iff_of_norm ha' norm_fst norm_snd |>.mp ?_
  have fact1 : ∀ᶠ xy in 𝓕, ‖‖xy.1‖⁻¹ • xy.1‖ = 1 ∧ ‖‖xy.2‖⁻¹ • xy.2‖ = 1 := by
    filter_upwards [eventually_gt_of_tendsto_gt ha' norm_fst,
      eventually_gt_of_tendsto_gt ha' norm_snd] with ⟨x, y⟩ hx hy
    simp [norm_smul, hx.ne', hy.ne']
  have fact2 : Tendsto (fun xy ↦ ‖‖xy.1‖⁻¹ • xy.1 + ‖xy.2‖⁻¹ • xy.2‖) 𝓕 (𝓝 2) := by
    rw [← one_add_one_eq_two, ← inv_mul_cancel₀ ha'.ne', ← mul_add]
    refine norm_add.const_mul a'⁻¹ |>.congr_dist ?_
    have : ∀ p : E × E, dist (a'⁻¹ * ‖p.1 + p.2‖) ‖‖p.1‖⁻¹ • p.1 + ‖p.2‖⁻¹ • p.2‖ ≤
        ‖a'⁻¹ - ‖p.1‖⁻¹‖ * ‖p.1‖ + ‖a'⁻¹ - ‖p.2‖⁻¹‖ * ‖p.2‖ := fun p ↦ by
      rw [← norm_smul_of_nonneg (inv_pos.mpr ha').le]
      refine dist_norm_norm_le _ _ |>.trans ?_
      rw [smul_add, add_sub_add_comm, ← sub_smul, ← sub_smul]
      exact norm_add_le_of_le (by rw [norm_smul]) (by rw [norm_smul])
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ ↦ dist_nonneg) this
    simpa using (tendsto_const_nhds (x := a'⁻¹) |>.sub <| norm_fst.inv₀ ha'.ne').norm.mul norm_fst
      |>.add <| (tendsto_const_nhds (x := a'⁻¹) |>.sub <| norm_snd.inv₀ ha'.ne').norm.mul norm_snd
  specialize H (map (Prod.map (fun x ↦ ‖x‖⁻¹ • x) (fun x ↦ ‖x‖⁻¹ • x)) 𝓕)
    (eventually_map.mpr <| fact1.mono fun _ ↦ And.left)
    (eventually_map.mpr <| fact1.mono fun _ ↦ And.right)
    (tendsto_map'_iff.mpr fact2)
  simpa only [uniformity_eq_comap_nhds_zero_swapped, map_le_iff_le_comap, comap_comap,
    ← tendsto_iff_comap] using H

theorem uniformConvexSpace_iff_comap_sphere_le_uniformity :
    UniformConvexSpace E ↔ comap (fun (xy : E × E) ↦ ‖xy.1 + xy.2‖) (𝓝 2 : Filter ℝ) ⊓
      𝓟 (sphere 0 1 ×ˢ sphere 0 1) ≤ 𝓤 E := by
  have : (sphere 0 1 : Set E) = (‖·‖) ⁻¹' {1} := ext fun _ ↦ mem_sphere_zero_iff_norm
  simp_rw [uniformConvexSpace_iff, Metric.uniformity_eq_comap_nhds_zero, dist_eq_norm,
    this, ← prod_principal_principal, ← comap_principal, ← comap_prod]
  sorry

theorem uniformConvexSpace_iff_filter_sphere :
    UniformConvexSpace E :=
  UniformConvexSpace.uniform_convex hε

theorem uniformConvexSpace_iff_comap_sphere_le_uniformity :
    ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ = 1 → ∀ ⦃y⦄, ‖y‖ = 1 → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ :=
  UniformConvexSpace.uniform_convex hε

variable (E) [SeminormedAddCommGroup E] [UniformConvexSpace E] {ε : ℝ}

theorem exists_forall_sphere_dist_add_le_two_sub (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ = 1 → ∀ ⦃y⦄, ‖y‖ = 1 → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ :=
  UniformConvexSpace.uniform_convex hε

variable [NormedSpace ℝ E]

theorem exists_forall_closed_ball_dist_add_le_two_sub (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ ≤ 1 → ∀ ⦃y⦄, ‖y‖ ≤ 1 → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ := by
  have hε' : 0 < ε / 3 := div_pos hε zero_lt_three
  obtain ⟨δ, hδ, h⟩ := exists_forall_sphere_dist_add_le_two_sub E hε'
  set δ' := min (1 / 2) (min (ε / 3) <| δ / 3)
  refine ⟨δ', lt_min one_half_pos <| lt_min hε' (div_pos hδ zero_lt_three), fun x hx y hy hxy => ?_⟩
  obtain hx' | hx' := le_or_lt ‖x‖ (1 - δ')
  · rw [← one_add_one_eq_two]
    exact (norm_add_le_of_le hx' hy).trans (sub_add_eq_add_sub _ _ _).le
  obtain hy' | hy' := le_or_lt ‖y‖ (1 - δ')
  · rw [← one_add_one_eq_two]
    exact (norm_add_le_of_le hx hy').trans (add_sub_assoc _ _ _).ge
  have hδ' : 0 < 1 - δ' := sub_pos_of_lt (min_lt_of_left_lt one_half_lt_one)
  have h₁ : ∀ z : E, 1 - δ' < ‖z‖ → ‖‖z‖⁻¹ • z‖ = 1 := by
    rintro z hz
    rw [norm_smul_of_nonneg (inv_nonneg.2 <| norm_nonneg _), inv_mul_cancel₀ (hδ'.trans hz).ne']
  have h₂ : ∀ z : E, ‖z‖ ≤ 1 → 1 - δ' ≤ ‖z‖ → ‖‖z‖⁻¹ • z - z‖ ≤ δ' := by
    rintro z hz hδz
    nth_rw 3 [← one_smul ℝ z]
    rwa [← sub_smul,
      norm_smul_of_nonneg (sub_nonneg_of_le <| (one_le_inv₀ (hδ'.trans_le hδz)).2 hz),
      sub_mul, inv_mul_cancel₀ (hδ'.trans_le hδz).ne', one_mul, sub_le_comm]
  set x' := ‖x‖⁻¹ • x
  set y' := ‖y‖⁻¹ • y
  have hxy' : ε / 3 ≤ ‖x' - y'‖ :=
    calc
      ε / 3 = ε - (ε / 3 + ε / 3) := by ring
      _ ≤ ‖x - y‖ - (‖x' - x‖ + ‖y' - y‖) := by
        gcongr
        · exact (h₂ _ hx hx'.le).trans <| min_le_of_right_le <| min_le_left _ _
        · exact (h₂ _ hy hy'.le).trans <| min_le_of_right_le <| min_le_left _ _
      _ ≤ _ := by
        have : ∀ x' y', x - y = x' - y' + (x - x') + (y' - y) := fun _ _ => by abel
        rw [sub_le_iff_le_add, norm_sub_rev _ x, ← add_assoc, this]
        exact norm_add₃_le
  calc
    ‖x + y‖ ≤ ‖x' + y'‖ + ‖x' - x‖ + ‖y' - y‖ := by
      have : ∀ x' y', x + y = x' + y' + (x - x') + (y - y') := fun _ _ => by abel
      rw [norm_sub_rev, norm_sub_rev y', this]
      exact norm_add₃_le
    _ ≤ 2 - δ + δ' + δ' :=
      (add_le_add_three (h (h₁ _ hx') (h₁ _ hy') hxy') (h₂ _ hx hx'.le) (h₂ _ hy hy'.le))
    _ ≤ 2 - δ' := by
      dsimp only [δ']
      rw [← le_sub_iff_add_le, ← le_sub_iff_add_le, sub_sub, sub_sub]
      refine sub_le_sub_left ?_ _
      ring_nf
      rw [← mul_div_cancel₀ δ three_ne_zero]
      norm_num
      -- Porting note: these three extra lines needed to make `exact` work
      have : 3 * (δ / 3) * (1 / 3) = δ / 3 := by linarith
      rw [this, mul_comm]
      gcongr
      exact min_le_of_right_le <| min_le_right _ _

theorem exists_forall_closed_ball_dist_add_le_two_mul_sub (hε : 0 < ε) (r : ℝ) :
    ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ ≤ r → ∀ ⦃y⦄, ‖y‖ ≤ r → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 * r - δ := by
  obtain hr | hr := le_or_lt r 0
  · exact ⟨1, one_pos, fun x hx y hy h => (hε.not_le <|
      h.trans <| (norm_sub_le _ _).trans <| add_nonpos (hx.trans hr) (hy.trans hr)).elim⟩
  obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (div_pos hε hr)
  refine ⟨δ * r, mul_pos hδ hr, fun x hx y hy hxy => ?_⟩
  rw [← div_le_one hr, div_eq_inv_mul, ← norm_smul_of_nonneg (inv_nonneg.2 hr.le)] at hx hy
  have := h hx hy
  simp_rw [← smul_add, ← smul_sub, norm_smul_of_nonneg (inv_nonneg.2 hr.le), ← div_eq_inv_mul,
    div_le_div_right hr, div_le_iff₀ hr, sub_mul] at this
  exact this hxy

end SeminormedAddCommGroup

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]

-- See note [lower instance priority]
instance (priority := 100) UniformConvexSpace.toStrictConvexSpace : StrictConvexSpace ℝ E :=
  StrictConvexSpace.of_norm_add_ne_two fun _ _ hx hy hxy =>
    let ⟨_, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (norm_sub_pos_iff.2 hxy)
    ((h hx.le hy.le le_rfl).trans_lt <| sub_lt_self _ hδ).ne
