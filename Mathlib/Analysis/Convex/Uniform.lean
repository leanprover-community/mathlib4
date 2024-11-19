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

theorem dist_div_norm_self_div_norm_self_le {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {x y : E} (hx : ‖x‖ ≠ 0) (hy : ‖y‖ ≠ 0) :
    dist (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) ≤ ‖x‖⁻¹ * dist x y + (‖y‖ - ‖x‖) :=
  calc dist (‖x‖⁻¹ • x) (‖y‖⁻¹ • y)
    _ = ‖(‖x‖⁻¹ • x - ‖x‖⁻¹ • y) + (‖x‖⁻¹ • y - ‖y‖⁻¹ • y)‖ := by
        simp_rw [dist_eq_norm, sub_add_sub_cancel]
    _ ≤ ‖‖x‖⁻¹ • x - ‖x‖⁻¹ • y‖ + ‖‖x‖⁻¹ • y - ‖y‖⁻¹ • y‖ := norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x - y‖ + ‖‖x‖⁻¹ • y - ‖y‖⁻¹ • y‖ := norm_add_le _ _
    _ ≤ ‖x‖⁻¹ * dist x y + (‖y‖ - ‖x‖) := sorry

theorem div_norm_self_tendsto_uniformity_iff

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
  protected comap_norm_add_le_uniformity : ∀ a : ℝ,
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
    UniformConvexSpace E ↔ ∀ a : ℝ, ∀ 𝓕 : Filter (E × E),
      Tendsto (fun xy ↦ ‖xy.1‖) 𝓕 (𝓝 a) →
      Tendsto (fun xy ↦ ‖xy.2‖) 𝓕 (𝓝 a) →
      Tendsto (fun xy ↦ ‖xy.1 + xy.2‖) 𝓕 (𝓝 (a+a)) →
      𝓕 ≤ 𝓤 E := by
  rw [uniformConvexSpace_iff_comap_norm_add_le_uniformity]
  congrm ∀ a, ?_
  rw [← forall_le_iff_le]
  congrm ∀ 𝓕, ?_
  simp_rw [← tendsto_iff_comap, nhds_prod_eq, tendsto_prod_iff', and_imp]

theorem tendsto_uniformity_of_norm_add {ι : Type*} [H : UniformConvexSpace E]
    {a : ℝ} {𝓕 : Filter ι} {f g : ι → E} (norm_f : Tendsto (fun i ↦ ‖f i‖) 𝓕 (𝓝 a))
    (norm_g : Tendsto (fun i ↦ ‖g i‖) 𝓕 (𝓝 a))
    (norm_add : Tendsto (fun i ↦ ‖f i + g i‖) 𝓕 (𝓝 (a+a))) :
    Tendsto (fun i ↦ (f i, g i)) 𝓕 (𝓤 E) := by
  apply uniformConvexSpace_iff_le_uniformity_of_norm_add.mp H a (map (fun i ↦ (f i, g i)) 𝓕) <;>
  rwa [tendsto_map'_iff]

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
  set φ : E × E → ℝ × ℝ × ℝ := fun xy ↦ ⟨‖xy.1‖, ‖xy.2‖, ‖xy.1 + xy.2‖⟩
  set 𝓕 := comap φ (𝓟 (Iic a) ×ˢ 𝓟 (Iic a) ×ˢ (𝓝 (a+a)))
  have norm_fst : ∀ᶠ xy in 𝓕, ‖xy.1‖ ≤ a := (tendsto_fst.eventually <| mem_principal_self _).comap φ
  have norm_snd : ∀ᶠ xy in 𝓕, ‖xy.2‖ ≤ a :=
    (tendsto_snd.eventually <| tendsto_fst.eventually <| mem_principal_self _).comap φ
  have norm_add : Tendsto (fun xy ↦ ‖xy.1 + xy.2‖) 𝓕 (𝓝 (a+a)) :=
    tendsto_snd.comp <| tendsto_snd.comp tendsto_comap
  have := tendsto_uniformity_of_norm_add_of_closedBall norm_fst norm_snd norm_add
    |>.eventually (dist_mem_uniformity ε_pos)
  simp_rw [𝓕, comap_prod, comap_principal, inf_comm (𝓟 _),
    eventually_inf_principal, nhds_basis_ball.comap _ |>.eventually_iff, Prod.forall,
    Real.ball_eq_Ioo, dist_eq_norm] at this
  rcases this with ⟨δ, δ_pos, hδ⟩
  exact ⟨δ, δ_pos, fun _ hxa _ hyb ↦ le_imp_le_of_lt_imp_lt fun hxy ↦ hδ _ _
    ⟨hxy, lt_add_of_le_of_pos (norm_add_le_of_le hxa hyb) δ_pos⟩ hyb hxa⟩

#check Real.uniformContinuous_mul

theorem uniformConvexSpace_iff_tendsto_uniformity_of_norm_add_of_unit_sphere
    [NormedSpace ℝ E] :
    UniformConvexSpace E ↔ ∀ 𝓕 : Filter (E × E),
      (∀ᶠ xy in 𝓕, ‖xy.1‖ = 1) →
      (∀ᶠ xy in 𝓕, ‖xy.2‖ = 1) →
      Tendsto (fun xy ↦ ‖xy.1 + xy.2‖) 𝓕 (𝓝 2) →
      𝓕 ≤ 𝓤 E := by
  refine ⟨fun H 𝓕 ↦ one_add_one_eq_two (R := ℝ) ▸ tendsto_uniformity_of_norm_add_of_sphere,
    fun H ↦ uniformConvexSpace_iff_le_uniformity_of_norm_add.mpr
      fun a' 𝓕 norm_fst norm_snd norm_add ↦ ?_⟩
  rcases eq_or_ne a' 0 with (rfl|ha)
  · rw [← tendsto_zero_iff_norm_tendsto_zero] at norm_fst norm_snd
    exact le_trans (Filter.le_prod.mpr ⟨norm_fst, norm_snd⟩)
      (nhds_prod_eq (X := E) (Y := E) ▸ nhds_le_uniformity (0 : E))
  --have ρ_tendsto : Tendsto ρ 𝓕 (𝓝 (a⁻¹ * a')) :=
  --  .const_mul a⁻¹ (max_self a' ▸ .max norm_fst norm_snd)
  set Φ : E × E → E × E := fun xy ↦ (‖xy.1‖ • xy.1, ‖xy.2‖ • xy.2) with Φ_def
  have Φ_tendsto : map Φ 𝓕 ≤ 𝓤 E := H _ sorry sorry sorry
  have : 𝓕 ⊓ 𝓤 E = 𝓕 ⊓ comap Φ (𝓤 E) := by
    refine le_antisymm (le_inf inf_le_left <| inf_le_of_left_le <|
      map_le_iff_le_comap.mp Φ_tendsto) (le_inf inf_le_left ?_)
    simp_rw [Metric.uniformity_eq_comap_nhds_zero, dist_eq_norm, comap_comap, Φ_def,
      Function.comp_def, ← tendsto_iff_comap]
    have key : ∀ p : E × E, ‖‖p.1‖ • p.1 ‖
    refine tendsto_inf_right tendsto_comap |>.congr_dist ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ _ _
    --have : Tendsto (fun )
    --refine (mul_zero ‖a‖ ▸ (tendsto_inf_left tendsto_comap).const_mul ‖a‖).congr_dist ?_
  rwa [← inf_eq_left, this, inf_eq_left, ← map_le_iff_le_comap]

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
