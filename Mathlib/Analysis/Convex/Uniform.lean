/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Filippo A. E. Nuccio, Aristotle AI
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Topology.Instances.Rat

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

`uniformConvexFilter` is the filter
`(𝓝 2).comap (fun p ↦ ‖p.1 + p.2‖) ⊓ 𝓟 {p | ‖p.1‖ = 1 ∧ ‖p.2‖ = 1}`. It captures pairs `(x, y)` on
the unit sphere whose midpoint norm `‖x + y‖` is close to `2`. Uniform convexity says precisely
that such pairs must be close to each other.

The ε-δ definition quantifies "for all ε > 0, there exists δ > 0 such that on the unit sphere,
`ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ`". The filter formulation is its contrapositive repackaged:
"`2 - δ < ‖x + y‖` implies `‖x - y‖ < ε`" becomes a `Filter.Tendsto` statement.


## Main results

* `UniformConvexSpace.tendsto_norm_sub`: In a uniformly convex space, the map
  `(x, y) ↦ ‖x - y‖` tends to `0` along the filter
  `(𝓝 2).comap (fun p ↦ ‖p.1 + p.2‖) ⊓ 𝓟 {p | ‖p.1‖ = 1 ∧ ‖p.2‖ = 1}`.

* `uniformConvexSpace_of_tendsto_norm_sub`: Conversely, the filter condition implies
  uniform convexity.

* `uniformConvexSpace_iff_tendsto`: The iff combining the above two directions.

* `UniformConvexSpace.tendsto_norm_sub_of_tendsto_norm_add`: For any filter `l` and
  functions `x y : ι → E` with `‖x i‖ = 1`, `‖y i‖ = 1` for all `i`, if
  `‖x i + y i‖ → 2` along `l`, then `‖x i - y i‖ → 0` along `l`.

* `UniformConvexSpace.tendsto_norm_sub_of_tendsto_norm_add_of_norm_le`: A variant where
  the norm-one condition is relaxed to `‖x i‖ ≤ 1` and `‖y i‖ ≤ 1` (requires `NormedSpace ℝ E`).


## TODO

* Milman-Pettis
* Hanner's inequalities

## Tags

convex, uniformly convex
-/

@[expose] public section

open Set Metric

open Convex Pointwise

/-- A *uniformly convex space* is a real normed space where the triangle inequality is strict with a
uniform bound. Namely, over the `x` and `y` of norm `1`, `‖x + y‖` is uniformly bounded above
by a constant `< 2` when `‖x - y‖` is uniformly bounded below by a positive constant. -/
class UniformConvexSpace (E : Type*) [SeminormedAddCommGroup E] : Prop where
  uniform_convex : ∀ ⦃ε : ℝ⦄,
    0 < ε → ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ = 1 → ∀ ⦃y⦄, ‖y‖ = 1 → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ

variable {E : Type*}

section SeminormedAddCommGroup

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
  obtain hx' | hx' := le_or_gt ‖x‖ (1 - δ')
  · rw [← one_add_one_eq_two]
    exact (norm_add_le_of_le hx' hy).trans (sub_add_eq_add_sub _ _ _).le
  obtain hy' | hy' := le_or_gt ‖y‖ (1 - δ')
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
    _ ≤ 2 - δ + δ' + δ' := by
      gcongr
      exacts [h (h₁ _ hx') (h₁ _ hy') hxy', h₂ _ hx hx'.le, h₂ _ hy hy'.le]
    _ ≤ 2 - δ' := by
      suffices δ' ≤ δ / 3 by linarith
      exact min_le_of_right_le <| min_le_right _ _

theorem exists_forall_closed_ball_dist_add_le_two_mul_sub (hε : 0 < ε) (r : ℝ) :
    ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ ≤ r → ∀ ⦃y⦄, ‖y‖ ≤ r → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 * r - δ := by
  obtain hr | hr := le_or_gt r 0
  · exact ⟨1, one_pos, fun x hx y hy h => (hε.not_ge <|
      h.trans <| (norm_sub_le _ _).trans <| add_nonpos (hx.trans hr) (hy.trans hr)).elim⟩
  obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (div_pos hε hr)
  refine ⟨δ * r, mul_pos hδ hr, fun x hx y hy hxy => ?_⟩
  rw [← div_le_one hr, div_eq_inv_mul, ← norm_smul_of_nonneg (inv_nonneg.2 hr.le)] at hx hy
  have := h hx hy
  simp_rw [← smul_add, ← smul_sub, norm_smul_of_nonneg (inv_nonneg.2 hr.le), ← div_eq_inv_mul,
    div_le_div_iff_of_pos_right hr, div_le_iff₀ hr, sub_mul] at this
  exact this hxy

end SeminormedAddCommGroup

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]

-- See note [lower instance priority]
instance (priority := 100) UniformConvexSpace.toStrictConvexSpace : StrictConvexSpace ℝ E :=
  StrictConvexSpace.of_norm_add_ne_two fun _ _ hx hy hxy =>
    let ⟨_, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (norm_sub_pos_iff.2 hxy)
    ((h hx.le hy.le le_rfl).trans_lt <| sub_lt_self _ hδ).ne


section Filter

open Filter Set Metric
open scoped Topology NNReal

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The filter on `E × E` capturing pairs on the unit sphere with `‖x + y‖` close to `2`. -/
def uniformConvexFilter (E : Type*) [SeminormedAddCommGroup E] : Filter (E × E) :=
  (𝓝 2).comap (fun p : E × E => ‖p.1 + p.2‖) ⊓ 𝓟 {p | ‖p.1‖ = 1 ∧ ‖p.2‖ = 1}

/-- In a uniformly convex space, the map `(x, y) ↦ ‖x - y‖` tends to `0` along the filter of
pairs on the unit sphere with `‖x + y‖` close to `2`. -/
theorem UniformConvexSpace.tendsto_norm_sub [UniformConvexSpace E] :
    Tendsto (fun p : E × E => ‖p.1 - p.2‖) (uniformConvexFilter E) (𝓝 0) := by
  rw [Metric.tendsto_nhds, uniformConvexFilter]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 →
      ‖x + y‖ > 2 - δ → ‖x - y‖ < ε := by
    rcases ‹UniformConvexSpace E› with ⟨h⟩
    exact Exists.elim (h hε) fun δ hδ =>
      ⟨δ, hδ.1, fun x y hx hy hxy =>
        not_le.1 fun hxy' => hxy.not_ge (hδ.2 hx hy hxy')⟩
  exact Filter.eventually_inf_principal.2 (by
    rw [Filter.eventually_comap]
    filter_upwards [Ioi_mem_nhds (show 2 - δ < 2 by linarith)] with x hx hx'
    aesop)

/-- If the map `(x, y) ↦ ‖x - y‖` tends to `0` along the filter of pairs on the unit sphere
with `‖x + y‖` close to `2`, then the space is uniformly convex. -/
theorem uniformConvexSpace_of_tendsto_norm_sub
    (h : Tendsto (fun p : E × E => ‖p.1 - p.2‖) (uniformConvexFilter E) (𝓝 0)) :
    UniformConvexSpace E := by
  have hεδ : ∀ ε > 0, ∃ δ > 0, ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 →
      ‖x + y‖ > 2 - δ → ‖x - y‖ < ε := by
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ p : E × E, ‖p.1‖ = 1 → ‖p.2‖ = 1 →
        2 - δ < ‖p.1 + p.2‖ → ‖p.1 - p.2‖ < ε := by
      rw [Metric.tendsto_nhds] at h
      obtain ⟨δ, hδ⟩ := Filter.mem_inf_principal.mp (h ε hε)
      rcases Metric.mem_nhds_iff.mp hδ.1 with ⟨δ', δ'_pos, hδ'⟩
      exact ⟨δ', δ'_pos, fun p hp₁ hp₂ hp₃ => by
        simpa using hδ.2 (hδ' <| mem_ball_iff_norm.mpr <| abs_lt.mpr
          ⟨by linarith, by linarith [norm_add_le p.1 p.2, hp₁, hp₂]⟩) ⟨hp₁, hp₂⟩⟩
    exact ⟨δ, hδ_pos, fun x y hx hy hxy => hδ (x, y) hx hy hxy⟩
  refine ⟨fun ε εpos => ?_⟩
  obtain ⟨δ, δpos, H⟩ := hεδ ε εpos
  exact ⟨δ, δpos, fun x hx y hy hxy => not_lt.1 fun h => hxy.not_gt <| H x y hx hy h⟩

/-- A seminormed space is uniformly convex if and only if the map `(x, y) ↦ ‖x - y‖` tends to `0`
along the filter `(𝓝 2).comap (fun p ↦ ‖p.1 + p.2‖) ⊓ 𝓟 {p | ‖p.1‖ = 1 ∧ ‖p.2‖ = 1}`. -/
theorem uniformConvexSpace_iff_tendsto :
    UniformConvexSpace E ↔
      Tendsto (fun p : E × E => ‖p.1 - p.2‖) (uniformConvexFilter E) (𝓝 0) :=
  ⟨fun _ => UniformConvexSpace.tendsto_norm_sub, uniformConvexSpace_of_tendsto_norm_sub⟩

section Sequences

variable {ι : Type*} {l : Filter ι}

/-- In a uniformly convex space, if `x i` and `y i` lie on the unit sphere and
`‖x i + y i‖ → 2` along a filter `l`, then `‖x i - y i‖ → 0` along `l`. -/
theorem UniformConvexSpace.tendsto_norm_sub_of_tendsto_norm_add [UniformConvexSpace E]
    {x y : ι → E} (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (h : Tendsto (fun i => ‖x i + y i‖) l (𝓝 2)) :
    Tendsto (fun i => ‖x i - y i‖) l (𝓝 0) := by
  have h_tendsto_map : Tendsto (fun i => (x i, y i)) l (uniformConvexFilter E) := by
    refine Filter.tendsto_inf.mpr ⟨?_, ?_⟩ <;> aesop;
  exact UniformConvexSpace.tendsto_norm_sub.comp h_tendsto_map

/-- Uniform convexity can be checked via the net/sequence criterion: if for every filter `l`
and functions `x y` on the unit sphere, `‖x i + y i‖ → 2` implies `‖x i - y i‖ → 0`,
then the space is uniformly convex. -/
theorem uniformConvexSpace_of_tendsto_norm_sub_of_tendsto_norm_add
    (h : ∀ (ι : Type*) (l : Filter ι) (x y : ι → E),
      (∀ i, ‖x i‖ = 1) → (∀ i, ‖y i‖ = 1) →
      Tendsto (fun i => ‖x i + y i‖) l (𝓝 2) →
      Tendsto (fun i => ‖x i - y i‖) l (𝓝 0)) :
    UniformConvexSpace E := by
  by_contra h_not_uniform_convex;
  obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ δ > 0, ∃ x y : E, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ ‖x - y‖ ≥ ε ∧
      ‖x + y‖ > 2 - δ := by
    contrapose! h_not_uniform_convex;
    refine ⟨fun ε hε => ?_⟩;
    grind;
  obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : ℕ → E, (∀ n, ‖x n‖ = 1) ∧ (∀ n, ‖y n‖ = 1) ∧
      (∀ n, ‖x n - y n‖ ≥ ε) ∧ (∀ n, ‖x n + y n‖ > 2 - 1 / (n + 2)) := by
    choose x y hxy using fun n : ℕ => hε.2 ( 1 / ( n + 2 ) ) ( by positivity );
    exact ⟨x, y, fun n => hxy n |>.1, fun n => hxy n |>.2.1, fun n => hxy n |>.2.2.1, fun n ↦
         hxy n |>.2.2.2⟩
  have h_sum : Filter.Tendsto (fun n => ‖x n + y n‖) Filter.atTop (nhds 2) := by
    have h_sum : ∀ n, ‖x n + y n‖ ≤ 2 := by
      exact fun n => le_trans ( norm_add_le _ _ ) ( by linarith [ hx n, hy n ])
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (α := ℝ) (β := ℕ) (b := (atTop : Filter ℕ))
    · have := @Tendsto.sub (G := ℝ) (α := ℕ) _ _ _ (f := fun n ↦ 2) (g := fun n ↦ 1/(n + 2))
        (l := atTop) (a := 2) (b := 0) (by simp) ?_
      · simpa [sub_zero]
      exact tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _
        tendsto_natCast_atTop_atTop
    · exact tendsto_const_nhds
    · intro; grind
    · intro; grind
  specialize h ( ULift ℕ ) ( Filter.map ULift.up Filter.atTop ) ( fun n => x n.down )
    ( fun n => y n.down )
  simp_all only [gt_iff_lt, ge_iff_le, exists_and_left, one_div, implies_true, tendsto_map'_iff,
    forall_const]
  apply absurd ( h ( h_sum.comp ( Filter.tendsto_atTop_atTop.mpr fun n => ⟨ n, fun m hm => hm⟩)))--
  intro H
  apply absurd ( le_of_tendsto_of_tendsto' tendsto_const_nhds H fun n => hxy.1 _ )
  linarith

/-- A seminormed space is uniformly convex if and only if for every filter `l` and functions
`x y : ι → E` with `‖x i‖ = 1` and `‖y i‖ = 1`, `‖x i + y i‖ → 2` along `l` implies
`‖x i - y i‖ → 0` along `l`. -/
theorem uniformConvexSpace_iff_tendsto_norm_sub_of_tendsto_norm_add :
    UniformConvexSpace E ↔
      ∀ (ι : Type*) (l : Filter ι) (x y : ι → E),
        (∀ i, ‖x i‖ = 1) → (∀ i, ‖y i‖ = 1) →
        Tendsto (fun i => ‖x i + y i‖) l (𝓝 2) →
        Tendsto (fun i => ‖x i - y i‖) l (𝓝 0) :=
  ⟨fun _ _ _ _ _ hx hy h => UniformConvexSpace.tendsto_norm_sub_of_tendsto_norm_add hx hy h,
   uniformConvexSpace_of_tendsto_norm_sub_of_tendsto_norm_add⟩

end Sequences

section ClosedBall

variable [NormedSpace ℝ E] {ι : Type*} {l : Filter ι}

/-- In a uniformly convex normed space, if `x i` and `y i` have norm at most `1` and
`‖x i + y i‖ → 2` along a filter `l`, then `‖x i - y i‖ → 0` along `l`. -/
theorem UniformConvexSpace.tendsto_norm_sub_of_tendsto_norm_add_of_norm_le [UniformConvexSpace E]
    {x y : ι → E} (hx : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1)
    (h : Tendsto (fun i => ‖x i + y i‖) l (𝓝 2)) :
    Tendsto (fun i => ‖x i - y i‖) l (𝓝 0) := by
  rw [Metric.tendsto_nhds] at *
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖x + y‖ > 2 - δ → ‖x - y‖ < ε := by
    exact Exists.elim (exists_forall_closed_ball_dist_add_le_two_sub E hε) fun δ hδ =>
      ⟨δ, hδ.1, fun x y hx hy hxy =>
        not_le.1 fun h => hxy.not_ge (hδ.2 hx hy h)⟩
  filter_upwards [h δ hδ_pos] with i hi using by
    simpa using hδ (x i) (y i) (hx i) (hy i) (by linarith [abs_lt.mp hi])

end ClosedBall

end Filter
