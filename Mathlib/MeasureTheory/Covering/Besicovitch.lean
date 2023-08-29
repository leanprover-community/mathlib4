/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Covering.VitaliFamily
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Topology.MetricSpace.Basic

#align_import measure_theory.covering.besicovitch from "leanprover-community/mathlib"@"5f6e827d81dfbeb6151d7016586ceeb0099b9655"

/-!
# Besicovitch covering theorems

The topological Besicovitch covering theorem ensures that, in a nice metric space, there exists a
number `N` such that, from any family of balls with bounded radii, one can extract `N` families,
each made of disjoint balls, covering together all the centers of the initial family.

By "nice metric space", we mean a technical property stated as follows: there exists no satellite
configuration of `N + 1` points (with a given parameter `τ > 1`). Such a configuration is a family
of `N + 1` balls, where the first `N` balls all intersect the last one, but none of them contains
the center of another one and their radii are controlled. This property is for instance
satisfied by finite-dimensional real vector spaces.

In this file, we prove the topological Besicovitch covering theorem,
in `Besicovitch.exist_disjoint_covering_families`.

The measurable Besicovitch theorem ensures that, in the same class of metric spaces, if at every
point one considers a class of balls of arbitrarily small radii, called admissible balls, then
one can cover almost all the space by a family of disjoint admissible balls.
It is deduced from the topological Besicovitch theorem, and proved
in `Besicovitch.exists_disjoint_closedBall_covering_ae`.

This implies that balls of small radius form a Vitali family in such spaces. Therefore, theorems
on differentiation of measures hold as a consequence of general results. We restate them in this
context to make them more easily usable.

## Main definitions and results

* `SatelliteConfig α N τ` is the type of all satellite configurations of `N + 1` points
  in the metric space `α`, with parameter `τ`.
* `HasBesicovitchCovering` is a class recording that there exist `N` and `τ > 1` such that
  there is no satellite configuration of `N + 1` points with parameter `τ`.
* `exist_disjoint_covering_families` is the topological Besicovitch covering theorem: from any
  family of balls one can extract finitely many disjoint subfamilies covering the same set.
* `exists_disjoint_closedBall_covering` is the measurable Besicovitch covering theorem: from any
  family of balls with arbitrarily small radii at every point, one can extract countably many
  disjoint balls covering almost all the space. While the value of `N` is relevant for the precise
  statement of the topological Besicovitch theorem, it becomes irrelevant for the measurable one.
  Therefore, this statement is expressed using the `Prop`-valued
  typeclass `HasBesicovitchCovering`.

We also restate the following specialized versions of general theorems on differentiation of
measures:
* `Besicovitch.ae_tendsto_rnDeriv` ensures that `ρ (closedBall x r) / μ (closedBall x r)` tends
  almost surely to the Radon-Nikodym derivative of `ρ` with respect to `μ` at `x`.
* `Besicovitch.ae_tendsto_measure_inter_div` states that almost every point in an arbitrary set `s`
  is a Lebesgue density point, i.e., `μ (s ∩ closedBall x r) / μ (closedBall x r)` tends to `1` as
  `r` tends to `0`. A stronger version for measurable sets is given in
  `Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`.

## Implementation

#### Sketch of proof of the topological Besicovitch theorem:

We choose balls in a greedy way. First choose a ball with maximal radius (or rather, since there
is no guarantee the maximal radius is realized, a ball with radius within a factor `τ` of the
supremum). Then, remove all balls whose center is covered by the first ball, and choose among the
remaining ones a ball with radius close to maximum. Go on forever until there is no available
center (this is a transfinite induction in general).

Then define inductively a coloring of the balls. A ball will be of color `i` if it intersects
already chosen balls of color `0`, ..., `i - 1`, but none of color `i`. In this way, balls of the
same color form a disjoint family, and the space is covered by the families of the different colors.

The nontrivial part is to show that at most `N` colors are used. If one needs `N + 1` colors,
consider the first time this happens. Then the corresponding ball intersects `N` balls of the
different colors. Moreover, the inductive construction ensures that the radii of all the balls are
controlled: they form a satellite configuration with `N + 1` balls (essentially by definition of
satellite configurations). Since we assume that there are no such configurations, this is a
contradiction.

#### Sketch of proof of the measurable Besicovitch theorem:

From the topological Besicovitch theorem, one can find a disjoint countable family of balls
covering a proportion `> 1 / (N + 1)` of the space. Taking a large enough finite subset of these
balls, one gets the same property for finitely many balls. Their union is closed. Therefore, any
point in the complement has around it an admissible ball not intersecting these finitely many balls.
Applying again the topological Besicovitch theorem, one extracts from these a disjoint countable
subfamily covering a proportion `> 1 / (N + 1)` of the remaining points, and then even a disjoint
finite subfamily. Then one goes on again and again, covering at each step a positive proportion of
the remaining points, while remaining disjoint from the already chosen balls. The union of all these
balls is the desired almost everywhere covering.
-/


noncomputable section

universe u

open Metric Set Filter Fin MeasureTheory TopologicalSpace

open scoped Topology Classical BigOperators ENNReal MeasureTheory NNReal

/-!
### Satellite configurations
-/


/-- A satellite configuration is a configuration of `N+1` points that shows up in the inductive
construction for the Besicovitch covering theorem. It depends on some parameter `τ ≥ 1`.

This is a family of balls (indexed by `i : Fin N.succ`, with center `c i` and radius `r i`) such
that the last ball intersects all the other balls (condition `inter`),
and given any two balls there is an order between them, ensuring that the first ball does not
contain the center of the other one, and the radius of the second ball can not be larger than
the radius of the first ball (up to a factor `τ`). This order corresponds to the order of choice
in the inductive construction: otherwise, the second ball would have been chosen before.
This is the condition `h`.

Finally, the last ball is chosen after all the other ones, meaning that `h` can be strengthened
by keeping only one side of the alternative in `hlast`.
-/
structure Besicovitch.SatelliteConfig (α : Type*) [MetricSpace α] (N : ℕ) (τ : ℝ) where
  c : Fin N.succ → α
  r : Fin N.succ → ℝ
  rpos : ∀ i, 0 < r i
  h : ∀ i j, i ≠ j → r i ≤ dist (c i) (c j) ∧ r j ≤ τ * r i ∨ r j ≤ dist (c j) (c i) ∧ r i ≤ τ * r j
  hlast : ∀ i < last N, r i ≤ dist (c i) (c (last N)) ∧ r (last N) ≤ τ * r i
  inter : ∀ i < last N, dist (c i) (c (last N)) ≤ r i + r (last N)
#align besicovitch.satellite_config Besicovitch.SatelliteConfig
#align besicovitch.satellite_config.c Besicovitch.SatelliteConfig.c
#align besicovitch.satellite_config.r Besicovitch.SatelliteConfig.r
#align besicovitch.satellite_config.rpos Besicovitch.SatelliteConfig.rpos
#align besicovitch.satellite_config.h Besicovitch.SatelliteConfig.h
#align besicovitch.satellite_config.hlast Besicovitch.SatelliteConfig.hlast
#align besicovitch.satellite_config.inter Besicovitch.SatelliteConfig.inter

/-- A metric space has the Besicovitch covering property if there exist `N` and `τ > 1` such that
there are no satellite configuration of parameter `τ` with `N+1` points. This is the condition that
guarantees that the measurable Besicovitch covering theorem holds. It is satisfied by
finite-dimensional real vector spaces. -/
class HasBesicovitchCovering (α : Type*) [MetricSpace α] : Prop where
  no_satelliteConfig : ∃ (N : ℕ) (τ : ℝ), 1 < τ ∧ IsEmpty (Besicovitch.SatelliteConfig α N τ)
#align has_besicovitch_covering HasBesicovitchCovering
#align has_besicovitch_covering.no_satellite_config HasBesicovitchCovering.no_satelliteConfig

/-- There is always a satellite configuration with a single point. -/
instance Besicovitch.SatelliteConfig.instInhabited {α : Type*} {τ : ℝ}
    [Inhabited α] [MetricSpace α] : Inhabited (Besicovitch.SatelliteConfig α 0 τ) :=
  ⟨{  c := default
      r := fun _ => 1
      rpos := fun _ => zero_lt_one
      h := fun i j hij => (hij (Subsingleton.elim (α := Fin 1) i j)).elim
      hlast := fun i hi => by
        rw [Subsingleton.elim (α := Fin 1) i (last 0)] at hi; exact (lt_irrefl _ hi).elim
        -- ⊢ (fun x => 1) i ≤ dist (default i) (default (last 0)) ∧ (fun x => 1) (last 0) …
                                                              -- 🎉 no goals
      inter := fun i hi => by
        rw [Subsingleton.elim (α := Fin 1) i (last 0)] at hi; exact (lt_irrefl _ hi).elim }⟩
        -- ⊢ dist (default i) (default (last 0)) ≤ (fun x => 1) i + (fun x => 1) (last 0)
                                                              -- 🎉 no goals
#align besicovitch.satellite_config.inhabited Besicovitch.SatelliteConfig.instInhabited

namespace Besicovitch

namespace SatelliteConfig

variable {α : Type*} [MetricSpace α] {N : ℕ} {τ : ℝ} (a : SatelliteConfig α N τ)

theorem inter' (i : Fin N.succ) : dist (a.c i) (a.c (last N)) ≤ a.r i + a.r (last N) := by
  rcases lt_or_le i (last N) with (H | H)
  -- ⊢ dist (c a i) (c a (last N)) ≤ r a i + r a (last N)
  · exact a.inter i H
    -- 🎉 no goals
  · have I : i = last N := top_le_iff.1 H
    -- ⊢ dist (c a i) (c a (last N)) ≤ r a i + r a (last N)
    have := (a.rpos (last N)).le
    -- ⊢ dist (c a i) (c a (last N)) ≤ r a i + r a (last N)
    simp only [I, add_nonneg this this, dist_self]
    -- 🎉 no goals
#align besicovitch.satellite_config.inter' Besicovitch.SatelliteConfig.inter'

theorem hlast' (i : Fin N.succ) (h : 1 ≤ τ) : a.r (last N) ≤ τ * a.r i := by
  rcases lt_or_le i (last N) with (H | H)
  -- ⊢ r a (last N) ≤ τ * r a i
  · exact (a.hlast i H).2
    -- 🎉 no goals
  · have : i = last N := top_le_iff.1 H
    -- ⊢ r a (last N) ≤ τ * r a i
    rw [this]
    -- ⊢ r a (last N) ≤ τ * r a (last N)
    exact le_mul_of_one_le_left (a.rpos _).le h
    -- 🎉 no goals
#align besicovitch.satellite_config.hlast' Besicovitch.SatelliteConfig.hlast'

end SatelliteConfig

/-! ### Extracting disjoint subfamilies from a ball covering -/


/-- A ball package is a family of balls in a metric space with positive bounded radii. -/
structure BallPackage (β : Type*) (α : Type*) where
  c : β → α
  r : β → ℝ
  rpos : ∀ b, 0 < r b
  r_bound : ℝ
  r_le : ∀ b, r b ≤ r_bound
#align besicovitch.ball_package Besicovitch.BallPackage
#align besicovitch.ball_package.c Besicovitch.BallPackage.c
#align besicovitch.ball_package.r Besicovitch.BallPackage.r
#align besicovitch.ball_package.rpos Besicovitch.BallPackage.rpos
#align besicovitch.ball_package.r_bound Besicovitch.BallPackage.r_bound
#align besicovitch.ball_package.r_le Besicovitch.BallPackage.r_le

/-- The ball package made of unit balls. -/
def unitBallPackage (α : Type*) : BallPackage α α where
  c := id
  r _ := 1
  rpos _ := zero_lt_one
  r_bound := 1
  r_le _ := le_rfl
#align besicovitch.unit_ball_package Besicovitch.unitBallPackage

instance BallPackage.instInhabited (α : Type*) : Inhabited (BallPackage α α) :=
  ⟨unitBallPackage α⟩
#align besicovitch.ball_package.inhabited Besicovitch.BallPackage.instInhabited

/-- A Besicovitch tau-package is a family of balls in a metric space with positive bounded radii,
together with enough data to proceed with the Besicovitch greedy algorithm. We register this in
a single structure to make sure that all our constructions in this algorithm only depend on
one variable. -/
structure TauPackage (β : Type*) (α : Type*) extends BallPackage β α where
  τ : ℝ
  one_lt_tau : 1 < τ
#align besicovitch.tau_package Besicovitch.TauPackage
#align besicovitch.tau_package.τ Besicovitch.TauPackage.τ
#align besicovitch.tau_package.one_lt_tau Besicovitch.TauPackage.one_lt_tau

instance TauPackage.instInhabited (α : Type*) : Inhabited (TauPackage α α) :=
  ⟨{ unitBallPackage α with
      τ := 2
      one_lt_tau := one_lt_two }⟩
#align besicovitch.tau_package.inhabited Besicovitch.TauPackage.instInhabited

variable {α : Type*} [MetricSpace α] {β : Type u}

namespace TauPackage

variable [Nonempty β] (p : TauPackage β α)

/-- Choose inductively large balls with centers that are not contained in the union of already
chosen balls. This is a transfinite induction. -/
noncomputable def index : Ordinal.{u} → β
  | i =>
      -- `Z` is the set of points that are covered by already constructed balls
      let Z := ⋃ j : { j // j < i }, ball (p.c (index j)) (p.r (index j))
      -- `R` is the supremum of the radii of balls with centers not in `Z`
      let R := iSup fun b : { b : β // p.c b ∉ Z } => p.r b
      -- return an index `b` for which the center `c b` is not in `Z`, and the radius is at
      -- least `R / τ`, if such an index exists (and garbage otherwise).
      Classical.epsilon fun b : β => p.c b ∉ Z ∧ R ≤ p.τ * p.r b
  termination_by index i => i
  decreasing_by exact j.2
                -- 🎉 no goals
                -- 🎉 no goals
#align besicovitch.tau_package.index Besicovitch.TauPackage.index

/-- The set of points that are covered by the union of balls selected at steps `< i`. -/
def iUnionUpTo (i : Ordinal.{u}) : Set α :=
  ⋃ j : { j // j < i }, ball (p.c (p.index j)) (p.r (p.index j))
#align besicovitch.tau_package.Union_up_to Besicovitch.TauPackage.iUnionUpTo

theorem monotone_iUnionUpTo : Monotone p.iUnionUpTo := by
  intro i j hij
  -- ⊢ iUnionUpTo p i ≤ iUnionUpTo p j
  simp only [iUnionUpTo]
  -- ⊢ ⋃ (j : { j // j < i }), ball (BallPackage.c p.toBallPackage (index p ↑j)) (B …
  exact iUnion_mono' fun r => ⟨⟨r, r.2.trans_le hij⟩, Subset.rfl⟩
  -- 🎉 no goals
#align besicovitch.tau_package.monotone_Union_up_to Besicovitch.TauPackage.monotone_iUnionUpTo

/-- Supremum of the radii of balls whose centers are not yet covered at step `i`. -/
def R (i : Ordinal.{u}) : ℝ :=
  iSup fun b : { b : β // p.c b ∉ p.iUnionUpTo i } => p.r b
set_option linter.uppercaseLean3 false in
#align besicovitch.tau_package.R Besicovitch.TauPackage.R

/-- Group the balls into disjoint families, by assigning to a ball the smallest color for which
it does not intersect any already chosen ball of this color. -/
noncomputable def color : Ordinal.{u} → ℕ
  | i =>
    let A : Set ℕ :=
      ⋃ (j : { j // j < i })
        (_ : (closedBall (p.c (p.index j)) (p.r (p.index j)) ∩
          closedBall (p.c (p.index i)) (p.r (p.index i))).Nonempty), {color j}
    sInf (univ \ A)
  termination_by color i => i
  decreasing_by exact j.2
                -- 🎉 no goals
#align besicovitch.tau_package.color Besicovitch.TauPackage.color

/-- `p.lastStep` is the first ordinal where the construction stops making sense, i.e., `f` returns
garbage since there is no point left to be chosen. We will only use ordinals before this step. -/
def lastStep : Ordinal.{u} :=
  sInf {i | ¬∃ b : β, p.c b ∉ p.iUnionUpTo i ∧ p.R i ≤ p.τ * p.r b}
#align besicovitch.tau_package.last_step Besicovitch.TauPackage.lastStep

theorem lastStep_nonempty :
    {i | ¬∃ b : β, p.c b ∉ p.iUnionUpTo i ∧ p.R i ≤ p.τ * p.r b}.Nonempty := by
  by_contra h
  -- ⊢ False
  suffices H : Function.Injective p.index; exact not_injective_of_ordinal p.index H
  -- ⊢ False
                                           -- ⊢ Function.Injective (index p)
  intro x y hxy
  -- ⊢ x = y
  wlog x_le_y : x ≤ y generalizing x y
  -- ⊢ x = y
  · exact (this hxy.symm (le_of_not_le x_le_y)).symm
    -- 🎉 no goals
  rcases eq_or_lt_of_le x_le_y with (rfl | H); · rfl
  -- ⊢ x = x
                                                 -- 🎉 no goals
  simp only [nonempty_def, not_exists, exists_prop, not_and, not_lt, not_le, mem_setOf_eq,
    not_forall] at h
  specialize h y
  -- ⊢ x = y
  have A : p.c (p.index y) ∉ p.iUnionUpTo y := by
    have :
        p.index y =
          Classical.epsilon fun b : β => p.c b ∉ p.iUnionUpTo y ∧ p.R y ≤ p.τ * p.r b := by
      rw [TauPackage.index]; rfl
    rw [this]
    exact (Classical.epsilon_spec h).1
  simp only [iUnionUpTo, not_exists, exists_prop, mem_iUnion, mem_closedBall, not_and, not_le,
    Subtype.exists, Subtype.coe_mk] at A
  specialize A x H
  -- ⊢ x = y
  simp [hxy] at A
  -- ⊢ x = y
  exact (lt_irrefl _ ((p.rpos (p.index y)).trans_le A)).elim
  -- 🎉 no goals
#align besicovitch.tau_package.last_step_nonempty Besicovitch.TauPackage.lastStep_nonempty

/-- Every point is covered by chosen balls, before `p.lastStep`. -/
theorem mem_iUnionUpTo_lastStep (x : β) : p.c x ∈ p.iUnionUpTo p.lastStep := by
  have A : ∀ z : β, p.c z ∈ p.iUnionUpTo p.lastStep ∨ p.τ * p.r z < p.R p.lastStep := by
    have : p.lastStep ∈ {i | ¬∃ b : β, p.c b ∉ p.iUnionUpTo i ∧ p.R i ≤ p.τ * p.r b} :=
      csInf_mem p.lastStep_nonempty
    simpa only [not_exists, mem_setOf_eq, not_and_or, not_le, not_not_mem]
  by_contra h
  -- ⊢ False
  rcases A x with (H | H); · exact h H
  -- ⊢ False
                             -- 🎉 no goals
  have Rpos : 0 < p.R p.lastStep := by
    apply lt_trans (mul_pos (_root_.zero_lt_one.trans p.one_lt_tau) (p.rpos _)) H
  have B : p.τ⁻¹ * p.R p.lastStep < p.R p.lastStep := by
    conv_rhs => rw [← one_mul (p.R p.lastStep)]
    exact mul_lt_mul (inv_lt_one p.one_lt_tau) le_rfl Rpos zero_le_one
  obtain ⟨y, hy1, hy2⟩ :
      ∃ y : β, p.c y ∉ p.iUnionUpTo p.lastStep ∧ p.τ⁻¹ * p.R p.lastStep < p.r y := by
    have := exists_lt_of_lt_csSup ?_ B
    · simpa only [exists_prop, mem_range, exists_exists_and_eq_and, Subtype.exists,
      Subtype.coe_mk]
    rw [← image_univ, nonempty_image_iff]
    exact ⟨⟨_, h⟩, mem_univ _⟩
  rcases A y with (Hy | Hy)
  -- ⊢ False
  · exact hy1 Hy
    -- 🎉 no goals
  · rw [← div_eq_inv_mul] at hy2
    -- ⊢ False
    have := (div_le_iff' (_root_.zero_lt_one.trans p.one_lt_tau)).1 hy2.le
    -- ⊢ False
    exact lt_irrefl _ (Hy.trans_le this)
    -- 🎉 no goals
#align besicovitch.tau_package.mem_Union_up_to_last_step Besicovitch.TauPackage.mem_iUnionUpTo_lastStep

/-- If there are no configurations of satellites with `N+1` points, one never uses more than `N`
distinct families in the Besicovitch inductive construction. -/
theorem color_lt {i : Ordinal.{u}} (hi : i < p.lastStep) {N : ℕ}
    (hN : IsEmpty (SatelliteConfig α N p.τ)) : p.color i < N := by
  /- By contradiction, consider the first ordinal `i` for which one would have `p.color i = N`.
    Choose for each `k < N` a ball with color `k` that intersects the ball at color `i`
    (there is such a ball, otherwise one would have used the color `k` and not `N`).
    Then this family of `N+1` balls forms a satellite configuration, which is forbidden by
    the assumption `hN`. -/
  induction' i using Ordinal.induction with i IH
  -- ⊢ color p i < N
  let A : Set ℕ :=
    ⋃ (j : { j // j < i })
      (_ : (closedBall (p.c (p.index j)) (p.r (p.index j)) ∩
        closedBall (p.c (p.index i)) (p.r (p.index i))).Nonempty),
      {p.color j}
  have color_i : p.color i = sInf (univ \ A) := by rw [color]
  -- ⊢ color p i < N
  rw [color_i]
  -- ⊢ sInf (univ \ A) < N
  have N_mem : N ∈ univ \ A := by
    simp only [not_exists, true_and_iff, exists_prop, mem_iUnion, mem_singleton_iff, mem_closedBall,
      not_and, mem_univ, mem_diff, Subtype.exists, Subtype.coe_mk]
    intro j ji _
    exact (IH j ji (ji.trans hi)).ne'
  suffices sInf (univ \ A) ≠ N by
    rcases(csInf_le (OrderBot.bddBelow (univ \ A)) N_mem).lt_or_eq with (H | H)
    · exact H
    · exact (this H).elim
  intro Inf_eq_N
  -- ⊢ False
  have :
    ∀ k, k < N → ∃ j, j < i ∧
      (closedBall (p.c (p.index j)) (p.r (p.index j)) ∩
        closedBall (p.c (p.index i)) (p.r (p.index i))).Nonempty ∧ k = p.color j := by
    intro k hk
    rw [← Inf_eq_N] at hk
    have : k ∈ A := by
      simpa only [true_and_iff, mem_univ, Classical.not_not, mem_diff] using
        Nat.not_mem_of_lt_sInf hk
    simp [and_assoc, -exists_and_left] at this
    simpa only [exists_prop, mem_iUnion, mem_singleton_iff, mem_closedBall, Subtype.exists,
      Subtype.coe_mk]
  choose! g hg using this
  -- ⊢ False
  -- Choose for each `k < N` an ordinal `G k < i` giving a ball of color `k` intersecting
  -- the last ball.
  let G : ℕ → Ordinal := fun n => if n = N then i else g n
  -- ⊢ False
  have color_G : ∀ n, n ≤ N → p.color (G n) = n := by
    intro n hn
    rcases hn.eq_or_lt with (rfl | H)
    · simp only; simp only [color_i, Inf_eq_N, if_true, eq_self_iff_true]
    · simp only; simp only [H.ne, (hg n H).right.right.symm, if_false]
  have G_lt_last : ∀ n, n ≤ N → G n < p.lastStep := by
    intro n hn
    rcases hn.eq_or_lt with (rfl | H)
    · simp only; simp only [hi, if_true, eq_self_iff_true]
    · simp only; simp only [H.ne, (hg n H).left.trans hi, if_false]
  have fGn :
      ∀ n, n ≤ N →
        p.c (p.index (G n)) ∉ p.iUnionUpTo (G n) ∧ p.R (G n) ≤ p.τ * p.r (p.index (G n)) := by
    intro n hn
    have :
      p.index (G n) =
        Classical.epsilon fun t => p.c t ∉ p.iUnionUpTo (G n) ∧ p.R (G n) ≤ p.τ * p.r t :=
      by rw [index]; rfl
    rw [this]
    have : ∃ t, p.c t ∉ p.iUnionUpTo (G n) ∧ p.R (G n) ≤ p.τ * p.r t := by
      simpa only [not_exists, exists_prop, not_and, not_lt, not_le, mem_setOf_eq, not_forall] using
        not_mem_of_lt_csInf (G_lt_last n hn) (OrderBot.bddBelow _)
    exact Classical.epsilon_spec this
  -- the balls with indices `G k` satisfy the characteristic property of satellite configurations.
  have Gab :
    ∀ a b : Fin (Nat.succ N),
      G a < G b →
        p.r (p.index (G a)) ≤ dist (p.c (p.index (G a))) (p.c (p.index (G b))) ∧
          p.r (p.index (G b)) ≤ p.τ * p.r (p.index (G a)) := by
    intro a b G_lt
    have ha : (a : ℕ) ≤ N := Nat.lt_succ_iff.1 a.2
    have hb : (b : ℕ) ≤ N := Nat.lt_succ_iff.1 b.2
    constructor
    · have := (fGn b hb).1
      simp only [iUnionUpTo, not_exists, exists_prop, mem_iUnion, mem_closedBall, not_and, not_le,
        Subtype.exists, Subtype.coe_mk] at this
      simpa only [dist_comm, mem_ball, not_lt] using this (G a) G_lt
    · apply le_trans _ (fGn a ha).2
      have B : p.c (p.index (G b)) ∉ p.iUnionUpTo (G a) := by
        intro H; exact (fGn b hb).1 (p.monotone_iUnionUpTo G_lt.le H)
      let b' : { t // p.c t ∉ p.iUnionUpTo (G a) } := ⟨p.index (G b), B⟩
      apply @le_ciSup _ _ _ (fun t : { t // p.c t ∉ p.iUnionUpTo (G a) } => p.r t) _ b'
      refine' ⟨p.r_bound, fun t ht => _⟩
      simp only [exists_prop, mem_range, Subtype.exists, Subtype.coe_mk] at ht
      rcases ht with ⟨u, hu⟩
      rw [← hu.2]
      exact p.r_le _
  -- therefore, one may use them to construct a satellite configuration with `N+1` points
  let sc : SatelliteConfig α N p.τ :=
    { c := fun k => p.c (p.index (G k))
      r := fun k => p.r (p.index (G k))
      rpos := fun k => p.rpos (p.index (G k))
      h := by
        intro a b a_ne_b
        wlog G_le : G a ≤ G b generalizing a b
        · exact (this b a a_ne_b.symm (le_of_not_le G_le)).symm
        have G_lt : G a < G b := by
          rcases G_le.lt_or_eq with (H | H); · exact H
          have A : (a : ℕ) ≠ b := Fin.val_injective.ne a_ne_b
          rw [← color_G a (Nat.lt_succ_iff.1 a.2), ← color_G b (Nat.lt_succ_iff.1 b.2), H] at A
          exact (A rfl).elim
        exact Or.inl (Gab a b G_lt)
      hlast := by
        intro a ha
        have I : (a : ℕ) < N := ha
        have : G a < G (Fin.last N) := by dsimp; simp [I.ne, (hg a I).1]
        exact Gab _ _ this
      inter := by
        intro a ha
        have I : (a : ℕ) < N := ha
        have J : G (Fin.last N) = i := by dsimp; simp only [if_true, eq_self_iff_true]
        have K : G a = g a := by dsimp; simp [I.ne, (hg a I).1]
        convert dist_le_add_of_nonempty_closedBall_inter_closedBall (hg _ I).2.1 }
  -- this is a contradiction
  exact hN.false sc
  -- 🎉 no goals
#align besicovitch.tau_package.color_lt Besicovitch.TauPackage.color_lt

end TauPackage

open TauPackage

/-- The topological Besicovitch covering theorem: there exist finitely many families of disjoint
balls covering all the centers in a package. More specifically, one can use `N` families if there
are no satellite configurations with `N+1` points. -/
theorem exist_disjoint_covering_families {N : ℕ} {τ : ℝ} (hτ : 1 < τ)
    (hN : IsEmpty (SatelliteConfig α N τ)) (q : BallPackage β α) :
    ∃ s : Fin N → Set β,
      (∀ i : Fin N, (s i).PairwiseDisjoint fun j => closedBall (q.c j) (q.r j)) ∧
        range q.c ⊆ ⋃ i : Fin N, ⋃ j ∈ s i, ball (q.c j) (q.r j) := by
  -- first exclude the trivial case where `β` is empty (we need non-emptiness for the transfinite
  -- induction, to be able to choose garbage when there is no point left).
  cases isEmpty_or_nonempty β
  -- ⊢ ∃ s, (∀ (i : Fin N), PairwiseDisjoint (s i) fun j => closedBall (BallPackage …
  · refine' ⟨fun _ => ∅, fun _ => pairwiseDisjoint_empty, _⟩
    -- ⊢ range q.c ⊆ ⋃ (i : Fin N) (j : β) (_ : j ∈ (fun x => ∅) i), ball (BallPackag …
    rw [← image_univ, eq_empty_of_isEmpty (univ : Set β)]
    -- ⊢ q.c '' ∅ ⊆ ⋃ (i : Fin N) (j : β) (_ : j ∈ (fun x => ∅) i), ball (BallPackage …
    simp
    -- 🎉 no goals
  -- Now, assume `β` is nonempty.
  let p : TauPackage β α :=
    { q with
      τ
      one_lt_tau := hτ }
  -- we use for `s i` the balls of color `i`.
  let s := fun i : Fin N =>
    ⋃ (k : Ordinal.{u}) (_ : k < p.lastStep) (_ : p.color k = i), ({p.index k} : Set β)
  refine' ⟨s, fun i => _, _⟩
  -- ⊢ PairwiseDisjoint (s i) fun j => closedBall (BallPackage.c q j) (BallPackage. …
  · -- show that balls of the same color are disjoint
    intro x hx y hy x_ne_y
    -- ⊢ (Disjoint on fun j => closedBall (BallPackage.c q j) (BallPackage.r q j)) x y
    obtain ⟨jx, jx_lt, jxi, rfl⟩ :
      ∃ jx : Ordinal, jx < p.lastStep ∧ p.color jx = i ∧ x = p.index jx := by
      simpa only [exists_prop, mem_iUnion, mem_singleton_iff] using hx
    obtain ⟨jy, jy_lt, jyi, rfl⟩ :
      ∃ jy : Ordinal, jy < p.lastStep ∧ p.color jy = i ∧ y = p.index jy := by
      simpa only [exists_prop, mem_iUnion, mem_singleton_iff] using hy
    wlog jxy : jx ≤ jy generalizing jx jy
    -- ⊢ (Disjoint on fun j => closedBall (BallPackage.c q j) (BallPackage.r q j)) (i …
    · exact (this jy jy_lt jyi hy jx jx_lt jxi hx x_ne_y.symm (le_of_not_le jxy)).symm
      -- 🎉 no goals
    replace jxy : jx < jy
    -- ⊢ jx < jy
    · rcases lt_or_eq_of_le jxy with (H | rfl); · { exact H }; · { exact (x_ne_y rfl).elim }
      -- ⊢ jx < jy
                                                  -- 🎉 no goals
                                                                 -- 🎉 no goals
    let A : Set ℕ :=
      ⋃ (j : { j // j < jy })
        (_ : (closedBall (p.c (p.index j)) (p.r (p.index j)) ∩
          closedBall (p.c (p.index jy)) (p.r (p.index jy))).Nonempty),
        {p.color j}
    have color_j : p.color jy = sInf (univ \ A) := by rw [TauPackage.color]
    -- ⊢ (Disjoint on fun j => closedBall (BallPackage.c q j) (BallPackage.r q j)) (i …
    have h : p.color jy ∈ univ \ A := by
      rw [color_j]
      apply csInf_mem
      refine' ⟨N, _⟩
      simp only [not_exists, true_and_iff, exists_prop, mem_iUnion, mem_singleton_iff, not_and,
        mem_univ, mem_diff, Subtype.exists, Subtype.coe_mk]
      intro k hk _
      exact (p.color_lt (hk.trans jy_lt) hN).ne'
    simp only [not_exists, true_and_iff, exists_prop, mem_iUnion, mem_singleton_iff, not_and,
      mem_univ, mem_diff, Subtype.exists, Subtype.coe_mk] at h
    specialize h jx jxy
    -- ⊢ (Disjoint on fun j => closedBall (BallPackage.c q j) (BallPackage.r q j)) (i …
    contrapose! h
    -- ⊢ Set.Nonempty (closedBall (BallPackage.c q (index { toBallPackage := { c := q …
    simpa only [jxi, jyi, and_true_iff, eq_self_iff_true, ← not_disjoint_iff_nonempty_inter] using h
    -- 🎉 no goals
  · -- show that the balls of color at most `N` cover every center.
    refine' range_subset_iff.2 fun b => _
    -- ⊢ BallPackage.c q b ∈ ⋃ (i : Fin N) (j : β) (_ : j ∈ s i), ball (BallPackage.c …
    obtain ⟨a, ha⟩ :
      ∃ a : Ordinal, a < p.lastStep ∧ dist (p.c b) (p.c (p.index a)) < p.r (p.index a) := by
      simpa only [iUnionUpTo, exists_prop, mem_iUnion, mem_ball, Subtype.exists,
        Subtype.coe_mk] using p.mem_iUnionUpTo_lastStep b
    simp only [exists_prop, mem_iUnion, mem_ball, mem_singleton_iff, biUnion_and', exists_eq_left,
      iUnion_exists, exists_and_left]
    exact ⟨⟨p.color a, p.color_lt ha.1 hN⟩, a, rfl, ha⟩
    -- 🎉 no goals
#align besicovitch.exist_disjoint_covering_families Besicovitch.exist_disjoint_covering_families

/-!
### The measurable Besicovitch covering theorem
-/


open scoped NNReal

variable [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]

/-- Consider, for each `x` in a set `s`, a radius `r x ∈ (0, 1]`. Then one can find finitely
many disjoint balls of the form `closedBall x (r x)` covering a proportion `1/(N+1)` of `s`, if
there are no satellite configurations with `N+1` points.
-/
theorem exist_finset_disjoint_balls_large_measure (μ : Measure α) [IsFiniteMeasure μ] {N : ℕ}
    {τ : ℝ} (hτ : 1 < τ) (hN : IsEmpty (SatelliteConfig α N τ)) (s : Set α) (r : α → ℝ)
    (rpos : ∀ x ∈ s, 0 < r x) (rle : ∀ x ∈ s, r x ≤ 1) :
    ∃ t : Finset α,
      ↑t ⊆ s ∧
        μ (s \ ⋃ x ∈ t, closedBall x (r x)) ≤ N / (N + 1) * μ s ∧
          (t : Set α).PairwiseDisjoint fun x => closedBall x (r x) := by
  -- exclude the trivial case where `μ s = 0`.
  rcases le_or_lt (μ s) 0 with (hμs | hμs)
  -- ⊢ ∃ t, ↑t ⊆ s ∧ ↑↑μ (s \ ⋃ (x : α) (_ : x ∈ t), closedBall x (r x)) ≤ ↑N / (↑N …
  · have : μ s = 0 := le_bot_iff.1 hμs
    -- ⊢ ∃ t, ↑t ⊆ s ∧ ↑↑μ (s \ ⋃ (x : α) (_ : x ∈ t), closedBall x (r x)) ≤ ↑N / (↑N …
    refine' ⟨∅, by simp only [Finset.coe_empty, empty_subset], _, _⟩
    -- ⊢ ↑↑μ (s \ ⋃ (x : α) (_ : x ∈ ∅), closedBall x (r x)) ≤ ↑N / (↑N + 1) * ↑↑μ s
    · simp only [this, Finset.not_mem_empty, diff_empty, iUnion_false, iUnion_empty,
        nonpos_iff_eq_zero, mul_zero]
    · simp only [Finset.coe_empty, pairwiseDisjoint_empty]
      -- 🎉 no goals
  cases isEmpty_or_nonempty α
  -- ⊢ ∃ t, ↑t ⊆ s ∧ ↑↑μ (s \ ⋃ (x : α) (_ : x ∈ t), closedBall x (r x)) ≤ ↑N / (↑N …
  · simp only [eq_empty_of_isEmpty s, measure_empty] at hμs
    -- ⊢ ∃ t, ↑t ⊆ s ∧ ↑↑μ (s \ ⋃ (x : α) (_ : x ∈ t), closedBall x (r x)) ≤ ↑N / (↑N …
    exact (lt_irrefl _ hμs).elim
    -- 🎉 no goals
  have Npos : N ≠ 0 := by
    rintro rfl
    inhabit α
    exact not_isEmpty_of_nonempty _ hN
  -- introduce a measurable superset `o` with the same measure, for measure computations
  obtain ⟨o, so, omeas, μo⟩ : ∃ o : Set α, s ⊆ o ∧ MeasurableSet o ∧ μ o = μ s :=
    exists_measurable_superset μ s
  /- We will apply the topological Besicovitch theorem, giving `N` disjoint subfamilies of balls
    covering `s`. Among these, one of them covers a proportion at least `1/N` of `s`. A large
    enough finite subfamily will then cover a proportion at least `1/(N+1)`. -/
  let a : BallPackage s α :=
    { c := fun x => x
      r := fun x => r x
      rpos := fun x => rpos x x.2
      r_bound := 1
      r_le := fun x => rle x x.2 }
  rcases exist_disjoint_covering_families hτ hN a with ⟨u, hu, hu'⟩
  -- ⊢ ∃ t, ↑t ⊆ s ∧ ↑↑μ (s \ ⋃ (x : α) (_ : x ∈ t), closedBall x (r x)) ≤ ↑N / (↑N …
  have u_count : ∀ i, (u i).Countable := by
    intro i
    refine' (hu i).countable_of_nonempty_interior fun j _ => _
    have : (ball (j : α) (r j)).Nonempty := nonempty_ball.2 (a.rpos _)
    exact this.mono ball_subset_interior_closedBall
  let v : Fin N → Set α := fun i => ⋃ (x : s) (_ : x ∈ u i), closedBall x (r x)
  -- ⊢ ∃ t, ↑t ⊆ s ∧ ↑↑μ (s \ ⋃ (x : α) (_ : x ∈ t), closedBall x (r x)) ≤ ↑N / (↑N …
  have A : s = ⋃ i : Fin N, s ∩ v i := by
    refine' Subset.antisymm _ (iUnion_subset fun i => inter_subset_left _ _)
    intro x hx
    obtain ⟨i, y, hxy, h'⟩ :
        ∃ (i : Fin N) (i_1 : ↥s), i_1 ∈ u i ∧ x ∈ ball (↑i_1) (r ↑i_1) := by
      have : x ∈ range a.c := by simpa only [Subtype.range_coe_subtype, setOf_mem_eq]
      simpa only [mem_iUnion, bex_def] using hu' this
    refine' mem_iUnion.2 ⟨i, ⟨hx, _⟩⟩
    simp only [exists_prop, mem_iUnion, SetCoe.exists, exists_and_right, Subtype.coe_mk]
    exact ⟨y, ⟨y.2, by simpa only [Subtype.coe_eta]⟩, ball_subset_closedBall h'⟩
  have S : ∑ _i : Fin N, μ s / N ≤ ∑ i, μ (s ∩ v i) :=
    calc
      ∑ _i : Fin N, μ s / N = μ s := by
        simp only [Finset.card_fin, Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.mul_div_cancel']
        · simp only [Npos, Ne.def, Nat.cast_eq_zero, not_false_iff]
        · exact ENNReal.nat_ne_top _
      _ ≤ ∑ i, μ (s ∩ v i) := by
        conv_lhs => rw [A]
        apply measure_iUnion_fintype_le
  -- choose an index `i` of a subfamily covering at least a proportion `1/N` of `s`.
  obtain ⟨i, -, hi⟩ : ∃ (i : Fin N), i ∈ Finset.univ ∧ μ s / N ≤ μ (s ∩ v i) := by
    apply ENNReal.exists_le_of_sum_le _ S
    exact ⟨⟨0, bot_lt_iff_ne_bot.2 Npos⟩, Finset.mem_univ _⟩
  replace hi : μ s / (N + 1) < μ (s ∩ v i)
  -- ⊢ ↑↑μ s / (↑N + 1) < ↑↑μ (s ∩ v i)
  · apply lt_of_lt_of_le _ hi
    -- ⊢ ↑↑μ s / (↑N + 1) < ↑↑μ s / ↑N
    apply (ENNReal.mul_lt_mul_left hμs.ne' (measure_lt_top μ s).ne).2
    -- ⊢ (↑N + 1)⁻¹ < (↑N)⁻¹
    rw [ENNReal.inv_lt_inv]
    -- ⊢ ↑N < ↑N + 1
    conv_lhs => rw [← add_zero (N : ℝ≥0∞)]
    -- ⊢ ↑N + 0 < ↑N + 1
    exact ENNReal.add_lt_add_left (ENNReal.nat_ne_top N) zero_lt_one
    -- 🎉 no goals
  have B : μ (o ∩ v i) = ∑' x : u i, μ (o ∩ closedBall x (r x)) := by
    have : o ∩ v i = ⋃ (x : s) (_ : x ∈ u i), o ∩ closedBall x (r x) := by simp only [inter_iUnion]
    rw [this, measure_biUnion (u_count i)]
    · exact (hu i).mono fun k => inter_subset_right _ _
    · exact fun b _ => omeas.inter measurableSet_closedBall
  -- A large enough finite subfamily of `u i` will also cover a proportion `> 1/(N+1)` of `s`.
  -- Since `s` might not be measurable, we express this in terms of the measurable superset `o`.
  obtain ⟨w, hw⟩ :
    ∃ w : Finset (u i), μ s / (N + 1) <
      ∑ x : u i in w, μ (o ∩ closedBall (x : α) (r (x : α))) := by
    have C : HasSum (fun x : u i => μ (o ∩ closedBall x (r x))) (μ (o ∩ v i)) := by
      rw [B]; exact ENNReal.summable.hasSum
    have : μ s / (N + 1) < μ (o ∩ v i) := hi.trans_le (measure_mono (inter_subset_inter_left _ so))
    exact ((tendsto_order.1 C).1 _ this).exists
  -- Bring back the finset `w i` of `↑(u i)` to a finset of `α`, and check that it works by design.
  refine' ⟨Finset.image (fun x : u i => x) w, _, _, _⟩
  -- show that the finset is included in `s`.
  · simp only [image_subset_iff, Finset.coe_image]
    -- ⊢ ↑w ⊆ (fun x => ↑↑x) ⁻¹' s
    intro y _
    -- ⊢ y ∈ (fun x => ↑↑x) ⁻¹' s
    simp only [Subtype.coe_prop, mem_preimage]
    -- 🎉 no goals
  -- show that it covers a large enough proportion of `s`. For measure computations, we do not
  -- use `s` (which might not be measurable), but its measurable superset `o`. Since their measures
  -- are the same, this does not spoil the estimates
  · suffices H : μ (o \ ⋃ x ∈ w, closedBall (↑x) (r ↑x)) ≤ N / (N + 1) * μ s
    -- ⊢ ↑↑μ (s \ ⋃ (x : α) (_ : x ∈ Finset.image (fun x => ↑↑x) w), closedBall x (r  …
    · rw [Finset.set_biUnion_finset_image]
      -- ⊢ ↑↑μ (s \ ⋃ (y : ↑(u i)) (_ : y ∈ w), closedBall (↑↑y) (r ↑↑y)) ≤ ↑N / (↑N +  …
      exact le_trans (measure_mono (diff_subset_diff so (Subset.refl _))) H
      -- 🎉 no goals
    rw [← diff_inter_self_eq_diff,
      measure_diff_le_iff_le_add _ (inter_subset_right _ _) (measure_lt_top μ _).ne]
    swap
    -- ⊢ MeasurableSet ((⋃ (x : ↑(u i)) (_ : x ∈ w), closedBall (↑↑x) (r ↑↑x)) ∩ o)
    · apply MeasurableSet.inter _ omeas
      -- ⊢ MeasurableSet (⋃ (x : ↑(u i)) (_ : x ∈ w), closedBall (↑↑x) (r ↑↑x))
      haveI : Encodable (u i) := (u_count i).toEncodable
      -- ⊢ MeasurableSet (⋃ (x : ↑(u i)) (_ : x ∈ w), closedBall (↑↑x) (r ↑↑x))
      exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ => measurableSet_closedBall
      -- 🎉 no goals
    calc
      μ o = 1 / (N + 1) * μ s + N / (N + 1) * μ s := by
        rw [μo, ← add_mul, ENNReal.div_add_div_same, add_comm, ENNReal.div_self, one_mul] <;> simp
      _ ≤ μ ((⋃ x ∈ w, closedBall (↑x) (r ↑x)) ∩ o) + N / (N + 1) * μ s := by
        refine' add_le_add _ le_rfl
        rw [div_eq_mul_inv, one_mul, mul_comm, ← div_eq_mul_inv]
        apply hw.le.trans (le_of_eq _)
        rw [← Finset.set_biUnion_coe, inter_comm _ o, inter_iUnion₂, Finset.set_biUnion_coe,
          measure_biUnion_finset]
        · have : (w : Set (u i)).PairwiseDisjoint
              fun b : u i => closedBall (b : α) (r (b : α)) := by
            intro k _ l _ hkl; exact hu i k.2 l.2 (Subtype.val_injective.ne hkl)
          exact this.mono fun k => inter_subset_right _ _
        · intro b _
          apply omeas.inter measurableSet_closedBall
  -- show that the balls are disjoint
  · intro k hk l hl hkl
    -- ⊢ (Disjoint on fun x => closedBall x (r x)) k l
    obtain ⟨k', _, rfl⟩ : ∃ k' : u i, k' ∈ w ∧ ↑k' = k := by
      simpa only [mem_image, Finset.mem_coe, Finset.coe_image] using hk
    obtain ⟨l', _, rfl⟩ : ∃ l' : u i, l' ∈ w ∧ ↑l' = l := by
      simpa only [mem_image, Finset.mem_coe, Finset.coe_image] using hl
    have k'nel' : (k' : s) ≠ l' := by intro h; rw [h] at hkl; exact hkl rfl
    -- ⊢ (Disjoint on fun x => closedBall x (r x)) ↑↑k' ↑↑l'
    exact hu i k'.2 l'.2 k'nel'
    -- 🎉 no goals
#align besicovitch.exist_finset_disjoint_balls_large_measure Besicovitch.exist_finset_disjoint_balls_large_measure

variable [HasBesicovitchCovering α]

/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`.
This version requires that the underlying measure is finite, and that the space has the Besicovitch
covering property (which is satisfied for instance by normed real vector spaces). It expresses the
conclusion in a slightly awkward form (with a subset of `α × ℝ`) coming from the proof technique.
For a version assuming that the measure is sigma-finite,
see `exists_disjoint_closedBall_covering_ae_aux`.
For a version giving the conclusion in a nicer form, see `exists_disjoint_closedBall_covering_ae`.
-/
theorem exists_disjoint_closedBall_covering_ae_of_finiteMeasure_aux (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → Set ℝ) (s : Set α)
    (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ t : Set (α × ℝ),
      t.Countable ∧
        (∀ p : α × ℝ, p ∈ t → p.1 ∈ s) ∧
          (∀ p : α × ℝ, p ∈ t → p.2 ∈ f p.1) ∧
            μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ t), closedBall p.1 p.2) = 0 ∧
              t.PairwiseDisjoint fun p => closedBall p.1 p.2 := by
  rcases HasBesicovitchCovering.no_satelliteConfig (α := α) with ⟨N, τ, hτ, hN⟩
  -- ⊢ ∃ t, Set.Countable t ∧ (∀ (p : α × ℝ), p ∈ t → p.fst ∈ s) ∧ (∀ (p : α × ℝ),  …
  /- Introduce a property `P` on finsets saying that we have a nice disjoint covering of a
      subset of `s` by admissible balls. -/
  let P : Finset (α × ℝ) → Prop := fun t =>
    ((t : Set (α × ℝ)).PairwiseDisjoint fun p => closedBall p.1 p.2) ∧
      (∀ p : α × ℝ, p ∈ t → p.1 ∈ s) ∧ ∀ p : α × ℝ, p ∈ t → p.2 ∈ f p.1
  /- Given a finite good covering of a subset `s`, one can find a larger finite good covering,
    covering additionally a proportion at least `1/(N+1)` of leftover points. This follows from
    `exist_finset_disjoint_balls_large_measure` applied to balls not intersecting the initial
    covering. -/
  have :
      ∀ t : Finset (α × ℝ), P t → ∃ u : Finset (α × ℝ), t ⊆ u ∧ P u ∧
        μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ u), closedBall p.1 p.2) ≤
          N / (N + 1) * μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ t), closedBall p.1 p.2) := by
    intro t ht
    set B := ⋃ (p : α × ℝ) (_ : p ∈ t), closedBall p.1 p.2 with hB
    have B_closed : IsClosed B :=
      isClosed_biUnion (Finset.finite_toSet _) fun i _ => isClosed_ball
    set s' := s \ B
    have : ∀ x ∈ s', ∃ r ∈ f x ∩ Ioo 0 1, Disjoint B (closedBall x r) := by
      intro x hx
      have xs : x ∈ s := ((mem_diff x).1 hx).1
      rcases eq_empty_or_nonempty B with (hB | hB)
      · rcases hf x xs 1 zero_lt_one with ⟨r, hr, h'r⟩
        exact ⟨r, ⟨hr, h'r⟩, by simp only [hB, empty_disjoint]⟩
      · let r := infDist x B
        have : 0 < min r 1 :=
          lt_min ((B_closed.not_mem_iff_infDist_pos hB).1 ((mem_diff x).1 hx).2) zero_lt_one
        rcases hf x xs _ this with ⟨r, hr, h'r⟩
        refine' ⟨r, ⟨hr, ⟨h'r.1, h'r.2.trans_le (min_le_right _ _)⟩⟩, _⟩
        rw [disjoint_comm]
        exact disjoint_closedBall_of_lt_infDist (h'r.2.trans_le (min_le_left _ _))
    choose! r hr using this
    obtain ⟨v, vs', hμv, hv⟩ :
      ∃ v : Finset α,
        ↑v ⊆ s' ∧
          μ (s' \ ⋃ x ∈ v, closedBall x (r x)) ≤ N / (N + 1) * μ s' ∧
            (v : Set α).PairwiseDisjoint fun x : α => closedBall x (r x) :=
      haveI rI : ∀ x ∈ s', r x ∈ Ioo (0 : ℝ) 1 := fun x hx => (hr x hx).1.2
      exist_finset_disjoint_balls_large_measure μ hτ hN s' r (fun x hx => (rI x hx).1) fun x hx =>
        (rI x hx).2.le
    refine' ⟨t ∪ Finset.image (fun x => (x, r x)) v, Finset.subset_union_left _ _, ⟨_, _, _⟩, _⟩
    · simp only [Finset.coe_union, pairwiseDisjoint_union, ht.1, true_and_iff, Finset.coe_image]
      constructor
      · intro p hp q hq hpq
        rcases(mem_image _ _ _).1 hp with ⟨p', p'v, rfl⟩
        rcases(mem_image _ _ _).1 hq with ⟨q', q'v, rfl⟩
        refine' hv p'v q'v fun hp'q' => _
        rw [hp'q'] at hpq
        exact hpq rfl
      · intro p hp q hq hpq
        rcases(mem_image _ _ _).1 hq with ⟨q', q'v, rfl⟩
        apply disjoint_of_subset_left _ (hr q' (vs' q'v)).2
        rw [hB, ← Finset.set_biUnion_coe]
        exact subset_biUnion_of_mem (u := fun x : α × ℝ => closedBall x.1 x.2) hp
    · intro p hp
      rcases Finset.mem_union.1 hp with (h'p | h'p)
      · exact ht.2.1 p h'p
      · rcases Finset.mem_image.1 h'p with ⟨p', p'v, rfl⟩
        exact ((mem_diff _).1 (vs' (Finset.mem_coe.2 p'v))).1
    · intro p hp
      rcases Finset.mem_union.1 hp with (h'p | h'p)
      · exact ht.2.2 p h'p
      · rcases Finset.mem_image.1 h'p with ⟨p', p'v, rfl⟩
        exact (hr p' (vs' p'v)).1.1
    · convert hμv using 2
      rw [Finset.set_biUnion_union, ← diff_diff, Finset.set_biUnion_finset_image]
  /- Define `F` associating to a finite good covering the above enlarged good covering, covering
    a proportion `1/(N+1)` of leftover points. Iterating `F`, one will get larger and larger good
    coverings, missing in the end only a measure-zero set. -/
  choose! F hF using this
  -- ⊢ ∃ t, Set.Countable t ∧ (∀ (p : α × ℝ), p ∈ t → p.fst ∈ s) ∧ (∀ (p : α × ℝ),  …
  let u n := F^[n] ∅
  -- ⊢ ∃ t, Set.Countable t ∧ (∀ (p : α × ℝ), p ∈ t → p.fst ∈ s) ∧ (∀ (p : α × ℝ),  …
  have u_succ : ∀ n : ℕ, u n.succ = F (u n) := fun n => by
    simp only [Function.comp_apply, Function.iterate_succ']
  have Pu : ∀ n, P (u n) := by
    intro n
    induction' n with n IH
    · simp only [Prod.forall, id.def, Function.iterate_zero, Nat.zero_eq]
      simp only [Finset.not_mem_empty, IsEmpty.forall_iff, Finset.coe_empty, forall₂_true_iff,
        and_self_iff, pairwiseDisjoint_empty]
    · rw [u_succ]
      exact (hF (u n) IH).2.1
  refine' ⟨⋃ n, u n, countable_iUnion fun n => (u n).countable_toSet, _, _, _, _⟩
  · intro p hp
    -- ⊢ p.fst ∈ s
    rcases mem_iUnion.1 hp with ⟨n, hn⟩
    -- ⊢ p.fst ∈ s
    exact (Pu n).2.1 p (Finset.mem_coe.1 hn)
    -- 🎉 no goals
  · intro p hp
    -- ⊢ p.snd ∈ f p.fst
    rcases mem_iUnion.1 hp with ⟨n, hn⟩
    -- ⊢ p.snd ∈ f p.fst
    exact (Pu n).2.2 p (Finset.mem_coe.1 hn)
    -- 🎉 no goals
  · have A :
      ∀ n,
        μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ ⋃ n : ℕ, (u n : Set (α × ℝ))), closedBall p.fst p.snd) ≤
          μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ u n), closedBall p.fst p.snd) := by
      intro n
      apply measure_mono
      apply diff_subset_diff (Subset.refl _)
      exact biUnion_subset_biUnion_left (subset_iUnion (fun i => (u i : Set (α × ℝ))) n)
    have B :
        ∀ n, μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ u n), closedBall p.fst p.snd) ≤
          (N / (N + 1) : ℝ≥0∞) ^ n * μ s := by
      intro n
      induction' n with n IH
      · simp only [le_refl, diff_empty, one_mul, iUnion_false, iUnion_empty, pow_zero, Nat.zero_eq,
          Function.iterate_zero, id.def, Finset.not_mem_empty]
      calc
        μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ u n.succ), closedBall p.fst p.snd) ≤
            N / (N + 1) * μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ u n), closedBall p.fst p.snd) := by
          rw [u_succ]; exact (hF (u n) (Pu n)).2.2
        _ ≤ (N / (N + 1) : ℝ≥0∞) ^ n.succ * μ s := by
          rw [pow_succ, mul_assoc]; exact mul_le_mul_left' IH _
    have C : Tendsto (fun n : ℕ => ((N : ℝ≥0∞) / (N + 1)) ^ n * μ s) atTop (𝓝 (0 * μ s)) := by
      apply ENNReal.Tendsto.mul_const _ (Or.inr (measure_lt_top μ s).ne)
      apply ENNReal.tendsto_pow_atTop_nhds_0_of_lt_1
      rw [ENNReal.div_lt_iff, one_mul]
      · conv_lhs => rw [← add_zero (N : ℝ≥0∞)]
        exact ENNReal.add_lt_add_left (ENNReal.nat_ne_top N) zero_lt_one
      · simp only [true_or_iff, add_eq_zero_iff, Ne.def, not_false_iff, one_ne_zero, and_false_iff]
      · simp only [ENNReal.nat_ne_top, Ne.def, not_false_iff, or_true_iff]
    rw [zero_mul] at C
    -- ⊢ ↑↑μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ ⋃ (n : ℕ), ↑(u n)), closedBall p.fst p.snd)  …
    apply le_bot_iff.1
    -- ⊢ ↑↑μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ ⋃ (n : ℕ), ↑(u n)), closedBall p.fst p.snd)  …
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds C fun n => (A n).trans (B n)
    -- 🎉 no goals
  · refine' (pairwiseDisjoint_iUnion _).2 fun n => (Pu n).1
    -- ⊢ Directed (fun x x_1 => x ⊆ x_1) fun n => ↑(u n)
    apply (monotone_nat_of_le_succ fun n => ?_).directed_le
    -- ⊢ ↑(u n) ≤ ↑(u (n + 1))
    rw [← Nat.succ_eq_add_one, u_succ]
    -- ⊢ ↑(u n) ≤ ↑(F (u n))
    exact (hF (u n) (Pu n)).1
    -- 🎉 no goals
#align besicovitch.exists_disjoint_closed_ball_covering_ae_of_finite_measure_aux Besicovitch.exists_disjoint_closedBall_covering_ae_of_finiteMeasure_aux

/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`.
This version requires that the underlying measure is sigma-finite, and that the space has the
Besicovitch covering property (which is satisfied for instance by normed real vector spaces).
It expresses the conclusion in a slightly awkward form (with a subset of `α × ℝ`) coming from the
proof technique.
For a version giving the conclusion in a nicer form, see `exists_disjoint_closedBall_covering_ae`.
-/
theorem exists_disjoint_closedBall_covering_ae_aux (μ : Measure α) [SigmaFinite μ] (f : α → Set ℝ)
    (s : Set α) (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ t : Set (α × ℝ), t.Countable ∧ (∀ p : α × ℝ, p ∈ t → p.1 ∈ s) ∧
      (∀ p : α × ℝ, p ∈ t → p.2 ∈ f p.1) ∧
        μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ t), closedBall p.1 p.2) = 0 ∧
          t.PairwiseDisjoint fun p => closedBall p.1 p.2 := by
  /- This is deduced from the finite measure case, by using a finite measure with respect to which
    the initial sigma-finite measure is absolutely continuous. -/
  rcases exists_absolutelyContinuous_isFiniteMeasure μ with ⟨ν, hν, hμν⟩
  -- ⊢ ∃ t, Set.Countable t ∧ (∀ (p : α × ℝ), p ∈ t → p.fst ∈ s) ∧ (∀ (p : α × ℝ),  …
  rcases exists_disjoint_closedBall_covering_ae_of_finiteMeasure_aux ν f s hf with
    ⟨t, t_count, ts, tr, tν, tdisj⟩
  exact ⟨t, t_count, ts, tr, hμν tν, tdisj⟩
  -- 🎉 no goals
#align besicovitch.exists_disjoint_closed_ball_covering_ae_aux Besicovitch.exists_disjoint_closedBall_covering_ae_aux

/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`. We can even require that the radius at `x` is bounded by a given function `R x`.
(Take `R = 1` if you don't need this additional feature).
This version requires that the underlying measure is sigma-finite, and that the space has the
Besicovitch covering property (which is satisfied for instance by normed real vector spaces).
-/
theorem exists_disjoint_closedBall_covering_ae (μ : Measure α) [SigmaFinite μ] (f : α → Set ℝ)
    (s : Set α) (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) (R : α → ℝ)
    (hR : ∀ x ∈ s, 0 < R x) :
    ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧
      (∀ x ∈ t, r x ∈ f x ∩ Ioo 0 (R x)) ∧ μ (s \ ⋃ x ∈ t, closedBall x (r x)) = 0 ∧
        t.PairwiseDisjoint fun x => closedBall x (r x) := by
  let g x := f x ∩ Ioo 0 (R x)
  -- ⊢ ∃ t r, Set.Countable t ∧ t ⊆ s ∧ (∀ (x : α), x ∈ t → r x ∈ f x ∩ Ioo 0 (R x) …
  have hg : ∀ x ∈ s, ∀ δ > 0, (g x ∩ Ioo 0 δ).Nonempty := by
    intro x hx δ δpos
    rcases hf x hx (min δ (R x)) (lt_min δpos (hR x hx)) with ⟨r, hr⟩
    exact
      ⟨r,
        ⟨⟨hr.1, hr.2.1, hr.2.2.trans_le (min_le_right _ _)⟩,
          ⟨hr.2.1, hr.2.2.trans_le (min_le_left _ _)⟩⟩⟩
  rcases exists_disjoint_closedBall_covering_ae_aux μ g s hg with ⟨v, v_count, vs, vg, μv, v_disj⟩
  -- ⊢ ∃ t r, Set.Countable t ∧ t ⊆ s ∧ (∀ (x : α), x ∈ t → r x ∈ f x ∩ Ioo 0 (R x) …
  let t := Prod.fst '' v
  -- ⊢ ∃ t r, Set.Countable t ∧ t ⊆ s ∧ (∀ (x : α), x ∈ t → r x ∈ f x ∩ Ioo 0 (R x) …
  have : ∀ x ∈ t, ∃ r : ℝ, (x, r) ∈ v := by
    intro x hx
    rcases(mem_image _ _ _).1 hx with ⟨⟨p, q⟩, hp, rfl⟩
    exact ⟨q, hp⟩
  choose! r hr using this
  -- ⊢ ∃ t r, Set.Countable t ∧ t ⊆ s ∧ (∀ (x : α), x ∈ t → r x ∈ f x ∩ Ioo 0 (R x) …
  have im_t : (fun x => (x, r x)) '' t = v := by
    have I : ∀ p : α × ℝ, p ∈ v → 0 ≤ p.2 := fun p hp => (vg p hp).2.1.le
    apply Subset.antisymm
    · simp only [image_subset_iff]
      rintro ⟨x, p⟩ hxp
      simp only [mem_preimage]
      exact hr _ (mem_image_of_mem _ hxp)
    · rintro ⟨x, p⟩ hxp
      have hxrx : (x, r x) ∈ v := hr _ (mem_image_of_mem _ hxp)
      have : p = r x := by
        by_contra h
        have A : (x, p) ≠ (x, r x) := by
          simpa only [true_and_iff, Prod.mk.inj_iff, eq_self_iff_true, Ne.def] using h
        have H := v_disj hxp hxrx A
        contrapose H
        rw [not_disjoint_iff_nonempty_inter]
        refine' ⟨x, by simp (config := { proj := false }) [I _ hxp, I _ hxrx]⟩
      rw [this]
      apply mem_image_of_mem
      exact mem_image_of_mem _ hxp
  refine' ⟨t, r, v_count.image _, _, _, _, _⟩
  · intro x hx
    -- ⊢ x ∈ s
    rcases (mem_image _ _ _).1 hx with ⟨⟨p, q⟩, hp, rfl⟩
    -- ⊢ (p, q).fst ∈ s
    exact vs _ hp
    -- 🎉 no goals
  · intro x hx
    -- ⊢ r x ∈ f x ∩ Ioo 0 (R x)
    rcases (mem_image _ _ _).1 hx with ⟨⟨p, q⟩, _, rfl⟩
    -- ⊢ r (p, q).fst ∈ f (p, q).fst ∩ Ioo 0 (R (p, q).fst)
    exact vg _ (hr _ hx)
    -- 🎉 no goals
  · have :
      ⋃ (x : α) (_ : x ∈ t), closedBall x (r x) =
        ⋃ (p : α × ℝ) (_ : p ∈ (fun x => (x, r x)) '' t), closedBall p.1 p.2 :=
      by conv_rhs => rw [biUnion_image]
    rw [this, im_t]
    -- ⊢ ↑↑μ (s \ ⋃ (p : α × ℝ) (_ : p ∈ v), closedBall p.fst p.snd) = 0
    exact μv
    -- 🎉 no goals
  · have A : InjOn (fun x : α => (x, r x)) t := by
      simp (config := { contextual := true }) only [InjOn, Prod.mk.inj_iff, imp_true_iff,
        eq_self_iff_true]
    rwa [← im_t, A.pairwiseDisjoint_image] at v_disj
    -- 🎉 no goals
#align besicovitch.exists_disjoint_closed_ball_covering_ae Besicovitch.exists_disjoint_closedBall_covering_ae

/-- In a space with the Besicovitch property, any set `s` can be covered with balls whose measures
add up to at most `μ s + ε`, for any positive `ε`. This works even if one restricts the set of
allowed radii around a point `x` to a set `f x` which accumulates at `0`. -/
theorem exists_closedBall_covering_tsum_measure_le (μ : Measure α) [SigmaFinite μ]
    [Measure.OuterRegular μ] {ε : ℝ≥0∞} (hε : ε ≠ 0) (f : α → Set ℝ) (s : Set α)
    (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x) ∧
      (s ⊆ ⋃ x ∈ t, closedBall x (r x)) ∧ (∑' x : t, μ (closedBall x (r x))) ≤ μ s + ε := by
  /- For the proof, first cover almost all `s` with disjoint balls thanks to the usual Besicovitch
    theorem. Taking the balls included in a well-chosen open neighborhood `u` of `s`, one may
    ensure that their measures add at most to `μ s + ε / 2`. Let `s'` be the remaining set, of
    measure `0`. Applying the other version of Besicovitch, one may cover it with at most `N`
    disjoint subfamilies. Making sure that they are all included in a neighborhood `v` of `s'` of
    measure at most `ε / (2 N)`, the sum of their measures is at most `ε / 2`,
    completing the proof. -/
  obtain ⟨u, su, u_open, μu⟩ : ∃ U, U ⊇ s ∧ IsOpen U ∧ μ U ≤ μ s + ε / 2 :=
    Set.exists_isOpen_le_add _ _
      (by
        simpa only [or_false_iff, Ne.def, ENNReal.div_eq_zero_iff, ENNReal.one_ne_top] using hε)
  have : ∀ x ∈ s, ∃ R > 0, ball x R ⊆ u := fun x hx =>
    Metric.mem_nhds_iff.1 (u_open.mem_nhds (su hx))
  choose! R hR using this
  -- ⊢ ∃ t r, Set.Countable t ∧ t ⊆ s ∧ (∀ (x : α), x ∈ t → r x ∈ f x) ∧ s ⊆ ⋃ (x : …
  obtain ⟨t0, r0, t0_count, t0s, hr0, μt0, t0_disj⟩ :
    ∃ (t0 : Set α) (r0 : α → ℝ), t0.Countable ∧ t0 ⊆ s ∧
      (∀ x ∈ t0, r0 x ∈ f x ∩ Ioo 0 (R x)) ∧ μ (s \ ⋃ x ∈ t0, closedBall x (r0 x)) = 0 ∧
        t0.PairwiseDisjoint fun x => closedBall x (r0 x) :=
    exists_disjoint_closedBall_covering_ae μ f s hf R fun x hx => (hR x hx).1
  -- we have constructed an almost everywhere covering of `s` by disjoint balls. Let `s'` be the
  -- remaining set.
  let s' := s \ ⋃ x ∈ t0, closedBall x (r0 x)
  -- ⊢ ∃ t r, Set.Countable t ∧ t ⊆ s ∧ (∀ (x : α), x ∈ t → r x ∈ f x) ∧ s ⊆ ⋃ (x : …
  have s's : s' ⊆ s := diff_subset _ _
  -- ⊢ ∃ t r, Set.Countable t ∧ t ⊆ s ∧ (∀ (x : α), x ∈ t → r x ∈ f x) ∧ s ⊆ ⋃ (x : …
  obtain ⟨N, τ, hτ, H⟩ : ∃ N τ, 1 < τ ∧ IsEmpty (Besicovitch.SatelliteConfig α N τ) :=
    HasBesicovitchCovering.no_satelliteConfig
  obtain ⟨v, s'v, v_open, μv⟩ : ∃ v, v ⊇ s' ∧ IsOpen v ∧ μ v ≤ μ s' + ε / 2 / N :=
    Set.exists_isOpen_le_add _ _
      (by
        simp only [hε, ENNReal.nat_ne_top, WithTop.mul_eq_top_iff, Ne.def, ENNReal.div_eq_zero_iff,
          ENNReal.one_ne_top, not_false_iff, and_false_iff, false_and_iff, or_self_iff])
  have : ∀ x ∈ s', ∃ r1 ∈ f x ∩ Ioo (0 : ℝ) 1, closedBall x r1 ⊆ v := by
    intro x hx
    rcases Metric.mem_nhds_iff.1 (v_open.mem_nhds (s'v hx)) with ⟨r, rpos, hr⟩
    rcases hf x (s's hx) (min r 1) (lt_min rpos zero_lt_one) with ⟨R', hR'⟩
    exact
      ⟨R', ⟨hR'.1, hR'.2.1, hR'.2.2.trans_le (min_le_right _ _)⟩,
        Subset.trans (closedBall_subset_ball (hR'.2.2.trans_le (min_le_left _ _))) hr⟩
  choose! r1 hr1 using this
  -- ⊢ ∃ t r, Set.Countable t ∧ t ⊆ s ∧ (∀ (x : α), x ∈ t → r x ∈ f x) ∧ s ⊆ ⋃ (x : …
  let q : BallPackage s' α :=
    { c := fun x => x
      r := fun x => r1 x
      rpos := fun x => (hr1 x.1 x.2).1.2.1
      r_bound := 1
      r_le := fun x => (hr1 x.1 x.2).1.2.2.le }
  -- by Besicovitch, we cover `s'` with at most `N` families of disjoint balls, all included in
  -- a suitable neighborhood `v` of `s'`.
  obtain ⟨S, S_disj, hS⟩ :
    ∃ S : Fin N → Set s',
      (∀ i : Fin N, (S i).PairwiseDisjoint fun j => closedBall (q.c j) (q.r j)) ∧
        range q.c ⊆ ⋃ i : Fin N, ⋃ j ∈ S i, ball (q.c j) (q.r j) :=
    exist_disjoint_covering_families hτ H q
  have S_count : ∀ i, (S i).Countable := by
    intro i
    apply (S_disj i).countable_of_nonempty_interior fun j _ => ?_
    have : (ball (j : α) (r1 j)).Nonempty := nonempty_ball.2 (q.rpos _)
    exact this.mono ball_subset_interior_closedBall
  let r x := if x ∈ s' then r1 x else r0 x
  -- ⊢ ∃ t r, Set.Countable t ∧ t ⊆ s ∧ (∀ (x : α), x ∈ t → r x ∈ f x) ∧ s ⊆ ⋃ (x : …
  have r_t0 : ∀ x ∈ t0, r x = r0 x := by
    intro x hx
    have : ¬x ∈ s' := by
      simp only [not_exists, exists_prop, mem_iUnion, mem_closedBall, not_and, not_lt, not_le,
        mem_diff, not_forall]
      intro _
      refine' ⟨x, hx, _⟩
      rw [dist_self]
      exact (hr0 x hx).2.1.le
    simp only [if_neg this]
  -- the desired covering set is given by the union of the families constructed in the first and
  -- second steps.
  refine' ⟨t0 ∪ ⋃ i : Fin N, ((↑) : s' → α) '' S i, r, _, _, _, _, _⟩
  -- it remains to check that they have the desired properties
  · exact t0_count.union (countable_iUnion fun i => (S_count i).image _)
    -- 🎉 no goals
  · simp only [t0s, true_and_iff, union_subset_iff, image_subset_iff, iUnion_subset_iff]
    -- ⊢ ∀ (i : Fin N), S i ⊆ (fun a => ↑a) ⁻¹' s
    intro i x _
    -- ⊢ x ∈ (fun a => ↑a) ⁻¹' s
    exact s's x.2
    -- 🎉 no goals
  · intro x hx
    -- ⊢ r x ∈ f x
    cases hx with
    | inl hx =>
      rw [r_t0 x hx]
      exact (hr0 _ hx).1
    | inr hx =>
      have h'x : x ∈ s' := by
        simp only [mem_iUnion, mem_image] at hx
        rcases hx with ⟨i, y, _, rfl⟩
        exact y.2
      simp only [if_pos h'x, (hr1 x h'x).1.1]
  · intro x hx
    -- ⊢ x ∈ ⋃ (x : α) (_ : x ∈ t0 ∪ ⋃ (i : Fin N), Subtype.val '' S i), closedBall x …
    by_cases h'x : x ∈ s'
    -- ⊢ x ∈ ⋃ (x : α) (_ : x ∈ t0 ∪ ⋃ (i : Fin N), Subtype.val '' S i), closedBall x …
    · obtain ⟨i, y, ySi, xy⟩ : ∃ (i : Fin N) (y : ↥s'), y ∈ S i ∧ x ∈ ball (y : α) (r1 y) := by
        have A : x ∈ range q.c := by
          simpa only [not_exists, exists_prop, mem_iUnion, mem_closedBall, not_and, not_le,
            mem_setOf_eq, Subtype.range_coe_subtype, mem_diff] using h'x
        simpa only [mem_iUnion, mem_image, bex_def] using hS A
      refine' mem_iUnion₂.2 ⟨y, Or.inr _, _⟩
      -- ⊢ ↑y ∈ ⋃ (i : Fin N), Subtype.val '' S i
      · simp only [mem_iUnion, mem_image]
        -- ⊢ ∃ i x, x ∈ S i ∧ ↑x = ↑y
        exact ⟨i, y, ySi, rfl⟩
        -- 🎉 no goals
      · have : (y : α) ∈ s' := y.2
        -- ⊢ x ∈ closedBall (↑y) (r ↑y)
        simp only [if_pos this]
        -- ⊢ x ∈ closedBall (↑y) (r1 ↑y)
        exact ball_subset_closedBall xy
        -- 🎉 no goals
    · obtain ⟨y, yt0, hxy⟩ : ∃ y : α, y ∈ t0 ∧ x ∈ closedBall y (r0 y) := by
        simpa [hx, -mem_closedBall] using h'x
      refine' mem_iUnion₂.2 ⟨y, Or.inl yt0, _⟩
      -- ⊢ x ∈ closedBall y (r y)
      rwa [r_t0 _ yt0]
      -- 🎉 no goals
  -- the only nontrivial property is the measure control, which we check now
  · -- the sets in the first step have measure at most `μ s + ε / 2`
    have A : (∑' x : t0, μ (closedBall x (r x))) ≤ μ s + ε / 2 :=
      calc
        (∑' x : t0, μ (closedBall x (r x))) = ∑' x : t0, μ (closedBall x (r0 x)) := by
          congr 1; ext x; rw [r_t0 x x.2]
        _ = μ (⋃ x : t0, closedBall x (r0 x)) := by
          haveI : Encodable t0 := t0_count.toEncodable
          rw [measure_iUnion]
          · exact (pairwise_subtype_iff_pairwise_set _ _).2 t0_disj
          · exact fun i => measurableSet_closedBall
        _ ≤ μ u := by
          apply measure_mono
          simp only [SetCoe.forall, Subtype.coe_mk, iUnion_subset_iff]
          intro x hx
          apply Subset.trans (closedBall_subset_ball (hr0 x hx).2.2) (hR x (t0s hx)).2
        _ ≤ μ s + ε / 2 := μu
    -- each subfamily in the second step has measure at most `ε / (2 N)`.
    have B : ∀ i : Fin N, (∑' x : ((↑) : s' → α) '' S i, μ (closedBall x (r x))) ≤ ε / 2 / N :=
      fun i =>
      calc
        (∑' x : ((↑) : s' → α) '' S i, μ (closedBall x (r x))) =
            ∑' x : S i, μ (closedBall x (r x)) := by
          have : InjOn ((↑) : s' → α) (S i) := Subtype.val_injective.injOn _
          let F : S i ≃ ((↑) : s' → α) '' S i := this.bijOn_image.equiv _
          exact (F.tsum_eq fun x => μ (closedBall x (r x))).symm
        _ = ∑' x : S i, μ (closedBall x (r1 x)) := by
          congr 1; ext x; have : (x : α) ∈ s' := x.1.2; simp only [if_pos this]
        _ = μ (⋃ x : S i, closedBall x (r1 x)) := by
          haveI : Encodable (S i) := (S_count i).toEncodable
          rw [measure_iUnion]
          · exact (pairwise_subtype_iff_pairwise_set _ _).2 (S_disj i)
          · exact fun i => measurableSet_closedBall
        _ ≤ μ v := by
          apply measure_mono
          simp only [SetCoe.forall, Subtype.coe_mk, iUnion_subset_iff]
          intro x xs' _
          exact (hr1 x xs').2
        _ ≤ ε / 2 / N := by have : μ s' = 0 := μt0; rwa [this, zero_add] at μv
    -- add up all these to prove the desired estimate
    calc
      (∑' x : ↥(t0 ∪ ⋃ i : Fin N, ((↑) : s' → α) '' S i), μ (closedBall x (r x))) ≤
          (∑' x : t0, μ (closedBall x (r x))) +
            ∑' x : ⋃ i : Fin N, ((↑) : s' → α) '' S i, μ (closedBall x (r x)) :=
        ENNReal.tsum_union_le (fun x => μ (closedBall x (r x))) _ _
      _ ≤
          (∑' x : t0, μ (closedBall x (r x))) +
            ∑ i : Fin N, ∑' x : ((↑) : s' → α) '' S i, μ (closedBall x (r x)) :=
        (add_le_add le_rfl (ENNReal.tsum_iUnion_le (fun x => μ (closedBall x (r x))) _))
      _ ≤ μ s + ε / 2 + ∑ i : Fin N, ε / 2 / N := by
        refine' add_le_add A _
        refine' Finset.sum_le_sum _
        intro i _
        exact B i
      _ ≤ μ s + ε / 2 + ε / 2 := by
        refine' add_le_add le_rfl _
        simp only [Finset.card_fin, Finset.sum_const, nsmul_eq_mul, ENNReal.mul_div_le]
      _ = μ s + ε := by rw [add_assoc, ENNReal.add_halves]
#align besicovitch.exists_closed_ball_covering_tsum_measure_le Besicovitch.exists_closedBall_covering_tsum_measure_le

/-! ### Consequences on differentiation of measures -/


/-- In a space with the Besicovitch covering property, the set of closed balls with positive radius
forms a Vitali family. This is essentially a restatement of the measurable Besicovitch theorem. -/
protected def vitaliFamily (μ : Measure α) [SigmaFinite μ] : VitaliFamily μ where
  setsAt x := (fun r : ℝ => closedBall x r) '' Ioi (0 : ℝ)
  MeasurableSet' := by
    intro x y hy
    -- ⊢ MeasurableSet y
    obtain ⟨r, _, rfl⟩ : ∃ r : ℝ, 0 < r ∧ closedBall x r = y := by
      simpa only [mem_image, mem_Ioi] using hy
    exact isClosed_ball.measurableSet
    -- 🎉 no goals
  nonempty_interior := by
    intro x y hy
    -- ⊢ Set.Nonempty (interior y)
    obtain ⟨r, rpos, rfl⟩ : ∃ r : ℝ, 0 < r ∧ closedBall x r = y := by
      simpa only [mem_image, mem_Ioi] using hy
    simp only [Nonempty.mono ball_subset_interior_closedBall, rpos, nonempty_ball]
    -- 🎉 no goals
  Nontrivial x ε εpos := ⟨closedBall x ε, mem_image_of_mem _ εpos, Subset.refl _⟩
  covering := by
    intro s f fsubset ffine
    -- ⊢ ∃ t, (∀ (p : α × Set α), p ∈ t → p.fst ∈ s) ∧ (PairwiseDisjoint t fun p => p …
    let g : α → Set ℝ := fun x => {r | 0 < r ∧ closedBall x r ∈ f x}
    -- ⊢ ∃ t, (∀ (p : α × Set α), p ∈ t → p.fst ∈ s) ∧ (PairwiseDisjoint t fun p => p …
    have A : ∀ x ∈ s, ∀ δ > 0, (g x ∩ Ioo 0 δ).Nonempty := by
      intro x xs δ δpos
      obtain ⟨t, tf, ht⟩ : ∃ (t : Set α), t ∈ f x ∧ t ⊆ closedBall x (δ / 2) :=
        ffine x xs (δ / 2) (half_pos δpos)
      obtain ⟨r, rpos, rfl⟩ : ∃ r : ℝ, 0 < r ∧ closedBall x r = t := by simpa using fsubset x xs tf
      rcases le_total r (δ / 2) with (H | H)
      · exact ⟨r, ⟨rpos, tf⟩, ⟨rpos, H.trans_lt (half_lt_self δpos)⟩⟩
      · have : closedBall x r = closedBall x (δ / 2) :=
          Subset.antisymm ht (closedBall_subset_closedBall H)
        rw [this] at tf
        refine' ⟨δ / 2, ⟨half_pos δpos, tf⟩, ⟨half_pos δpos, half_lt_self δpos⟩⟩
    obtain ⟨t, r, _, ts, tg, μt, tdisj⟩ :
      ∃ (t : Set α) (r : α → ℝ),
        t.Countable ∧
          t ⊆ s ∧
            (∀ x ∈ t, r x ∈ g x ∩ Ioo 0 1) ∧
              μ (s \ ⋃ x ∈ t, closedBall x (r x)) = 0 ∧
                t.PairwiseDisjoint fun x => closedBall x (r x) :=
      exists_disjoint_closedBall_covering_ae μ g s A (fun _ => 1) fun _ _ => zero_lt_one
    let F : α → α × Set α := fun x => (x, closedBall x (r x))
    -- ⊢ ∃ t, (∀ (p : α × Set α), p ∈ t → p.fst ∈ s) ∧ (PairwiseDisjoint t fun p => p …
    refine' ⟨F '' t, _, _, _, _⟩
    · rintro - ⟨x, hx, rfl⟩; exact ts hx
      -- ⊢ (F x).fst ∈ s
                             -- 🎉 no goals
    · rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩ hxy
      -- ⊢ (Disjoint on fun p => p.snd) (F x) (F y)
      exact tdisj hx hy (ne_of_apply_ne F hxy)
      -- 🎉 no goals
    · rintro - ⟨x, hx, rfl⟩; exact (tg x hx).1.2
      -- ⊢ (F x).snd ∈ f (F x).fst
                             -- 🎉 no goals
    · rwa [biUnion_image]
      -- 🎉 no goals
#align besicovitch.vitali_family Besicovitch.vitaliFamily

/-- The main feature of the Besicovitch Vitali family is that its filter at a point `x` corresponds
to convergence along closed balls. We record one of the two implications here, which will enable us
to deduce specific statements on differentiation of measures in this context from the general
versions. -/
theorem tendsto_filterAt (μ : Measure α) [SigmaFinite μ] (x : α) :
    Tendsto (fun r => closedBall x r) (𝓝[>] 0) ((Besicovitch.vitaliFamily μ).filterAt x) := by
  intro s hs
  -- ⊢ s ∈ map (fun r => closedBall x r) (𝓝[Ioi 0] 0)
  simp only [mem_map]
  -- ⊢ (fun r => closedBall x r) ⁻¹' s ∈ 𝓝[Ioi 0] 0
  obtain ⟨ε, εpos, hε⟩ :
    ∃ (ε : ℝ), ε > 0 ∧
      ∀ a : Set α, a ∈ (Besicovitch.vitaliFamily μ).setsAt x → a ⊆ closedBall x ε → a ∈ s :=
    (VitaliFamily.mem_filterAt_iff _).1 hs
  have : Ioc (0 : ℝ) ε ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsWithin_Ioi ⟨le_rfl, εpos⟩
  -- ⊢ (fun r => closedBall x r) ⁻¹' s ∈ 𝓝[Ioi 0] 0
  filter_upwards [this] with _ hr
  -- ⊢ a✝ ∈ (fun r => closedBall x r) ⁻¹' s
  apply hε
  -- ⊢ (fun r => closedBall x r) a✝ ∈ VitaliFamily.setsAt (Besicovitch.vitaliFamily …
  · exact mem_image_of_mem _ hr.1
    -- 🎉 no goals
  · exact closedBall_subset_closedBall hr.2
    -- 🎉 no goals
#align besicovitch.tendsto_filter_at Besicovitch.tendsto_filterAt

variable [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
  [HasBesicovitchCovering β]

/-- In a space with the Besicovitch covering property, the ratio of the measure of balls converges
almost surely to the Radon-Nikodym derivative. -/
theorem ae_tendsto_rnDeriv (ρ μ : Measure β) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ρ] :
    ∀ᵐ x ∂μ,
      Tendsto (fun r => ρ (closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 (ρ.rnDeriv μ x)) := by
  filter_upwards [VitaliFamily.ae_tendsto_rnDeriv (Besicovitch.vitaliFamily μ) ρ] with x hx
  -- ⊢ Tendsto (fun r => ↑↑ρ (closedBall x r) / ↑↑μ (closedBall x r)) (𝓝[Ioi 0] 0)  …
  exact hx.comp (tendsto_filterAt μ x)
  -- 🎉 no goals
#align besicovitch.ae_tendsto_rn_deriv Besicovitch.ae_tendsto_rnDeriv

/-- Given a measurable set `s`, then `μ (s ∩ closedBall x r) / μ (closedBall x r)` converges when
`r` tends to `0`, for almost every `x`. The limit is `1` for `x ∈ s` and `0` for `x ∉ s`.
This shows that almost every point of `s` is a Lebesgue density point for `s`.
A version for non-measurable sets holds, but it only gives the first conclusion,
see `ae_tendsto_measure_inter_div`. -/
theorem ae_tendsto_measure_inter_div_of_measurableSet (μ : Measure β) [IsLocallyFiniteMeasure μ]
    {s : Set β} (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ,
      Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0)
        (𝓝 (s.indicator 1 x)) := by
  filter_upwards [VitaliFamily.ae_tendsto_measure_inter_div_of_measurableSet
      (Besicovitch.vitaliFamily μ) hs]
  intro x hx
  -- ⊢ Tendsto (fun r => ↑↑μ (s ∩ closedBall x r) / ↑↑μ (closedBall x r)) (𝓝[Ioi 0] …
  exact hx.comp (tendsto_filterAt μ x)
  -- 🎉 no goals
#align besicovitch.ae_tendsto_measure_inter_div_of_measurable_set Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet

/-- Given an arbitrary set `s`, then `μ (s ∩ closedBall x r) / μ (closedBall x r)` converges
to `1` when `r` tends to `0`, for almost every `x` in `s`.
This shows that almost every point of `s` is a Lebesgue density point for `s`.
A stronger version holds for measurable sets, see `ae_tendsto_measure_inter_div_of_measurableSet`.

See also `IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`. -/
theorem ae_tendsto_measure_inter_div (μ : Measure β) [IsLocallyFiniteMeasure μ] (s : Set β) :
    ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1) := by
  filter_upwards [VitaliFamily.ae_tendsto_measure_inter_div (Besicovitch.vitaliFamily μ) s] with x
    hx using hx.comp (tendsto_filterAt μ x)
#align besicovitch.ae_tendsto_measure_inter_div Besicovitch.ae_tendsto_measure_inter_div

end Besicovitch
