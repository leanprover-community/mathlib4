/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.gluing
! leanprover-community/mathlib commit e1a7bdeb4fd826b7e71d130d34988f0a2d26a177
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.Isometry

/-!
# Metric space gluing

Gluing two metric spaces along a common subset. Formally, we are given

```
     Φ
  Z ---> X
  |
  |Ψ
  v
  Y
```
where `hΦ : isometry Φ` and `hΨ : isometry Ψ`.
We want to complete the square by a space `glue_space hΦ hΨ` and two isometries
`to_glue_l hΦ hΨ` and `to_glue_r hΦ hΨ` that make the square commute.
We start by defining a predistance on the disjoint union `X ⊕ Y`, for which
points `Φ p` and `Ψ p` are at distance 0. The (quotient) metric space associated
to this predistance is the desired space.

This is an instance of a more general construction, where `Φ` and `Ψ` do not have to be isometries,
but the distances in the image almost coincide, up to `2ε` say. Then one can almost glue the two
spaces so that the images of a point under `Φ` and `Ψ` are `ε`-close. If `ε > 0`, this yields a
metric space structure on `X ⊕ Y`, without the need to take a quotient. In particular,
this gives a natural metric space structure on `X ⊕ Y`, where the basepoints
are at distance 1, say, and the distances between other points are obtained by going through the two
basepoints.
(We also register the same metric space structure on a general disjoint union `Σ i, E i`).

We also define the inductive limit of metric spaces. Given
```
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
```
where the `X n` are metric spaces and `f n` isometric embeddings, we define the inductive
limit of the `X n`, also known as the increasing union of the `X n` in this context, if we
identify `X n` and `X (n+1)` through `f n`. This is a metric space in which all `X n` embed
isometrically and in a way compatible with `f n`.

-/


noncomputable section

universe u v w

open Function Set

open uniformity

namespace Metric

section ApproxGluing

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [MetricSpace X] [MetricSpace Y] {Φ : Z → X} {Ψ : Z → Y} {ε : ℝ}

open _Root_.Sum (inl inr)

/-- Define a predistance on `X ⊕ Y`, for which `Φ p` and `Ψ p` are at distance `ε` -/
def glueDist (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : Sum X Y → Sum X Y → ℝ
  | inl x, inl y => dist x y
  | inr x, inr y => dist x y
  | inl x, inr y => (⨅ p, dist x (Φ p) + dist y (Ψ p)) + ε
  | inr x, inl y => (⨅ p, dist y (Φ p) + dist x (Ψ p)) + ε
#align metric.glue_dist Metric.glueDist

private theorem glue_dist_self (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : ∀ x, glueDist Φ Ψ ε x x = 0
  | inl x => dist_self _
  | inr x => dist_self _
#align metric.glue_dist_self metric.glue_dist_self

theorem glueDist_glued_points [Nonempty Z] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (p : Z) :
    glueDist Φ Ψ ε (inl (Φ p)) (inr (Ψ p)) = ε :=
  by
  have : (⨅ q, dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q)) = 0 :=
    by
    have A : ∀ q, 0 ≤ dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) := fun q => by
      rw [← add_zero (0 : ℝ)] <;> exact add_le_add dist_nonneg dist_nonneg
    refine' le_antisymm _ (le_cinfᵢ A)
    have : 0 = dist (Φ p) (Φ p) + dist (Ψ p) (Ψ p) := by simp
    rw [this]
    exact cinfᵢ_le ⟨0, forall_range_iff.2 A⟩ p
  rw [glue_dist, this, zero_add]
#align metric.glue_dist_glued_points Metric.glueDist_glued_points

private theorem glue_dist_comm (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) :
    ∀ x y, glueDist Φ Ψ ε x y = glueDist Φ Ψ ε y x
  | inl x, inl y => dist_comm _ _
  | inr x, inr y => dist_comm _ _
  | inl x, inr y => rfl
  | inr x, inl y => rfl
#align metric.glue_dist_comm metric.glue_dist_comm

variable [Nonempty Z]

private theorem glue_dist_triangle (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)
    (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) :
    ∀ x y z, glueDist Φ Ψ ε x z ≤ glueDist Φ Ψ ε x y + glueDist Φ Ψ ε y z
  | inl x, inl y, inl z => dist_triangle _ _ _
  | inr x, inr y, inr z => dist_triangle _ _ _
  | inr x, inl y, inl z =>
    by
    have B : ∀ a b, BddBelow (range fun p : Z => dist a (Φ p) + dist b (Ψ p)) := fun a b =>
      ⟨0, forall_range_iff.2 fun p => add_nonneg dist_nonneg dist_nonneg⟩
    unfold glue_dist
    have : (⨅ p, dist z (Φ p) + dist x (Ψ p)) ≤ (⨅ p, dist y (Φ p) + dist x (Ψ p)) + dist y z :=
      by
      have :
        (⨅ p, dist y (Φ p) + dist x (Ψ p)) + dist y z =
          infᵢ ((fun t => t + dist y z) ∘ fun p => dist y (Φ p) + dist x (Ψ p)) :=
        by
        refine'
          Monotone.map_cinfᵢ_of_continuousAt (continuous_at_id.add continuousAt_const) _ (B _ _)
        intro x y hx
        simpa
      rw [this, comp]
      refine' cinfᵢ_mono (B _ _) fun p => _
      calc
        dist z (Φ p) + dist x (Ψ p) ≤ dist y z + dist y (Φ p) + dist x (Ψ p) :=
          add_le_add (dist_triangle_left _ _ _) le_rfl
        _ = dist y (Φ p) + dist x (Ψ p) + dist y z := by ring
        
    linarith
  | inr x, inr y, inl z =>
    by
    have B : ∀ a b, BddBelow (range fun p : Z => dist a (Φ p) + dist b (Ψ p)) := fun a b =>
      ⟨0, forall_range_iff.2 fun p => add_nonneg dist_nonneg dist_nonneg⟩
    unfold glue_dist
    have : (⨅ p, dist z (Φ p) + dist x (Ψ p)) ≤ dist x y + ⨅ p, dist z (Φ p) + dist y (Ψ p) :=
      by
      have :
        (dist x y + ⨅ p, dist z (Φ p) + dist y (Ψ p)) =
          infᵢ ((fun t => dist x y + t) ∘ fun p => dist z (Φ p) + dist y (Ψ p)) :=
        by
        refine'
          Monotone.map_cinfᵢ_of_continuousAt (continuous_at_const.add continuousAt_id) _ (B _ _)
        intro x y hx
        simpa
      rw [this, comp]
      refine' cinfᵢ_mono (B _ _) fun p => _
      calc
        dist z (Φ p) + dist x (Ψ p) ≤ dist z (Φ p) + (dist x y + dist y (Ψ p)) :=
          add_le_add le_rfl (dist_triangle _ _ _)
        _ = dist x y + (dist z (Φ p) + dist y (Ψ p)) := by ring
        
    linarith
  | inl x, inl y, inr z =>
    by
    have B : ∀ a b, BddBelow (range fun p : Z => dist a (Φ p) + dist b (Ψ p)) := fun a b =>
      ⟨0, forall_range_iff.2 fun p => add_nonneg dist_nonneg dist_nonneg⟩
    unfold glue_dist
    have : (⨅ p, dist x (Φ p) + dist z (Ψ p)) ≤ dist x y + ⨅ p, dist y (Φ p) + dist z (Ψ p) :=
      by
      have :
        (dist x y + ⨅ p, dist y (Φ p) + dist z (Ψ p)) =
          infᵢ ((fun t => dist x y + t) ∘ fun p => dist y (Φ p) + dist z (Ψ p)) :=
        by
        refine'
          Monotone.map_cinfᵢ_of_continuousAt (continuous_at_const.add continuousAt_id) _ (B _ _)
        intro x y hx
        simpa
      rw [this, comp]
      refine' cinfᵢ_mono (B _ _) fun p => _
      calc
        dist x (Φ p) + dist z (Ψ p) ≤ dist x y + dist y (Φ p) + dist z (Ψ p) :=
          add_le_add (dist_triangle _ _ _) le_rfl
        _ = dist x y + (dist y (Φ p) + dist z (Ψ p)) := by ring
        
    linarith
  | inl x, inr y, inr z =>
    by
    have B : ∀ a b, BddBelow (range fun p : Z => dist a (Φ p) + dist b (Ψ p)) := fun a b =>
      ⟨0, forall_range_iff.2 fun p => add_nonneg dist_nonneg dist_nonneg⟩
    unfold glue_dist
    have : (⨅ p, dist x (Φ p) + dist z (Ψ p)) ≤ (⨅ p, dist x (Φ p) + dist y (Ψ p)) + dist y z :=
      by
      have :
        (⨅ p, dist x (Φ p) + dist y (Ψ p)) + dist y z =
          infᵢ ((fun t => t + dist y z) ∘ fun p => dist x (Φ p) + dist y (Ψ p)) :=
        by
        refine'
          Monotone.map_cinfᵢ_of_continuousAt (continuous_at_id.add continuousAt_const) _ (B _ _)
        intro x y hx
        simpa
      rw [this, comp]
      refine' cinfᵢ_mono (B _ _) fun p => _
      calc
        dist x (Φ p) + dist z (Ψ p) ≤ dist x (Φ p) + (dist y z + dist y (Ψ p)) :=
          add_le_add le_rfl (dist_triangle_left _ _ _)
        _ = dist x (Φ p) + dist y (Ψ p) + dist y z := by ring
        
    linarith
  | inl x, inr y, inl z =>
    le_of_forall_pos_le_add fun δ δpos =>
      by
      obtain ⟨p, hp⟩ : ∃ p, dist x (Φ p) + dist y (Ψ p) < (⨅ p, dist x (Φ p) + dist y (Ψ p)) + δ / 2
      exact exists_lt_of_cinfᵢ_lt (by linarith)
      obtain ⟨q, hq⟩ : ∃ q, dist z (Φ q) + dist y (Ψ q) < (⨅ p, dist z (Φ p) + dist y (Ψ p)) + δ / 2
      exact exists_lt_of_cinfᵢ_lt (by linarith)
      have : dist (Φ p) (Φ q) ≤ dist (Ψ p) (Ψ q) + 2 * ε :=
        by
        have := le_trans (le_abs_self _) (H p q)
        · linarith
      calc
        dist x z ≤ dist x (Φ p) + dist (Φ p) (Φ q) + dist (Φ q) z := dist_triangle4 _ _ _ _
        _ ≤ dist x (Φ p) + dist (Ψ p) (Ψ q) + dist z (Φ q) + 2 * ε := by
          rw [dist_comm z] <;> linarith
        _ ≤ dist x (Φ p) + (dist y (Ψ p) + dist y (Ψ q)) + dist z (Φ q) + 2 * ε :=
          (add_le_add (add_le_add (add_le_add le_rfl (dist_triangle_left _ _ _)) le_rfl) le_rfl)
        _ ≤ (⨅ p, dist x (Φ p) + dist y (Ψ p)) + ε + ((⨅ p, dist z (Φ p) + dist y (Ψ p)) + ε) + δ :=
          by linarith
        
  | inr x, inl y, inr z =>
    le_of_forall_pos_le_add fun δ δpos =>
      by
      obtain ⟨p, hp⟩ : ∃ p, dist y (Φ p) + dist x (Ψ p) < (⨅ p, dist y (Φ p) + dist x (Ψ p)) + δ / 2
      exact exists_lt_of_cinfᵢ_lt (by linarith)
      obtain ⟨q, hq⟩ : ∃ q, dist y (Φ q) + dist z (Ψ q) < (⨅ p, dist y (Φ p) + dist z (Ψ p)) + δ / 2
      exact exists_lt_of_cinfᵢ_lt (by linarith)
      have : dist (Ψ p) (Ψ q) ≤ dist (Φ p) (Φ q) + 2 * ε :=
        by
        have := le_trans (neg_le_abs_self _) (H p q)
        · linarith
      calc
        dist x z ≤ dist x (Ψ p) + dist (Ψ p) (Ψ q) + dist (Ψ q) z := dist_triangle4 _ _ _ _
        _ ≤ dist x (Ψ p) + dist (Φ p) (Φ q) + dist z (Ψ q) + 2 * ε := by
          rw [dist_comm z] <;> linarith
        _ ≤ dist x (Ψ p) + (dist y (Φ p) + dist y (Φ q)) + dist z (Ψ q) + 2 * ε :=
          (add_le_add (add_le_add (add_le_add le_rfl (dist_triangle_left _ _ _)) le_rfl) le_rfl)
        _ ≤ (⨅ p, dist y (Φ p) + dist x (Ψ p)) + ε + ((⨅ p, dist y (Φ p) + dist z (Ψ p)) + ε) + δ :=
          by linarith
        
#align metric.glue_dist_triangle metric.glue_dist_triangle

private theorem glue_eq_of_dist_eq_zero (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (ε0 : 0 < ε) :
    ∀ p q : Sum X Y, glueDist Φ Ψ ε p q = 0 → p = q
  | inl x, inl y, h => by rw [eq_of_dist_eq_zero h]
  | inl x, inr y, h =>
    by
    have : 0 ≤ ⨅ p, dist x (Φ p) + dist y (Ψ p) :=
      le_cinfᵢ fun p => by simpa using add_le_add (@dist_nonneg _ _ x _) (@dist_nonneg _ _ y _)
    have : 0 + ε ≤ glue_dist Φ Ψ ε (inl x) (inr y) := add_le_add this (le_refl ε)
    exfalso
    linarith
  | inr x, inl y, h =>
    by
    have : 0 ≤ ⨅ p, dist y (Φ p) + dist x (Ψ p) :=
      le_cinfᵢ fun p => by
        simpa [add_comm] using add_le_add (@dist_nonneg _ _ x _) (@dist_nonneg _ _ y _)
    have : 0 + ε ≤ glue_dist Φ Ψ ε (inr x) (inl y) := add_le_add this (le_refl ε)
    exfalso
    linarith
  | inr x, inr y, h => by rw [eq_of_dist_eq_zero h]
#align metric.glue_eq_of_dist_eq_zero metric.glue_eq_of_dist_eq_zero

/-- Given two maps `Φ` and `Ψ` intro metric spaces `X` and `Y` such that the distances between
`Φ p` and `Φ q`, and between `Ψ p` and `Ψ q`, coincide up to `2 ε` where `ε > 0`, one can almost
glue the two spaces `X` and `Y` along the images of `Φ` and `Ψ`, so that `Φ p` and `Ψ p` are
at distance `ε`. -/
def glueMetricApprox (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (ε0 : 0 < ε)
    (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) : MetricSpace (Sum X Y)
    where
  dist := glueDist Φ Ψ ε
  dist_self := glueDist_self Φ Ψ ε
  dist_comm := glueDist_comm Φ Ψ ε
  dist_triangle := glueDist_triangle Φ Ψ ε H
  eq_of_dist_eq_zero := glue_eq_of_dist_eq_zero Φ Ψ ε ε0
#align metric.glue_metric_approx Metric.glueMetricApprox

end ApproxGluing

section Sum

/- A particular case of the previous construction is when one uses basepoints in `X` and `Y` and one
glues only along the basepoints, putting them at distance 1. We give a direct definition of
the distance, without infi, as it is easier to use in applications, and show that it is equal to
the gluing distance defined above to take advantage of the lemmas we have already proved. -/
variable {X : Type u} {Y : Type v} {Z : Type w}

variable [MetricSpace X] [MetricSpace Y]

open Sum (inl inr)

/-- Distance on a disjoint union. There are many (noncanonical) ways to put a distance compatible
with each factor.
If the two spaces are bounded, one can say for instance that each point in the first is at distance
`diam X + diam Y + 1` of each point in the second.
Instead, we choose a construction that works for unbounded spaces, but requires basepoints,
chosen arbitrarily.
We embed isometrically each factor, set the basepoints at distance 1,
arbitrarily, and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
def Sum.dist : Sum X Y → Sum X Y → ℝ
  | inl a, inl a' => dist a a'
  | inr b, inr b' => dist b b'
  | inl a, inr b => dist a (Nonempty.some ⟨a⟩) + 1 + dist (Nonempty.some ⟨b⟩) b
  | inr b, inl a => dist b (Nonempty.some ⟨b⟩) + 1 + dist (Nonempty.some ⟨a⟩) a
#align metric.sum.dist Metric.Sum.dist

theorem Sum.dist_eq_glueDist {p q : Sum X Y} (x : X) (y : Y) :
    Sum.dist p q =
      glueDist (fun _ : Unit => Nonempty.some ⟨x⟩) (fun _ : Unit => Nonempty.some ⟨y⟩) 1 p q :=
  by
  cases p <;> cases q <;> first |rfl|simp [sum.dist, glue_dist, dist_comm, add_comm, add_left_comm]
#align metric.sum.dist_eq_glue_dist Metric.Sum.dist_eq_glueDist

private theorem sum.dist_comm (x y : Sum X Y) : Sum.dist x y = Sum.dist y x := by
  cases x <;> cases y <;> simp only [sum.dist, dist_comm, add_comm, add_left_comm]
#align metric.sum.dist_comm metric.sum.dist_comm

theorem Sum.one_dist_le {x : X} {y : Y} : 1 ≤ Sum.dist (inl x) (inr y) :=
  le_trans (le_add_of_nonneg_right dist_nonneg) <|
    add_le_add_right (le_add_of_nonneg_left dist_nonneg) _
#align metric.sum.one_dist_le Metric.Sum.one_dist_le

theorem Sum.one_dist_le' {x : X} {y : Y} : 1 ≤ Sum.dist (inr y) (inl x) := by
  rw [sum.dist_comm] <;> exact sum.one_dist_le
#align metric.sum.one_dist_le' Metric.Sum.one_dist_le'

private theorem sum.mem_uniformity (s : Set (Sum X Y × Sum X Y)) :
    s ∈ 𝓤 (Sum X Y) ↔ ∃ ε > 0, ∀ a b, Sum.dist a b < ε → (a, b) ∈ s :=
  by
  constructor
  · rintro ⟨hsX, hsY⟩
    rcases mem_uniformity_dist.1 hsX with ⟨εX, εX0, hX⟩
    rcases mem_uniformity_dist.1 hsY with ⟨εY, εY0, hY⟩
    refine' ⟨min (min εX εY) 1, lt_min (lt_min εX0 εY0) zero_lt_one, _⟩
    rintro (a | a) (b | b) h
    · exact hX (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_left _ _)))
    · cases not_le_of_lt (lt_of_lt_of_le h (min_le_right _ _)) sum.one_dist_le
    · cases not_le_of_lt (lt_of_lt_of_le h (min_le_right _ _)) sum.one_dist_le'
    · exact hY (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_right _ _)))
  · rintro ⟨ε, ε0, H⟩
    constructor <;> rw [Filter.mem_sets, Filter.mem_map, mem_uniformity_dist] <;>
      exact ⟨ε, ε0, fun x y h => H _ _ h⟩
#align metric.sum.mem_uniformity metric.sum.mem_uniformity

/-- The distance on the disjoint union indeed defines a metric space. All the distance properties
follow from our choice of the distance. The harder work is to show that the uniform structure
defined by the distance coincides with the disjoint union uniform structure. -/
def metricSpaceSum : MetricSpace (Sum X Y)
    where
  dist := Sum.dist
  dist_self x := by cases x <;> simp only [sum.dist, dist_self]
  dist_comm := Sum.dist_comm
  dist_triangle p q r := by
    cases p <;> cases q <;> cases r
    · exact dist_triangle _ _ _
    · simp only [dist, sum.dist_eq_glue_dist p r]
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _
    · simp only [dist, sum.dist_eq_glue_dist p q]
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _
    · simp only [dist, sum.dist_eq_glue_dist p q]
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _
    · simp only [dist, sum.dist_eq_glue_dist q p]
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _
    · simp only [dist, sum.dist_eq_glue_dist q p]
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _
    · simp only [dist, sum.dist_eq_glue_dist r p]
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _
    · exact dist_triangle _ _ _
  eq_of_dist_eq_zero p q := by
    cases p <;> cases q
    · simp only [sum.dist, dist_eq_zero, imp_self]
    · intro h
      simp only [dist, sum.dist_eq_glue_dist p q] at h
      exact glue_eq_of_dist_eq_zero _ _ _ zero_lt_one _ _ h
    · intro h
      simp only [dist, sum.dist_eq_glue_dist q p] at h
      exact glue_eq_of_dist_eq_zero _ _ _ zero_lt_one _ _ h
    · simp only [sum.dist, dist_eq_zero, imp_self]
  toUniformSpace := Sum.uniformSpace
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ Sum.mem_uniformity
#align metric.metric_space_sum Metric.metricSpaceSum

attribute [local instance] metric_space_sum

theorem Sum.dist_eq {x y : Sum X Y} : dist x y = Sum.dist x y :=
  rfl
#align metric.sum.dist_eq Metric.Sum.dist_eq

/-- The left injection of a space in a disjoint union is an isometry -/
theorem isometry_inl : Isometry (Sum.inl : X → Sum X Y) :=
  Isometry.of_dist_eq fun x y => rfl
#align metric.isometry_inl Metric.isometry_inl

/-- The right injection of a space in a disjoint union is an isometry -/
theorem isometry_inr : Isometry (Sum.inr : Y → Sum X Y) :=
  Isometry.of_dist_eq fun x y => rfl
#align metric.isometry_inr Metric.isometry_inr

end Sum

namespace Sigma

/- Copy of the previous paragraph, but for arbitrary disjoint unions instead of the disjoint union
of two spaces. I.e., work with sigma types instead of sum types. -/
variable {ι : Type _} {E : ι → Type _} [∀ i, MetricSpace (E i)]

open Classical

/-- Distance on a disjoint union. There are many (noncanonical) ways to put a distance compatible
with each factor.
We choose a construction that works for unbounded spaces, but requires basepoints,
chosen arbitrarily.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
protected def dist : (Σi, E i) → (Σi, E i) → ℝ
  | ⟨i, x⟩, ⟨j, y⟩ =>
    if h : i = j then
      haveI : E j = E i := by rw [h]
      Dist.dist x (cast this y)
    else Dist.dist x (Nonempty.some ⟨x⟩) + 1 + Dist.dist (Nonempty.some ⟨y⟩) y
#align metric.sigma.dist Metric.Sigma.dist

/-- A `has_dist` instance on the disjoint union `Σ i, E i`.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
def hasDist : Dist (Σi, E i) :=
  ⟨Sigma.dist⟩
#align metric.sigma.has_dist Metric.Sigma.hasDist

attribute [local instance] sigma.has_dist

@[simp]
theorem dist_same (i : ι) (x : E i) (y : E i) : dist (⟨i, x⟩ : Σj, E j) ⟨i, y⟩ = dist x y := by
  simp [Dist.dist, sigma.dist]
#align metric.sigma.dist_same Metric.Sigma.dist_same

@[simp]
theorem dist_ne {i j : ι} (h : i ≠ j) (x : E i) (y : E j) :
    dist (⟨i, x⟩ : Σk, E k) ⟨j, y⟩ = dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨y⟩) y :=
  by simp [Dist.dist, sigma.dist, h]
#align metric.sigma.dist_ne Metric.Sigma.dist_ne

theorem one_le_dist_of_ne {i j : ι} (h : i ≠ j) (x : E i) (y : E j) :
    1 ≤ dist (⟨i, x⟩ : Σk, E k) ⟨j, y⟩ :=
  by
  rw [sigma.dist_ne h x y]
  linarith [@dist_nonneg _ _ x (Nonempty.some ⟨x⟩), @dist_nonneg _ _ (Nonempty.some ⟨y⟩) y]
#align metric.sigma.one_le_dist_of_ne Metric.Sigma.one_le_dist_of_ne

theorem fst_eq_of_dist_lt_one (x y : Σi, E i) (h : dist x y < 1) : x.1 = y.1 :=
  by
  cases x; cases y
  contrapose! h
  apply one_le_dist_of_ne h
#align metric.sigma.fst_eq_of_dist_lt_one Metric.Sigma.fst_eq_of_dist_lt_one

protected theorem dist_triangle (x y z : Σi, E i) : dist x z ≤ dist x y + dist y z :=
  by
  rcases x with ⟨i, x⟩; rcases y with ⟨j, y⟩; rcases z with ⟨k, z⟩
  rcases eq_or_ne i k with (rfl | hik)
  · rcases eq_or_ne i j with (rfl | hij)
    · simpa using dist_triangle x y z
    · simp only [hij, hij.symm, sigma.dist_same, sigma.dist_ne, Ne.def, not_false_iff]
      calc
        dist x z ≤ dist x (Nonempty.some ⟨x⟩) + 0 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) := by
          simpa only [zero_add, add_zero] using dist_triangle _ _ _
        _ ≤ _ := by apply_rules [add_le_add, le_rfl, dist_nonneg, zero_le_one]
        
  · rcases eq_or_ne i j with (rfl | hij)
    · simp only [hik, sigma.dist_ne, Ne.def, not_false_iff, sigma.dist_same]
      calc
        dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z ≤
            dist x y + dist y (Nonempty.some ⟨y⟩) + 1 + dist (Nonempty.some ⟨z⟩) z :=
          by apply_rules [add_le_add, le_rfl, dist_triangle]
        _ = _ := by abel
        
    · rcases eq_or_ne j k with (rfl | hjk)
      · simp only [hij, sigma.dist_ne, Ne.def, not_false_iff, sigma.dist_same]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z ≤
              dist x (Nonempty.some ⟨x⟩) + 1 + (dist (Nonempty.some ⟨z⟩) y + dist y z) :=
            by apply_rules [add_le_add, le_rfl, dist_triangle]
          _ = _ := by abel
          
      · simp only [hik, hij, hjk, sigma.dist_ne, Ne.def, not_false_iff]
        calc
          dist x (Nonempty.some ⟨x⟩) + 1 + dist (Nonempty.some ⟨z⟩) z =
              dist x (Nonempty.some ⟨x⟩) + 1 + 0 + (0 + 0 + dist (Nonempty.some ⟨z⟩) z) :=
            by simp only [add_zero, zero_add]
          _ ≤ _ := by apply_rules [add_le_add, zero_le_one, dist_nonneg, le_rfl]
          
#align metric.sigma.dist_triangle Metric.Sigma.dist_triangle

protected theorem isOpen_iff (s : Set (Σi, E i)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s :=
  by
  constructor
  · rintro hs ⟨i, x⟩ hx
    obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ)(H : ε > 0), ball x ε ⊆ Sigma.mk i ⁻¹' s :=
      Metric.isOpen_iff.1 (isOpen_sigma_iff.1 hs i) x hx
    refine' ⟨min ε 1, lt_min εpos zero_lt_one, _⟩
    rintro ⟨j, y⟩ hy
    rcases eq_or_ne i j with (rfl | hij)
    · simp only [sigma.dist_same, lt_min_iff] at hy
      exact hε (mem_ball'.2 hy.1)
    · apply (lt_irrefl (1 : ℝ) _).elim
      calc
        1 ≤ sigma.dist ⟨i, x⟩ ⟨j, y⟩ := sigma.one_le_dist_of_ne hij _ _
        _ < 1 := hy.trans_le (min_le_right _ _)
        
  · intro H
    apply isOpen_sigma_iff.2 fun i => _
    apply Metric.isOpen_iff.2 fun x hx => _
    obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ)(H : ε > 0), ∀ y, dist (⟨i, x⟩ : Σj, E j) y < ε → y ∈ s :=
      H ⟨i, x⟩ hx
    refine' ⟨ε, εpos, fun y hy => _⟩
    apply hε ⟨i, y⟩
    rw [sigma.dist_same]
    exact mem_ball'.1 hy
#align metric.sigma.is_open_iff Metric.Sigma.isOpen_iff

/-- A metric space structure on the disjoint union `Σ i, E i`.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
protected def metricSpace : MetricSpace (Σi, E i) :=
  by
  refine' MetricSpace.ofDistTopology sigma.dist _ _ sigma.dist_triangle sigma.is_open_iff _
  · rintro ⟨i, x⟩
    simp [sigma.dist]
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | h)
    · simp [sigma.dist, dist_comm]
    · simp only [sigma.dist, dist_comm, h, h.symm, not_false_iff, dif_neg]
      abel
  · rintro ⟨i, x⟩ ⟨j, y⟩
    rcases eq_or_ne i j with (rfl | hij)
    · simp [sigma.dist]
    · intro h
      apply (lt_irrefl (1 : ℝ) _).elim
      calc
        1 ≤ sigma.dist (⟨i, x⟩ : Σk, E k) ⟨j, y⟩ := sigma.one_le_dist_of_ne hij _ _
        _ < 1 := by
          rw [h]
          exact zero_lt_one
        
#align metric.sigma.metric_space Metric.Sigma.metricSpace

attribute [local instance] sigma.metric_space

open Topology

open Filter

/-- The injection of a space in a disjoint union is an isometry -/
theorem isometry_mk (i : ι) : Isometry (Sigma.mk i : E i → Σk, E k) :=
  Isometry.of_dist_eq fun x y => by simp
#align metric.sigma.isometry_mk Metric.Sigma.isometry_mk

/-- A disjoint union of complete metric spaces is complete. -/
protected theorem completeSpace [∀ i, CompleteSpace (E i)] : CompleteSpace (Σi, E i) :=
  by
  set s : ι → Set (Σi, E i) := fun i => Sigma.fst ⁻¹' {i}
  set U := { p : (Σk, E k) × Σk, E k | dist p.1 p.2 < 1 }
  have hc : ∀ i, IsComplete (s i) := by
    intro i
    simp only [s, ← range_sigma_mk]
    exact (isometry_mk i).UniformInducing.isComplete_range
  have hd : ∀ (i j), ∀ x ∈ s i, ∀ y ∈ s j, (x, y) ∈ U → i = j := fun i j x hx y hy hxy =>
    (Eq.symm hx).trans ((fst_eq_of_dist_lt_one _ _ hxy).trans hy)
  refine' completeSpace_of_isComplete_univ _
  convert isComplete_unionᵢ_separated hc (dist_mem_uniformity zero_lt_one) hd
  simp [s, ← preimage_Union]
#align metric.sigma.complete_space Metric.Sigma.completeSpace

end Sigma

section Gluing

-- Exact gluing of two metric spaces along isometric subsets.
variable {X : Type u} {Y : Type v} {Z : Type w}

variable [Nonempty Z] [MetricSpace Z] [MetricSpace X] [MetricSpace Y] {Φ : Z → X} {Ψ : Z → Y}
  {ε : ℝ}

open _Root_.Sum (inl inr)

attribute [local instance] UniformSpace.separationSetoid

/-- Given two isometric embeddings `Φ : Z → X` and `Ψ : Z → Y`, we define a pseudo metric space
structure on `X ⊕ Y` by declaring that `Φ x` and `Ψ x` are at distance `0`. -/
def gluePremetric (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : PseudoMetricSpace (Sum X Y)
    where
  dist := glueDist Φ Ψ 0
  dist_self := glueDist_self Φ Ψ 0
  dist_comm := glueDist_comm Φ Ψ 0
  dist_triangle := glueDist_triangle Φ Ψ 0 fun p q => by rw [hΦ.dist_eq, hΨ.dist_eq] <;> simp
#align metric.glue_premetric Metric.gluePremetric

/-- Given two isometric embeddings `Φ : Z → X` and `Ψ : Z → Y`, we define a
space  `glue_space hΦ hΨ` by identifying in `X ⊕ Y` the points `Φ x` and `Ψ x`. -/
def GlueSpace (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Type _ :=
  @UniformSpace.SeparationQuotient _ (gluePremetric hΦ hΨ).toUniformSpace deriving MetricSpace
#align metric.glue_space Metric.GlueSpace

/-- The canonical map from `X` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
def toGlueL (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (x : X) : GlueSpace hΦ hΨ :=
  Quotient.mk'' (inl x)
#align metric.to_glue_l Metric.toGlueL

/-- The canonical map from `Y` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
def toGlueR (hΦ : Isometry Φ) (hΨ : Isometry Ψ) (y : Y) : GlueSpace hΦ hΨ :=
  Quotient.mk'' (inr y)
#align metric.to_glue_r Metric.toGlueR

instance inhabitedLeft (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited X] :
    Inhabited (GlueSpace hΦ hΨ) :=
  ⟨toGlueL _ _ default⟩
#align metric.inhabited_left Metric.inhabitedLeft

instance inhabitedRight (hΦ : Isometry Φ) (hΨ : Isometry Ψ) [Inhabited Y] :
    Inhabited (GlueSpace hΦ hΨ) :=
  ⟨toGlueR _ _ default⟩
#align metric.inhabited_right Metric.inhabitedRight

theorem to_glue_commute (hΦ : Isometry Φ) (hΨ : Isometry Ψ) :
    toGlueL hΦ hΨ ∘ Φ = toGlueR hΦ hΨ ∘ Ψ :=
  by
  letI i : PseudoMetricSpace (Sum X Y) := glue_premetric hΦ hΨ
  letI := i.to_uniform_space
  funext
  simp only [comp, to_glue_l, to_glue_r]
  refine' UniformSpace.SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 _)
  exact glue_dist_glued_points Φ Ψ 0 x
#align metric.to_glue_commute Metric.to_glue_commute

theorem toGlueL_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (toGlueL hΦ hΨ) :=
  Isometry.of_dist_eq fun _ _ => rfl
#align metric.to_glue_l_isometry Metric.toGlueL_isometry

theorem toGlueR_isometry (hΦ : Isometry Φ) (hΨ : Isometry Ψ) : Isometry (toGlueR hΦ hΨ) :=
  Isometry.of_dist_eq fun _ _ => rfl
#align metric.to_glue_r_isometry Metric.toGlueR_isometry

end Gluing

--section
section InductiveLimit

/- In this section, we define the inductive limit of
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
where the X n are metric spaces and f n isometric embeddings. We do it by defining a premetric
space structure on Σ n, X n, where the predistance dist x y is obtained by pushing x and y in a
common X k using composition by the f n, and taking the distance there. This does not depend on
the choice of k as the f n are isometries. The metric space associated to this premetric space
is the desired inductive limit.-/
open Nat

variable {X : ℕ → Type u} [∀ n, MetricSpace (X n)] {f : ∀ n, X n → X (n + 1)}

/-- Predistance on the disjoint union `Σ n, X n`. -/
def inductiveLimitDist (f : ∀ n, X n → X (n + 1)) (x y : Σn, X n) : ℝ :=
  dist (leRecOn (le_max_left x.1 y.1) f x.2 : X (max x.1 y.1))
    (leRecOn (le_max_right x.1 y.1) f y.2 : X (max x.1 y.1))
#align metric.inductive_limit_dist Metric.inductiveLimitDist

/-- The predistance on the disjoint union `Σ n, X n` can be computed in any `X k` for large
enough `k`. -/
theorem inductiveLimitDist_eq_dist (I : ∀ n, Isometry (f n)) (x y : Σn, X n) (m : ℕ) :
    ∀ hx : x.1 ≤ m,
      ∀ hy : y.1 ≤ m,
        inductiveLimitDist f x y = dist (leRecOn hx f x.2 : X m) (leRecOn hy f y.2 : X m) :=
  by
  induction' m with m hm
  · intro hx hy
    have A : max x.1 y.1 = 0 :=
      by
      rw [nonpos_iff_eq_zero.1 hx, nonpos_iff_eq_zero.1 hy]
      simp
    unfold inductive_limit_dist
    congr <;> simp only [A]
  · intro hx hy
    by_cases h : max x.1 y.1 = m.succ
    · unfold inductive_limit_dist
      congr <;> simp only [h]
    · have : max x.1 y.1 ≤ succ m := by simp [hx, hy]
      have : max x.1 y.1 ≤ m := by simpa [h] using of_le_succ this
      have xm : x.1 ≤ m := le_trans (le_max_left _ _) this
      have ym : y.1 ≤ m := le_trans (le_max_right _ _) this
      rw [le_rec_on_succ xm, le_rec_on_succ ym, (I m).dist_eq]
      exact hm xm ym
#align metric.inductive_limit_dist_eq_dist Metric.inductiveLimitDist_eq_dist

/-- Premetric space structure on `Σ n, X n`.-/
def inductivePremetric (I : ∀ n, Isometry (f n)) : PseudoMetricSpace (Σn, X n)
    where
  dist := inductiveLimitDist f
  dist_self x := by simp [dist, inductive_limit_dist]
  dist_comm x y := by
    let m := max x.1 y.1
    have hx : x.1 ≤ m := le_max_left _ _
    have hy : y.1 ≤ m := le_max_right _ _
    unfold dist
    rw [inductive_limit_dist_eq_dist I x y m hx hy, inductive_limit_dist_eq_dist I y x m hy hx,
      dist_comm]
  dist_triangle x y z := by
    let m := max (max x.1 y.1) z.1
    have hx : x.1 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
    have hy : y.1 ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
    have hz : z.1 ≤ m := le_max_right _ _
    calc
      inductive_limit_dist f x z = dist (le_rec_on hx f x.2 : X m) (le_rec_on hz f z.2 : X m) :=
        inductive_limit_dist_eq_dist I x z m hx hz
      _ ≤
          dist (le_rec_on hx f x.2 : X m) (le_rec_on hy f y.2 : X m) +
            dist (le_rec_on hy f y.2 : X m) (le_rec_on hz f z.2 : X m) :=
        (dist_triangle _ _ _)
      _ = inductive_limit_dist f x y + inductive_limit_dist f y z := by
        rw [inductive_limit_dist_eq_dist I x y m hx hy, inductive_limit_dist_eq_dist I y z m hy hz]
      
#align metric.inductive_premetric Metric.inductivePremetric

attribute [local instance] inductive_premetric UniformSpace.separationSetoid

/-- The type giving the inductive limit in a metric space context. -/
def InductiveLimit (I : ∀ n, Isometry (f n)) : Type _ :=
  @UniformSpace.SeparationQuotient _ (inductivePremetric I).toUniformSpace deriving MetricSpace
#align metric.inductive_limit Metric.InductiveLimit

/-- Mapping each `X n` to the inductive limit. -/
def toInductiveLimit (I : ∀ n, Isometry (f n)) (n : ℕ) (x : X n) : Metric.InductiveLimit I :=
  Quotient.mk'' (Sigma.mk n x)
#align metric.to_inductive_limit Metric.toInductiveLimit

instance (I : ∀ n, Isometry (f n)) [Inhabited (X 0)] : Inhabited (InductiveLimit I) :=
  ⟨toInductiveLimit _ 0 default⟩

/-- The map `to_inductive_limit n` mapping `X n` to the inductive limit is an isometry. -/
theorem toInductiveLimit_isometry (I : ∀ n, Isometry (f n)) (n : ℕ) :
    Isometry (toInductiveLimit I n) :=
  Isometry.of_dist_eq fun x y =>
    by
    change inductive_limit_dist f ⟨n, x⟩ ⟨n, y⟩ = dist x y
    rw [inductive_limit_dist_eq_dist I ⟨n, x⟩ ⟨n, y⟩ n (le_refl n) (le_refl n), le_rec_on_self,
      le_rec_on_self]
#align metric.to_inductive_limit_isometry Metric.toInductiveLimit_isometry

/-- The maps `to_inductive_limit n` are compatible with the maps `f n`. -/
theorem toInductiveLimit_commute (I : ∀ n, Isometry (f n)) (n : ℕ) :
    toInductiveLimit I n.succ ∘ f n = toInductiveLimit I n :=
  by
  letI := inductive_premetric I
  funext
  simp only [comp, to_inductive_limit]
  refine' UniformSpace.SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 _)
  show inductive_limit_dist f ⟨n.succ, f n x⟩ ⟨n, x⟩ = 0
  · rw [inductive_limit_dist_eq_dist I ⟨n.succ, f n x⟩ ⟨n, x⟩ n.succ, le_rec_on_self,
      le_rec_on_succ, le_rec_on_self, dist_self]
    exact le_rfl
    exact le_rfl
    exact le_succ _
#align metric.to_inductive_limit_commute Metric.toInductiveLimit_commute

end InductiveLimit

--section
end Metric

--namespace
