/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Data.ENNReal.Lemmas
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.EMetricSpace.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Product of pseudometric spaces

This file constructs the infinity distance on finite products of pseudometric spaces.
-/

open Bornology Filter Metric Set
open scoped NNReal Topology

variable {α β : Type*} [PseudoMetricSpace α]

open Finset

variable {X : β → Type*} [Fintype β] [∀ b, PseudoMetricSpace (X b)]

/-- A finite product of pseudometric spaces is a pseudometric space, with the sup distance. -/
instance pseudoMetricSpacePi : PseudoMetricSpace (∀ b, X b) := by
  /- we construct the instance from the pseudoemetric space instance to avoid checking again that
    the uniformity is the same as the product uniformity, but we register nevertheless a nice
    formula for the distance -/
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g : ∀ b, X b => ((sup univ fun b => nndist (f b) (g b) : ℝ≥0) : ℝ))
    (fun f g => NNReal.zero_le_coe)
    (fun f g => by simp [edist_pi_def])
  refine i.replaceBornology fun s => ?_
  simp only [isBounded_iff_eventually, ← forall_isBounded_image_eval_iff,
    forall_mem_image, ← Filter.eventually_all, @dist_nndist (X _)]
  refine eventually_congr ((eventually_ge_atTop 0).mono fun C hC ↦ ?_)
  lift C to ℝ≥0 using hC
  refine ⟨fun H x hx y hy ↦ NNReal.coe_le_coe.2 <| Finset.sup_le fun b _ ↦ H b hx hy,
    fun H b x hx y hy ↦ NNReal.coe_le_coe.2 ?_⟩
  simpa only using Finset.sup_le_iff.1 (NNReal.coe_le_coe.1 <| H hx hy) b (Finset.mem_univ b)

lemma nndist_pi_def (f g : ∀ b, X b) : nndist f g = sup univ fun b => nndist (f b) (g b) := rfl

lemma dist_pi_def (f g : ∀ b, X b) : dist f g = (sup univ fun b => nndist (f b) (g b) : ℝ≥0) := rfl

lemma nndist_pi_le_iff {f g : ∀ b, X b} {r : ℝ≥0} :
    nndist f g ≤ r ↔ ∀ b, nndist (f b) (g b) ≤ r := by simp [nndist_pi_def]

lemma nndist_pi_lt_iff {f g : ∀ b, X b} {r : ℝ≥0} (hr : 0 < r) :
    nndist f g < r ↔ ∀ b, nndist (f b) (g b) < r := by
  simp [nndist_pi_def, Finset.sup_lt_iff hr]

lemma nndist_pi_eq_iff {f g : ∀ b, X b} {r : ℝ≥0} (hr : 0 < r) :
    nndist f g = r ↔ (∃ i, nndist (f i) (g i) = r) ∧ ∀ b, nndist (f b) (g b) ≤ r := by
  rw [eq_iff_le_not_lt, nndist_pi_lt_iff hr, nndist_pi_le_iff, not_forall, and_comm]
  simp_rw [not_lt, and_congr_left_iff, le_antisymm_iff]
  intro h
  refine exists_congr fun b => ?_
  apply (and_iff_right <| h _).symm

lemma dist_pi_lt_iff {f g : ∀ b, X b} {r : ℝ} (hr : 0 < r) :
    dist f g < r ↔ ∀ b, dist (f b) (g b) < r := by
  lift r to ℝ≥0 using hr.le
  exact nndist_pi_lt_iff hr

lemma dist_pi_le_iff {f g : ∀ b, X b} {r : ℝ} (hr : 0 ≤ r) :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r := by
  lift r to ℝ≥0 using hr
  exact nndist_pi_le_iff

lemma dist_pi_eq_iff {f g : ∀ b, X b} {r : ℝ} (hr : 0 < r) :
    dist f g = r ↔ (∃ i, dist (f i) (g i) = r) ∧ ∀ b, dist (f b) (g b) ≤ r := by
  lift r to ℝ≥0 using hr.le
  simp_rw [← coe_nndist, NNReal.coe_inj, nndist_pi_eq_iff hr, NNReal.coe_le_coe]

lemma dist_pi_le_iff' [Nonempty β] {f g : ∀ b, X b} {r : ℝ} :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r := by
  by_cases hr : 0 ≤ r
  · exact dist_pi_le_iff hr
  · exact iff_of_false (fun h => hr <| dist_nonneg.trans h) fun h =>
      hr <| dist_nonneg.trans <| h <| Classical.arbitrary _

lemma dist_pi_const_le (a b : α) : (dist (fun _ : β => a) fun _ => b) ≤ dist a b :=
  (dist_pi_le_iff dist_nonneg).2 fun _ => le_rfl

lemma nndist_pi_const_le (a b : α) : (nndist (fun _ : β => a) fun _ => b) ≤ nndist a b :=
  nndist_pi_le_iff.2 fun _ => le_rfl

@[simp]
lemma dist_pi_const [Nonempty β] (a b : α) : (dist (fun _ : β => a) fun _ => b) = dist a b := by
  simpa only [dist_edist] using congr_arg ENNReal.toReal (edist_pi_const a b)

@[simp]
lemma nndist_pi_const [Nonempty β] (a b : α) : (nndist (fun _ : β => a) fun _ => b) = nndist a b :=
  NNReal.eq <| dist_pi_const a b

lemma nndist_le_pi_nndist (f g : ∀ b, X b) (b : β) : nndist (f b) (g b) ≤ nndist f g := by
  rw [← ENNReal.coe_le_coe, ← edist_nndist, ← edist_nndist]
  exact edist_le_pi_edist f g b

lemma dist_le_pi_dist (f g : ∀ b, X b) (b : β) : dist (f b) (g b) ≤ dist f g := by
  simp only [dist_nndist, NNReal.coe_le_coe, nndist_le_pi_nndist f g b]

/-- An open ball in a product space is a product of open balls. See also `ball_pi'`
for a version assuming `Nonempty β` instead of `0 < r`. -/
lemma ball_pi (x : ∀ b, X b) {r : ℝ} (hr : 0 < r) :
    ball x r = Set.pi univ fun b => ball (x b) r := by
  ext p
  simp [dist_pi_lt_iff hr]

/-- An open ball in a product space is a product of open balls. See also `ball_pi`
for a version assuming `0 < r` instead of `Nonempty β`. -/
lemma ball_pi' [Nonempty β] (x : ∀ b, X b) (r : ℝ) :
    ball x r = Set.pi univ fun b => ball (x b) r :=
  (lt_or_ge 0 r).elim (ball_pi x) fun hr => by simp [ball_eq_empty.2 hr]

/-- A closed ball in a product space is a product of closed balls. See also `closedBall_pi'`
for a version assuming `Nonempty β` instead of `0 ≤ r`. -/
lemma closedBall_pi (x : ∀ b, X b) {r : ℝ} (hr : 0 ≤ r) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r := by
  ext p
  simp [dist_pi_le_iff hr]

/-- A closed ball in a product space is a product of closed balls. See also `closedBall_pi`
for a version assuming `0 ≤ r` instead of `Nonempty β`. -/
lemma closedBall_pi' [Nonempty β] (x : ∀ b, X b) (r : ℝ) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r :=
  (le_or_gt 0 r).elim (closedBall_pi x) fun hr => by simp [closedBall_eq_empty.2 hr]

/-- A sphere in a product space is a union of spheres on each component restricted to the closed
ball. -/
lemma sphere_pi (x : ∀ b, X b) {r : ℝ} (h : 0 < r ∨ Nonempty β) :
    sphere x r = (⋃ i : β, Function.eval i ⁻¹' sphere (x i) r) ∩ closedBall x r := by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · rw [closedBall_eq_sphere_of_nonpos le_rfl, eq_comm, Set.inter_eq_right]
    letI := h.resolve_left (lt_irrefl _)
    inhabit β
    refine subset_iUnion_of_subset default ?_
    intro x hx
    replace hx := hx.le
    rw [dist_pi_le_iff le_rfl] at hx
    exact le_antisymm (hx default) dist_nonneg
  · ext
    simp [dist_pi_eq_iff hr, dist_pi_le_iff hr.le]

@[simp]
lemma Fin.nndist_insertNth_insertNth {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : ∀ j, α (i.succAbove j)) :
    nndist (i.insertNth x f) (i.insertNth y g) = max (nndist x y) (nndist f g) :=
  eq_of_forall_ge_iff fun c => by simp [nndist_pi_le_iff, i.forall_iff_succAbove]

@[simp]
lemma Fin.dist_insertNth_insertNth {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : ∀ j, α (i.succAbove j)) :
    dist (i.insertNth x f) (i.insertNth y g) = max (dist x y) (dist f g) := by
  simp only [dist_nndist, Fin.nndist_insertNth_insertNth, NNReal.coe_max]
