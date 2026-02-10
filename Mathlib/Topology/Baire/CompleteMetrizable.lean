/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Finiteness
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# First Baire theorem

In this file we prove that a completely pseudometrizable topological space is a Baire space.
-/

@[expose] public section

open Filter Metric Set TopologicalSpace
open scoped Uniformity ENNReal

variable {X : Type*} [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X]

/-- **First Baire theorem**: a completely pseudometrizable topological space has Baire property. -/
instance (priority := 100) BaireSpace.of_completelyPseudoMetrizable : BaireSpace X := by
  let _ := upgradeIsCompletelyPseudoMetrizable X
  refine ⟨fun f ho hd => ?_⟩
  let B : ℕ → ℝ≥0∞ := fun n => 1 / 2 ^ n
  have Bpos : ∀ n, 0 < B n := fun n ↦
    ENNReal.div_pos one_ne_zero <| by finiteness
  /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closedEBall center radius` is included both in `f n` and in `closedEBall x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have : ∀ n x δ, δ ≠ 0 →
      ∃ y r, 0 < r ∧ r ≤ B (n + 1) ∧ closedEBall y r ⊆ closedEBall x δ ∩ f n := by
    intro n x δ δpos
    have : x ∈ closure (f n) := hd n x
    rcases EMetric.mem_closure_iff.1 this (δ / 2) (ENNReal.half_pos δpos) with ⟨y, ys, xy⟩
    rw [edist_comm] at xy
    obtain ⟨r, rpos, hr⟩ : ∃ r > 0, closedEBall y r ⊆ f n :=
      nhds_basis_closedEBall.mem_iff.1 (isOpen_iff_mem_nhds.1 (ho n) y ys)
    refine ⟨y, min (min (δ / 2) r) (B (n + 1)), ?_, ?_, fun z hz => ⟨?_, ?_⟩⟩
    · show 0 < min (min (δ / 2) r) (B (n + 1))
      exact lt_min (lt_min (ENNReal.half_pos δpos) rpos) (Bpos (n + 1))
    · show min (min (δ / 2) r) (B (n + 1)) ≤ B (n + 1)
      exact min_le_right _ _
    · show z ∈ closedEBall x δ
      calc
        edist z x ≤ edist z y + edist y x := edist_triangle _ _ _
        _ ≤ min (min (δ / 2) r) (B (n + 1)) + δ / 2 := add_le_add hz (le_of_lt xy)
        _ ≤ δ / 2 + δ / 2 := (add_le_add (le_trans (min_le_left _ _) (min_le_left _ _)) le_rfl)
        _ = δ := ENNReal.add_halves δ
    show z ∈ f n
    exact hr (calc
      edist z y ≤ min (min (δ / 2) r) (B (n + 1)) := hz
      _ ≤ r := le_trans (min_le_left _ _) (min_le_right _ _))
  choose! center radius Hpos HB Hball using this
  refine fun x => (mem_closure_iff_nhds_basis nhds_basis_closedEBall).2 fun ε εpos => ?_
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x` belonging to all
    `f n`. For this, we construct inductively a sequence `F n = (c n, r n)` such that the closed
    ball `closedEBall (c n) (r n)` is included in the previous ball and in `f n`, and such that
    `r n` is small enough to ensure that `c n` is a Cauchy sequence. Then `c n` converges to a
    limit which belongs to all the `f n`. -/
  let F : ℕ → X × ℝ≥0∞ := fun n =>
    Nat.recOn n (Prod.mk x (min ε (B 0))) fun n p => Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n => (F n).1
  let r : ℕ → ℝ≥0∞ := fun n => (F n).2
  have rpos : ∀ n, 0 < r n := by
    intro n
    induction n with
    | zero => exact lt_min εpos (Bpos 0)
    | succ n hn => exact Hpos n (c n) (r n) hn.ne'
  have r0 : ∀ n, r n ≠ 0 := fun n => (rpos n).ne'
  have rB : ∀ n, r n ≤ B n := by
    intro n
    cases n with
    | zero => exact min_le_right _ _
    | succ n => exact HB n (c n) (r n) (r0 n)
  have incl : ∀ n, closedEBall (c (n + 1)) (r (n + 1)) ⊆ closedEBall (c n) (r n) ∩ f n :=
    fun n => Hball n (c n) (r n) (r0 n)
  have cdist : ∀ n, edist (c n) (c (n + 1)) ≤ B n := by
    intro n
    rw [edist_comm]
    have A : c (n + 1) ∈ closedEBall (c (n + 1)) (r (n + 1)) := mem_closedEBall_self
    have I :=
      calc
        closedEBall (c (n + 1)) (r (n + 1)) ⊆ closedEBall (c n) (r n) :=
          Subset.trans (incl n) inter_subset_left
        _ ⊆ closedEBall (c n) (B n) := closedEBall_subset_closedEBall (rB n)
    exact I A
  have : CauchySeq c := cauchySeq_of_edist_le_geometric_two _ ENNReal.one_ne_top cdist
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y
  simp only [Set.mem_iInter]
  have I : ∀ n, ∀ m ≥ n, closedEBall (c m) (r m) ⊆ closedEBall (c n) (r n) := by
    intro n
    refine Nat.le_induction ?_ fun m _ h => ?_
    · exact Subset.refl _
    · exact Subset.trans (incl m) (Subset.trans inter_subset_left h)
  have yball : ∀ n, y ∈ closedEBall (c n) (r n) := by
    intro n
    refine isClosed_closedEBall.mem_of_tendsto ylim ?_
    refine (Filter.eventually_ge_atTop n).mono fun m hm => ?_
    exact I n m hm mem_closedEBall_self
  constructor
  · show ∀ n, y ∈ f n
    intro n
    have : closedEBall (c (n + 1)) (r (n + 1)) ⊆ f n :=
      Subset.trans (incl n) inter_subset_right
    exact this (yball (n + 1))
  change edist y x ≤ ε
  exact le_trans (yball 0) (min_le_left _ _)
