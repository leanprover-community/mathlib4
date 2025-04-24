/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov
-/
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Sequential compacts in metric spaces

In this file we prove 2 versions of Bolzano-Weierstrass theorem for proper metric spaces.
-/

open Filter Bornology Metric
open scoped Topology

variable {X : Type*} [PseudoMetricSpace X]

variable [ProperSpace X] {s : Set X}

/-- A version of **Bolzano-Weierstrass**: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
theorem tendsto_subseq_of_frequently_bounded (hs : IsBounded s) {x : ℕ → X}
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  have hcs : IsSeqCompact (closure s) := hs.isCompact_closure.isSeqCompact
  have hu' : ∃ᶠ n in atTop, x n ∈ closure s := hx.mono fun _n hn => subset_closure hn
  hcs.subseq_of_frequently_in hu'

/-- A version of **Bolzano-Weierstrass**: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
theorem tendsto_subseq_of_bounded (hs : IsBounded s) {x : ℕ → X} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  tendsto_subseq_of_frequently_bounded hs <| Frequently.of_forall hx
