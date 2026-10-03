/-
Copyright (c) 2026 Lior Horesh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Horesh
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# `Finset` version of the metric ball in a simple graph

This module introduces `SimpleGraph.ballFinset`, the `Finset` companion
to `SimpleGraph.ball` for graphs with a `Fintype` vertex set, together
with the basic identities `ballFinset_zero` and `ballFinset_one`.

`SimpleGraph.ball` is the *open* metric ball `{u | edist u c < r}` and
is indexed by `ℕ∞`; `ballFinset` is typed `ℕ → Finset V` for ergonomics
at cardinality-facing call sites.  The classical closed-ball
cardinality at radius `r`, `|{u | edist u c ≤ r}|`, corresponds to
`|ballFinset v (r + 1)|` in this setup.

## Main definitions

* `SimpleGraph.ballFinset`: the `Finset` version of `SimpleGraph.ball`
  on graphs with a `Fintype` vertex set.

## Main results

* `SimpleGraph.mem_ballFinset`: membership in `ballFinset`.
* `SimpleGraph.ballFinset_zero`: `ballFinset v 0 = ∅`.
* `SimpleGraph.ballFinset_one`: `ballFinset v 1 = {v}`.

## Tags

graph metric, ball, cardinality
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [Fintype V]

/-- `Finset` version of `SimpleGraph.ball`.  On graphs with a `Fintype`
vertex set every set of vertices is finite, so the open metric ball
coerces to a `Finset`.  The radius is typed `ℕ` for ergonomics at
cardinality-facing call sites; `SimpleGraph.ball` itself takes `ℕ∞`. -/
noncomputable def ballFinset (c : V) (r : ℕ) : Finset V :=
  (G.ball c r).toFinite.toFinset

@[simp] lemma mem_ballFinset {c v : V} {r : ℕ} :
    v ∈ G.ballFinset c r ↔ G.edist v c < (r : ℕ∞) := by
  simp [ballFinset]

/-- The radius-`0` ball is empty. -/
@[simp] lemma ballFinset_zero (c : V) : G.ballFinset c 0 = ∅ := by
  ext v
  simp [ballFinset, ball_zero]

/-- The radius-`1` ball is the singleton `{c}`. -/
@[simp] lemma ballFinset_one (c : V) : G.ballFinset c 1 = {c} := by
  ext v
  simp [ballFinset, ball_one]

end SimpleGraph
