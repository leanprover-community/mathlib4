module

/-
Copyright (c) 2026 Felix Pernegger,. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Order.Real

universe u v

@[expose] public section

open NNReal EReal

namespace FlowNetwork

structure PseudoFlow {V : Type u} (G : Quiver.{v} V) (u : {v : V} → {w : V} → G.Hom v w → ℝ≥0) where
  flow : {v : V} → {w : V} → G.Hom v w → ℝ≥0
  le_cap {v w : V} (e : G.Hom v w) : flow e ≤ u e

variable {V : Type u} {G : Quiver.{v} V} {u : {v : V} → {w : V} → G.Hom v w → ℝ≥0}

noncomputable def excessAt (N : PseudoFlow G u) (v : V) : EReal :=
  ∑' w : V, ∑' e : G.Hom w v, (↑(N.flow e) : EReal) -
    ∑' w : V, ∑' e : G.Hom v w, (↑(N.flow e) : EReal)

structure Flow {V : Type u} {G : Quiver.{v} V} (s t : V) (u : {v : V} → {w : V} → G.Hom v w → ℝ≥0)
    extends PseudoFlow G u where
  excessAt_zero' (v : V) :
    v ≠ s → v ≠ t → ∑' w : V, ∑' e : G.Hom v w, (↑(flow e) : EReal) =
      ∑' w : V, ∑' e : G.Hom w v, (↑(flow e) : EReal)
  excessAt_sink_noneg' :
     ∑' v : V, ∑' e : G.Hom t v, ((flow e) : EReal) ≤
      ∑' v : V, ∑' e : G.Hom v t, ((flow e) : EReal)

noncomputable def Flow.val {V : Type u} {G : Quiver.{v} V} {s t : V}
    {u : {v : V} → {w : V} → G.Hom v w → ℝ≥0} (N : Flow s t u) : ENNReal :=
  (excessAt N.toPseudoFlow t).toENNReal

variable {s t : V}

example : (⊤ : EReal) - ⊤ = ⊥ := by simp only [sub_top]

theorem Flow.excessAt_zero (N : Flow s t u) {v : V} (vs : v ≠ s) (vt : v ≠ t)
    (hv : ∑' w : V, ∑' e : G.Hom w v, (↑(N.flow e) : EReal) ≠ ⊤) :
    excessAt N.toPseudoFlow v = 0 := by
  rw [excessAt, N.excessAt_zero' v vs vt]
  exact EReal.sub_self hv (LT.lt.ne <| lt_of_lt_of_le bot_lt_zero (by positivity)).symm

end FlowNetwork
