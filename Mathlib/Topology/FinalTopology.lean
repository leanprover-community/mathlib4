/-
Copyright (c) 2025 Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiangyu Li
-/
import Mathlib.Topology.Basic
import Mathlib.Topology.Order

/-!
# Final Topology

This file defines the final topology on a type `β`, which is the finest (largest) topology
making a given family of maps `f i : α i → β` continuous.

For a family of maps `f i : α i → β`, the final topology on `β` is the supremum of the
topologies coinduced by each `f i`. This is the categorical colimit in the category of
topological spaces, and is dual to the initial topology.

## Main Definitions

- `Topology.finalTopology`: The finest topology on `β` making a family of functions `f i`
  continuous.

## Main Statements

- `Topology.finalTopology.continuous`: Each map `f i` in the family is continuous with respect
  to the final topology.
- `Topology.finalTopology.continuous_iff`: The universal property of the final topology. A map
  `g : β → γ` is continuous if and only if `g ∘ f i` is continuous for all `i`.

## Tags

final topology, quotient topology, coinduced topology, universal property
-/

open Topology

universe u v w

/--
The **final topology** on `β` with respect to a family of functions `f i : α i → β` is the
finest topology on `β` for which each `f i` is continuous. It is the supremum of the
topologies coinduced by each function.
-/
@[reducible, simp]
def Topology.finalTopology {ι : Type u} {β : Type v} {α : ι → Type w}
    [∀ i, TopologicalSpace (α i)] (f : ∀ i, α i → β) : TopologicalSpace β :=
  ⨆ i, TopologicalSpace.coinduced (f i) (inferInstance : TopologicalSpace (α i))

namespace Topology

variable {ι : Type u} {β : Type v} {α : ι → Type w}
variable [∀ i, TopologicalSpace (α i)] {f : ∀ i, α i → β}

/-- Each generating map `f i` is continuous with respect to the final topology. -/
@[simp]
lemma finalTopology.continuous (i : ι) :
    @Continuous (α i) β _ (finalTopology f) (f i) := by
  apply continuous_iff_coinduced_le.2
  exact le_iSup (fun j ↦ TopologicalSpace.coinduced (f j) _) i

/--
**Universal Property of the Final Topology**: A map `g` from a space equipped with the final
topology is continuous if and only if its composition with each of the generating maps `f i`
is continuous.
-/
lemma finalTopology.continuous_iff {γ : Type*} [TopologicalSpace γ] {g : β → γ} :
    @Continuous β γ (finalTopology f) _ g ↔ ∀ i, Continuous (g ∘ f i) := by
  letI : TopologicalSpace β := finalTopology f
  refine ⟨?forward, ?backward⟩
  · intro hg i
    exact hg.comp (finalTopology.continuous (f := f) i)
  · intro hcomp
    have h_each :
        ∀ i, @Continuous β γ
              (TopologicalSpace.coinduced (f i) (inferInstance)) _ g := by
      intro i
      simpa using (continuous_coinduced_dom).2 (hcomp i)
    dsimp [finalTopology] at h_each ⊢
    exact (continuous_iSup_dom).2 h_each

end Topology
