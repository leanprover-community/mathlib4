/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.Combinatorics.SimpleGraph.QuotientGraph
import Mathlib.Data.ZMod.Basic

/-!
# Voltage graphs on K₂: Heawood and Möbius-Kantor graphs

A voltage graph on K₂ with cyclic group Zₘ and three voltages {v₁, v₂, v₃}
gives a cubic graph on 2m vertices. Vertices are `Fin 2 × ZMod m`, and
`(0, g) ~ (1, g + vⱼ)` for each voltage.

Every cubic arc-transitive graph of small order arises this way:
* Heawood (F014A): K₂ with Z₇, voltages {0, 4, 6}, 14 vertices
* Möbius-Kantor (F016A): K₂ with Z₈, voltages {0, 1, 3}, 16 vertices

Both quotient to K₂ under the fibre projection `Prod.fst`.

## Main definitions

* `voltageGraphK2` — cubic voltage graph on K₂ with cyclic voltage group
* `heawoodVoltage` — the Heawood graph (Levi graph of the Fano plane)
* `mobiusKantorVoltage` — the Möbius-Kantor graph (GP(8,3))

## Visualizations

* [The Heawood graph](https://raw.githubusercontent.com/RaggedR/symmetric-graphs/main/lean/named_graphs/heawood-F014A.jpg) — F014A, the Levi graph of the Fano plane
* [The Möbius-Kantor graph](https://raw.githubusercontent.com/RaggedR/symmetric-graphs/main/lean/named_graphs/mobius-kantor-F016A.jpg) — F016A, the generalized Petersen graph GP(8,3)

## References

* Gross & Tucker, *Topological Graph Theory*, 1987
* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
-/

set_option linter.style.nativeDecide false

/-- A cubic voltage graph on K₂ with voltage group `ZMod m`.
Three voltages v₁, v₂, v₃ give a cubic graph on 2m vertices.
`(0, g) ~ (1, g + vⱼ)` for each voltage. -/
def voltageGraphK2 (m : ℕ) [NeZero m]
    (v₁ v₂ v₃ : ZMod m) : SimpleGraph (Fin 2 × ZMod m) where
  Adj p q :=
    (p.1 = 0 ∧ q.1 = 1 ∧ q.2 - p.2 ∈ ({v₁, v₂, v₃} : Set (ZMod m))) ∨
    (p.1 = 1 ∧ q.1 = 0 ∧ p.2 - q.2 ∈ ({v₁, v₂, v₃} : Set (ZMod m)))
  symm := by
    intro p q hpq
    rcases hpq with ⟨hp, hq, hv⟩ | ⟨hp, hq, hv⟩
    · exact Or.inr ⟨hq, hp, hv⟩
    · exact Or.inl ⟨hq, hp, hv⟩
  loopless := ⟨fun p hp => by
    rcases hp with ⟨hp, hq, _⟩ | ⟨hp, hq, _⟩ <;> simp [hp] at hq⟩

/-! ### The Heawood graph -/

/-- The **Heawood graph**: voltage graph on K₂ with Z₇ voltages {0, 4, 6}.
Levi graph of the Fano plane PG(2,2). 14 vertices, cubic, girth 6.
Sab(G₄₂, C₃) where G₄₂ = Z₇ ⋊ Z₆. -/
def heawoodVoltage : SimpleGraph (Fin 2 × ZMod 7) :=
  voltageGraphK2 7 0 4 6

instance : DecidableRel heawoodVoltage.Adj := by
  intro p q; unfold heawoodVoltage voltageGraphK2; simp only; exact instDecidableOr

/-- The Heawood graph is 3-regular. -/
theorem heawoodVoltage_regular :
    ∀ v : Fin 2 × ZMod 7,
      (Finset.univ.filter fun w => heawoodVoltage.Adj v w).card = 3 := by
  native_decide

/-- The Heawood graph has 42 directed edges (21 undirected). -/
theorem heawoodVoltage_directedEdges :
    (Finset.univ.filter fun p : (Fin 2 × ZMod 7) × (Fin 2 × ZMod 7) =>
      heawoodVoltage.Adj p.1 p.2).card = 42 := by
  native_decide

/-! ### The Möbius-Kantor graph -/

/-- The **Möbius-Kantor graph**: voltage graph on K₂ with Z₈ voltages {0, 1, 3}.
GP(8,3), the generalised Petersen graph. 16 vertices, cubic, girth 6.
Sab(GL(2,3), C₃). -/
def mobiusKantorVoltage : SimpleGraph (Fin 2 × ZMod 8) :=
  voltageGraphK2 8 0 1 3

instance : DecidableRel mobiusKantorVoltage.Adj := by
  intro p q; unfold mobiusKantorVoltage voltageGraphK2; simp only; exact instDecidableOr

/-- The Möbius-Kantor graph is 3-regular. -/
theorem mobiusKantorVoltage_regular :
    ∀ v : Fin 2 × ZMod 8,
      (Finset.univ.filter fun w => mobiusKantorVoltage.Adj v w).card = 3 := by
  native_decide

/-- The Möbius-Kantor graph has 48 directed edges (24 undirected). -/
theorem mobiusKantorVoltage_directedEdges :
    (Finset.univ.filter fun p : (Fin 2 × ZMod 8) × (Fin 2 × ZMod 8) =>
      mobiusKantorVoltage.Adj p.1 p.2).card = 48 := by
  native_decide

/-! ### Fibre quotients to K₂ -/

instance : DecidableRel (heawoodVoltage.quotientGraph
    (Prod.fst : Fin 2 × ZMod 7 → Fin 2)).Adj := by
  intro i j; unfold SimpleGraph.quotientGraph; simp only; exact instDecidableAnd

/-- The Heawood graph quotients to K₂ under the fibre projection. -/
theorem heawoodVoltage_quotient_complete :
    ∀ i j : Fin 2, i ≠ j →
    (heawoodVoltage.quotientGraph
      (Prod.fst : Fin 2 × ZMod 7 → Fin 2)).Adj i j := by
  native_decide

instance : DecidableRel (mobiusKantorVoltage.quotientGraph
    (Prod.fst : Fin 2 × ZMod 8 → Fin 2)).Adj := by
  intro i j; unfold SimpleGraph.quotientGraph; simp only; exact instDecidableAnd

/-- The Möbius-Kantor graph quotients to K₂ under the fibre projection. -/
theorem mobiusKantorVoltage_quotient_complete :
    ∀ i j : Fin 2, i ≠ j →
    (mobiusKantorVoltage.quotientGraph
      (Prod.fst : Fin 2 × ZMod 8 → Fin 2)).Adj i j := by
  native_decide
