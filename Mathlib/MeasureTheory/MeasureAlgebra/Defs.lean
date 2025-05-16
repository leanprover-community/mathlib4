/-
Copyright (c) 2025 William Du. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Du
-/
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Order.SigmaOrderCompleteLattice

/-!
TODO: docstring
-/

open scoped ENNReal

open scoped Function -- required for scoped `on` notation

variable {α : Type*}

class MeasurableAlgebra (α : Type*) extends SigmaOrderCompleteBoundedLattice α, BooleanAlgebra α
class CMeasurableAlgebra (α : Type*) extends CSigmaOrderCompleteLattice α, BooleanAlgebra α

structure MeasureAlgebraMeasure (α : Type*) [MeasurableAlgebra α] where
  protected measureOf : α → ℝ≥0∞
  protected zero' : measureOf ⊥ = 0
  protected nonzero' : ∀ x, x ≠ ⊥ → measureOf x > 0
  protected disjoint' : ∀ s : ℕ → α, Pairwise (Disjoint on s) →
    measureOf (⨆i s) = ∑' (i : ℕ), measureOf (s i)
structure CMeasureAlgebraMeasure (α : Type*) [CMeasurableAlgebra α] where
  protected measureOf : α → ℝ≥0∞
  protected zero' : measureOf ⊥ = 0
  protected nonzero' : ∀ a : α, a ≠ ⊥ → measureOf a > 0
  protected disjoint' (s : Set α) :
    s.Countable → s.Nonempty → BddAbove s → Pairwise (Disjoint on s) →
    -- restrict the domain of measureOf
    measureOf (sSup s) = ∑' x, measureOf x

-- scoped notation "MeasureAlgebraMeasure[" mα "] " α:arg => @MeasureAlgebraMeasure α mα

instance MeasureAlgebraMeasure.instFunLike [MeasurableAlgebra α] :
  FunLike (MeasureAlgebraMeasure α) α ℝ≥0∞ where
  coe μ := μ.measureOf
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
instance CMeasureAlgebraMeasure.instFunLike [CMeasurableAlgebra α] :
  FunLike (CMeasureAlgebraMeasure α) α ℝ≥0∞ where
  coe μ := μ.measureOf
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

class MeasureAlgebra (α : Type*) extends MeasurableAlgebra α where
  measure : MeasureAlgebraMeasure α
class CMeasureAlgebra (α : Type*) extends CMeasurableAlgebra α where
  measure : CMeasureAlgebraMeasure α

namespace MeasureAlgebraMeasure

variable {m : MeasurableAlgebra α} {μ : MeasureAlgebraMeasure α}

lemma zero : μ ⊥ = 0 := by exact μ.zero'

lemma nonzero {x : α} : x ≠ ⊥ → μ x > 0 := by exact μ.nonzero' x

lemma disjoint {s : ℕ → α} :
  Pairwise (Disjoint on s) → μ (⨆i s) = ∑' i, μ (s i) := by
  exact μ.disjoint' s

end MeasureAlgebraMeasure


namespace CMeasureAlgebraMeasure

variable {m : CMeasurableAlgebra α} {μ : CMeasureAlgebraMeasure α}

lemma zero : μ ⊥ = 0 := by exact μ.zero'

lemma nonzero {x : α} : x ≠ ⊥ → μ x > 0 := by exact μ.nonzero' x

lemma disjoint {s : Set α} :
  -- restrict the domain of measureOf
  s.Countable → s.Nonempty → BddAbove s → Pairwise (Disjoint on s) → μ (sSup s) = ∑' x, μ x := by
  intro hc hn hb hpd
  exact μ.disjoint' s hc hn hb hpd

end CMeasureAlgebraMeasure
