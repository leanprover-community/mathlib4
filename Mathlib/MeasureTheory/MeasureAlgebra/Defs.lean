import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Order.SigmaOrderCompleteLattice

open scoped ENNReal

open scoped Function -- required for scoped `on` notation

variable {α : Type*}

class MeasurableAlgebra (α : Type*) extends SigmaOrderCompleteLattice α, BooleanAlgebra α

structure MeasureAlgebraMeasure (α : Type*) [MeasurableAlgebra α] where
  protected measureOf : α → ℝ≥0∞
  protected zero : measureOf ⊥ = 0
  protected nonzero : ∀ s, s ≠ ⊥ → measureOf s > 0
  protected disjoint : ∀ s : ℕ → α, Pairwise (Disjoint on s) →
    measureOf (⨆i s) = ∑' i, measureOf (s i)

-- scoped notation "MeasureAlgebraMeasure[" mα "] " α:arg => @MeasureAlgebraMeasure α mα

instance MeasureAlgebraMeasure.instFunLike [MeasurableAlgebra α] :
  FunLike (MeasureAlgebraMeasure α) α ℝ≥0∞ where
  coe μ := μ.measureOf
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

class MeasureAlgebra (α : Type*) extends MeasurableAlgebra α where
  measure : MeasureAlgebraMeasure α
