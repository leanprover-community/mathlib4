import Mathlib.MeasureTheory.Group.AEStabilizer
import Mathlib.MeasureTheory.Measure.ContinuousPreimage

open scoped Pointwise ENNReal
open MeasureTheory Set

variable {G X : Type*}
  [Group G] [TopologicalSpace G] [TopologicalGroup G]
  [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]
  {μ : Measure X} [SMulInvariantMeasure G X μ] [μ.InnerRegularCompactLTTop]

@[to_additive]
theorem MulAction.isClosed_aestabilizer [IsLocallyFiniteMeasure μ]
    {s : Set X} (hs : NullMeasurableSet s μ) (htop : μ s ≠ ∞) :
    IsClosed (aestabilizer G μ s : Set G) := by
  borelize G
  simp only [aestabilizer_coe, ← preimage_smul_inv]
  set f : C(G × X, X) := .mk fun p ↦ p.1⁻¹ • p.2
  exact isClosed_setOf_preimage_ae_eq f.curry.continuous (measurePreserving_smul ·⁻¹ μ) _ hs htop
