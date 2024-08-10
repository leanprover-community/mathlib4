/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Group.AEStabilizer
import Mathlib.MeasureTheory.Measure.ContinuousPreimage

/-!
# A.e. stabilizer of a set is closed.

In this file we prove that the a.e.-stabilizer of a null measurable set of finite measure
is a closed set.
-/

open scoped Pointwise ENNReal
open MeasureTheory Set

variable {G X : Type*}
  [Group G] [TopologicalSpace G] [TopologicalGroup G]
  [TopologicalSpace X] [R1Space X] [MulAction G X] [ContinuousSMul G X]
  [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [SMulInvariantMeasure G X μ]
  [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

namespace MulAction

@[to_additive]
theorem isClosed_aestabilizer {s : Set X} (hs : NullMeasurableSet s μ) (htop : μ s ≠ ∞) :
    IsClosed (aestabilizer G μ s : Set G) := by
  borelize G
  simp only [aestabilizer_coe, ← preimage_smul_inv]
  set f : C(G × X, X) := .mk fun p ↦ p.1⁻¹ • p.2
  exact isClosed_setOf_preimage_ae_eq f.curry.continuous (measurePreserving_smul ·⁻¹ μ) _ hs htop

@[to_additive]
theorem forall_smul_ae_eq_of_dense {s : Set X} (hs : NullMeasurableSet s μ) (htop : μ s ≠ ∞)
    (hd : Dense {g : G | g • s =ᵐ[μ] s}) (g : G) : g • s =ᵐ[μ] s := by
  rw [← aestabilizer_coe, dense_iff_closure_eq, (isClosed_aestabilizer hs htop).closure_eq,
    eq_univ_iff_forall] at hd
  exact hd g
  
end MulAction
