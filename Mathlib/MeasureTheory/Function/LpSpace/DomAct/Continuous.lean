/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Algebra.Constructions.DomAct

/-!
# Continuity of the action of `Mᵈᵐᵃ` on `MeasureSpace.Lp E p μ`

In this file we prove that under certain 
-/

open scoped ENNReal
open DomMulAct

namespace MeasureTheory

variable {X M E : Type _}
  [TopologicalSpace X] [NormalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [Monoid M] [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [MulAction M X] [ContinuousSMul M X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopologyEither X E]
  {μ : Measure X} [SMulInvariantMeasure M X μ] [IsFiniteMeasure μ] [μ.WeaklyRegular]
  [Fact (1 ≤ p)] [hp : Fact (p ≠ ∞)]

#check ContinuousMap.toLp

-- instance : ContinuousSMul Mᵈᵐᵃ (Lp E p μ) where
--   continuous_smul := by
--     refine ((Homeomorph.prodComm _ _).trans <|
--       mkHomeomorph.prodCongr (Homeomorph.refl _)).comp_continuous_iff'.1 ?_
--     apply continuous_prod_of_dense_continuous_lipschitzWith _ 1
--       (Lp.boundedContinuousFunction_dense E μ hp.out)
--     · -- Lp.mem_boundedContinuousFunction_iff
--       rintro _ ⟨f, rfl⟩
--       have : Continuous (fun c : M ↦ f.comp ⟨(c • · : X → X), continuous_const_smul c⟩) :=
--         f.continuous_comp.comp (ContinuousMap.mk _ continuous_smul).curry.continuous
--       exact (ContinuousMap.toLp p μ ℝ).continuous.comp this
    -- · exact fun c ↦ (isometry_smul _ (mk c)).lipschitz
