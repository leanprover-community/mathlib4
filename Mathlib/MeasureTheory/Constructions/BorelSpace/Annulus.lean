/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Topology.MetricSpace.Annulus

/-!
# Measurability of annuli

This file proves measurability of the annuli defined in `Mathlib/Topology/MetricSpace/Annulus.lean`,
assuming `OpensMeasurableSpace` on the ambient (pseudo)(e)metric space.
-/

@[expose] public section

open Set Metric

namespace Metric

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {x : X} {r R : ℝ}

@[measurability]
lemma measurableSet_annulusIoo : MeasurableSet (Metric.annulusIoo x r R) := by
  rw [Metric.annulusIoo_eq]
  measurability

@[measurability]
lemma measurableSet_annulusIoc : MeasurableSet (Metric.annulusIoc x r R) := by
  rw [Metric.annulusIoc_eq]
  measurability

@[measurability]
lemma measurableSet_annulusIco : MeasurableSet (Metric.annulusIco x r R) := by
  rw [Metric.annulusIco_eq]
  measurability

@[measurability]
lemma measurableSet_annulusIcc : MeasurableSet (Metric.annulusIcc x r R) := by
  rw [Metric.annulusIcc_eq]
  measurability

@[measurability]
lemma measurableSet_annulusIoi : MeasurableSet (Metric.annulusIoi x r) := by
  rw [Metric.annulusIoi_eq]
  measurability

@[measurability]
lemma measurableSet_annulusIci : MeasurableSet (Metric.annulusIci x r) := by
  rw [Metric.annulusIci_eq]
  measurability

end Metric

namespace EMetric

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {x : X} {r R : ℝ≥0∞}

@[measurability]
lemma measurableSet_annulusIoo : MeasurableSet (EMetric.annulusIoo x r R) := by
  simpa [EMetric.annulusIoo] using (measurable_edist_left (x := x)).measurableSet_preimage
    (measurableSet_Ioo : MeasurableSet (Set.Ioo r R))

@[measurability]
lemma measurableSet_annulusIoc : MeasurableSet (EMetric.annulusIoc x r R) := by
  simpa [EMetric.annulusIoc] using (measurable_edist_left (x := x)).measurableSet_preimage
    (measurableSet_Ioc : MeasurableSet (Set.Ioc r R))

@[measurability]
lemma measurableSet_annulusIco : MeasurableSet (EMetric.annulusIco x r R) := by
  simpa [EMetric.annulusIco] using (measurable_edist_left (x := x)).measurableSet_preimage
    (measurableSet_Ico : MeasurableSet (Set.Ico r R))

@[measurability]
lemma measurableSet_annulusIcc : MeasurableSet (EMetric.annulusIcc x r R) := by
  simpa [EMetric.annulusIcc] using (measurable_edist_left (x := x)).measurableSet_preimage
    (measurableSet_Icc : MeasurableSet (Set.Icc r R))

@[measurability]
lemma measurableSet_annulusIoi : MeasurableSet (EMetric.annulusIoi x r) := by
  simpa [EMetric.annulusIoi] using (measurable_edist_left (x := x)).measurableSet_preimage
    (measurableSet_Ioi : MeasurableSet (Set.Ioi r))

@[measurability]
lemma measurableSet_annulusIci : MeasurableSet (EMetric.annulusIci x r) := by
  simpa [EMetric.annulusIci] using (measurable_edist_left (x := x)).measurableSet_preimage
    (measurableSet_Ici : MeasurableSet (Set.Ici r))

end EMetric
