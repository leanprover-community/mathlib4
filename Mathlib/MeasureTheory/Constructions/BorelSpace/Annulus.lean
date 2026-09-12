/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.MetricSpace.Annulus

/-!
# Measurability of annuli

This file proves measurability of the annuli defined in `Mathlib/Topology/MetricSpace/Annulus.lean`,
assuming `OpensMeasurableSpace` on the ambient (pseudo)(e)metric space.
-/

@[expose] public section

open Set Metric
open scoped NNReal ENNReal

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

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {x : X} {r R : ℝ≥0∞}

@[measurability]
lemma measurableSet_eannulusIoo : MeasurableSet (Metric.eannulusIoo x r R) := by
  simpa [Metric.eannulusIoo_eq_preimage] using
    (measurableSet_Ioo : MeasurableSet (Set.Ioo r R)).preimage (measurable_edist_left (x := x))

@[measurability]
lemma measurableSet_eannulusIoc : MeasurableSet (Metric.eannulusIoc x r R) := by
  simpa [Metric.eannulusIoc_eq_preimage] using
    (measurableSet_Ioc : MeasurableSet (Set.Ioc r R)).preimage (measurable_edist_left (x := x))

@[measurability]
lemma measurableSet_eannulusIco : MeasurableSet (Metric.eannulusIco x r R) := by
  simpa [Metric.eannulusIco_eq_preimage] using
    (measurableSet_Ico : MeasurableSet (Set.Ico r R)).preimage (measurable_edist_left (x := x))

@[measurability]
lemma measurableSet_eannulusIcc : MeasurableSet (Metric.eannulusIcc x r R) := by
  simpa [Metric.eannulusIcc_eq_preimage] using
    (measurableSet_Icc : MeasurableSet (Set.Icc r R)).preimage (measurable_edist_left (x := x))

@[measurability]
lemma measurableSet_eannulusIoi : MeasurableSet (Metric.eannulusIoi x r) := by
  simpa [Metric.eannulusIoi_eq_preimage] using
    (measurableSet_Ioi : MeasurableSet (Set.Ioi r)).preimage (measurable_edist_left (x := x))

@[measurability]
lemma measurableSet_eannulusIci : MeasurableSet (Metric.eannulusIci x r) := by
  simpa [Metric.eannulusIci_eq_preimage] using
    (measurableSet_Ici : MeasurableSet (Set.Ici r)).preimage (measurable_edist_left (x := x))

end Metric
