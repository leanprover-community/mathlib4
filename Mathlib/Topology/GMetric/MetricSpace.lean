import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.GMetric.Basic

def PseudoMetricSpace.toGPseudoMetric (X : Type*) [PseudoMetricSpace X] : GPseudoMetric X ℝ where
  toFun := dist
  gdist_self := dist_self
  comm' := dist_comm
  triangle' := dist_triangle

def MetricSpace.toGMetric (X : Type*) [MetricSpace X]: GMetric X ℝ where
  toFun := dist
  gdist_self := dist_self
  comm' := dist_comm
  triangle' := dist_triangle
  eq_of_dist_eq_zero := dist_eq_zero.mp
