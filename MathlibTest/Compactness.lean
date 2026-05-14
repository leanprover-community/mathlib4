module

public import Mathlib

open Set MeasureTheory

example : IsCompact <| Icc (1 : ℝ) (3 : ℝ) := by compactness

example : IsCompact <| Metric.closedBall (0 : Fin 5 → ℝ) 7 := by compactness

example {a b c d : ℝ} : IsCompact (Icc a b ∩ Icc c d) := by compactness

example : IsCompact {0} := by compactness

example {a b c : ℝ} : IsCompact {a, b, c} := by compactness

example {a b c d e : ℝ} : IsCompact {a, b, c, d, e} := by compactness

example {s : Set ℝ} (h : s.Finite) : IsCompact s := by compactness

example : IsCompact <| closure (Ioo (1 : ℝ) (3 : ℝ)) := by
  grind only [compactness, closedness]

-- fails due to https://github.com/leanprover/lean4/issues/13725
-- succeeds (noisily) when adding `IsClosed.closure_eq`
-- example : IsCompact <| closure (Icc (1 : ℝ) (3 : ℝ)) := by
--   grind only [compactness, closedness]

example : closure (Icc (1 : ℝ) (3 : ℝ)) = Icc (1 : ℝ) (3 : ℝ) := by
  grind only [compactness, closedness]

example : IsCompact <| closure (uIoc (1 : ℝ) (3 : ℝ)) := by
  grind only [compactness, closedness]

example : IsCompact <| closure (Metric.ball (0 : Fin 5 → ℝ) 7) := by
  grind only [compactness, closedness]

-- fails due to https://github.com/leanprover/lean4/issues/13725
-- succeeds (noisily) when adding `IsClosed.closure_eq`
-- example : IsCompact <| closure (Metric.closedBall (0 : Fin 5 → ℝ) 7) := by
--   grind only [compactness, closedness]

example (x : EuclideanSpace ℝ (Fin 4)) : IsCompact <| closure (Metric.ball x 7) := by
  grind only [compactness, closedness]

set_option maxHeartbeats 10000 in
example {a b c : ℝ} : IsCompact (Icc a b ∩ Ici c ∩ Iic b ∩ Ici c ∩ Icc a b ∩ Ici c ∩ Icc a b ∩
    Ici c ∩ Icc a b ∩ Ici c ∩ Icc a b ∩ Ici c ∩ Icc a b ∩ Ici c) := by
  grind (ematch := 30) (gen := 30) only [compactness, closedness]

example {a b c : ℝ} : IsCompact (Icc a b ∩ Ici c) := by
  grind only [compactness, closedness]

-- fails due to https://github.com/leanprover/lean4/issues/13725
-- succeeds (noisily) when adding `IsClosed.closure_eq`
-- example {a b c d : ℝ} : IsCompact (closure (Icc a b ∩ Icc c d)) := by
--   grind only [compactness, closedness]

-- fails due to https://github.com/leanprover/lean4/issues/13725
-- succeeds (noisily) when adding `IsClosed.closure_eq`
-- example {a b : ℝ} : IsCompact (closure (Ici a ∩ Iic b)) := by
--   grind only [compactness, closedness, Ici_inter_Iic]
