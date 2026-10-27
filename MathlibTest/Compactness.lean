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

example : IsCompact <| closure (Icc (1 : ℝ) (3 : ℝ)) := by
  grind only [compactness, closedness]

example : closure (Icc (1 : ℝ) (3 : ℝ)) = Icc (1 : ℝ) (3 : ℝ) := by
  grind only [compactness, closedness]

example : IsCompact <| closure (Metric.closedBall (0 : Fin 5 → ℝ) 7) := by
  grind only [compactness, closedness]

example {a b c : ℝ} : IsCompact (Icc a b ∩ Ici c) := by
  grind only [compactness, closedness]

example {a b c d : ℝ} : IsCompact (closure (Icc a b ∩ Icc c d)) := by
  grind only [compactness, closedness]

example {a b : ℝ} : IsCompact (closure (Ici a ∩ Iic b)) := by
  grind only [compactness, closedness, Ici_inter_Iic]
