module

import Mathlib.GroupTheory.Coxeter.Matrix

-- The two fork tips commute, including in the degenerate case D₂ = A₁ × A₁.
example : (CoxeterMatrix.D 2).M = !![1, 2; 2, 1] := by decide

-- D₃ is a path, with vertex 0 joined to vertices 1 and 2.
example : (CoxeterMatrix.D 3).M = !![1, 3, 3; 3, 1, 2; 3, 2, 1] := by decide

-- D₄ is a three-pronged fork centered at vertex 1.
example : (CoxeterMatrix.D 4).M =
    !![1, 3, 2, 2; 3, 1, 3, 3; 2, 3, 1, 2; 2, 3, 2, 1] := by decide

-- D₅ extends the tail while retaining two commuting fork tips.
example : (CoxeterMatrix.D 5).M =
    !![1, 3, 2, 2, 2; 3, 1, 3, 2, 2; 2, 3, 1, 3, 3; 2, 2, 3, 1, 2; 2, 2, 3, 2, 1] := by decide
