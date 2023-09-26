import Mathlib.Data.Matrix.Basic


structure CanonicalLP where
  {m n : ℕ}
  A : Matrix (Fin m) (Fin n) ℚ
  b : (Fin m) → ℚ
  c : (Fin n) → ℚ

def CanonicalLP.Admits (P : CanonicalLP) (x : (Fin P.n) → ℚ) : Prop :=
  P.A.mulVec x = P.b ∧ 0 ≤ x

example : (CanonicalLP.mk ![![1, 2, 0], ![1, -1, 4]] ![5, 3] 0).Admits ![1, 2, 1] :=
by
  constructor
  · ext i : 1
    match i with
    | 0 =>
      rfl
    | 1 =>
      rfl
  · simp [LE.le]
