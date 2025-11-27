import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open WeierstrassCurve Affine Point

instance : Fact (Nat.Prime 29) := by decide
instance : Fact (Nat.Prime 37) := by decide

/- A tiny example curve from Example 3.5,
D. Hankerson, A. Menezes, S. Vanstone, Guide to Elliptic Curve Cryptography, Springer, 2004 -/
abbrev curve : Affine (ZMod 29) := ⟨0, 0, 0, 4, 20⟩

def basepoint : curve.Point :=
  .some (x := 1) (y := 5) <| by
    rw [nonsingular_iff, equation_iff]
    decide

theorem valid_base_order : addOrderOf basepoint = 37 := by
  apply addOrderOf_eq_prime
  · rfl
  · simp [basepoint]
